/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Algebra.Order.Round
public import UnitaryProducts.Evolution.RegulatedComparison
public import UnitaryProducts.Evolution.RoundedClockEvolution
public import UnitaryProducts.Spectral.SinTheta
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Mathematical details in the prose of Section 2

## Declarations

- `exists_uniform_hermitian_step_approximation`
- `exists_uniform_step_approximation`
- `real_coefficient_apply`
- `regulated_real_coefficient`
- `rounded_clock_tie`
-/

@[expose] public section

noncomputable section
open scoped Matrix.Norms.L2Operator Topology InnerProductSpace
open Complex Set Filter MeasureTheory Matrix

namespace UnitaryProducts.Prose

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2, after Definition 2.1: a global step approximation, including every partition
node. The times are `a + switchTime τ j`; their lengths are positive, and the last is `b`.
The matrices on the open pieces are samples of the original family. -/
theorem exists_uniform_step_approximation {H : ℝ → 𝕄} {a b ε : ℝ}
    (hab : a ≤ b) (hH : Regulated H a b) (hε : 0 < ε) :
    ∃ (m : ℕ) (τ c : ℕ → ℝ) (K : ℝ → 𝕄),
      (∀ j, 0 < τ j) ∧ a + switchTime τ m = b ∧
      (∀ j < m, c j ∈ Icc a b) ∧
      (∀ j < m, ∀ t ∈ Ioo (a + switchTime τ j) (a + switchTime τ (j + 1)),
        K t = H (c j)) ∧
      (∀ j ≤ m, K (a + switchTime τ j) = H (a + switchTime τ j)) ∧
      (∀ t ∈ Icc a b, ‖H t - K t‖ < ε) := by
  classical
  obtain ⟨m, τ, c, hτ, hend, hc, he⟩ :=
    exists_pieces_of_regulated (sub_nonneg.mpr hab) hH.translate_to_zero (half_pos hε)
  let P := fun t j ↦ j < m ∧ t - a ∈ Ioo (switchTime τ j) (switchTime τ (j + 1))
  let K : ℝ → 𝕄 := fun t ↦ if h : ∃ j, P t j then H (c h.choose + a) else H t
  refine ⟨m, τ, fun j ↦ c j + a, K, hτ, by linarith, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hlo, hhi⟩ := hc j hj
    exact ⟨by linarith, by linarith⟩
  · intro j hj t ht
    have ht' : t - a ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hp : ∃ i, P t i := ⟨j, hj, ht'⟩
    have hi : hp.choose = j := piece_index_unique (fun i ↦ (hτ i).le) hp.choose_spec.2 ht'
    simp only [K, dif_pos hp, hi]
  · intro j hj
    have hn : ¬ ∃ i, P (a + switchTime τ j) i := by
      rintro ⟨i, -, hi⟩
      simp only [add_sub_cancel_left] at hi
      have hm := switchTime_mono (fun k ↦ (hτ k).le)
      by_cases hij : j ≤ i
      · exact (not_lt_of_ge (hm hij)) hi.1
      · exact (not_lt_of_ge (hm (by omega : i + 1 ≤ j))) hi.2
    exact dif_neg hn
  · intro t ht
    by_cases hp : ∃ j, P t j
    · rw [show K t = H (c hp.choose + a) from dif_pos hp]
      have h := he hp.choose hp.choose_spec.1 (t - a) hp.choose_spec.2
      simp only [sub_add_cancel] at h
      exact h.trans_lt (by linarith)
    · rw [show K t = H t from dif_neg hp, sub_self, norm_zero]
      exact hε


/-- Section 2, existence paragraph after Theorem 2.2: the real linear coefficient
`X ↦ -i G(t) X`, as a continuous linear operator, has the required one-sided limits. -/
theorem regulated_real_coefficient {G : ℝ → 𝕄} {a b : ℝ} (hG : Regulated G a b) :
    let A := fun t ↦ ContinuousLinearMap.mul ℝ 𝕄 (-I • G t)
    (∀ t ∈ Ico a b, ∃ L : 𝕄 →L[ℝ] 𝕄, Tendsto A (𝓝[>] t) (𝓝 L)) ∧
    (∀ t ∈ Ioc a b, ∃ L : 𝕄 →L[ℝ] 𝕄, Tendsto A (𝓝[<] t) (𝓝 L)) := by
  have hc : Continuous (fun X : 𝕄 ↦ ContinuousLinearMap.mul ℝ 𝕄 (-I • X)) :=
    (ContinuousLinearMap.mul ℝ 𝕄).continuous.comp (continuous_id.const_smul (-I))
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hG.1 t ht
    exact ⟨_, hc.continuousAt.tendsto.comp hL⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hG.2 t ht
    exact ⟨_, hc.continuousAt.tendsto.comp hL⟩

/-- Section 2, rounded-clock paragraph: at either sign of half-integer, ties are resolved upward. -/
theorem rounded_clock_tie (z : ℤ) : ⌊(z : ℝ) + 1 / 2 + 1 / 2⌋ = z + 1 := by
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith


/-- Section 2, after Definition 2.1: the endpoint-completed approximation is a Hermitian
family when the original is. Partition nodes and the open pieces together cover `[a,b]`. -/
theorem exists_uniform_hermitian_step_approximation {H : ℝ → 𝕄} {a b ε : ℝ}
    (hab : a ≤ b) (hH : Regulated H a b)
    (hHh : ∀ t ∈ Icc a b, (H t).IsHermitian) (hε : 0 < ε) :
    ∃ (m : ℕ) (τ c : ℕ → ℝ) (K : ℝ → 𝕄),
      (∀ j, 0 < τ j) ∧ a + switchTime τ m = b ∧
      (∀ j < m, c j ∈ Icc a b) ∧
      (∀ j < m, ∀ t ∈ Ioo (a + switchTime τ j) (a + switchTime τ (j + 1)),
        K t = H (c j)) ∧
      (∀ t ∈ Icc a b, (K t).IsHermitian) ∧
      (∀ t ∈ Icc a b, ‖H t - K t‖ < ε) := by
  obtain ⟨m, τ, c, K, hτ, hend, hc, hp, hn, he⟩ :=
    exists_uniform_step_approximation hab hH hε
  refine ⟨m, τ, c, K, hτ, hend, hc, hp, ?_, he⟩
  intro t ht
  obtain ⟨j, hj, hjt⟩ | ⟨j, hj, hjt⟩ := checkpoint_or_mem_piece (τ := τ) m
    (t := t - a) (by constructor <;> linarith [ht.1, ht.2])
  · have htj : t = a + switchTime τ j := by linarith
    rw [htj, hn j hj]
    exact hHh _ (htj ▸ ht)
  · rw [hp j hj t ⟨by linarith [hjt.1], by linarith [hjt.2]⟩]
    exact hHh _ (hc j hj)

/-- Section 2, existence paragraph: the continuous real linear operator in
`regulated_real_coefficient` acts by exactly the coefficient of the Schrödinger equation. -/
theorem real_coefficient_apply (G X : 𝕄) :
    ContinuousLinearMap.mul ℝ 𝕄 (-I • G) X = -I • (G * X) := by
  simp only [ContinuousLinearMap.mul_apply', smul_mul_assoc]


end UnitaryProducts.Prose
