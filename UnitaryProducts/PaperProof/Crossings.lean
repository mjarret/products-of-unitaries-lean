/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UniformConsequences

/-! # Transfer through eigenvalue crossings -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
open Set Real Filter
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 5: Proposition 2.4 removes the endpoint half-step phases when the
orthogonal endpoint projectors commute with the Hamiltonian. -/
theorem commuting_endpoint_transfer (H : ℝ → 𝕄) (T : ℕ) (U P Q : 𝕄)
    (hH0 : (H 0).IsHermitian) (hH1 : (H 1).IsHermitian)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1)) :
    |‖(1 - Q) * (unitProduct H T).1 * P‖ - ‖(1 - Q) * U * P‖| ≤
      ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U‖ := by
  have htransfer := prop_transfer (U := U) (W := (unitProduct H T).1)
    hP hQ hP hQ (evol_mem_unitary hH1 (1 / 2))
    (evol_mem_unitary hH0 (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simpa only [sub_self, norm_zero, add_zero, mul_zero] using htransfer

/-- **Example 5.3** (`ex:crossings`): the leakage inequality and the explicit
`1/T` comparison from (4.6). Only the endpoint projectors are needed, so the
statement also covers the paper's continuous projector family at a crossing. -/
theorem ex_crossings [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U P : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, IsStarProjection (P s))
    (hPc : ∀ s ∈ Icc (0 : ℝ) 1, Commute (P s) (H s)) :
    let V := evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    |‖(1 - P 1) * (unitProduct H T).1 * P 0‖ - ‖(1 - P 1) * U T * P 0‖| ≤
      ‖V - U T‖ ∧
    ‖V - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
      (1 / 24 + frameMult w) * L + (c₁ + 2 * deriv frameMult w) * unitSupNorm Hd ^ 2) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  refine ⟨commuting_endpoint_transfer H T (U T) (P 0) (P 1)
    (hH 0 hzero) (hH 1 hone) (hP 0 hzero) (hP 1 hone) (hPc 0 hzero) (hPc 1 hone), ?_⟩
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hbound := unit_steps_endpoint_bounds hT H Hd U V hH hd hlip hw hwidth hU hV
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simpa only [heV, div_self ht.ne', one_smul, hhalf] using hbound

/-- The final implication in Section 5: a continuous leakage tending to zero
transfers through an operator comparison tending to zero. The cited
Avron--Elgart theorem supplies the continuous limit, not a new project axiom. -/
theorem crossing_leakage_tendsto_zero {a b e : ℕ → ℝ}
    (hbound : ∀ᶠ T in atTop, |a T - b T| ≤ e T)
    (hb : Tendsto b atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  have hdiff : Tendsto (fun T ↦ a T - b T) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr
      (squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ abs_nonneg _)) hbound he)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hb

/-- Section 5's opening to the crossing example: two diagonal eigenvalues cross
while their rank-one coordinate projectors extend continuously through the crossing. -/
theorem diagonal_crossing_witness :
    let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun s ↦ (s - 1 / 2) • Matrix.diagonal ![1, -1]
    Continuous H ∧ Continuous (fun _ : ℝ ↦ P) ∧ IsStarProjection P ∧
      (∀ s, (H s).IsHermitian ∧ Commute (H s) P ∧
        H s * P = (s - 1 / 2) • P ∧
        H s * (1 - P) = -(s - 1 / 2) • (1 - P)) ∧ H (1 / 2) = 0 := by
  intro P H
  have hdiag : (Matrix.diagonal ![(1 : ℂ), -1]).IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    change star ![(1 : ℂ), -1] = ![1, -1]
    ext i
    fin_cases i <;> simp
  have hP : IsStarProjection P := by
    constructor
    · change P * P = P
      simp [P, Matrix.diagonal_mul_diagonal]
    · change star P = P
      simp [P, Matrix.star_eq_conjTranspose]
  refine ⟨(continuous_id.sub continuous_const).smul continuous_const,
    continuous_const, hP, ?_, ?_⟩
  · intro s
    refine ⟨UnitaryProducts.Separation.isHermitian_real_smul hdiag _, ?_, ?_, ?_⟩
    all_goals ext i j; fin_cases i <;> fin_cases j <;>
      simp [H, P, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  · simp [H]


end UnitaryProducts.PaperProof
