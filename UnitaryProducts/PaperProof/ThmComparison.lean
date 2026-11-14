/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Prose.LocalSteps
public import UnitaryProducts.Prose.Preliminaries
public import UnitaryProducts.PaperProof.Steps2

/-!
# The paper's proof of comparison of evolutions

## Declarations

- `thm_comparison`
- `duhamel_integral_identity`
- `duhamel_bound`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Theorem 2.2** (`thm:comparison`): Duhamel's formula integrated by parts
against a piece family, with every jump included.
The generators are regulated, and each piece derivative agrees off a countable
set with a regulated representative. The residual identity (2.2) is `hYd`;
its interval integrability follows inside the proof from those hypotheses.
The integration and telescoping argument is `comparison_with_jumps` in
`Evolution/RegulatedComparison.lean`; this head only regroups the correction terms.
Separate Hermiticity hypotheses are unnecessary once unitary evolutions are given. -/
theorem thm_comparison {a b : ℝ}  -- Easier-to-read statement (v1.1.0): https://github.com/mjarret/products-of-unitaries-lean/blob/v1.1.0/UnitaryProducts/PaperProof/ThmComparison.lean#L43
    (m : ℕ) (p : ℕ → ℝ) (hp : Monotone p) (ha : p 0 = a) (hb : p (m + 1) = b)
    (K G U V R : ℝ → 𝕄) (Y : ℕ → ℝ → 𝕄) (S : Set ℝ) (hS : S.Countable)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b)
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hYreg : ∀ j ≤ m, ∃ Yd : ℝ → 𝕄, IsRegulated Yd (p j) (p (j + 1)) ∧
      ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S → HasDerivAt (Y j) (Yd t) t)
    (hYc : ∀ j ≤ m, ContinuousOn (Y j) (Icc (p j) (p (j + 1))))
    (hYd : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S →
      HasDerivAt (Y j) (K t - G t - I • (K t * Y j t - Y j t * G t) - R t) t) :
    star (U b) * V b - 1 = (∫ t in a..b, I • (star (U t) * R t * V t)) +
      I • (star (U b) * Y m b * V b) - I • Y 0 a -
      I • ∑ j ∈ Finset.range m,
        star (U (p (j + 1))) * (Y (j + 1) (p (j + 1)) - Y j (p (j + 1))) *
          V (p (j + 1)) := by
  have hab : a ≤ b := ha ▸ hb ▸ hp (Nat.zero_le (m + 1))
  have hpiece (j : ℕ) (hj : j ≤ m) : uIcc (p j) (p (j + 1)) ⊆ uIcc a b := by
    rw [uIcc_of_le (hp (Nat.le_succ j)), uIcc_of_le hab]
    exact Icc_subset_Icc (ha ▸ hp (Nat.zero_le j))
      (hb ▸ hp (Nat.add_le_add_right hj 1))
  -- On each piece the residual equals an integrable regulated expression almost everywhere.
  have hRi_piece (j : ℕ) (hj : j ≤ m) :
      IntervalIntegrable R volume (p j) (p (j + 1)) := by
    obtain ⟨Yd, hYdr, hYdd⟩ := hYreg j hj
    have hle : p j ≤ p (j + 1) := hp (Nat.le_succ j)
    have hKi := (hKr.intervalIntegrable_on hab).mono_set (hpiece j hj)
    have hGi := (hGr.intervalIntegrable_on hab).mono_set (hpiece j hj)
    have hYu : ContinuousOn (Y j) (uIcc (p j) (p (j + 1))) := by
      simpa only [uIcc_of_le hle] using hYc j hj
    have hcandidate := ((hKi.sub hGi).sub (hYdr.intervalIntegrable_on hle)).sub
      (((hKi.mul_continuousOn hYu).sub (hGi.continuousOn_mul hYu)).smul I)
    apply hcandidate.congr_ae
    rw [uIoc_of_le hle, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    change ∀ᵐ t ∂volume.restrict (Ioo (p j) (p (j + 1))),
      K t - G t - Yd t - I • (K t * Y j t - Y j t * G t) = R t
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hS.ae_notMem volume] with t ht hti
    have hderiv := (hYdd t hti ht).unique (hYd j hj t hti ht)
    rw [hderiv]
    abel
  -- Adjacent integrable pieces cover the interval, including repeated partition points.
  have hRi_prefix : ∀ k ≤ m + 1, IntervalIntegrable R volume (p 0) (p k) := by
    intro k
    induction k with
    | zero => intro _; exact IntervalIntegrable.refl
    | succ k ih =>
      intro hk
      exact (ih (by omega)).trans (hRi_piece k (by omega))
  have hRi : IntervalIntegrable R volume a b := by
    simpa only [ha, hb] using hRi_prefix (m + 1) le_rfl
  have hpiecewise := comparison_with_jumps m p hp ha hb K G U V R Y S hS
    hU hV hRi hYc hYd
  -- Distribute I over the endpoint difference and regroup the right side.
  simpa only [smul_sub, add_sub_assoc] using hpiecewise

/-- The Duhamel identity preceding equation (2.3): the difference of the two
unitary evolutions equals the integral of the interaction-picture generator
 difference. This is Theorem 2.2 with one piece and zero correction. -/
theorem duhamel_integral_identity {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    star (U b) * V b - 1 = ∫ t in a..b, I • (star (U t) * (K t - G t) * V t) := by
  -- One piece, with endpoints a and b, zero correction, and residual K - G.
  have hp : Monotone (fun j : ℕ ↦ if j = 0 then a else b) := by
    intro i j hij
    dsimp only
    split_ifs <;> first | exact le_rfl | exact hab | omega
  have hidentity := comparison_with_jumps 0 (fun j ↦ if j = 0 then a else b) hp
    (by simp) (by simp) K G U V (fun t ↦ K t - G t) (fun _ _ ↦ 0)
    ∅ countable_empty hU hV
    ((hKr.intervalIntegrable_on hab).sub (hGr.intervalIntegrable_on hab))
    (fun _ _ ↦ continuousOn_const) (by intro _ _ t _ _; simpa using hasDerivAt_const t (0 : 𝕄))
  simpa only [smul_zero, mul_zero, zero_mul, sub_zero, add_zero, Finset.sum_const_zero] using
    hidentity

/-- Equation (2.3), `eq:duhamel`: Theorem 2.2 with one piece (`m = 0`) and
zero correction, followed by unitary invariance and the norm of the integral. -/
theorem duhamel_bound {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    ‖V b - U b‖ ≤ ∫ t in a..b, ‖K t - G t‖ := by
  have hidentity := duhamel_integral_identity hab hKr hGr hU hV
  obtain ⟨hunitary, hintegral, hnorm⟩ := duhamel_display_chain hab hU hV hidentity
  -- Equation (2.3): unitary invariance, the Duhamel identity, then the integral norm bound.
  have hcompare := (hunitary.trans hintegral).le
  exact hcompare.trans hnorm

/-- Section 4.1: sufficient rates for a correction. A residual bounded by
`cR / T²`, each of the `T` jumps bounded by `cJ / T²`, and endpoint bounds
`c₀ / T` and `c₁ / T` give error at most `(cR + c₀ + c₁ + cJ) / T`.
The constants may be fixed uniformly in `T`, giving the stated reciprocal-time order. -/
theorem correction_rate_bound {T : ℕ} (hT : 0 < T)
    (p : ℕ → ℝ) (hp : Monotone p) (ha : p 0 = 0) (hb : p (T + 1) = T)
    (K G U V R : ℝ → 𝕄) (Y : ℕ → ℝ → 𝕄) (S : Set ℝ) (hS : S.Countable)
    (hU : IsEvolution K U 0 T) (hV : IsEvolution G V 0 T)
    (hRi : IntervalIntegrable R volume 0 T)
    (hYc : ∀ j ≤ T, ContinuousOn (Y j) (Icc (p j) (p (j + 1))))
    (hYd : ∀ j ≤ T, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S →
      HasDerivAt (Y j) (K t - G t - I • (K t * Y j t - Y j t * G t) - R t) t)
    (cR c₀ c₁ cJ : ℝ)
    (hres : ∀ t ∈ Icc (0 : ℝ) T, ‖R t‖ ≤ cR / (T : ℝ) ^ 2)
    (hleft : ‖Y 0 0‖ ≤ c₀ / T) (hright : ‖Y T T‖ ≤ c₁ / T)
    (hjump : ∀ j < T, ‖Y (j + 1) (p (j + 1)) - Y j (p (j + 1))‖ ≤
      cJ / (T : ℝ) ^ 2) :
    ‖V T - U T‖ ≤ (cR + c₀ + c₁ + cJ) / T := by
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hcontract (t : ℝ) (htm : t ∈ Icc (0 : ℝ) T) (A : 𝕄) :
      ‖star (U t) * A * V t‖ = ‖A‖ := by
    have hu := Matrix.mem_unitaryGroup_iff'.mpr (hU.2.2.1 t htm)
    have hv := Matrix.mem_unitaryGroup_iff'.mpr (hV.2.2.1 t htm)
    rw [CStarRing.norm_mul_mem_unitary _ hv,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hu)]
  have hintegral : ‖∫ t in (0 : ℝ)..T, star (U t) * R t * V t‖ ≤
      (T : ℝ) * (cR / (T : ℝ) ^ 2) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht.le
      (Filter.Eventually.of_forall fun t ht' ↦
        (hcontract t (Ioc_subset_Icc_self ht') (R t)).le.trans
          (hres t (Ioc_subset_Icc_self ht')))
      (intervalIntegrable_const (c := cR / (T : ℝ) ^ 2))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hbound
  have hsum : ‖∑ j ∈ Finset.range T,
      star (U (p (j + 1))) * (Y (j + 1) (p (j + 1)) - Y j (p (j + 1))) *
        V (p (j + 1))‖ ≤ (T : ℝ) * (cJ / (T : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range T, cJ / (T : ℝ) ^ 2 := by
        apply norm_sum_le_of_le
        intro j hj
        have hjT := Finset.mem_range.mp hj
        have hpoint : p (j + 1) ∈ Icc (0 : ℝ) T :=
          ⟨ha ▸ hp (Nat.zero_le _), hb ▸ hp (by omega)⟩
        exact (hcontract _ hpoint _).le.trans (hjump j hjT)
      _ = _ := by simp
  have hidentity := comparison_with_jumps T p hp ha hb K G U V R Y S hS hU hV hRi hYc hYd
  simp only [smul_sub, ← add_sub_assoc] at hidentity
  have hu := Matrix.mem_unitaryGroup_iff'.mpr (hU.2.2.1 T ⟨ht.le, le_rfl⟩)
  rw [Prose.unitary_difference_norm ⟨U T, hu⟩, hidentity,
    intervalIntegral.integral_smul, add_sub_assoc, ← smul_sub, ← smul_add, ← smul_sub,
    norm_smul, Complex.norm_I, one_mul]
  have hboundary : ‖star (U T) * Y T T * V T - Y 0 0‖ ≤ c₁ / T + c₀ / T :=
    norm_sub_le_of_le ((hcontract T ⟨ht.le, le_rfl⟩ _).le.trans hright) hleft
  calc
    _ ≤ (T : ℝ) * (cR / (T : ℝ) ^ 2) + (c₁ / T + c₀ / T) +
        (T : ℝ) * (cJ / (T : ℝ) ^ 2) :=
      norm_sub_le_of_le (norm_add_le_of_le hintegral hboundary) hsum
    _ = _ := by field_simp; ring

end UnitaryProducts.PaperProof
