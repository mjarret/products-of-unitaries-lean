/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.Prose.UnitStepsWalks

/-! # Matrix forms of the series calculations in Appendix A -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
open Complex Real Set Matrix
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Powers of the commutator in any unitary diagonalization, not a selected
basis. This makes the basis-independence assertion precise. -/
theorem ad_power_arbitrary_eigenbasis_entry (Ω E : 𝕄) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (ev : Fin d → ℝ)
    (hdiag : star (U : 𝕄) * Ω * (U : 𝕄) = diagonal (fun p ↦ (ev p : ℂ)))
    (n : ℕ) (p q : Fin d) :
    (star (U : 𝕄) * (adL Ω ^ n) E * (U : 𝕄)) p q =
      ((ev p - ev q : ℝ) : ℂ) ^ n * (star (U : 𝕄) * E * (U : 𝕄)) p q := by
  let e := Unitary.conjStarAlgAut ℂ 𝕄 (star U)
  have he (X : 𝕄) : e X = star (U : 𝕄) * X * (U : 𝕄) := by
    simp only [e, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
  have hΩe : e Ω = diagonal (fun p ↦ (ev p : ℂ)) := (he Ω).trans hdiag
  simp only [← he]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, adL_apply, map_sub, map_mul, map_mul, hΩe]
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [ih, pow_succ]
    push_cast
    ring

set_option maxHeartbeats 800000 in
-- Matrix and operator-algebra instance synthesis requires a larger elaboration budget.
/-- The Section 4.1 multiplier `frameOp Ω E` has entries `N(evp-evq) E_pq`
in every unitary eigenbasis. Its definition is therefore independent of the basis. -/
theorem frameOp_arbitrary_eigenbasis_entry [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    (E : 𝕄) (U : Matrix.unitaryGroup (Fin d) ℂ) (ev : Fin d → ℝ)
    (hdiag : star (U : 𝕄) * Ω * (U : 𝕄) = diagonal (fun p ↦ (ev p : ℂ)))
    (hev : ∀ p q, |ev p - ev q| < 2 * π) (p q : Fin d) :
    (star (U : 𝕄) * frameOp Ω E * (U : 𝕄)) p q =
      (frameMult (ev p - ev q) : ℂ) * (star (U : 𝕄) * E * (U : 𝕄)) p q := by
  have ha : ‖I • adL Ω‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL Ω‖ ≤ w by simpa using ad_power_norm_le hΩ hwidth 1).trans_lt hw
  let c : ℕ → ℝ := fun n ↦ |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ)
  have hs := (summable_norm_frameSeries_terms (I • adL Ω) ha).of_norm
  have hpos : Summable (fun n ↦ (c n : ℂ) • adL Ω ^ n) :=
    hs.congr (UnitaryProducts.Prose.frame_term_I_smul (adL Ω))
  have hsE := (ContinuousLinearMap.apply ℂ 𝕄 E).summable hpos
  have he := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star (U : 𝕄)) (U : 𝕄))).map_tsum hsE
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.apply_apply,
    show ∀ X : 𝕄, entryCLM p q X = X p q from fun _ ↦ rfl] at he
  rw [UnitaryProducts.Prose.frameOp_eq_positive_series Ω E ha,
    frameMult_positive_power_series (hev p q), Complex.ofReal_tsum, ← tsum_mul_right]
  change _ = ∑' n, ((c n * (ev p - ev q) ^ n : ℝ) : ℂ) * _
  erw [he]
  apply tsum_congr
  intro n
  simp only [ContinuousLinearMap.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [ad_power_arbitrary_eigenbasis_entry Ω E U ev hdiag]
  ring

end UnitaryProducts.PaperProof
