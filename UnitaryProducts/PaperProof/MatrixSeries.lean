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

end UnitaryProducts.PaperProof
