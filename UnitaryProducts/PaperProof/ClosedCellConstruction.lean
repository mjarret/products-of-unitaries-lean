/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.IntegralCell
/-! # The closed-form construction in the proof of Lemma A.1 -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- At zero time the guessed entry is the negative cosecant multiplier,
including the removable value `-a/24` at zero frequency. -/
theorem cell_center_ansatz_verified (x : ℝ) (a : ℂ) :
    closedCellMultiplier 0 x * a = -(cellConstant x : ℂ) * a := by
  by_cases hx : x = 0
  · subst x
    norm_num [closedCellMultiplier, cellConstant]
  · rw [closedCellMultiplier, if_neg hx, cellConstant, if_neg hx]
    push_cast
    simp only [mul_zero, zero_mul, neg_zero, Complex.exp_zero, sub_zero]
    ring

/-- The center of the scalar closed form, identified with the convergent
frame-series difference by the verified cosecant guess. -/
theorem closedCellMultiplier_center {x : ℝ} (hx : |x| < 2 * π) :
    closedCellMultiplier 0 x = -((frameMult x - frameMult (x / 2) / 2 : ℝ) : ℂ) := by
  simpa only [mul_one, cellConstant_eq_frameMult hx] using
    cell_center_ansatz_verified x 1

/-- The matrix in Appendix A is defined entrywise by the displayed closed form. -/
def closedCell (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄) (τ : ℝ) : 𝕄 :=
  complexSpectralMultiplier Ω hΩ (closedCellMultiplier τ) D

/-- Differentiating the scalar formula and integrating its conjugated equation
identifies the closed-form matrix with its center-integral representation. -/
theorem closedCell_eq_integralCell {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    (D : 𝕄) (τ : ℝ) : closedCell Ω hΩ D τ = integralCell Ω D τ := by
  rcases Nat.eq_zero_or_pos d with rfl | hdim
  · exact Subsingleton.elim _ _
  letI : NeZero d := ⟨hdim.ne'⟩
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  apply e.symm.injective
  change star U * closedCell Ω hΩ D τ * U = star U * integralCell Ω D τ * U
  ext p q
  rw [closedCell, spectralMultiplier_eigenbasis_entry]
  let x := hΩ.eigenvalues p - hΩ.eigenvalues q
  let a := (star U * D * U) p q
  let y : ℝ → ℂ := fun t ↦ closedCellMultiplier t x * a
  have hy (t : ℝ) : HasDerivAt y ((t : ℂ) * a - I * x * y t) t :=
    (cell_entry_ansatz_verified ((hwidth p q).trans_lt hw) a).1 t
  have hclosed := cell_entry_integrating_factor x a y hy τ
  have hintegral := cell_entry_integrating_factor x a
    (fun t ↦ (star U * integralCell Ω D t * U) p q)
    (fun t ↦ corrector_eigenbasis_derivative Ω hΩ D (integralCell_hasDerivAt Ω D t) p q) τ
  have hzero : integralCell Ω D 0 = integralCellCenter Ω D := by
    simp [integralCell, evol_zero]
  have hcenter : y 0 = (star U * integralCell Ω D 0 * U) p q := by
    rw [hzero, integralCellCenter_entry hw hΩ hwidth D p q]
    exact congrArg (· * a) (closedCellMultiplier_center ((hwidth p q).trans_lt hw))
  rw [hcenter] at hclosed
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hclosed.trans hintegral.symm)

/-- Lemma A.1: read the center norm from the guessed multiplier. The
positive Taylor series gives the middle inequality, and the scalar center
identity identifies its majorant with the printed cosecant constant. -/
theorem cell_center_multiplier_bound {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    ‖closedCell Ω hΩ D 0‖ =
        ‖complexSpectralMultiplier Ω hΩ (closedCellMultiplier 0) D‖ ∧
    ‖complexSpectralMultiplier Ω hΩ (closedCellMultiplier 0) D‖ ≤
        -(closedCellMultiplier 0 w).re * ‖D‖ ∧
    -(closedCellMultiplier 0 w).re = cellConstant w := by
  have hcenter : -(closedCellMultiplier 0 w).re = cellConstant w := by
    have he := cell_center_ansatz_verified w 1
    simp only [mul_one] at he
    rw [he]
    simp
  refine ⟨rfl, ?_, hcenter⟩
  rw [hcenter, cellConstant_eq_frameBound hw0 hw]
  change ‖closedCell Ω hΩ D 0‖ ≤ _
  rw [closedCell_eq_integralCell hw hΩ hwidth D 0, integralCell_zero]
  exact integralCellCenter_norm hw hΩ hwidth D

/-- Both closed-form matrix endpoints equal the end-value multiplier N. -/
theorem closedCell_endpoints {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    (D : 𝕄) : closedCell Ω hΩ D (-1 / 2) = frameOp Ω D ∧
      closedCell Ω hΩ D (1 / 2) = frameOp Ω D := by
  rw [frameOp_eq_paper_value hΩ hw hwidth D]
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  constructor <;> apply e.symm.injective
  · change star U * closedCell Ω hΩ D (-1 / 2) * U = _
    ext p q
    rw [closedCell, spectralMultiplier_eigenbasis_entry,
      (closedCellMultiplier_endpoints ((hwidth p q).trans_lt hw)).2]
    exact (corrector_end_eigenbasis_entry hΩ D p q ((hwidth p q).trans_lt hw)).symm
  · change star U * closedCell Ω hΩ D (1 / 2) * U = _
    ext p q
    rw [closedCell, spectralMultiplier_eigenbasis_entry,
      (closedCellMultiplier_endpoints ((hwidth p q).trans_lt hw)).1]
    exact (corrector_end_eigenbasis_entry hΩ D p q ((hwidth p q).trans_lt hw)).symm

end UnitaryProducts.PaperProof
