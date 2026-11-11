/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.PaperProof.ExponentialDefinitions
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Corrector.PartialFractionMultiplier
/-! # The closed-form corrector used by Appendix A -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The scalar closed form used in the proof of Lemma A.1. -/
def closedCellMultiplier (τ x : ℝ) : ℂ :=
  if x = 0 then (τ : ℂ)^2 / 2 - 1 / 24 else
    (1 - I * τ * x) / (x : ℂ)^2 -
      Complex.exp (-(I * τ * x)) / (2 * x * Real.sin (x / 2))

/-- Away from zero, the displayed formula is the scalar particular solution with
its periodic integration constant, as computed in `corrector_entry_solutions`. -/
theorem closedCellMultiplier_eq_solution {x : ℝ} (hx : x ≠ 0) (τ : ℝ) :
    closedCellMultiplier τ x =
      (1 / (x : ℂ)^2 - I * τ / x) * 1 +
        (-1 / (2 * x * Real.sin (x / 2))) * Complex.exp (-(I * τ * x)) := by
  rw [closedCellMultiplier, if_neg hx]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp
  ring

/-- Differentiation of the closed form gives the scalar corrector equation,
including its prescribed value at zero frequency. -/
theorem closedCellMultiplier_derivative (x τ : ℝ) :
    HasDerivAt (fun t ↦ closedCellMultiplier t x)
      ((τ : ℂ) - I * x * closedCellMultiplier τ x) τ := by
  by_cases hx : x = 0
  · subst x
    simpa [closedCellMultiplier] using
      (periodic_corrector_zero_limit (1 : ℂ)).2.1 τ
  · simp_rw [closedCellMultiplier_eq_solution hx]
    simpa only [mul_one] using (corrector_entry_solutions hx (1 : ℂ)).1
      (-1 / (2 * x * Real.sin (x / 2))) τ

/-- Both endpoint values of the closed form are the multiplier N. -/
theorem closedCellMultiplier_endpoints {x : ℝ} (hx : |x| < 2 * π) :
    closedCellMultiplier (1 / 2) x = (frameMult x : ℂ) ∧
      closedCellMultiplier (-1 / 2) x = (frameMult x : ℂ) := by
  by_cases hx₀ : x = 0
  · subst x
    norm_num [closedCellMultiplier, frameMult]
  · have hs := (Separation.zero_or_sin_half_ne_zero (ne_two_pi_mul_of_abs_lt hx)).resolve_left hx₀
    simpa only [closedCellMultiplier_eq_solution hx₀, mul_one] using
      (corrector_entry_solutions hx₀ (1 : ℂ)).2.2.2 hs

/-- The cotangent difference needed by the closed-form center calculation,
with positive and negative frequencies treated symmetrically. -/
theorem closedCell_cot_difference {x : ℝ} (hx₀ : x ≠ 0) (hx : |x| < 2 * π) :
    Real.cot (x / 4) - Real.cot (x / 2) = 1 / Real.sin (x / 2) := by
  rcases lt_or_gt_of_ne hx₀ with hn | hp
  · have h := cot_half_sub_cot (y := -x / 2) (by linarith) (by
      have := (abs_lt.mp hx).1
      linarith)
    simp only [neg_div, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg,
      div_neg] at h ⊢
    convert congrArg Neg.neg h using 1 <;> ring_nf
  · convert cot_half_sub_cot (y := x / 2) (by linarith) (by
      have := (abs_lt.mp hx).2
      linarith) using 1
    congr 1
    ring

/-- The constant in Theorem 4.2 and the positive scalar center multiplier in
Lemma A.1, with its removable singularity filled by `1/24`. -/
def cellConstant (x : ℝ) : ℝ :=
  if x = 0 then 1 / 24 else 1 / (2 * x * Real.sin (x / 2)) - 1 / x ^ 2

/-- The cosecant center multiplier equals the difference of frame
multipliers for every signed frequency inside the convergence interval. -/
theorem cellConstant_eq_frameMult {x : ℝ} (hx : |x| < 2 * π) :
    cellConstant x = frameMult x - frameMult (x / 2) / 2 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [cellConstant, frameMult]
  have hhalf : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
  have hcot := closedCell_cot_difference hx0 hx
  rw [cellConstant, if_neg hx0, frameMult, if_neg hx0, frameMult, if_neg hhalf]
  rw [show x / 2 / 2 = x / 4 by ring]
  have hcoteq : Real.cot (x / 4) = Real.cot (x / 2) + 1 / Real.sin (x / 2) := by
    linarith [hcot]
  rw [hcoteq]
  field_simp
  ring

/-- The new printed value of `c₀` agrees with the frame-series majorant used
by all comparison estimates. -/
theorem cellConstant_eq_frameBound {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    cellConstant w = frameBound w - frameBound (w / 2) / 2 := by
  have habs : |w| < 2 * π := by rwa [abs_of_nonneg hw0]
  have hhalf0 : 0 ≤ w / 2 := div_nonneg hw0 (by norm_num)
  have hhalf : |w / 2| < 2 * π := by
    rw [abs_of_nonneg hhalf0]
    linarith [pi_pos]
  rw [cellConstant_eq_frameMult habs, ← frameBound_abs_eq_frameMult habs,
    ← frameBound_abs_eq_frameMult hhalf, abs_of_nonneg hw0, abs_of_nonneg hhalf0]

/-- The guessed entry in Lemma A.1 solves the displayed differential equation
and has the two prescribed end values. -/
theorem cell_entry_ansatz_verified {x : ℝ} (hx : |x| < 2 * π) (a : ℂ) :
    (∀ τ : ℝ, HasDerivAt (fun t ↦ closedCellMultiplier t x * a)
      ((τ : ℂ) * a - I * x * (closedCellMultiplier τ x * a)) τ) ∧
    closedCellMultiplier (-1 / 2) x * a = (frameMult x : ℂ) * a ∧
    closedCellMultiplier (1 / 2) x * a = (frameMult x : ℂ) * a := by
  refine ⟨?_, congrArg (· * a) (closedCellMultiplier_endpoints hx).2,
    congrArg (· * a) (closedCellMultiplier_endpoints hx).1⟩
  intro τ
  convert (closedCellMultiplier_derivative x τ).mul_const a using 1
  ring

/-- The closed scalar formula equals any solution with the prescribed left
endpoint. This identifies the matrix corrector with the closed formula. -/
theorem closedCellMultiplier_eq_entry {x : ℝ} (hx : |x| < 2 * π) (a : ℂ)
    (y : ℝ → ℂ) (hy : ∀ t : ℝ, HasDerivAt y ((t : ℂ)*a-I*x*y t) t)
    (hi : y (-1/2) = (frameMult x : ℂ)*a) (τ : ℝ) :
    y τ = closedCellMultiplier τ x * a := by
  by_cases hx₀ : x = 0
  · subst x
    have h := (corrector_entry_solutions_zero a y (by simpa using hy)).1
    have hleft := h (-1/2)
    rw [hi] at hleft
    norm_num [frameMult] at hleft
    rw [h τ, closedCellMultiplier, if_pos rfl]
    linear_combination -hleft
  · let z : ℝ → ℂ := fun t ↦ closedCellMultiplier t x * a
    have hz (t : ℝ) : HasDerivAt z ((t : ℂ)*a-I*x*z t) t := by
      convert (closedCellMultiplier_derivative x t).mul_const a using 1
      dsimp [z]
      ring
    have hzi : z (-1/2) = (frameMult x : ℂ)*a := by
      exact congrArg (· * a) (closedCellMultiplier_endpoints hx).2
    obtain ⟨_, hall, _, _⟩ := corrector_entry_solutions hx₀ a
    obtain ⟨c, hc⟩ := hall y hy
    obtain ⟨c', hc'⟩ := hall z hz
    have he : y (-1/2) = z (-1/2) := hi.trans hzi.symm
    rw [hc, hc'] at he
    have hc_eq : c = c' :=
      mul_right_cancel₀ (Complex.exp_ne_zero _) (add_left_cancel he)
    change y τ = z τ
    rw [hc, hc', hc_eq]

/-- The matrix corrector is exactly `yτ(ad Ω)(D)`, by its scalar entries. -/
theorem periodicCorrector_eq_closedCell {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π) (D : 𝕄) (τ : ℝ) :
    (periodicCorrectorData Ω hΩ D).2.2 τ =
      complexSpectralMultiplier Ω hΩ (closedCellMultiplier τ) D := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  let E (p q : Fin d) := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).restrictScalars ℝ
  apply e.symm.injective
  change star U * ((periodicCorrectorData Ω hΩ D).2.2 τ) * U =
    star U * (complexSpectralMultiplier Ω hΩ (closedCellMultiplier τ) D) * U
  ext p q
  rw [spectralMultiplier_eigenbasis_entry Ω hΩ (closedCellMultiplier τ) D p q]
  have hinit : (periodicCorrectorData Ω hΩ D).2.2 (-1/2) =
      (periodicCorrectorData Ω hΩ D).2.1 := by
    simp [periodicCorrectorData, exponentialOperators, neg_div, frameExtension_zero]
  exact closedCellMultiplier_eq_entry (hw p q) (E p q D)
    (fun t ↦ E p q ((periodicCorrectorData Ω hΩ D).2.2 t))
    (fun t ↦ corrector_eigenbasis_derivative Ω hΩ D
      (hasDerivAt_periodic_corrector Ω hΩ D t) p q)
    ((congrArg (E p q) hinit).trans (corrector_end_eigenbasis_entry hΩ D p q (hw p q))) τ

/-- Appendix A: the cotangent multiplier has the positive coefficient expansion
obtained directly from its partial fractions. -/
theorem frameMult_positive_power_series {x : ℝ} (hx : |x| < 2 * π) :
    frameMult x = ∑' n : ℕ, frameCoeff n * x ^ n :=
  frameMult_eq_frameCoeff_series hx

/-- The cosecant partial fractions in Lemma A.1, including the removable value at zero.
The cotangent half-angle identity identifies the scalar value; summing the
alternating coefficients gives the cosecant pole sum. -/
theorem cellConstant_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    cellConstant x = ∑' m : ℕ, (-1 : ℝ) ^ m *
      (2 / (4 * π ^ 2 * (m + 1 : ℝ) ^ 2 - x ^ 2)) := by
  have hxhalf : |x / 2| < 2 * π := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg x, pi_pos]
  rw [cellConstant_eq_frameMult hx, frameMult_eq_frameCoeff_series hx,
    frameMult_eq_frameCoeff_series hxhalf, ← centerCoeff_power_eq_difference hx,
    centerCoeff_power_eq_partialFractions hx]
  apply tsum_congr
  intro m
  congr 2
  ring

/-- The negative center multiplier has a nonnegative Taylor series: its scalar
value comes from the cosecant partial fractions, and each even coefficient is
an alternating inverse-power sum with strictly decreasing terms. -/
theorem cellConstant_positive_power_series {x : ℝ} (hx : |x| < 2 * π) :
    (∀ n, 0 ≤ centerCoeff n) ∧ Summable (fun n ↦ centerCoeff n * x ^ n) ∧
      cellConstant x = ∑' n, centerCoeff n * x ^ n := by
  refine ⟨centerCoeff_nonneg, summable_centerCoeff_power hx, ?_⟩
  rw [cellConstant_eq_partialFractions hx, centerCoeff_power_eq_partialFractions hx]
  apply tsum_congr
  intro m
  congr 2
  ring

end UnitaryProducts.PaperProof
