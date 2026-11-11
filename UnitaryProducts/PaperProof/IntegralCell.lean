/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.PaperProof.GeneralSeries
public import UnitaryProducts.Corrector.PartialFractions
/-! # The center-integral construction in the proof of Lemma A.1 -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra

/-- The scalar integral in the endpoint calculation, evaluated by its antiderivative. -/
theorem cell_scalar_integral {x : ℝ} (hx : x ≠ 0) (τ : ℝ) :
    (∫ s in (0 : ℝ)..τ, (s : ℂ) * Complex.exp (I * s * x)) =
      (Complex.exp (I * τ * x) * (1 - I * τ * x) - 1) / (x : ℂ)^2 := by
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  let P : ℝ → ℂ := fun t ↦ Complex.exp (I * t * x) * (1 - I * t * x) / (x : ℂ)^2
  have hd (t : ℝ) : HasDerivAt P ((t : ℂ) * Complex.exp (I * t * x)) t := by
    have ht := ((hasDerivAt_ofReal t).const_mul I).mul_const (x : ℂ)
    convert ((ht.cexp.mul (ht.const_sub 1)).div_const ((x : ℂ)^2)) using 1
    dsimp [P]
    field_simp
    ring_nf
    simp [I_sq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((by fun_prop : Continuous fun t : ℝ ↦
      (t : ℂ) * Complex.exp (I * t * x)).intervalIntegrable _ _)]
  simp only [P, ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, sub_zero, one_mul]
  ring

/-- The paired-sign trigonometric identity in the endpoint calculation. -/
theorem cell_exp_cot {x : ℝ} (hs : Real.sin (x / 2) ≠ 0) :
    Complex.exp (I * x / 2) * ((Real.cot (x / 2) : ℂ) - I) =
        1 / (Real.sin (x / 2) : ℂ) ∧
    Complex.exp (-(I * x / 2)) * ((Real.cot (x / 2) : ℂ) + I) =
        1 / (Real.sin (x / 2) : ℂ) := by
  have h := corrector_entry_exp_cot hs
  have hsC : (Real.sin (x / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  have hi : Complex.exp (I * x / 2) * Complex.exp (-(I * x / 2)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor
  · apply (eq_div_iff hsC).mpr
    calc
      _ = Complex.exp (I * x / 2) * Complex.exp (-(I * x / 2)) := by rw [h.1]; ring
      _ = 1 := hi
  · apply (eq_div_iff hsC).mpr
    calc
      _ = Complex.exp (I * x / 2) * Complex.exp (-(I * x / 2)) := by rw [h.2]; ring
      _ = 1 := hi

/-- At zero frequency both endpoint integrals equal one eighth. -/
theorem cell_scalar_endpoint_zero {τ : ℝ} (hτ : τ = 1 / 2 ∨ τ = -1 / 2) :
    (∫ s in (0 : ℝ)..τ, (s : ℂ) * Complex.exp (I * s * (0 : ℝ))) = 1 / 8 ∧
    ((frameMult 0 - frameMult (0 / 2) / 2 : ℝ) : ℂ) +
      Complex.exp (I * τ * (0 : ℝ)) * (frameMult 0 : ℂ) = 1 / 8 := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ)^2 / 2) (t : ℂ) t := by
    convert ((hasDerivAt_ofReal t).pow 2).div_const 2 using 1; ring
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ)).intervalIntegrable _ _)]
  rcases hτ with rfl | rfl <;> norm_num [frameMult]

/-- Both scalar endpoint integrals, including the zero mode, give the prescribed
multiplier after subtracting the center series. -/
theorem cell_scalar_endpoint {x : ℝ} (hx : |x| < 2 * π) {τ : ℝ}
    (hτ : τ = 1 / 2 ∨ τ = -1 / 2) :
    (∫ s in (0 : ℝ)..τ, (s : ℂ) * Complex.exp (I * s * x)) =
      ((frameMult x - frameMult (x / 2) / 2 : ℝ) : ℂ) +
        Complex.exp (I * τ * x) * (frameMult x : ℂ) := by
  by_cases hx0 : x = 0
  · subst x
    exact (cell_scalar_endpoint_zero hτ).1.trans (cell_scalar_endpoint_zero hτ).2.symm
  · have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0
    have hxhalf : x / 2 ≠ 0 := div_ne_zero hx0 (by norm_num)
    have hs := (Separation.zero_or_sin_half_ne_zero (ne_two_pi_mul_of_abs_lt hx)).resolve_left hx0
    have hc := congrArg Complex.ofReal (closedCell_cot_difference hx0 hx)
    have he := cell_exp_cot hs
    rw [cell_scalar_integral hx0, frameMult, if_neg hx0, frameMult, if_neg hxhalf]
    push_cast at hc he ⊢
    rw [show (x : ℂ) / 2 / 2 = x / 4 by ring]
    rcases hτ with rfl | rfl
    · simp only [ofReal_div, ofReal_one, ofReal_ofNat]
      rw [show I * (1 / 2 : ℂ) * x = I * x / 2 by ring]
      field_simp
      linear_combination -(4 * (x : ℂ)) * hc + (4 * (x : ℂ)) * he.1
    · simp only [ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
      rw [show I * (-1 / 2 : ℂ) * x = -(I * x / 2) by ring]
      field_simp
      linear_combination -(4 * (x : ℂ)) * hc + (4 * (x : ℂ)) * he.2

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The cosecant center coefficients satisfy the general series hypotheses.
Their signs come from pairing the decreasing terms of the alternating partial fractions. -/
theorem center_nonnegative_series : NonnegativeSeries centerCoeff :=
  ⟨centerCoeff_nonneg, fun r hr0 hr ↦
    summable_centerCoeff_power (by rwa [abs_of_nonneg hr0])⟩

/-- The negative center multiplier in the construction of Lemma A.1. -/
def integralCellCenter (Ω D : 𝕄) : 𝕄 :=
  -commutatorSeries centerCoeff Ω D

/-- The matrix center is the negative of the cosecant's nonnegative power series. -/
theorem integralCellCenter_series [NeZero d] {Ω : 𝕄} (D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦ (centerCoeff n : ℂ) • (adL Ω ^ n) D) ∧
    integralCellCenter Ω D = -∑' n : ℕ, (centerCoeff n : ℂ) • (adL Ω ^ n) D := by
  have hs := (center_nonnegative_series.summable_norm
    (A := 𝕄 →L[ℂ] 𝕄) (a := adL Ω) le_rfl ha).of_norm
  refine ⟨?_, ?_⟩
  · simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply] using
      (ContinuousLinearMap.apply ℂ 𝕄 D).summable hs
  · rw [integralCellCenter, commutatorSeries_eq_tsum center_nonnegative_series Ω D ha]

/-- The cell constructed by its center value and the conjugated integral. -/
def integralCell (Ω D : 𝕄) (τ : ℝ) : 𝕄 :=
  evol Ω τ * (integralCellCenter Ω D +
    ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s)) * evol Ω (-τ)

/-- The center in the integral formula is the actual value of the corrector at zero. -/
theorem integralCell_zero (Ω D : 𝕄) :
    integralCell Ω D 0 = integralCellCenter Ω D := by
  simp [integralCell, evol_zero]

/-- The defining conjugated-integral equality, before any endpoint calculation. -/
theorem integralCell_conjugated (Ω D : 𝕄) (τ : ℝ) :
    evol Ω (-τ) * integralCell Ω D τ * evol Ω τ = integralCellCenter Ω D +
      ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s) := by
  have hi : evol Ω (-τ) * evol Ω τ = 1 := by rw [← evol_add, neg_add_cancel, evol_zero]
  simp only [integralCell, ← mul_assoc, hi, one_mul]
  rw [mul_assoc, hi, mul_one]

/-- The correction with arbitrary center value `C`, in local time τ=t-j. -/
def centeredCorrection (Ω D C : 𝕄) (τ : ℝ) : 𝕄 :=
  evol Ω τ * (C + ∫ s in (0 : ℝ)..τ,
    s • (evol Ω (-s) * D * evol Ω s)) * evol Ω (-τ)


/-- The displayed variation-of-constants formula solves the cell equation for
every center value, with no width or Hermiticity assumption. -/
theorem centeredCorrection_hasDerivAt (Ω D C : 𝕄) (t : ℝ) :
    HasDerivAt (centeredCorrection Ω D C)
      (t • D - I • (Ω * centeredCorrection Ω D C t - centeredCorrection Ω D C t * Ω)) t := by
  have hc : Continuous (fun s : ℝ ↦ s • (evol Ω (-s) * D * evol Ω s)) := by
    exact continuous_id.smul
      ((((continuous_evol Ω).comp continuous_neg).mul continuous_const).mul (continuous_evol Ω))
  have hp := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hn : HasDerivAt (fun s : ℝ ↦ evol Ω (-s)) (I • (Ω * evol Ω (-t))) t := by
    simpa only [smul_mul_assoc, neg_smul, neg_neg, one_smul, neg_mul] using
      (hasDerivAt_evol Ω (-t)).scomp t (hasDerivAt_neg t)
  have hinv : evol Ω t * evol Ω (-t) = 1 := by rw [← evol_add, add_neg_cancel, evol_zero]
  have hcomm := ((Commute.smul_left_iff₀ (neg_ne_zero.mpr I_ne_zero)).mp
    (commute_evol Ω (-t))).eq.symm
  have he : evol Ω t * (t • (evol Ω (-t) * D * evol Ω t)) * evol Ω (-t) = t • D := by
    simp only [mul_smul_comm, smul_mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [mul_assoc D, hinv, mul_one]
  convert ((hasDerivAt_evol Ω t).mul
    ((hasDerivAt_const t C).add hp)).mul hn using 1
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [zero_add, add_mul, mul_add, he, centeredCorrection]
  simp only [mul_smul_comm, smul_sub, neg_smul, mul_assoc]
  rw [← hcomm]
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc, neg_mul, mul_assoc]
  abel

/-- The conjugated integral representation with the actual value at zero.
Its derivative satisfies the cell equation; the integrating-factor theorem below
derives this representation for every solution of that equation. -/
theorem cell_integral_formula (Ω D : 𝕄) :
    let Z : ℝ → 𝕄 := fun τ ↦ evol Ω τ * (integralCell Ω D 0 +
      ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s)) * evol Ω (-τ)
    (∀ τ, integralCell Ω D τ = Z τ) ∧ Z 0 = integralCell Ω D 0 ∧
      ∀ τ, HasDerivAt Z (τ • D - I • (Ω * Z τ - Z τ * Ω)) τ := by
  intro Z
  have heq : Z = centeredCorrection Ω D (integralCellCenter Ω D) := by
    funext τ
    simp only [Z, integralCell_zero, centeredCorrection]
  refine ⟨fun τ ↦ ?_, ?_, ?_⟩
  · rw [heq]
    rfl
  · simp only [Z, intervalIntegral.integral_same, add_zero, neg_zero, evol_zero,
      one_mul, mul_one]
  · rw [heq]
    exact centeredCorrection_hasDerivAt Ω D (integralCellCenter Ω D)

/-- Differentiating the canonical construction specializes the arbitrary-center formula. -/
theorem integralCell_hasDerivAt (Ω D : 𝕄) (t : ℝ) :
    HasDerivAt (integralCell Ω D)
      (t • D - I • (Ω * integralCell Ω D t - integralCell Ω D t * Ω)) t :=
  by
    simpa only [integralCell_zero] using (cell_integral_formula Ω D).2.2 t

/-- Lemma A.1: multiplying the cell equation by the two integrating factors
cancels its commutator. This applies to any solution, not just the constructed one. -/
theorem cell_conjugated_hasDerivAt (Ω D : 𝕄) {Y : ℝ → 𝕄} {τ : ℝ}
    (hY : HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ) :
    HasDerivAt (fun t ↦ evol Ω (-t) * Y t * evol Ω t)
      (τ • (evol Ω (-τ) * D * evol Ω τ)) τ := by
  have hcomm (t : ℝ) : Ω * evol Ω t = evol Ω t * Ω := by
    have hh := (commute_evol Ω t).eq
    simp only [smul_mul_assoc, mul_smul_comm] at hh
    exact (smul_right_injective 𝕄 (neg_ne_zero.mpr I_ne_zero)) hh
  have hn : HasDerivAt (fun t : ℝ ↦ evol Ω (-t))
      (I • (Ω * evol Ω (-τ))) τ := by
    simpa only [smul_mul_assoc, neg_smul, neg_neg, one_smul, neg_mul] using
      (hasDerivAt_evol Ω (-τ)).scomp τ (hasDerivAt_neg τ)
  convert (hn.mul hY).mul (hasDerivAt_evol Ω τ) using 1
  simp only [Pi.mul_apply, smul_mul_assoc, mul_smul_comm, smul_sub, neg_smul,
    neg_mul, mul_neg, add_mul, mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc Ω (evol Ω (-τ)), hcomm (-τ)]
  simp only [mul_assoc]
  module

/-- Lemma A.1: integration of the conjugated derivative from zero to local time
produces the displayed variation-of-constants formula, with the actual value `Y 0`. -/
theorem cell_integrating_factor (Ω D : 𝕄) {Y : ℝ → 𝕄}
    (hY : ∀ t, HasDerivAt Y (t • D - I • (Ω * Y t - Y t * Ω)) t) (τ : ℝ) :
    Y τ = evol Ω τ * (Y 0 + ∫ σ in (0 : ℝ)..τ,
      σ • (evol Ω (-σ) * D * evol Ω σ)) * evol Ω (-τ) := by
  have hc : Continuous (fun σ : ℝ ↦ σ • (evol Ω (-σ) * D * evol Ω σ)) := by
    exact continuous_id.smul
      ((((continuous_evol Ω).comp continuous_neg).mul continuous_const).mul (continuous_evol Ω))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ cell_conjugated_hasDerivAt Ω D (hY t)) (hc.intervalIntegrable 0 τ)
  simp only [neg_zero, evol_zero, one_mul, mul_one] at hFTC
  have heq : Y 0 + (∫ σ in (0 : ℝ)..τ,
      σ • (evol Ω (-σ) * D * evol Ω σ)) = evol Ω (-τ) * Y τ * evol Ω τ := by
    rw [hFTC]
    abel
  have hi : evol Ω τ * evol Ω (-τ) = 1 := by
    rw [← evol_add, add_neg_cancel, evol_zero]
  rw [heq]
  simp only [← mul_assoc, hi, one_mul]
  rw [mul_assoc, hi, mul_one]

/-- The center in an eigenbasis is the negative scalar center multiplier. -/
theorem integralCellCenter_entry [NeZero d] {w : ℝ} (hw : w < 2 * π)
    {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * integralCellCenter Ω D * U) p q =
      -((frameMult (hΩ.eigenvalues p - hΩ.eigenvalues q) -
        frameMult ((hΩ.eigenvalues p - hΩ.eigenvalues q) / 2) / 2 : ℝ) : ℂ) *
        (star U * D * U) p q := by
  intro U
  have ha : ‖adL Ω‖ < 2 * π :=
    (show ‖adL Ω‖ ≤ w by simpa only [pow_one] using ad_power_norm_le hΩ hwid 1).trans_lt hw
  have hdiag : star U * Ω * U = diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
      using hΩ.conjStarAlgAut_star_eigenvectorUnitary
  have he := general_series_eigenbasis_entry center_nonnegative_series Ω D ha
    hΩ.eigenvectorUnitary hΩ.eigenvalues hdiag p q
  have hx := (hwid p q).trans_lt hw
  have hscalar : scalarSeries centerCoeff (hΩ.eigenvalues p - hΩ.eigenvalues q) =
      frameMult (hΩ.eigenvalues p - hΩ.eigenvalues q) -
        frameMult ((hΩ.eigenvalues p - hΩ.eigenvalues q) / 2) / 2 := by
    rw [← cellConstant_eq_frameMult hx]
    exact (cellConstant_positive_power_series hx).2.2.symm
  simp only [integralCellCenter, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
  rw [he, hscalar]
  ring

/-- Integrating the scalar cell equation after conjugation. This is the
entrywise form of the defining integral, with arbitrary center data. -/
theorem cell_entry_integrating_factor (x : ℝ) (a : ℂ) (y : ℝ → ℂ)
    (hy : ∀ t : ℝ, HasDerivAt y ((t : ℂ) * a - I * x * y t) t) (τ : ℝ) :
    Complex.exp (I * τ * x) * y τ = y 0 +
      (∫ s in (0 : ℝ)..τ, (s : ℂ) * Complex.exp (I * s * x)) * a := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Complex.exp (I * s * x) * y s)
      (((t : ℂ) * Complex.exp (I * t * x)) * a) t := by
    convert ((((hasDerivAt_ofReal t).const_mul I).mul_const (x : ℂ)).cexp).mul (hy t) using 1
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((by fun_prop : Continuous fun t : ℝ ↦
      ((t : ℂ) * Complex.exp (I * t * x)) * a).intervalIntegrable 0 τ)
  rw [intervalIntegral.integral_mul_const] at hi
  simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul] at hi
  linear_combination -hi

/-- The scalar endpoint identity gives both matrix endpoint values of the
center-integral construction; no periodicity hypothesis is used. -/
theorem integralCell_endpoints {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄)
    {τ : ℝ} (hτ : τ = 1 / 2 ∨ τ = -1 / 2) :
    integralCell Ω D τ = frameOp Ω D := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  letI : NeZero d := ⟨hd.ne'⟩
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let E (p q : Fin d) := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).restrictScalars ℝ
  apply (Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary).symm.injective
  change star U * integralCell Ω D τ * U = star U * frameOp Ω D * U
  ext p q
  have hi := cell_entry_integrating_factor (hΩ.eigenvalues p - hΩ.eigenvalues q)
    (E p q D) (fun t ↦ E p q (integralCell Ω D t))
    (fun t ↦ corrector_eigenbasis_derivative Ω hΩ D (integralCell_hasDerivAt Ω D t) p q) τ
  have hzero : integralCell Ω D 0 = integralCellCenter Ω D := by
    simp [integralCell, evol_zero]
  rw [cell_scalar_endpoint ((hwid p q).trans_lt hw) hτ, hzero] at hi
  change Complex.exp _ * (star U * integralCell Ω D τ * U) p q =
    (star U * integralCellCenter Ω D * U) p q + _ at hi
  rw [integralCellCenter_entry hw hΩ hwid D p q] at hi
  rw [frameOp_eq_paper_value hΩ hw hwid D]
  change _ = (star U * (periodicCorrectorData Ω hΩ D).2.1 * U) p q
  rw [corrector_end_eigenbasis_entry hΩ D p q ((hwid p q).trans_lt hw)]
  apply mul_left_cancel₀ (Complex.exp_ne_zero (I * τ * (hΩ.eigenvalues p - hΩ.eigenvalues q)))
  have hE : E p q D = (star U * D * U) p q := rfl
  rw [hE] at hi
  convert hi using 1 <;> dsimp [U] <;> push_cast <;> ring

/-- Equation `eq:series-bound`, applied to the positive cosecant coefficients,
gives the center norm in Lemma A.1. -/
theorem integralCellCenter_norm {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    ‖integralCellCenter Ω D‖ ≤ (frameBound w - frameBound (w / 2) / 2) * ‖D‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, mul_zero, le_refl]
  letI : NeZero d := ⟨hd.ne'⟩
  have hw0 : 0 ≤ w := (norm_nonneg (adL Ω)).trans
    (show ‖adL Ω‖ ≤ w by simpa only [pow_one] using ad_power_norm_le hΩ hwid 1)
  have hs := (cellConstant_positive_power_series
    (show |w| < 2 * π by rwa [abs_of_nonneg hw0])).2.2
  have hb := general_series_bound center_nonnegative_series hΩ hw0 hw hwid D
  rw [integralCellCenter, norm_neg]
  rw [scalarSeries, ← hs, cellConstant_eq_frameBound hw0 hw] at hb
  exact hb

/-- The final equality in Lemma A.1: unitary invariance applied to the
integrating-factor formula leaves exactly its center-plus-integral bracket. -/
theorem integralCell_norm_eq_integral {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (D : 𝕄) (τ : ℝ) :
    ‖integralCell Ω D τ‖ = ‖integralCell Ω D 0 +
      ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s)‖ := by
  rw [cell_integrating_factor Ω D (integralCell_hasDerivAt Ω D) τ,
    CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hΩ _),
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hΩ _)]

/-- Unitary conjugation and the integral triangle inequality bound growth from
its actual center value, as in Lemma A.1(ii), for either sign of the local time. -/
theorem integralCell_norm {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄) (τ : ℝ) :
    ‖integralCell Ω D τ‖ ≤ ‖integralCell Ω D 0‖ + τ ^ 2 * ‖D‖ / 2 := by
  have hint : ‖∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s)‖ ≤ τ ^ 2 / 2 * ‖D‖ := by
    have hn (s : ℝ) : ‖s • (evol Ω (-s) * D * evol Ω s)‖ ≤ |s| * ‖D‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_evol_conj_le hΩ D s) (abs_nonneg s)
    refine (intervalIntegral.norm_integral_le_abs_of_norm_le (ae_of_all _ hn)
      ((by fun_prop : Continuous fun s : ℝ ↦ |s| * ‖D‖).intervalIntegrable _ _)).trans_eq ?_
    rw [intervalIntegral.integral_mul_const, abs_mul, abs_of_nonneg (norm_nonneg D)]
    rw [abs_integral_abs_zero τ]
  rw [integralCell_norm_eq_integral hΩ D τ]
  exact ((norm_add_le _ _).trans (add_le_add le_rfl hint)).trans_eq (by ring)

/-- The continuously differentiable construction satisfies the paper's literal
center-series equation. The series is read as a sum of iterated commutators. -/
theorem integralCell_spec {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    ContDiff ℝ 1 (integralCell Ω D) ∧
    ∀ τ : ℝ, evol Ω (-τ) * integralCell Ω D τ * evol Ω τ =
      -(∑' n : ℕ, (centerCoeff n : ℂ) • (adL Ω ^ n) D) +
      ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s) := by
  have hd := integralCell_hasDerivAt Ω D
  have hc : Continuous (integralCell Ω D) :=
    (show Differentiable ℝ (integralCell Ω D) from fun τ ↦ (hd τ).differentiableAt).continuous
  constructor
  · refine contDiff_one_iff_deriv.mpr ⟨fun τ ↦ (hd τ).differentiableAt, ?_⟩
    rw [funext fun τ ↦ (hd τ).deriv]
    fun_prop
  · intro τ
    rw [integralCell_conjugated]
    rcases Nat.eq_zero_or_pos d with rfl | hdim
    · exact Subsingleton.elim _ _
    · letI : NeZero d := ⟨hdim.ne'⟩
      have hA : ‖adL Ω‖ < 2 * π :=
        ((fact_adjoint Ω Ω Ω hΩ hwid 0).1.2.2.2.2).trans_lt hw
      rw [(integralCellCenter_series D hA).2]


end UnitaryProducts.PaperProof
