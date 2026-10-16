/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.Comparison.EndpointComparison
/-! # The center-integral construction in the proof of Lemma A.1 -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof

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

/-- Bounded scalar weights preserve absolute convergence of the frame series.
Elaborate this Banach-algebra fact before specializing to operator algebras. -/
theorem summable_frameSeries_center_terms {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]
    {a : A} (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦ ((1 - (1 / 2 : ℝ)^(n + 1) : ℝ) : ℂ) •
      (((bernoulli (n + 2) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • a ^ n)) := by
  apply (summable_norm_frameSeries_terms a ha).of_norm_bounded
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))]
  exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (pow_nonneg (by norm_num) _))

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The negative center series in the construction of Lemma A.1. -/
def integralCellCenter (Ω D : 𝕄) : 𝕄 :=
  -((frameSeries (I • adL Ω) -
    (1 / 2 : ℂ) • frameSeries ((1 / 2 : ℂ) • (I • adL Ω))) D)

/-- The center is exactly the norm-convergent positive commutator series
printed in the defining equation of Lemma A.1. -/
theorem integralCellCenter_series [NeZero d] {Ω : 𝕄} (D : 𝕄)
    (hA : ‖I • adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      (((1 - (1 / 2 : ℝ)^(n + 1)) * |((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) • (adL Ω ^ n) D) ∧
    integralCellCenter Ω D = -∑' n : ℕ,
      (((1 - (1 / 2 : ℝ)^(n + 1)) * |((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) • (adL Ω ^ n) D := by
  let k : ℕ → ℝ := fun n ↦ 1 - (1 / 2 : ℝ)^(n + 1)
  let c : ℕ → ℂ := fun n ↦ (bernoulli (n + 2) : ℂ) / (Nat.factorial (n + 2) : ℂ)
  have hs : Summable (fun n ↦ ((k n : ℂ) * c n) • (I • adL Ω) ^ n) := by
    simpa only [k, c, smul_smul] using
      summable_frameSeries_center_terms (A := 𝕄 →L[ℂ] 𝕄) hA
  have he (n : ℕ) : (((k n : ℂ) * c n) • (I • adL Ω) ^ n) D =
      (((1 - (1 / 2 : ℝ)^(n + 1)) * |((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) • (adL Ω ^ n) D := by
    rw [SemigroupAction.mul_smul (k n : ℂ) (c n) ((I • adL Ω) ^ n)]
    dsimp only [c]
    rw [Prose.frame_term_I_smul (adL Ω) n]
    simp only [ContinuousLinearMap.smul_apply, smul_smul]
    congr 1
    dsimp [k]
    push_cast
    ring
  have hsD := (ContinuousLinearMap.apply ℂ 𝕄 D).summable hs
  have hsD' : Summable (fun n ↦ (((k n : ℂ) * c n) • (I • adL Ω) ^ n) D) := hsD
  refine ⟨hsD'.congr he, ?_⟩
  rw [integralCellCenter, frameSeries_sub_half_eq_tsum hA]
  have heq : (fun n : ℕ ↦ ((1 - (1 / 2 : ℂ)^(n + 1)) *
      ((bernoulli (n + 2) : ℂ) / (Nat.factorial (n + 2) : ℂ))) • (I • adL Ω) ^ n) =
      (fun n ↦ ((k n : ℂ) * c n) • (I • adL Ω) ^ n) := by
    ext n
    dsimp [k, c]
    push_cast
    rfl
  rw [heq, tsum_apply_of_summable hs]
  congr 1
  exact tsum_congr he

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

/-- The second guess in Lemma A.1 is the conjugated integral with the
actual value at zero. It agrees with the constructed corrector and is verified
by its differential equation and initial value. -/
theorem cell_integral_ansatz_verified (Ω D : 𝕄) :
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
    simpa only [integralCell_zero] using (cell_integral_ansatz_verified Ω D).2.2 t

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
  have hA : ‖I • adL Ω‖ < 2 * π := by
    rw [closedCell_norm_smul I (adL Ω), Complex.norm_I, one_mul]
    exact ((fact_adjoint Ω Ω Ω hΩ hwid 0).1.2.2.2.2).trans_lt hw
  have hhalf : ‖((1 / 2 : ℂ) * I) • adL Ω‖ < 2 * π := by
    rw [← smul_smul, closedCell_norm_smul (1 / 2 : ℂ) (I • adL Ω)]
    norm_num
    linarith [norm_nonneg (I • adL Ω), Real.pi_pos]
  simp only [integralCellCenter, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.neg_apply, Matrix.sub_apply,
    Matrix.smul_apply]
  rw [frameSeries_smul_ad_entry Ω hΩ D I hA,
    frameSeries_smul_ad_entry Ω hΩ D ((1 / 2:ℂ)*I) hhalf]
  have hx := (hwid p q).trans_lt hw
  have hxhalf : |(hΩ.eigenvalues p-hΩ.eigenvalues q) / 2| < 2 * π := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg (hΩ.eigenvalues p-hΩ.eigenvalues q), pi_pos]
  rw [mul_comm I, frameSeries_ofReal_mul_I, frameBound_abs_eq_frameMult hx]
  rw [show (1 / 2:ℂ)*I*((hΩ.eigenvalues p-hΩ.eigenvalues q:ℝ):ℂ) =
    (((hΩ.eigenvalues p-hΩ.eigenvalues q) / 2:ℝ):ℂ)*I by push_cast; ring,
    frameSeries_ofReal_mul_I, frameBound_abs_eq_frameMult hxhalf]
  push_cast
  simp only [smul_eq_mul]
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

/-- The nonnegative center-series majorant, used directly in the norm profile. -/
theorem integralCellCenter_norm {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    ‖integralCellCenter Ω D‖ ≤ (frameBound w - frameBound (w / 2) / 2) * ‖D‖ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, mul_zero, le_refl]
  letI : NeZero d := ⟨hd.ne'⟩
  have hA : ‖I • adL Ω‖ ≤ w := by
    rw [closedCell_norm_smul I (adL Ω), Complex.norm_I, one_mul]
    exact (fact_adjoint Ω Ω Ω hΩ hwid 0).1.2.2.2.2
  let c : ℕ → ℝ := fun n ↦ (1 - (1 / 2 : ℝ)^(n + 1)) *
    |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ)
  have hw0 : 0 ≤ w := (norm_nonneg (I • adL Ω)).trans hA
  obtain ⟨hc, hs, hsum⟩ := cellConstant_positive_power_series
    (show |w| < 2 * π by rwa [abs_of_nonneg hw0])
  have hseries := integralCellCenter_series D (hA.trans_lt hw)
  have hterm (n : ℕ) : ‖(c n : ℂ) • (adL Ω ^ n) D‖ ≤ c n * w^n * ‖D‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
    have hop : ‖(adL Ω ^ n) D‖ ≤ w^n * ‖D‖ :=
      ((adL Ω ^ n).le_opNorm D).trans
        (mul_le_mul_of_nonneg_right (ad_power_norm_le hΩ hwid n) (norm_nonneg D))
    exact (mul_le_mul_of_nonneg_left hop (hc n)).trans_eq (by ring)
  rw [hseries.2, norm_neg]
  have hbound := hseries.1.hasSum.norm_le_of_bounded (hs.mul_right ‖D‖).hasSum hterm
  rw [tsum_mul_right, ← hsum, cellConstant_eq_frameBound hw0 hw] at hbound
  exact hbound

/-- The final equality in Lemma A.1: unitary invariance applied to the
verified integral guess leaves exactly its center-plus-integral bracket. -/
theorem integralCell_norm_eq_integral {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (D : 𝕄) (τ : ℝ) :
    ‖integralCell Ω D τ‖ = ‖integralCell Ω D 0 +
      ∫ s in (0 : ℝ)..τ, s • (evol Ω (-s) * D * evol Ω s)‖ := by
  rw [(cell_integral_ansatz_verified Ω D).1 τ,
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
      -(∑' n : ℕ, (((1 - (1 / 2 : ℝ)^(n + 1)) * |((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) • (adL Ω ^ n) D) +
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
      have hA : ‖I • adL Ω‖ < 2 * π := by
        rw [closedCell_norm_smul I (adL Ω), Complex.norm_I, one_mul]
        exact ((fact_adjoint Ω Ω Ω hΩ hwid 0).1.2.2.2.2).trans_lt hw
      rw [(integralCellCenter_series D hA).2]


end UnitaryProducts.PaperProof
