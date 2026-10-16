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

/-- Scalar multiples of the adjoint map have the expected frame-series entries.
This is the convergent power-series calculation used at the corrector center. -/
theorem frameSeries_smul_ad_entry [NeZero d] (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄)
    (z : ℂ) (hz : ‖z • adL Ω‖ < 2 * π) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * (frameSeries (z • adL Ω) D) * U) p q =
      frameSeries (z * ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ)) *
        (star U * D * U) p q := by
  intro U
  have hs := (summable_norm_frameSeries_terms (z • adL Ω) hz).of_norm
  have hsD := (ContinuousLinearMap.apply ℂ 𝕄 D).summable hs
  have he := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).map_tsum hsD
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.apply_apply,
    show ∀ X : 𝕄, entryCLM p q X = X p q from fun _ ↦ rfl] at he
  rw [frameSeries, frameSeries, tsum_apply_of_summable hs, he, ← tsum_mul_right]
  refine tsum_congr fun n ↦ ?_
  rw [ContinuousLinearMap.smul_apply, UnitaryProducts.Prose.complex_smul_pow z (adL Ω) n,
    ContinuousLinearMap.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    ad_power_eigenbasis_entry]
  simp only [mul_pow, smul_eq_mul]
  ring

/-- Scalar norm identity instantiated only after elaboration in a generic algebra. -/
theorem closedCell_norm_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (z : ℂ) (a : A) : ‖z • a‖ = ‖z‖ * ‖a‖ := norm_smul z a

/-- The two inequalities in Appendix A's general positive-series estimate,
stated in a generic normed algebra before specializing to adjoint operators. -/
theorem norm_nonnegative_power_series_le {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [NormOneClass A]
    (a : A) {w : ℝ} (haw : ‖a‖ ≤ w) (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable (fun n ↦ c n * w ^ n)) :
    ‖∑' n, (c n : ℂ) • a ^ n‖ ≤ ∑' n, c n * ‖a‖ ^ n ∧
      (∑' n, c n * ‖a‖ ^ n) ≤ ∑' n, c n * w ^ n := by
  have hterm (n : ℕ) : c n * ‖a‖ ^ n ≤ c n * w ^ n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) haw n) (hc n)
  have hsmall : Summable (fun n ↦ c n * ‖a‖ ^ n) :=
    Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (hc n) (pow_nonneg (norm_nonneg a) n)) hterm hs
  have hnorm (n : ℕ) : ‖(c n : ℂ) • a ^ n‖ ≤ c n * ‖a‖ ^ n := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
    exact mul_le_mul_of_nonneg_left (norm_pow_le a n) (hc n)
  have hsNorm := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hnorm hsmall
  exact ⟨(norm_tsum_le_tsum_norm hsNorm).trans (hsNorm.tsum_le_tsum hnorm hsmall),
    hsmall.tsum_le_tsum hterm hs⟩

/-- Equation `eq:series-bound`: the spectral multiplier of a convergent series
with nonnegative coefficients satisfies both displayed operator-norm bounds. -/
theorem spectralMultiplier_nonnegative_series_bound [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ}
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hs : Summable (fun n ↦ c n * w ^ n)) :
    ‖spectralMultiplier Ω hΩ (fun x ↦ ∑' n, c n * x ^ n)‖ ≤
      ∑' n, c n * ‖adL Ω‖ ^ n ∧
    (∑' n, c n * ‖adL Ω‖ ^ n) ≤ ∑' n, c n * w ^ n := by
  rw [spectralMultiplier_eq_series_signed hΩ hw
    (by simpa only [abs_of_nonneg (hc _)] using hs)]
  exact norm_nonnegative_power_series_le (adL Ω)
    (by simpa only [pow_one] using ad_power_norm_le hΩ hw 1) c hc hs

/-- The nonnegative-coefficient expansion in equation `eq:N-series`, valid for
both signs of the frequency. -/
theorem frameMult_positive_power_series {x : ℝ} (hx : |x| < 2 * π) :
    frameMult x = ∑' n : ℕ,
      |((bernoulli (n+2) : ℚ) : ℝ)| / (Nat.factorial (n+2) : ℝ) * x^n := by
  rw [← frameBound_abs_eq_frameMult hx, frameBound_abs, frameBound]
  exact tsum_congr fun n ↦ by ring

/-- The Taylor coefficients of the positive cosecant center multiplier are
`(1 - 2^(-n-1)) νₙ`. This verifies the center guess and its coefficient signs. -/
theorem cellConstant_positive_power_series {x : ℝ} (hx : |x| < 2 * π) :
    let c : ℕ → ℝ := fun n ↦ (1 - (1 / 2 : ℝ)^(n + 1)) *
      |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ)
    (∀ n, 0 ≤ c n) ∧ Summable (fun n ↦ c n * x^n) ∧
      cellConstant x = ∑' n, c n * x^n := by
  intro c
  have hs (y : ℝ) (hy : |y| < 2 * π) :
      Summable (fun n : ℕ ↦ |((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) * y^n) := by
    apply (summable_frameBound_majorant (abs_nonneg y) hy).of_norm_bounded
    intro n
    simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_abs, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ (Nat.factorial (n + 2) : ℝ) from
        Nat.cast_nonneg _)]
    exact le_of_eq (by ring)
  have hxhalf : |x / 2| < 2 * π := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg x, pi_pos]
  have hsub := (hs x hx).sub ((hs (x / 2) hxhalf).mul_right (1 / 2 : ℝ))
  have he (n : ℕ) :
      |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) * x^n -
      (|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) * (x / 2)^n) *
        (1 / 2 : ℝ) = c n * x^n := by
    dsimp [c]
    rw [pow_succ, div_pow, div_pow]
    ring
  refine ⟨fun n ↦ div_nonneg
    (mul_nonneg (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))
      (abs_nonneg _)) (Nat.cast_nonneg _), hsub.congr he, ?_⟩
  rw [cellConstant_eq_frameMult hx, frameMult_positive_power_series hx,
    frameMult_positive_power_series hxhalf, div_eq_mul_inv, ← tsum_mul_right,
    ← (hs x hx).tsum_sub ((hs (x / 2) hxhalf).mul_right (2 : ℝ)⁻¹)]
  exact tsum_congr fun n ↦ by simpa only [one_div] using he n

end UnitaryProducts.PaperProof
