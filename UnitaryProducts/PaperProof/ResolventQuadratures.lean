/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Prose.ChainSteps

/-! # The substitution `v = 2u - 1` in Lemma A.2 -/
@[expose] public section
noncomputable section
open Real Set MeasureTheory
open UnitaryProducts.Paper UnitaryProducts.Prose
namespace UnitaryProducts.PaperProof

/-- The squared scalar radius after the centered substitution. -/
def radius (w v : ℝ) : ℝ := Real.cos (w / 4) ^ 2 + v ^ 2 * Real.sin (w / 4) ^ 2

/-- The radius is positive throughout the integration interval, indeed on the real line. -/
theorem radius_pos {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    0 < radius w v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The two endpoint radii in the last antiderivative evaluation are one. -/
theorem radius_endpoints (w : ℝ) : radius w (-1) = 1 ∧ radius w 1 = 1 := by
  simp [radius, Real.cos_sq_add_sin_sq]

/-- The exact first antiderivative printed in Lemma A.2. -/
theorem arctan_antiderivative {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.arctan (v * Real.tan (w / 4)) / Real.sin (w / 2))
      (1 / (2 * radius w v)) v := by
  have h := (chord_arctan_antiderivative hw0 hw v).div_const 2
  have hsin : Real.sin (w / 2) = 2 * Real.sin (w / 4) * Real.cos (w / 4) := by
    rw [show w / 2 = 2 * (w / 4) by ring, Real.sin_two_mul]
  convert h using 1
  · ext x
    rw [hsin]
    ring
  · simp only [radius, mul_comm (v ^ 2), one_div, mul_inv_rev]
    ring

/-- The exact second antiderivative printed in Lemma A.2, using square roots. -/
theorem cube_antiderivative {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ v / (Real.cos (w / 4) ^ 2 * Real.sqrt (radius w v)))
      (1 / Real.sqrt (radius w v) ^ 3) v := by
  simpa only [radius, mul_comm (Real.sin (w / 4) ^ 2)] using
    chord_cube_antiderivative hw0 hw v

/-- The first line of Lemma A.2's quadrature display, including zero width. -/
theorem square_quadrature {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (1 / 2 : ℝ) * (∫ v : ℝ in (-1 : ℝ)..1, 1 / radius w v) = walkLogSlope w := by
  by_cases hz : w = 0
  · subst w
    norm_num [radius, walkLogSlope_zero]
  · have hp : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hz)
    have hcont : Continuous (fun v : ℝ ↦ 1 / (2 * radius w v)) :=
      continuous_const.div (by unfold radius; fun_prop)
        (fun v ↦ mul_ne_zero (by norm_num) (radius_pos hw0 hw v).ne')
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-1 : ℝ)) (b := 1)
      (fun v _ ↦ arctan_antiderivative hp hw v) (hcont.intervalIntegrable _ _)
    have hid (v : ℝ) : 1 / (2 * radius w v) = (1 / 2 : ℝ) * (1 / radius w v) := by ring
    simp_rw [hid] at hFTC
    rw [intervalIntegral.integral_const_mul] at hFTC
    rw [hFTC]
    simp only [one_mul, neg_one_mul, Real.arctan_neg]
    rw [Real.arctan_tan (by linarith [pi_pos]) (by linarith),
      ← walkLogSlope_closed hw0 hw, if_neg hz]
    ring

/-- The last quadrature of Lemma A.2, from the second antiderivative and `r(±1)=1`. -/
theorem cube_quadrature {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (1 / 2 : ℝ) * (∫ v : ℝ in (-1 : ℝ)..1, 1 / Real.sqrt (radius w v) ^ 3) =
      1 / Real.cos (w / 4) ^ 2 := by
  have hcont : Continuous (fun v : ℝ ↦ 1 / Real.sqrt (radius w v) ^ 3) :=
    continuous_const.div ((Real.continuous_sqrt.comp (by unfold radius; fun_prop)).pow 3)
      (fun v ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (radius_pos hw0 hw v)).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ ↦ cube_antiderivative hw0 hw v) (hcont.intervalIntegrable _ _)]
  rw [(radius_endpoints w).1, (radius_endpoints w).2, Real.sqrt_one]
  ring

/-- The integrand `v r(v)^(-3/2)` in Lemma A.2 is odd. -/
theorem cube_odd (w : ℝ) :
    Function.Odd (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) := by
  intro v
  simp only [radius, neg_sq, neg_div]

/-- The odd part of the weight `1+v` integrates to zero. -/
theorem cube_odd_integral (w : ℝ) :
    (∫ v : ℝ in (-1 : ℝ)..1, v / Real.sqrt (radius w v) ^ 3) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) (a := (-1 : ℝ)) (b := 1)
  have hodd (v : ℝ) : (-v) / Real.sqrt (radius w (-v)) ^ 3 =
      -(v / Real.sqrt (radius w v) ^ 3) := cube_odd w v
  simp only [hodd, intervalIntegral.integral_neg, neg_neg] at h
  linarith

/-- The fifth line of the norm display removes the odd summand explicitly. -/
theorem cube_weighted_integral {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / Real.sqrt (radius w v) ^ 3) =
      ∫ v : ℝ in (-1 : ℝ)..1, 1 / Real.sqrt (radius w v) ^ 3 := by
  have hcont : Continuous (fun v : ℝ ↦ 1 / Real.sqrt (radius w v) ^ 3) :=
    continuous_const.div ((Real.continuous_sqrt.comp (by unfold radius; fun_prop)).pow 3)
      (fun v ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (radius_pos hw0 hw v)).ne')
  have hoddcont : Continuous (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) := by
    convert continuous_id.mul hcont using 1
    ext v
    exact (mul_one_div v (Real.sqrt (radius w v) ^ 3)).symm
  simp_rw [add_div]
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
    (hoddcont.intervalIntegrable _ _),
    cube_odd_integral, add_zero]

/-- The substitution in the second and fourth lines, before cancelling odd terms. -/
theorem quadrature_substitution (w : ℝ) :
    (∫ u : ℝ in (0 : ℝ)..1, 1 / radius w (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, 1 / radius w v ∧
    (∫ u : ℝ in (0 : ℝ)..1, (2 * u) / Real.sqrt (radius w (2 * u - 1)) ^ 3) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / Real.sqrt (radius w v) ^ 3 := by
  refine ⟨chord_change_variable (fun v ↦ 1 / radius w v), ?_⟩
  have h := chord_change_variable (fun v ↦ (1 + v) / Real.sqrt (radius w v) ^ 3)
  simpa only [show ∀ u : ℝ, 1 + (2 * u - 1) = 2 * u by intro u; ring] using h

/-- The paper's power `r^(3/2)` equals the cubed square root used in the quadratures. -/
theorem radius_three_halves {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    (radius w v) ^ (3 / 2 : ℝ) = Real.sqrt (radius w v) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (radius_pos hw0 hw v).le]
  congr 1
  norm_num

/-- The original resolvent denominator is the centered radius after substitution. -/
theorem radius_substitution (w u : ℝ) :
    1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2)) = radius w (2 * u - 1) := by
  rw [walkLogDenom_halfAngle]
  dsimp [radius]
  ring

/-- The scalar chord factorization written before the quadratures. -/
theorem chord_factorization (φ u : ℝ) :
    1 + (u : ℂ) * (Complex.exp (-Complex.I * (φ : ℂ)) - 1) =
      Complex.exp (-Complex.I * ((φ / 2 : ℝ) : ℂ)) *
        ((Real.cos (φ / 2) : ℂ) - Complex.I * (2 * u - 1 : ℝ) * Real.sin (φ / 2)) := by
  have hexp (x : ℝ) : Complex.exp (-Complex.I * (x : ℂ)) =
      (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
    apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]
  rw [hexp φ, hexp (φ / 2)]
  have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, show 2 * (φ / 2) = φ by ring]
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul, show 2 * (φ / 2) = φ by ring]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.one_im,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, sub_zero, zero_sub]
  · rw [hc]
    linear_combination (2 * u - 1) * Real.cos_sq_add_sin_sq (φ / 2)
  · rw [hs]
    ring

/-- The squared modulus of the scalar chord in the centered variable. -/
theorem chord_norm_sq (φ u : ℝ) :
    ‖1 + u • (Complex.exp (-Complex.I * (φ : ℂ)) - 1)‖ ^ 2 =
      1 - (1 - (2 * u - 1) ^ 2) * Real.sin (φ / 2) ^ 2 := by
  rw [Complex.real_smul, chord_factorization, norm_mul]
  have he : -Complex.I * ((φ / 2 : ℝ) : ℂ) = ((-φ / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
    mul_zero, zero_mul, sub_zero, zero_sub, one_mul, zero_add]
  linear_combination Real.cos_sq_add_sin_sq (φ / 2)

/-- The scalar squared modulus dominates the radius at the maximal phase width. -/
theorem chord_radius_lower {w φ u : ℝ} (hw : w < 2 * π)
    (hφ : |φ| ≤ w / 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    radius w (2 * u - 1) ≤
      1 - (1 - (2 * u - 1) ^ 2) * Real.sin (φ / 2) ^ 2 := by
  have h := chord_square_antitone hu (abs_nonneg φ) hφ (by linarith : w / 2 ≤ π)
  have habs : Real.sin (|φ| / 2) ^ 2 = Real.sin (φ / 2) ^ 2 := by
    rcases le_total 0 φ with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, neg_div, Real.sin_neg, neg_sq]
  rw [habs, show w / 2 / 2 = w / 4 by ring] at h
  dsimp [radius]
  linear_combination h + Real.cos_sq_add_sin_sq (w / 4)

/-- The first derivative's norm bound before either scalar integral is evaluated.
Keeping this inequality separate ensures the walk-log proof uses only the
subsequent `v = 2u - 1` quadratures. -/
theorem norm_sandwich_integral_le {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (Z : ℝ → A) (D : A) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hZ : ∀ u ∈ Icc (0 : ℝ) 1, ‖Z u‖ ≤
      (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) :
    ‖∫ u : ℝ in (0 : ℝ)..1, Z u * D * Z u‖ ≤
      ‖D‖ * (∫ u : ℝ in (0 : ℝ)..1,
        ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 2) := by
  have hc : -1 < Real.cos (w / 2) := by
    simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith : 0 ≤ w / 2) le_rfl (by linarith : w / 2 < π)
  have hpos (u : ℝ) := UnitaryProducts.walkLogDenom_pos (t := u) hc (Real.cos_le_one _)
  have hcont : Continuous (fun u : ℝ ↦
      ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 2) := by
    apply Continuous.pow
    apply Continuous.inv₀ (by fun_prop)
    exact fun u ↦ (Real.sqrt_pos.mpr (hpos u)).ne'
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall ?_) ((continuous_const.mul hcont).intervalIntegrable 0 1)
  intro u hu
  have hz := hZ u ⟨hu.1.le, hu.2⟩
  have hn : 0 ≤ (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    _ ≤ ‖Z u‖ * ‖D‖ * ‖Z u‖ := norm_mul₃_le
    _ ≤ (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ *
        ‖D‖ * (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ := by
      gcongr
    _ = _ := by dsimp only [Pi.mul_apply]; ring

/-- The weighted transformed quadrature in the paper's literal `r^(3/2)` notation.
The power bridge, odd cancellation, and primitive evaluation are all used. -/
theorem cube_rpow_weighted_quadrature {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (1 / 2 : ℝ) * (∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / (radius w v) ^ (3 / 2 : ℝ)) =
      1 / Real.cos (w / 4) ^ 2 := by
  simp_rw [radius_three_halves hw0 hw]
  rw [cube_weighted_integral hw0 hw, cube_quadrature hw0 hw]

/-- Lemma A.2's quadratures, proved by the displayed substitution, antiderivatives,
and odd cancellation in that order. This replaces the direct-`u` proof. -/
theorem resolvent_chord_quadratures {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∫ u : ℝ in (0 : ℝ)..1,
      ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 2) =
        walkLogSlope w ∧
    (∫ u : ℝ in (0 : ℝ)..1, (2 * u) *
      ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 3) =
        (Real.cos (w / 4))⁻¹ ^ 2 := by
  simp_rw [radius_substitution, inv_pow, ← one_div]
  constructor
  · simp_rw [Real.sq_sqrt (radius_pos hw0 hw _).le]
    rw [(quadrature_substitution w).1]
    exact square_quadrature hw0 hw
  · simp_rw [mul_one_div]
    rw [(quadrature_substitution w).2]
    simp_rw [← radius_three_halves hw0 hw]
    exact cube_rpow_weighted_quadrature hw0 hw

end UnitaryProducts.PaperProof
