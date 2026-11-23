/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Constants at width pi

Fact B.1 evaluates the multiplier and its derivative at width `π`, then derives the constants used
in Theorem A.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- At `π`, the multiplier and its derivative have the values displayed in Fact B.1. -/
theorem multiplier_values_at_pi :
    𝒩 π = 1 / π ^ 2 ∧ deriv 𝒩 π = 1 / (4 * π) - 2 / π ^ 3 := by
  have hvalue : 𝒩 π = 1 / π ^ 2 := by
    simp only [𝒩, if_neg Real.pi_ne_zero, Real.cot_eq_cos_div_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, mul_zero, sub_zero]
  refine ⟨hvalue, ?_⟩
  let f : ℝ → ℝ := fun x ↦
    (1 - (x / 2) * (Real.cos (x / 2) / Real.sin (x / 2))) / x ^ 2
  have he : 𝒩 =ᶠ[𝓝 π] f := by
    filter_upwards [eventually_ne_nhds Real.pi_ne_zero] with x hx
    simp only [𝒩, if_neg hx, Real.cot_eq_cos_div_sin, f]
  have hh := (hasDerivAt_id π).div_const 2
  have hd := ((hasDerivAt_const π (1 : ℝ)).sub
    (hh.mul (hh.cos.div hh.sin (by simp [Real.sin_pi_div_two])))).div
      ((hasDerivAt_id π).pow 2) (pow_ne_zero _ Real.pi_ne_zero)
  have hd' : HasDerivAt f (1 / (4 * π) - 2 / π ^ 3) π := by
    convert hd using 1
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    field_simp
    ring
  exact (he.hasDerivAt_iff.mpr hd').deriv

/-- The three rational decimal bounds used in Fact B.1. -/
theorem constants_pi_decimal_bounds :
    2 * (1 / (2 * π) - 1 / π ^ 2) < (116 / 1000 : ℝ) ∧
    1 / 24 + 1 / π ^ 2 < (143 / 1000 : ℝ) ∧
    5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 < (61 / 1000 : ℝ) := by
  have hlo : (10000 / 31416 : ℝ) ≤ 1 / π := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d4]
  have hhi : 1 / π ≤ (10000 / 31415 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_gt_d4]
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 2
  have hsqhi := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / π) hhi 2
  have hcubelo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 3
  refine ⟨?_, ?_, ?_⟩
  · rw [show 2 * (1 / (2 * π) - 1 / π ^ 2) = 1 / π - 2 * (1 / π) ^ 2 by ring]
    linarith
  · rw [show 1 / π ^ 2 = (1 / π) ^ 2 by ring]
    linarith
  · rw [show 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 =
        5 / 8 * (1 / π) - 1 / 4 * (1 / π) ^ 2 - 4 * (1 / π) ^ 3 + 1 / 64 by
      ring]
    linarith

/-- A Lipschitz derivative is bounded at each endpoint by its supremum on `[0,1]`. -/
theorem endpoint_derivatives_le_supNorm {H : ℝ → 𝕄} {L : ℝ}
    (hH : HasLipschitzDerivative H L) : ‖∂H 0‖ ≤ ‖∂H‖∞ ∧ ‖∂H 1‖ ≤ ‖∂H‖∞ := by
  have hL : 0 ≤ L := by
    have h := hH.2 0 (by norm_num) 1 (by norm_num)
    norm_num at h
    exact (norm_nonneg _).trans h
  have hlip : LipschitzOnWith ⟨L, hL⟩ (∂H) (Icc (0 : ℝ) 1) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      simpa only [dist_eq_norm, Real.dist_eq] using hH.2 x hx y hy
  exact ⟨hlip.continuousOn.norm.le_sSup_image_Icc (by norm_num),
    hlip.continuousOn.norm.le_sSup_image_Icc (by norm_num)⟩

/-- Fact B.1 after substituting the three exact values and bounding both endpoints. -/
theorem energy_pi_bound (H : ℝ → 𝕄) (L : ℝ) (hH : HasLipschitzDerivative H L) :
    ℰ π L H ≤ 0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2 := by
  have hL : 0 ≤ L := by
    have h := hH.2 0 (by norm_num) 1 (by norm_num)
    norm_num at h
    exact (norm_nonneg _).trans h
  have hc0 : c₀ π = 1 / (2 * π) - 1 / π ^ 2 := by
    simp only [c₀, if_neg Real.pi_ne_zero, Real.sin_pi_div_two]
    ring
  have hN := multiplier_values_at_pi
  have hend := endpoint_derivatives_le_supNorm hH
  have hsup : 0 ≤ ‖∂H‖∞ := (norm_nonneg _).trans hend.1
  have hc0_nonneg : 0 ≤ 1 / (2 * π) - 1 / π ^ 2 := by
    rw [show 1 / (2 * π) - 1 / π ^ 2 = (π - 2) / (2 * π ^ 2) by
      field_simp [Real.pi_ne_zero]]
    exact div_nonneg (sub_nonneg.mpr (by linarith [Real.pi_gt_three])) (by positivity)
  obtain ⟨hc, hLcoeff, hquad⟩ := constants_pi_decimal_bounds
  rw [ℰ, c₁, hc0, hN.1, hN.2]
  have hends :
      (1 / (2 * π) - 1 / π ^ 2) * (‖∂H 0‖ + ‖∂H 1‖) ≤
        (116 / 1000 : ℝ) * ‖∂H‖∞ := by
    calc
      _ ≤ (1 / (2 * π) - 1 / π ^ 2) * (‖∂H‖∞ + ‖∂H‖∞) :=
        mul_le_mul_of_nonneg_left (add_le_add hend.1 hend.2) hc0_nonneg
      _ = (2 * (1 / (2 * π) - 1 / π ^ 2)) * ‖∂H‖∞ := by ring
      _ ≤ (116 / 1000 : ℝ) * ‖∂H‖∞ := mul_le_mul_of_nonneg_right hc.le hsup
  have hcoeff := add_le_add (add_le_add hends
    (mul_le_mul_of_nonneg_right hLcoeff.le hL))
    (mul_le_mul_of_nonneg_right hquad.le (sq_nonneg ‖∂H‖∞))
  rw [show (1 / (2 * π) - 1 / π ^ 2) / 4 + 1 / 64 +
      2 * (1 / (4 * π) - 2 / π ^ 3) =
      5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 by ring]
  norm_num at hcoeff ⊢
  exact hcoeff

end RoundedClocks
