/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.PositiveSeries

/-! # Monotonicity of the multiplier

Theorems 4.4 and 4.6 use the positive Taylor coefficients of `𝒩` to prove its monotonicity and the
nonnegativity of its derivative on `[0, 2π)`.
-/

@[expose] public section

open scoped Real Topology
open Set Filter

noncomputable section

namespace RoundedClocks

/-- `𝒩` is monotone on `[0, 2π)`. -/
theorem 𝒩_monotoneOn : MonotoneOn 𝒩 (Ico 0 (2 * π)) := by
  have habs {z : ℝ} (hz : z ∈ Ico 0 (2 * π)) : |z| < 2 * π := by
    rw [abs_of_nonneg hz.1]
    exact hz.2
  intro x hx y hy hxy
  rw [← multiplierCoeff_series_eq x (habs hx), ← multiplierCoeff_series_eq y (habs hy)]
  exact Summable.tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy n) (multiplierCoeff_nonneg n))
    (summable_multiplierCoeff_power (habs hx)) (summable_multiplierCoeff_power (habs hy))

/-- `𝒩` is even. -/
theorem 𝒩_neg (x : ℝ) : 𝒩 (-x) = 𝒩 x := by
  unfold 𝒩
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx, Real.cot_eq_cos_div_sin,
      Real.cot_eq_cos_div_sin, neg_div, Real.cos_neg, Real.sin_neg]
    ring

/-- `𝒩(0) ≤ 𝒩(w)` for `0 ≤ w < 2π`. -/
theorem 𝒩_zero_le {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 𝒩 0 ≤ 𝒩 w :=
  𝒩_monotoneOn ⟨le_rfl, by positivity⟩ ⟨hw0, hw⟩ hw0

/-- `𝒩(w) ≥ 0` for `0 ≤ w < 2π`. -/
theorem 𝒩_nonneg_of_width {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 0 ≤ 𝒩 w :=
  (show (0 : ℝ) ≤ 𝒩 0 by norm_num [𝒩]).trans (𝒩_zero_le hw0 hw)

/-- `𝒩'(w) ≥ 0` for `0 ≤ w < 2π`. -/
theorem deriv_𝒩_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 0 ≤ deriv 𝒩 w := by
  rcases hw0.eq_or_lt with rfl | hpos
  · have h := deriv_comp_neg 𝒩 0
    simp only [𝒩_neg, neg_zero] at h
    linarith
  · have hnhds : Ioo 0 (2 * π) ∈ 𝓝 w := Ioo_mem_nhds hpos hw
    rw [← derivWithin_of_mem_nhds hnhds]
    exact (𝒩_monotoneOn.mono Ioo_subset_Ico_self).derivWithin_nonneg

end RoundedClocks
