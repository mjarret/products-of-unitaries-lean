/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Constants as the free arc closes

Fact B.2 follows from the trigonometric reflections at width `2π - ϑ` and the resulting limits of
the constants as the free arc closes.
-/

@[expose] public section

open scoped Topology Real Asymptotics
open Set Filter

noncomputable section

namespace RoundedClocks

/-- The trigonometric reflections at width `2π - ϑ`. -/
private theorem free_arc_reflections (ϑ : ℝ) :
    Real.sin ((2 * π - ϑ) / 2) = Real.sin (ϑ / 2) ∧
      Real.cos ((2 * π - ϑ) / 2) = -Real.cos (ϑ / 2) ∧
      Real.cos ((2 * π - ϑ) / 4) = Real.sin (ϑ / 4) := by
  rw [show (2 * π - ϑ) / 2 = π - ϑ / 2 by ring,
    show (2 * π - ϑ) / 4 = π / 2 - ϑ / 4 by ring,
    Real.sin_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_two_sub]
  exact ⟨rfl, rfl, rfl⟩

/-- The manuscript's closed formula for `𝒩'` on the open spectral interval. -/
theorem deriv_𝒩_closed {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    deriv 𝒩 x = -2 / x ^ 3 + Real.cot (x / 2) / (2 * x ^ 2) +
      1 / (4 * x * Real.sin (x / 2) ^ 2) := by
  let f : ℝ → ℝ := fun y ↦
    (1 - (y / 2) * (Real.cos (y / 2) / Real.sin (y / 2))) / y ^ 2
  have hxne : x ≠ 0 := hx0.ne'
  have hsin : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have he : 𝒩 =ᶠ[𝓝 x] f := by
    filter_upwards [eventually_ne_nhds hxne] with y hy
    simp only [𝒩, if_neg hy, Real.cot_eq_cos_div_sin, f]
  have hh := (hasDerivAt_id x).div_const 2
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub
    (hh.mul (hh.cos.div hh.sin hsin))).div
      ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hxne)
  have hd' : HasDerivAt f
      (-2 / x ^ 3 + Real.cot (x / 2) / (2 * x ^ 2) +
        1 / (4 * x * Real.sin (x / 2) ^ 2)) x := by
    convert hd using 1
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
      Real.cot_eq_cos_div_sin]
    norm_num
    field_simp
    ring_nf
    have htrig : Real.sin (x * (1 / 2)) ^ 2 + Real.cos (x * (1 / 2)) ^ 2 = 1 := by
      rw [show x * (1 / 2 : ℝ) = x / 2 by ring]
      exact Real.sin_sq_add_cos_sq (x / 2)
    -- The two sides differ by 4x²(sin²(x/2) + cos²(x/2) - 1).
    linear_combination (-4 * x ^ 2) * htrig
  exact (he.hasDerivAt_iff.mpr hd').deriv

/-- The four scaled limits stated in the first sentence of Fact B.2's proof. -/
theorem free_arc_edge_limits :
    Tendsto (fun ϑ ↦ ϑ * κ (2 * π - ϑ)) (𝓝[>] 0) (𝓝 (2 * π)) ∧
    Tendsto (fun ϑ ↦ ϑ * c₀ (2 * π - ϑ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun ϑ ↦ ϑ * 𝒩 (2 * π - ϑ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun ϑ ↦ ϑ ^ 2 * deriv 𝒩 (2 * π - ϑ))
      (𝓝[>] 0) (𝓝 (1 / (2 * π))) := by
  have hev : ∀ᶠ ϑ in 𝓝[>] (0 : ℝ), ϑ ∈ Ioo 0 π := Ioo_mem_nhdsGT Real.pi_pos
  have hsinc : ContinuousAt (fun ϑ : ℝ ↦ Real.sinc (ϑ / 2)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 2)).continuousAt
  have hw : ContinuousAt (fun ϑ : ℝ ↦ 2 * π - ϑ) 0 :=
    continuousAt_const.sub continuousAt_id
  have hw0 : 2 * π - 0 ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  have hc2 : ContinuousAt (fun ϑ : ℝ ↦ Real.cos (ϑ / 2)) 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt
  have hs0 : Real.sinc ((0 : ℝ) / 2) ≠ 0 := by simp
  have hgt : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 := nhdsWithin_le_nhds
  have hreflect {ϑ : ℝ} (hϑ : ϑ ≠ 0) :
      Real.sin (ϑ / 2) = ϑ / 2 * Real.sinc (ϑ / 2) ∧
      Real.sin ((2 * π - ϑ) / 2) = Real.sin (ϑ / 2) ∧
      Real.cos ((2 * π - ϑ) / 2) = -Real.cos (ϑ / 2) := by
    refine ⟨?_, (free_arc_reflections ϑ).1, (free_arc_reflections ϑ).2.1⟩
    rw [Real.sinc_of_ne_zero (div_ne_zero hϑ two_ne_zero)]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hcont : ContinuousAt (fun ϑ : ℝ ↦
        (2 * π - ϑ) / Real.sinc (ϑ / 2)) 0 := hw.div hsinc hs0
    have hlim := hcont.tendsto.mono_left hgt
    simp only [zero_div, Real.sinc_zero, sub_zero, div_one] at hlim
    apply hlim.congr'
    filter_upwards [hev] with ϑ hϑ
    have hϑ0 := hϑ.1.ne'
    have hwn : 2 * π - ϑ ≠ 0 := by linarith [hϑ.2, Real.pi_pos]
    rw [κ, if_neg hwn, (free_arc_reflections ϑ).1, (hreflect hϑ0).1]
    field_simp
  · have hcont : ContinuousAt (fun ϑ : ℝ ↦
        1 / ((2 * π - ϑ) * Real.sinc (ϑ / 2)) - ϑ / (2 * π - ϑ) ^ 2) 0 :=
      (continuousAt_const.div (hw.mul hsinc) (mul_ne_zero hw0 hs0)).sub
        (continuousAt_id.div (hw.pow 2) (pow_ne_zero _ hw0))
    have hlim := hcont.tendsto.mono_left hgt
    have heq : (fun ϑ ↦ ϑ * c₀ (2 * π - ϑ)) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun ϑ ↦ 1 / ((2 * π - ϑ) * Real.sinc (ϑ / 2)) - ϑ / (2 * π - ϑ) ^ 2) := by
      filter_upwards [hev] with ϑ hϑ
      have hϑ0 := hϑ.1.ne'
      have hwn : 2 * π - ϑ ≠ 0 := by linarith [hϑ.2, Real.pi_pos]
      rw [c₀, if_neg hwn, (free_arc_reflections ϑ).1, (hreflect hϑ0).1]
      field_simp
    have ht := hlim.congr' heq.symm
    simpa only [zero_div, Real.sinc_zero, sub_zero, mul_one] using ht
  · have hcont : ContinuousAt (fun ϑ : ℝ ↦
        ϑ / (2 * π - ϑ) ^ 2 +
          Real.cos (ϑ / 2) / (Real.sinc (ϑ / 2) * (2 * π - ϑ))) 0 :=
      (continuousAt_id.div (hw.pow 2) (pow_ne_zero _ hw0)).add
        (hc2.div (hsinc.mul hw) (mul_ne_zero hs0 hw0))
    have hlim := hcont.tendsto.mono_left hgt
    have heq : (fun ϑ ↦ ϑ * 𝒩 (2 * π - ϑ)) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun ϑ ↦ ϑ / (2 * π - ϑ) ^ 2 +
          Real.cos (ϑ / 2) / (Real.sinc (ϑ / 2) * (2 * π - ϑ))) := by
      filter_upwards [hev] with ϑ hϑ
      have hϑ0 := hϑ.1.ne'
      have hwn : 2 * π - ϑ ≠ 0 := by linarith [hϑ.2, Real.pi_pos]
      rw [𝒩, if_neg hwn, Real.cot_eq_cos_div_sin,
        (free_arc_reflections ϑ).1, (free_arc_reflections ϑ).2.1,
        (hreflect hϑ0).1]
      generalize Real.sinc (ϑ / 2) = σ
      generalize Real.cos (ϑ / 2) = γ
      field_simp
      ring
    have ht := hlim.congr' heq.symm
    simpa only [zero_div, Real.sinc_zero, Real.cos_zero, sub_zero, zero_add, one_mul] using ht
  · have hcont : ContinuousAt (fun ϑ : ℝ ↦
        -2 * ϑ ^ 2 / (2 * π - ϑ) ^ 3 -
          ϑ * Real.cos (ϑ / 2) /
            ((2 * π - ϑ) ^ 2 * Real.sinc (ϑ / 2)) +
          1 / ((2 * π - ϑ) * Real.sinc (ϑ / 2) ^ 2)) 0 :=
      (((continuousAt_const.mul (continuousAt_id.pow 2)).div
        (hw.pow 3) (pow_ne_zero _ hw0)).sub
        ((continuousAt_id.mul hc2).div ((hw.pow 2).mul hsinc)
          (mul_ne_zero (pow_ne_zero _ hw0) hs0))).add
        (continuousAt_const.div (hw.mul (hsinc.pow 2))
          (mul_ne_zero hw0 (pow_ne_zero _ hs0)))
    have hlim := hcont.tendsto.mono_left hgt
    have heq : (fun ϑ ↦ ϑ ^ 2 * deriv 𝒩 (2 * π - ϑ)) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun ϑ ↦ -2 * ϑ ^ 2 / (2 * π - ϑ) ^ 3 -
          ϑ * Real.cos (ϑ / 2) / ((2 * π - ϑ) ^ 2 * Real.sinc (ϑ / 2)) +
          1 / ((2 * π - ϑ) * Real.sinc (ϑ / 2) ^ 2)) := by
      filter_upwards [hev] with ϑ hϑ
      have hϑ0 := hϑ.1.ne'
      have hwpos : 0 < 2 * π - ϑ := by linarith [hϑ.2, Real.pi_pos]
      rw [deriv_𝒩_closed hwpos (by linarith [hϑ.1]), Real.cot_eq_cos_div_sin,
        (free_arc_reflections ϑ).1, (free_arc_reflections ϑ).2.1,
        (hreflect hϑ0).1]
      generalize Real.sinc (ϑ / 2) = σ
      generalize Real.cos (ϑ / 2) = γ
      field_simp
      ring
    have ht := hlim.congr' heq.symm
    convert ht using 1
    all_goals norm_num

/-- The quarter-gap denominator contributes the factor `4` in the proof of Fact B.2. -/
theorem tendsto_free_arc_div_cos :
    Tendsto (fun ϑ : ℝ ↦ ϑ / Real.cos ((2 * π - ϑ) / 4))
      (𝓝[>] 0) (𝓝 4) := by
  have hev : ∀ᶠ ϑ in 𝓝[>] (0 : ℝ), ϑ ∈ Ioo 0 π := Ioo_mem_nhdsGT Real.pi_pos
  have hsinc : ContinuousAt (fun ϑ : ℝ ↦ Real.sinc (ϑ / 4)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 4)).continuousAt
  have hs0 : Real.sinc ((0 : ℝ) / 4) ≠ 0 := by simp
  have hgt : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 := nhdsWithin_le_nhds
  have hlim : Tendsto (fun ϑ : ℝ ↦ 4 / Real.sinc (ϑ / 4))
      (𝓝[>] 0) (𝓝 4) := by
    simpa using (continuousAt_const.div hsinc hs0).tendsto.mono_left hgt
  apply hlim.congr'
  filter_upwards [hev] with ϑ hϑ
  have hquarter_pos : 0 < ϑ / 4 := div_pos hϑ.1 (by norm_num)
  have hquarter_lt : ϑ / 4 < π := by linarith [hϑ.2, Real.pi_pos]
  have hsin : Real.sin (ϑ / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hquarter_pos hquarter_lt).ne'
  rw [(free_arc_reflections ϑ).2.2,
    Real.sinc_of_ne_zero (div_ne_zero hϑ.1.ne' four_ne_zero)]
  field_simp

/-- Multiplying the three coefficients by their natural powers of the free arc gives the
limits displayed in Fact B.2. -/
theorem free_arc_coefficient_limits :
    Tendsto (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ) * ϑ ^ 2)
      (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ) * ϑ ^ 2)
      (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun ϑ ↦ c₂ (2 * π - ϑ) * ϑ ^ 3)
      (𝓝[>] 0) (𝓝 (8 / π + 5 * π / 2 + 2)) := by
  obtain ⟨hκ, hc0, hN, hN'⟩ := free_arc_edge_limits
  have hid : Tendsto (fun ϑ : ℝ ↦ ϑ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hc1 : Tendsto (fun ϑ ↦ ϑ * c₁ (2 * π - ϑ))
      (𝓝[>] 0) (𝓝 (1 / (8 * π))) := by
    have h := (hc0.div_const 4).add (hid.div_const 64)
    rw [zero_div, add_zero] at h
    rw [show 1 / (2 * π) / 4 = 1 / (8 * π) by ring] at h
    convert h using 1
    exact funext fun ϑ ↦ by simp only [c₁]; ring
  refine ⟨?_, ?_, ?_⟩
  · have h := hc0.mul hκ
    rw [show 1 / (2 * π) * (2 * π) = 1 by field_simp] at h
    convert h using 1
    exact funext fun ϑ ↦ by ring
  · have h := ((hid.div_const 24).add hN).mul hκ
    rw [zero_div, zero_add, show 1 / (2 * π) * (2 * π) = 1 by field_simp] at h
    convert h using 1
    exact funext fun ϑ ↦ by ring
  · have hcos := tendsto_free_arc_div_cos
    have h1 := ((hid.div_const 24).add hN).mul (hcos.pow 2)
    have h2 := hc1.mul (hκ.pow 2)
    have h3 := (hN'.const_mul 2).mul hκ
    have h4 := (hN.sub (hid.mul_const (𝒩 0))).mul (hκ.pow 2)
    have h := ((h1.add h2).add h3).add h4
    rw [show (0 / 24 + 1 / (2 * π)) * 4 ^ 2 +
        1 / (8 * π) * (2 * π) ^ 2 +
        2 * (1 / (2 * π)) * (2 * π) +
        (1 / (2 * π) - 0 * 𝒩 0) * (2 * π) ^ 2 =
        8 / π + 5 * π / 2 + 2 by field_simp; ring] at h
    convert h using 1
    exact funext fun ϑ ↦ by simp only [c₂]; ring

/-- The three asymptotic equivalents in Fact B.2. -/
theorem free_arc_equivalents :
    (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) ~[𝓝[>] 0]
      (fun ϑ ↦ 1 / ϑ ^ 2) ∧
    (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) ~[𝓝[>] 0]
      (fun ϑ ↦ 1 / ϑ ^ 2) ∧
    (fun ϑ ↦ c₂ (2 * π - ϑ)) ~[𝓝[>] 0]
      (fun ϑ ↦ (8 / π + 5 * π / 2 + 2) / ϑ ^ 3) := by
  have convert_limit (f : ℝ → ℝ) (p : ℕ) (c : ℝ) (hc : c ≠ 0)
      (h : Tendsto (fun ϑ ↦ f ϑ * ϑ ^ p) (𝓝[>] 0) (𝓝 c)) :
      f ~[𝓝[>] 0] (fun ϑ ↦ c / ϑ ^ p) := by
    apply Asymptotics.isEquivalent_of_tendsto_one
    have hh := h.div_const c
    rw [div_self hc] at hh
    simpa only [Pi.div_def, div_div_eq_mul_div] using hh
  obtain ⟨h1, h2, h3⟩ := free_arc_coefficient_limits
  exact ⟨convert_limit _ 2 1 one_ne_zero h1,
    convert_limit _ 2 1 one_ne_zero h2,
    convert_limit _ 3 _ (by positivity) h3⟩

/-- Each coefficient is also bounded by the common inverse-cube scale. -/
theorem free_arc_isBigO :
    (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) =O[𝓝[>] 0]
      (fun ϑ ↦ 1 / ϑ ^ 3) ∧
    (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) =O[𝓝[>] 0]
      (fun ϑ ↦ 1 / ϑ ^ 3) ∧
    (fun ϑ ↦ c₂ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) := by
  have of_scaled_limit (f : ℝ → ℝ) (c : ℝ)
      (h : Tendsto (fun ϑ ↦ f ϑ * ϑ ^ 3) (𝓝[>] 0) (𝓝 c)) :
      f =O[𝓝[>] 0] (fun ϑ : ℝ ↦ 1 / ϑ ^ 3) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c ?_
    · filter_upwards [self_mem_nhdsWithin] with ϑ hϑ
      have hϑpos : 0 < ϑ := by simpa only [mem_Ioi] using hϑ
      intro hzero
      exact (one_div_ne_zero (pow_ne_zero 3 hϑpos.ne')) hzero |>.elim
    · simpa only [Pi.div_def, div_div_eq_mul_div, div_one] using h
  obtain ⟨h1, h2, h3⟩ := free_arc_coefficient_limits
  have hid : Tendsto (fun ϑ : ℝ ↦ ϑ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨of_scaled_limit _ 0 ?_, of_scaled_limit _ 0 ?_,
    of_scaled_limit _ (8 / π + 5 * π / 2 + 2) h3⟩
  · have h := h1.mul hid
    rw [mul_zero] at h
    convert h using 1
    exact funext fun ϑ ↦ by ring
  · have h := h2.mul hid
    rw [mul_zero] at h
    convert h using 1
    exact funext fun ϑ ↦ by ring

end RoundedClocks
