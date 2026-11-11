/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib

/-! # The elementary half-gap limit in the walk coefficient asymptotics -/
@[expose] public section
noncomputable section
open Real Set Filter
open scoped Topology
namespace UnitaryProducts.PaperProof

/-- The cosine denominator in the walk bounds is the sine of the quarter gap. -/
theorem cos_gap_identity (θ : ℝ) :
    Real.cos ((2 * π - θ) / 4) = Real.sin (θ / 4) := by
  rw [show (2 * π - θ) / 4 = π / 2 - θ / 4 by ring, Real.cos_pi_div_two_sub]

/-- The scalar limit used in the walk coefficient asymptotics follows from
continuity of `sinc` at zero. It does not require an old walk comparison theorem. -/
theorem tendsto_gap_div_cos :
    Tendsto (fun θ : ℝ ↦ θ / Real.cos ((2 * π - θ) / 4)) (𝓝[>] 0) (𝓝 4) := by
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  have hsinc : ContinuousAt (fun θ : ℝ ↦ Real.sinc (θ / 4)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 4)).continuousAt
  have hs0 : Real.sinc ((0 : ℝ) / 4) ≠ 0 := by rw [zero_div, Real.sinc_zero]; norm_num
  have hcontinuous : ContinuousAt (fun θ : ℝ ↦ 4 / Real.sinc (θ / 4)) 0 :=
    continuousAt_const.div hsinc hs0
  have hlimit : Tendsto (fun θ : ℝ ↦ 4 / Real.sinc (θ / 4)) (𝓝[>] 0) (𝓝 4) := by
    simpa only [zero_div, Real.sinc_zero, div_one] using
      hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  refine hlimit.congr' ?_
  filter_upwards [hev] with θ hθ
  have hs : Real.sin (θ / 4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, pi_pos])).ne'
  rw [cos_gap_identity, Real.sinc_of_ne_zero (div_ne_zero hθ.1.ne' four_ne_zero)]
  field_simp

end UnitaryProducts.PaperProof
