/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-! The rationalized phase and axis-angle limits in Example 5.2. -/

@[expose] public section

open Filter Topology Real

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- First-order scaling of a differentiable scalar function at the small axis angle. -/
theorem scaled_derivative_limit {f : ℝ → ℝ} {b a : ℝ} {x : ℕ → ℝ}
    (hf : HasDerivAt f b 0) (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (f (x n) - f 0)) atTop (𝓝 (a * b)) := by
  have hd := (continuousAt_dslope_same.mpr hf.differentiableAt).tendsto
  rw [dslope_same, hf.deriv] at hd
  apply (ha.mul (hd.comp hx)).congr'
  apply Eventually.of_forall
  intro n
  have he := sub_smul_dslope f 0 (x n)
  simp only [sub_zero, smul_eq_mul] at he
  dsimp only [Function.comp_def]
  rw [mul_assoc, he]

/-- Rationalizing the difference of the two rotation phases avoids cancellation. -/
theorem phase_defect_rationalized {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (θ : ℝ) :
    t * (Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) / 2 - a * t / 2) =
      θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a)) := by
  have hinside : a ^ 2 * t ^ 2 + θ ^ 2 = t ^ 2 * (a ^ 2 + (θ / t) ^ 2) := by
    field_simp
  have hroot : Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) =
      t * Real.sqrt (a ^ 2 + (θ / t) ^ 2) := by
    rw [hinside, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hden : Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg (θ / t)))
  rw [hroot]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hden)).mpr
  calc
    t * (t * Real.sqrt (a ^ 2 + (θ / t) ^ 2) / 2 - a * t / 2) *
        (2 * (Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a)) =
        t ^ 2 * ((Real.sqrt (a ^ 2 + (θ / t) ^ 2)) ^ 2 - a ^ 2) := by ring
    _ = θ ^ 2 := by rw [hs]; field_simp; ring

/-- The phase displacement used in Example 5.2(i); `a = π` gives
`T (ρ - πT/2) → θ²/(4π)`. The full-turn proof uses `a = 2π`. -/
theorem phase_defect_limit {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2))
      atTop (𝓝 (θ ^ 2 / (4 * a))) := by
  have hzero : Tendsto (fun T : ℕ ↦ θ / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat θ
  have hroot : Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2))
      atTop (𝓝 a) := by
    have harg : Tendsto (fun T : ℕ ↦ a ^ 2 + (θ / (T : ℝ)) ^ 2)
        atTop (𝓝 (a ^ 2)) := by
      simpa using (tendsto_const_nhds (x := a ^ 2)).add (hzero.pow 2)
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    rw [Real.sqrt_sq ha.le] at hs
    exact hs
  have hlim : Tendsto (fun T : ℕ ↦ θ ^ 2 /
      (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) atTop
      (𝓝 (θ ^ 2 / (2 * (a + a)))) :=
    tendsto_const_nhds.div ((hroot.add_const a).const_mul 2)
      (by positivity : 2 * (a + a) ≠ 0)
  have heq : (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)) =ᶠ[atTop]
      (fun T : ℕ ↦ θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact phase_defect_rationalized ha (by exact_mod_cast hT) θ
  simpa only [show 2 * (a + a) = 4 * a by ring] using hlim.congr' heq.symm

/-- The unscaled phase defect tends to zero; this is the small quantity in
Example 5.2(ii). -/
theorem phase_defect_tendsto_zero {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)
      atTop (𝓝 0) := by
  have hp := (phase_defect_limit ha θ).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  field_simp

/-- Scaling the axis parameter a/T cancels T on the eventual positive tail. -/
theorem scaled_div_limit (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (a / n)) atTop (𝓝 a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- The arctangent axis angle has the same first-order scaling as its argument. -/
theorem scaled_arctan_limit (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.arctan (a / n)) atTop (𝓝 a) := by
  simpa using scaled_derivative_limit (Real.hasDerivAt_arctan 0)
    (tendsto_const_div_atTop_nhds_zero_nat a) (scaled_div_limit a)

end RoundedClocks.PrecessingSpin
