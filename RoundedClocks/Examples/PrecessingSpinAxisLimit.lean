/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinLimits
public import RoundedClocks.Examples.PrecessingSpinMatrix

/-! The fourth norm display of Example 5.2, in axis-angle coordinates. -/

@[expose] public section

open Filter Topology Real
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- The Z axis has unit operator norm, as used in the fourth norm display. -/
theorem norm_Z : ‖Z‖ = 1 := by
  have h := congrArg norm matrix_relations.2.2.2.1
  rw [matrix_relations.2.1.isSelfAdjoint.norm_mul_self, norm_one] at h
  exact (sq_eq_sq₀ (norm_nonneg Z) zero_le_one).mp (by simpa using h)

/-- Multiplying a small angle by its sine preserves its first-order limit. -/
theorem scaled_sin_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.sin (x n)) atTop (𝓝 a) := by
  simpa only [Real.sin_zero, Real.cos_zero, sub_zero, mul_one] using
    scaled_derivative_limit (Real.hasDerivAt_sin 0) hx ha

/-- A small angle with bounded first-order scaling has cosine defect
negligible at first order. -/
theorem scaled_cos_sub_one_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (Real.cos (x n) - 1)) atTop (𝓝 0) := by
  simpa only [Real.cos_zero, Real.sin_zero, neg_zero, mul_zero] using
    scaled_derivative_limit (Real.hasDerivAt_cos 0) hx ha

/-- The axes in the norm display have the first-order separation asserted
in Example 5.2(i); the cosine defect contributes zero at that order. -/
theorem odd_axis_norm_limit (θ : ℝ) :
    let ζ := fun n : ℕ ↦ Real.sqrt (π ^ 2 * (n : ℝ) ^ 2 + θ ^ 2) / 2 - π * n / 2
    let α := fun n : ℕ ↦ θ / (2 * n)
    let β := fun n : ℕ ↦ Real.arctan (θ / (π * n))
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ‖(Real.cos (α n) • X - Real.sin (α n) • Z) -
      (Real.cos (ζ n) : ℂ) • (Real.cos (β n) • X - Real.sin (β n) • Z)‖)
      atTop (𝓝 ((π - 2) * |θ| / (2 * π))) := by
  intro ζ α β
  have hα : Tendsto α atTop (𝓝 0) := by
    simpa [α, div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ / 2)
  have hnα : Tendsto (fun n : ℕ ↦ (n : ℝ) * α n) atTop (𝓝 (θ / 2)) := by
    simpa only [α, div_div] using scaled_div_limit (θ / 2)
  have hβ : Tendsto β atTop (𝓝 0) := by
    have hh := (Real.continuous_arctan.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (θ / π))
    simpa [β, div_div] using hh
  have hnβ : Tendsto (fun n : ℕ ↦ (n : ℝ) * β n) atTop (𝓝 (θ / π)) := by
    simpa only [β, div_div] using scaled_arctan_limit (θ / π)
  have hcα := scaled_cos_sub_one_limit hα hnα
  have hcβ := scaled_cos_sub_one_limit hβ hnβ
  have hcζ := scaled_cos_sub_one_limit
    (phase_defect_tendsto_zero pi_pos θ) (phase_defect_limit pi_pos θ)
  have hcβ0 : Tendsto (fun n ↦ Real.cos (β n)) atTop (𝓝 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp hβ
  have hsβ0 : Tendsto (fun n ↦ Real.sin (β n)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sin.tendsto 0).comp hβ
  have hx := (hcα.sub hcβ).sub (hcζ.mul hcβ0)
  have hz := ((scaled_sin_limit hβ hnβ).sub (scaled_sin_limit hα hnα)).add
    (hcζ.mul hsβ0)
  have hv := (hx.smul_const X).add (hz.smul_const Z)
  have hh := hv.norm
  simp only [sub_zero, zero_mul, add_zero, zero_smul, zero_add,
    norm_smul, Real.norm_eq_abs, norm_Z, mul_one] at hh
  have habs : |θ / π - θ / 2| = (π - 2) * |θ| / (2 * π) := by
    rw [show θ / π - θ / 2 = -((π - 2) * θ / (2 * π)) by field_simp; ring,
      abs_neg, abs_div, abs_mul, abs_of_pos (by linarith [pi_gt_three] : 0 < π - 2),
      abs_of_pos (by positivity : 0 < 2 * π)]
  rw [habs] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have he : ((n : ℝ) * (Real.cos (α n) - 1) - n * (Real.cos (β n) - 1) -
        n * (Real.cos (ζ n) - 1) * Real.cos (β n)) • X +
      (n * Real.sin (β n) - n * Real.sin (α n) +
        n * (Real.cos (ζ n) - 1) * Real.sin (β n)) • Z =
      (n : ℝ) • ((Real.cos (α n) • X - Real.sin (α n) • Z) -
        (Real.cos (ζ n) : ℂ) • (Real.cos (β n) • X - Real.sin (β n) • Z)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  dsimp only
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)
      from Nat.cast_nonneg n)]

/-- Example 5.2's normalized axis M has the stated arctangent angle. -/
theorem normalized_axis_angle {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    (Real.sqrt (a ^ 2 + θ ^ 2))⁻¹ • (a • X - θ • Z) =
      Real.cos (Real.arctan (θ / a)) • X -
        Real.sin (Real.arctan (θ / a)) • Z := by
  have hr : Real.sqrt (1 + (θ / a) ^ 2) = Real.sqrt (a ^ 2 + θ ^ 2) / a := by
    rw [show 1 + (θ / a) ^ 2 = (a ^ 2 + θ ^ 2) / a ^ 2 by field_simp,
      Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sqrt_sq ha.le]
  rw [Real.cos_arctan, Real.sin_arctan, hr, smul_sub, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

/-- Example 5.2, fourth norm display, with the manuscript's N, M, ρ and ζ. -/
theorem matrix_residual_norm_limit (θ : ℝ) :
    let N := fun T : ℕ ↦ Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    let ρ := fun T : ℕ ↦ Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := fun T : ℕ ↦ (2 * ρ T)⁻¹ • ((Real.pi * T) • X - θ • Z)
    let ζ := fun T : ℕ ↦ ρ T - Real.pi * T / 2
    Tendsto (fun T : ℕ ↦ (T : ℝ) * ‖N T - (Real.cos (ζ T) : ℂ) • M T‖)
      atTop (𝓝 ((Real.pi - 2) * |θ| / (2 * Real.pi))) := by
  intro N ρ M ζ
  apply (odd_axis_norm_limit θ).congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hM : M T = Real.cos (Real.arctan (θ / (Real.pi * T))) • X -
      Real.sin (Real.arctan (θ / (Real.pi * T))) • Z := by
    convert normalized_axis_angle (mul_pos Real.pi_pos ht) θ using 1
    all_goals
      dsimp only [M, ρ]
      congr 1
      ring_nf
  rw [hM]

/-- Example 5.2(i): factor the two squared limits into the endpoint coefficient. -/
theorem odd_limit_factored (θ : ℝ) :
    Real.sqrt (((π - 2) * |θ| / (2 * π)) ^ 2 + (θ ^ 2 / (4 * π)) ^ 2) =
      (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) *
        Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2)) := by
  have hp : 0 < π - 2 := by linarith [pi_gt_three]
  have hc : (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) =
      (π - 2) * |θ| / (2 * π) := by field_simp
  rw [hc]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simp only [div_pow, mul_pow, sq_abs]
  field_simp
  ring

end RoundedClocks.PrecessingSpin
