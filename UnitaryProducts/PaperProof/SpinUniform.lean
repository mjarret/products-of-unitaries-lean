/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.SpinRemainders

/-! # Runtime-uniform spin estimates

The order of limits in the optimality paragraph after Example 5.2 is runtime,
precession angle, then width. Local estimates below use the step angle as their
variable, so their constants do not depend on the runtime.
-/
@[expose] public section
noncomputable section
open Real Set Filter Asymptotics Complex Matrix
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof.Spin

attribute [local instance] matrixCStarAlgebra

/-- The real unit axis in the X-Z plane, with the paper's orientation. -/
def angleAxis (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  xz (Real.cos α) (-Real.sin α)

/-- The elementary exponential of a unit real axis. -/
theorem angleAxis_rotation (α t : ℝ) :
    evol (angleAxis α) t = (Real.cos t : ℂ) • 1 -
      (I * Real.sin t : ℂ) • angleAxis α :=
  evol_involution (xz_angle_relations α).1 (xz_angle_relations α).2 t

/-- The direction of the bracket in the general-width symmetric step. -/
def stepAngle (ω ε : ℝ) : ℝ := Real.arctan (Real.tan ε / Real.sin (ω / 2))

/-- The principal phase of the symmetric spin step. -/
def stepPhase (ω ε : ℝ) : ℝ := Real.arccos (Real.cos (ω / 2) * Real.cos ε)

/-- Inside the admissible width interval the base phase stays away from both
endpoints of arccos, as its sine is strictly positive. -/
theorem phase_cos_ne_endpoints {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    Real.cos (ω / 2) ≠ -1 ∧ Real.cos (ω / 2) ≠ 1 := by
  have hs : Real.sin (ω / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < ω / 2) (by linarith)).ne'
  have htrig := Real.cos_sq_add_sin_sq (ω / 2)
  constructor
  · intro h
    rw [h] at htrig
    apply hs
    apply sq_eq_zero_iff.mp
    linarith
  · intro h
    rw [h] at htrig
    apply hs
    apply sq_eq_zero_iff.mp
    linarith

/-- The exact step phase is ω/2 at zero precession. -/
theorem stepPhase_zero {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    stepPhase ω 0 = ω / 2 := by
  simpa [stepPhase] using Real.arccos_cos (show 0 ≤ ω / 2 by positivity)
    (show ω / 2 ≤ π by linarith)

/-- The step phase has zero first variation and therefore a quadratic
remainder. Its constants are fixed before the runtime is introduced. -/
theorem step_phase_quadratic {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    (fun ε : ℝ ↦ stepPhase ω ε - ω / 2) =O[𝓝 (0 : ℝ)] (fun ε : ℝ ↦ ε ^ 2) := by
  obtain ⟨hneg, hpos⟩ := phase_cos_ne_endpoints hω hω2
  have harg : HasDerivAt (fun ε : ℝ ↦ Real.cos (ω / 2) * Real.cos ε) 0 0 := by
    simpa using (Real.hasDerivAt_cos (0 : ℝ)).const_mul (Real.cos (ω / 2))
  have hd : HasDerivAt (stepPhase ω) 0 0 := by
    convert (Real.hasDerivAt_arccos hneg hpos).comp_of_eq 0 harg (by simp) using 1
    simp
  have hout : ContDiffAt ℝ 2 Real.arccos (Real.cos (ω / 2) * Real.cos 0) := by
    simpa using Real.contDiffAt_arccos hneg hpos
  have hc : ContDiffAt ℝ 2 (stepPhase ω) 0 := hout.comp 0 (by fun_prop)
  simpa only [stepPhase_zero hω hω2] using quadratic_remainder hc hd.deriv

/-- The phase estimate written with the paper's parameters: one constant
bounds ξ−ω/2 by θ²/T² for every positive integer runtime. -/
theorem step_phase_uniform {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    ∃ C > 0, ∃ δ > 0, ∀ θ : ℝ, |θ| < δ → ∀ T : ℕ, 0 < T →
      |stepPhase ω (θ / (2 * T)) - ω / 2| ≤ C * θ ^ 2 / (T : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := (step_phase_quadratic hω hω2).exists_pos
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨C / 4, by positivity, 2 * δ, by positivity, ?_⟩
  intro θ hθ T hT
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsmall : dist (θ / (2 * T)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (by positivity : 0 < 2 * (T : ℝ))]
    apply (div_lt_iff₀ (by positivity)).mpr
    exact hθ.trans_le (by
      have hscaled := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * δ by positivity)
      linarith only [hscaled])
  have hb := hlocal hsmall
  simp only [Real.norm_eq_abs, abs_pow, sq_abs] at hb
  convert hb using 1
  field_simp
  ring

/-- The direction chosen by the arctangent is exactly the normalized bracket
in the closed step formula, whenever the step angle has positive cosine. -/
theorem step_axis_coordinates {ω ε : ℝ} (hs : 0 < Real.sin (ω / 2))
    (hc : 0 < Real.cos ε) :
    Real.cos (stepAngle ω ε) = Real.sin (ω / 2) * Real.cos ε /
      Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) ∧
    Real.sin (stepAngle ω ε) = Real.sin ε /
      Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) := by
  have hangle : stepAngle ω ε =
      Real.arctan (Real.sin ε / (Real.sin (ω / 2) * Real.cos ε)) := by
    unfold stepAngle
    rw [Real.tan_eq_sin_div_cos]
    congr 1
    ring
  rw [hangle]
  exact axis_arctan_coordinates (mul_pos hs hc) (Real.sin ε)

/-- The exact general-width normal form S = exp(-i ξ N), with ξ the
principal phase and N the paper's normalized X-Z combination. -/
theorem step_phase_axis {ω ε : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    (hc : 0 < Real.cos ε) :
    step ω ε = evol (angleAxis (stepAngle ω ε)) (stepPhase ω ε) := by
  have hs : 0 < Real.sin (ω / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hprod : |Real.cos (ω / 2) * Real.cos ε| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hcos : Real.cos (stepPhase ω ε) = Real.cos (ω / 2) * Real.cos ε :=
    Real.cos_arccos (abs_le.mp hprod).1 (abs_le.mp hprod).2
  have hrad : (Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2 =
      1 - (Real.cos (ω / 2) * Real.cos ε) ^ 2 := by
    linear_combination (Real.cos ε) ^ 2 * Real.cos_sq_add_sin_sq (ω / 2) +
      Real.cos_sq_add_sin_sq ε
  have hsin : Real.sin (stepPhase ω ε) =
      Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) := by
    rw [stepPhase, Real.sin_arccos, hrad]
  obtain ⟨hca, hsa⟩ := step_axis_coordinates hs hc
  have hr : Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos (mul_pos hs hc)) (sq_nonneg _))).ne'
  rw [step_closed, angleAxis_rotation, hcos, hsin, angleAxis, xz, hca, hsa]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Complex.real_smul,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
  have hrc : (Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr
  generalize hrdef : (Real.sqrt ((Real.sin (ω / 2) * Real.cos ε) ^ 2 + Real.sin ε ^ 2) : ℂ) = r at *
  field_simp [hrc]
  ring

/-- For each fixed precession angle, the exact normal form applies at all
sufficiently large runtimes; positivity of the step cosine is automatic. -/
theorem step_phase_axis_eventually {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) (θ : ℝ) :
    ∀ᶠ T : ℕ in atTop, step ω (θ / (2 * T)) =
      evol (angleAxis (stepAngle ω (θ / (2 * T)))) (stepPhase ω (θ / (2 * T))) := by
  have he : Tendsto (fun T : ℕ ↦ θ / (2 * T)) atTop (𝓝 0) := by
    simpa only [div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ / 2)
  have hc : Tendsto (fun T : ℕ ↦ Real.cos (θ / (2 * T))) atTop (𝓝 1) := by
    simpa only [Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp he
  filter_upwards [(tendsto_order.1 hc).1 0 zero_lt_one] with T hT
  exact step_phase_axis hω hω2 hT

/-- Differentiating a unit axis at angle zero gives its Z component. -/
theorem angleAxis_derivative {α : ℝ → ℝ} {a : ℝ}
    (hα : HasDerivAt α a 0) (hzero : α 0 = 0) :
    HasDerivAt (fun ε ↦ angleAxis (α ε)) ((-a) • Z) 0 := by
  have hc : HasDerivAt (fun ε ↦ Real.cos (α ε)) 0 0 := by
    simpa only [hzero, Real.sin_zero, neg_zero, zero_mul] using hα.cos
  have hs : HasDerivAt (fun ε ↦ Real.sin (α ε)) a 0 := by
    simpa only [hzero, Real.cos_zero, one_mul] using hα.sin
  simpa only [angleAxis, xz, zero_smul, zero_sub, neg_smul] using
    (hc.smul_const X).sub (hs.smul_const Z)

/-- The derivative of the exact discrete-axis angle at zero. -/
theorem stepAngle_derivative (ω : ℝ) :
    HasDerivAt (stepAngle ω) (1 / Real.sin (ω / 2)) 0 := by
  have ht : HasDerivAt Real.tan 1 0 := by
    simpa using Real.hasDerivAt_tan (x := (0 : ℝ)) (by simp)
  simpa only [stepAngle, Real.tan_zero, zero_div, zero_pow (by decide : 2 ≠ 0),
    add_zero, div_one, one_mul] using (ht.div_const (Real.sin (ω / 2))).arctan

/-- Unit axes have operator norm one. -/
theorem angleAxis_norm (α : ℝ) : ‖angleAxis α‖ = 1 := by
  have hh := xz_norm_sq (Real.cos α) (-Real.sin α)
  rw [neg_sq, Real.cos_sq_add_sin_sq] at hh
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [angleAxis] using hh)

/-- Changing only the phase of a unit-axis rotation costs at most twice the
phase change; the scalar sine and cosine bounds are Mathlib's. -/
theorem angleAxis_phase_bound (α r t : ℝ) :
    ‖evol (angleAxis α) r - evol (angleAxis α) t‖ ≤ 2 * |r - t| := by
  rw [angleAxis_rotation, angleAxis_rotation]
  have he : (Real.cos r : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (I * Real.sin r : ℂ) • angleAxis α -
      ((Real.cos t : ℂ) • 1 - (I * Real.sin t : ℂ) • angleAxis α) =
      ((Real.cos r - Real.cos t : ℝ) : ℂ) • 1 -
        (I * ((Real.sin r - Real.sin t : ℝ) : ℂ)) • angleAxis α := by
    push_cast
    simp only [sub_smul, mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖((Real.cos r - Real.cos t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ +
        ‖(I * ((Real.sin r - Real.sin t : ℝ) : ℂ)) • angleAxis α‖ := norm_sub_le _ _
    _ = |Real.cos r - Real.cos t| + |Real.sin r - Real.sin t| := by
      simp only [norm_smul, norm_one, mul_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, one_mul, angleAxis_norm]
    _ ≤ 2 * |r - t| := by linarith [Real.abs_cos_sub_cos_le r t, Real.abs_sin_sub_sin_le r t]

/-- The exact step phase and the group law turn its quadratic phase error
into a power estimate with one constant for every integer runtime T ≥ 1. -/
theorem step_power_uniform {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    ∃ C > 0, ∃ δ > 0, ∀ θ : ℝ, |θ| < δ → ∀ T : ℕ, 0 < T →
      (T : ℝ) * ‖step ω (θ / (2 * T)) ^ T -
        evol (angleAxis (stepAngle ω (θ / (2 * T)))) ((T : ℝ) * (ω / 2))‖ ≤
          C * θ ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hphase⟩ := step_phase_uniform hω hω2
  refine ⟨2 * C, by positivity, min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro θ hθ T hT
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hsmall : |θ / (2 * T)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (T : ℝ))]
    apply (div_le_iff₀ (by positivity)).mpr
    have hθ1 := (lt_min_iff.mp hθ).2
    linarith
  have hc := Real.cos_pos_of_le_one hsmall
  rw [step_phase_axis hω hω2 hc, ← evol_nat_mul]
  have hb := mul_le_mul_of_nonneg_left
    (angleAxis_phase_bound (stepAngle ω (θ / (2 * T)))
      ((T : ℝ) * stepPhase ω (θ / (2 * T))) ((T : ℝ) * (ω / 2))) ht0.le
  have hp := hphase θ (lt_min_iff.mp hθ).1 T hT
  rw [← mul_sub, abs_mul, abs_of_pos ht0] at hb
  calc
    _ ≤ (T : ℝ) * (2 * ((T : ℝ) * |stepPhase ω (θ / (2 * T)) - ω / 2|)) := hb
    _ ≤ (T : ℝ) * (2 * ((T : ℝ) * (C * θ ^ 2 / (T : ℝ) ^ 2))) := by gcongr
    _ = (2 * C) * θ ^ 2 := by field_simp

/-- The continuous phase ρ differs from ωT/2 by O(θ²/T), with an explicit
bound valid for every precession angle and positive runtime. -/
theorem continuous_phase_uniform {ω : ℝ} (hω : 0 < ω) (θ : ℝ) {T : ℕ} (hT : 0 < T) :
    (T : ℝ) * |Real.sqrt (ω ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - ω * T / 2| ≤
      θ ^ 2 / (2 * ω) := by
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have he : (T : ℝ) * |Real.sqrt (ω ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - ω * T / 2| =
      |(T : ℝ) * (Real.sqrt (ω ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - ω * T / 2)| := by
    rw [abs_mul, abs_of_pos ht]
  rw [he, phase_defect_rationalized hω ht,
    abs_of_nonneg (by positivity : 0 ≤ θ ^ 2 / (2 * (Real.sqrt (ω ^ 2 + (θ / T) ^ 2) + ω)))]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  linarith [Real.sqrt_nonneg (ω ^ 2 + (θ / T) ^ 2)]

/-- Rationalization gives the continuous phase estimate with a constant
independent of runtime and precession angle. -/
theorem frozen_phase_uniform {ω : ℝ} (hω : 0 < ω) (θ : ℝ) {T : ℕ} (hT : 0 < T) :
    (T : ℝ) * ‖evol ((ω * T) • X - θ • Z) (1 / 2) -
      evol (angleAxis (Real.arctan (θ / (ω * T)))) (ω * T / 2)‖ ≤ θ ^ 2 / ω := by
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  rw [frozen_axis_angle (mul_pos hω ht)]
  have hb := mul_le_mul_of_nonneg_left
    (angleAxis_phase_bound (Real.arctan (θ / (ω * T)))
      (Real.sqrt ((ω * T) ^ 2 + θ ^ 2) / 2) (ω * T / 2)) ht.le
  have hphase := continuous_phase_uniform hω θ hT
  have he : (T : ℝ) * (2 * |Real.sqrt ((ω * T) ^ 2 + θ ^ 2) / 2 - ω * T / 2|) =
      2 * ((T : ℝ) * |Real.sqrt (ω ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - ω * T / 2|) := by
    rw [mul_pow]
    ring
  rw [he] at hb
  calc
    _ ≤ 2 * ((T : ℝ) * |Real.sqrt (ω ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - ω * T / 2|) := hb
    _ ≤ 2 * (θ ^ 2 / (2 * ω)) := mul_le_mul_of_nonneg_left hphase (by norm_num)
    _ = θ ^ 2 / ω := by ring

/-- A differentiable curve, sampled at θ/T and multiplied by T, converges
to θ times its derivative. This is the derivative expressed by Mathlib's
continuous divided slope, including θ = 0. -/
theorem scaled_curve_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} (hd : HasDerivAt f v 0) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) • (f (θ / T) - f 0)) atTop (𝓝 (θ • v)) := by
  have hds := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto
  rw [dslope_same, hd.deriv] at hds
  have hh := (hds.comp (tendsto_const_div_atTop_nhds_zero_nat θ)).const_smul θ
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  dsimp only [Function.comp_def]
  have he := sub_smul_dslope f 0 (θ / T)
  simp only [sub_zero] at he
  rw [← he, smul_smul]
  congr 1
  field_simp

set_option maxHeartbeats 1000000 in
-- Elaborating the composed matrix derivative and its norm limit needs a larger budget.
/-- The distance between the paper's discrete and continuous unit axes has
its asserted runtime limit at every width in (0,2π). -/
theorem general_axis_norm_limit {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) * ‖angleAxis (stepAngle ω (θ / (2 * T))) -
      angleAxis (Real.arctan (θ / (ω * T)))‖) atTop
      (𝓝 (|θ| * (1 / (2 * Real.sin (ω / 2)) - 1 / ω))) := by
  have hs : 0 < Real.sin (ω / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  let a := 1 / (2 * Real.sin (ω / 2)) - 1 / ω
  have ha : 0 ≤ a := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    linarith [Real.sin_le (by positivity : 0 ≤ ω / 2)]
  let f := fun ε : ℝ ↦ angleAxis (stepAngle ω (ε / 2)) -
    angleAxis (Real.arctan (ε / ω))
  have hd1 : HasDerivAt (fun ε : ℝ ↦ stepAngle ω (ε / 2))
      (1 / (2 * Real.sin (ω / 2))) 0 := by
    convert (stepAngle_derivative ω).comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).div_const 2)
      (by simp) using 1
    ring
  have hd2 : HasDerivAt (fun ε : ℝ ↦ Real.arctan (ε / ω)) (1 / ω) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const ω).arctan
  have hd : HasDerivAt f ((-a) • Z) 0 := by
    convert (angleAxis_derivative hd1 (by simp [stepAngle])).sub
      (angleAxis_derivative hd2 (by simp)) using 1
    rw [← sub_smul]
    congr 1
    dsimp [a]
    ring
  have hf0 : f 0 = 0 := by simp [f, stepAngle]
  have hh := (scaled_curve_limit hd θ).norm
  simp only [hf0, sub_zero, norm_smul, Real.norm_eq_abs, norm_Z, mul_one,
    abs_neg, abs_of_nonneg ha, Nat.abs_cast] at hh
  convert hh using 1
  funext T
  dsimp [f]
  rw [show θ / (2 * (T : ℝ)) = θ / T / 2 by ring,
    show θ / (ω * (T : ℝ)) = θ / T / ω by ring]

/-- At an odd resonance the common phase is a unit scalar, leaving exactly
the distance of the two real axes. -/
theorem resonant_axis_distance (α β ω : ℝ) {T : ℕ} (m : ℕ)
    (hodd : (T : ℝ) * ω = (2 * m + 1) * π) :
    ‖evol (angleAxis α) ((T : ℝ) * (ω / 2)) -
      evol (angleAxis β) ((T : ℝ) * (ω / 2))‖ = ‖angleAxis α - angleAxis β‖ := by
  have ht : (T : ℝ) * (ω / 2) = π * (2 * m + 1) / 2 + 0 := by linarith
  have hα := odd_frozen_rotation_factor α 0 m
  have hβ := odd_frozen_rotation_factor β 0 m
  simp only [evol_zero, mul_one] at hα hβ
  rw [ht]
  change ‖evol (xz (Real.cos α) (-Real.sin α)) _ -
    evol (xz (Real.cos β) (-Real.sin β)) _‖ = _
  rw [hα, hβ, ← smul_sub, norm_smul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  rfl

/-- The scaled comparison error differs from the scaled axis distance by
O(θ²), with one constant and one θ-neighborhood for every positive runtime.
This is the uniform estimate used before taking T to infinity in the paper. -/
theorem odd_resonance_uniform {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) :
    ∃ C > 0, ∃ δ > 0, ∀ θ : ℝ, |θ| < δ → ∀ T m : ℕ, 0 < T →
      (T : ℝ) * ω = (2 * m + 1) * π →
      |(T : ℝ) * ‖frameError ω θ T‖ - (T : ℝ) *
        ‖angleAxis (stepAngle ω (θ / (2 * T))) -
          angleAxis (Real.arctan (θ / (ω * T)))‖| ≤ C * θ ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hstep⟩ := step_power_uniform hω hω2
  refine ⟨C + 1 / ω, by positivity, δ, hδ, ?_⟩
  intro θ hθ T m hT hodd
  let N := angleAxis (stepAngle ω (θ / (2 * T)))
  let M := angleAxis (Real.arctan (θ / (ω * T)))
  let P := step ω (θ / (2 * T)) ^ T
  let U := evol ((ω * T) • X - θ • Z) (1 / 2)
  let R := evol N ((T : ℝ) * (ω / 2))
  let Q := evol M ((T : ℝ) * (ω / 2))
  have haxis : ‖R - Q‖ = ‖N - M‖ := resonant_axis_distance _ _ ω m hodd
  have he : frameError ω θ T = P - U := rfl
  have hnorm := abs_norm_sub_norm_le (P - U) (R - Q)
  have hrearrange : P - U - (R - Q) = (P - R) - (U - Q) := by abel
  rw [hrearrange, haxis] at hnorm
  have ht : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hscaled := mul_le_mul_of_nonneg_left
    (hnorm.trans (norm_sub_le (P - R) (U - Q))) ht
  have hpow : (T : ℝ) * ‖P - R‖ ≤ C * θ ^ 2 := hstep θ hθ T hT
  have hfrozen : (T : ℝ) * ‖U - Q‖ ≤ θ ^ 2 / ω := by
    convert frozen_phase_uniform hω θ hT using 1
    dsimp [U, Q, M]
    congr 3
    ring
  rw [he, ← mul_sub, abs_mul, abs_of_nonneg ht]
  calc
    _ ≤ (T : ℝ) * (‖P - R‖ + ‖U - Q‖) := hscaled
    _ = (T : ℝ) * ‖P - R‖ + (T : ℝ) * ‖U - Q‖ := mul_add _ _ _
    _ ≤ C * θ ^ 2 + θ ^ 2 / ω := add_le_add hpow hfrozen
    _ = (C + 1 / ω) * θ ^ 2 := by ring

/-- Odd-resonant spins force the endpoint coefficient at every positive width.
The residual term contains exactly the Lipschitz and squared-derivative terms
from the unit-step comparison, both quadratic in the angular speed. -/
theorem precessing_spin_optimal {w c A B : ℝ} (hw : 0 < w) (hw2 : w < 2 * π)
    (hcomparison : ∀ (ω : ℝ) (T : ℕ), 0 < ω → ω < w → 0 < T → ∀ θ : ℝ,
      (T : ℝ) * ‖frameError ω θ T‖ ≤
        c * (‖familySlope ω θ 0‖ + ‖familySlope ω θ 1‖) +
        A * (ω * θ ^ 2 / 2) + B * unitSupNorm (familySlope ω θ) ^ 2) :
    1 / (2 * w * Real.sin (w / 2)) - 1 / w ^ 2 ≤ c := by
  apply endpoint_coefficient_optimal_time_first
    (E := fun ω T θ ↦ (T : ℝ) * ‖frameError ω θ T‖)
    (A := fun ω T θ ↦ (T : ℝ) * ‖angleAxis (stepAngle ω (θ / (2 * T))) -
      angleAxis (Real.arctan (θ / (ω * T)))‖) hw hw2
  · intro ω hω hωw θ
    exact general_axis_norm_limit hω (hωw.trans hw2) θ
  · intro ω hω hωw
    obtain ⟨C, _, δ, hδ, hbound⟩ := odd_resonance_uniform hω (hωw.trans hw2)
    refine ⟨C, ?_⟩
    have hsmall : ∀ᶠ θ : ℝ in 𝓝[≠] 0, |θ| < δ :=
      (Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun y hy ↦ by
        simpa only [Real.dist_eq, sub_zero] using hy⟩).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall] with θ hθ
    exact hbound θ hθ
  · intro ω hω hωw
    refine ⟨A * ω / 2 + B * ω ^ 2 / 4, Eventually.of_forall (fun θ T _ hT _ ↦ ?_)⟩
    have hh := hcomparison ω T hω hωw hT θ
    rw [familySlope_norm hω.le, familySlope_norm hω.le, familySlope_supNorm hω.le] at hh
    convert hh using 1
    simp only [div_pow, mul_pow, sq_abs]
    ring

end UnitaryProducts.PaperProof.Spin
