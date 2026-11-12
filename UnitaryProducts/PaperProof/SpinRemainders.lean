/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import UnitaryProducts.PaperProof.PrecessingSpin

/-! # Taylor remainders in the precessing-spin optimality argument -/
@[expose] public section
noncomputable section
open Real Set Filter Asymptotics
open scoped Topology Matrix.Norms.L2Operator
namespace UnitaryProducts.PaperProof.Spin

/-- Integrating a derivative estimate raises its power by one. This is the
one-variable specialization of Mathlib's integral remainder estimate. -/
theorem derivative_power_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (n : ℕ)
    (hdf : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x)
    (hd : deriv f =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ n)) :
    (fun x : ℝ ↦ f x - f 0) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ (n + 1)) := by
  have hderiv : fderiv ℝ f =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ ‖x - 0‖ ^ (n : ℝ)) := by
    rw [isBigO_iff] at hd ⊢
    obtain ⟨C, hC⟩ := hd
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    simpa only [← norm_deriv_eq_norm_fderiv, sub_zero, Real.rpow_natCast,
      norm_pow, Real.norm_eq_abs, abs_pow, abs_abs] using hx
  have h := sub_isBigO_norm_rpow_add_one_of_fderiv (by positivity : (0 : ℝ) ≤ n) hdf hderiv
  rw [isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  simpa only [sub_zero, ← Nat.cast_add_one, Real.rpow_natCast,
    norm_pow, Real.norm_eq_abs, abs_pow, abs_abs] using hx

/-- A twice differentiable function with zero first derivative has a quadratic
remainder, obtained by applying the standard derivative and integral estimates. -/
theorem quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiffAt ℝ 2 f 0) (hd0 : deriv f 0 = 0) :
    (fun x : ℝ ↦ f x - f 0) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ 2) := by
  have hc : ContDiffAt ℝ 1 (deriv f) 0 := hf.derivWithin (by norm_num)
  have hd := hc.differentiableAt (by norm_num)
  have hb := hd.hasDerivAt.isBigO_sub
  simp only [hd0, sub_zero] at hb
  apply derivative_power_remainder 1 ?_ (by simpa only [pow_one] using hb)
  filter_upwards [hf.eventually (by norm_num)] with x hx
  exact hx.differentiableAt (by norm_num)

/-- Subtracting the linear Taylor term of a `C²` map leaves a quadratic
remainder. The codomain can be a matrix Banach space. -/
theorem linear_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} (hf : ContDiffAt ℝ 2 f 0) (hd : HasDerivAt f v 0) :
    (fun x : ℝ ↦ f x - f 0 - x • v) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ 2) := by
  let g := fun x : ℝ ↦ f x - f 0 - x • v
  have hg : ContDiffAt ℝ 2 g 0 := (hf.sub contDiffAt_const).sub (by fun_prop)
  have hgd : HasDerivAt g 0 0 := by
    convert (hd.sub_const (f 0)).sub ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1; simp
  have h := quadratic_remainder hg hgd.deriv
  simpa only [g, sub_self, zero_smul, sub_zero] using h


/-- The symmetric step varies smoothly with the precession angle. -/
theorem step_contDiff (ω : ℝ) (T : ℕ) :
    ContDiff ℝ 2 (fun θ : ℝ ↦ step ω (θ / (2 * T))) := by
  simp_rw [step_closed]
  simp only [← Complex.ofRealCLM_apply]
  fun_prop

/-- The continuous frame factor varies smoothly near zero precession, as
seen in its elementary SU(2) formula. -/
theorem frozen_contDiffAt {a : ℝ} (ha : 0 < a) :
    ContDiffAt ℝ 2 (fun θ : ℝ ↦ UnitaryProducts.evol (a • X - θ • Z) (1 / 2)) 0 := by
  have he : (fun θ : ℝ ↦ UnitaryProducts.evol (a • X - θ • Z) (1 / 2)) =
      (fun θ : ℝ ↦ (Real.cos (Real.sqrt (a ^ 2 + (-θ) ^ 2) / 2) : ℂ) • 1 -
        (Complex.I * Real.sin (Real.sqrt (a ^ 2 + (-θ) ^ 2) / 2) /
          Real.sqrt (a ^ 2 + (-θ) ^ 2) : ℂ) • xz a (-θ)) := by
    funext θ
    have hp : 0 < a ^ 2 + (-θ) ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
    have hG : a • X - θ • Z = xz a (-θ) := by simp only [xz, neg_smul, sub_eq_add_neg]
    rw [hG, evol_xz_formula hp]
  rw [he]
  let r := fun θ : ℝ ↦ Real.sqrt (a ^ 2 + (-θ) ^ 2)
  have hp : a ^ 2 + (-(0 : ℝ)) ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 ha.ne'
  have hr : ContDiffAt ℝ 2 r 0 :=
    (show ContDiffAt ℝ 2 (fun θ : ℝ ↦ a ^ 2 + (-θ) ^ 2) 0 by fun_prop).sqrt hp
  have hr0 : 0 < r 0 := Real.sqrt_pos.mpr (by positivity)
  have hcast {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
      ContDiffAt ℝ 2 (fun θ : ℝ ↦ (g θ : ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hg
  have hcos := hcast ((hr.div_const 2).cos)
  have hsin := hcast ((hr.div_const 2).sin)
  have hratio : ContDiffAt ℝ 2 (fun θ : ℝ ↦ (Complex.I * Real.sin (r θ / 2) / r θ : ℂ)) 0 := by
    simpa only [div_eq_mul_inv] using
      ((contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ ↦ Complex.I) 0).mul hsin).mul
        ((hcast hr).inv (Complex.ofReal_ne_zero.mpr hr0.ne'))
  have haxis : ContDiffAt ℝ 2 (fun θ : ℝ ↦ xz a (-θ)) 0 := by unfold xz; fun_prop
  exact (hcos.smul contDiffAt_const).sub (hratio.smul haxis)

/-- The actual frame error has the regularity needed for a quadratic Taylor
remainder. Powers are finite because the runtime is fixed here. -/
theorem frameError_contDiffAt {ω : ℝ} (hω : 0 < ω) {T : ℕ} (hT : 0 < T) :
    ContDiffAt ℝ 2 (fun θ : ℝ ↦ frameError ω θ T) 0 :=
  ((step_contDiff ω T).contDiffAt.pow T).sub
    (frozen_contDiffAt (mul_pos hω (Nat.cast_pos.mpr hT)))

/-- Taking the norm of a `C²` Taylor expansion preserves a quadratic remainder,
even though the norm itself need not be differentiable at zero. -/
theorem norm_linear_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} (hf : ContDiffAt ℝ 2 f 0) (hd : HasDerivAt f v 0)
    (hzero : f 0 = 0) :
    (fun θ : ℝ ↦ ‖f θ‖ - |θ| * ‖v‖) =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 2) := by
  have hb := linear_taylor_remainder hf hd
  simp only [hzero, sub_zero] at hb
  have he : (fun θ : ℝ ↦ ‖f θ‖ - |θ| * ‖v‖) =O[𝓝 (0 : ℝ)]
      (fun θ : ℝ ↦ f θ - θ • v) := by
    apply IsBigO.of_bound'
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs, norm_smul] using abs_norm_sub_norm_le (f θ) (θ • v)
  exact he.trans hb

/-- At an odd resonance, the comparison error has the exact leading term and
quadratic remainder asserted after Example 5.2, with runtime fixed. -/
theorem odd_resonance_error_quadratic {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    {T : ℕ} (hT : 0 < T) (m : ℕ) (hodd : (T : ℝ) * ω = (2 * m + 1) * π) :
    (fun θ : ℝ ↦ (T : ℝ) * ‖frameError ω θ T‖ -
      (1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2) * (ω * |θ|))
      =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 2) := by
  have hs : Real.sin (ω / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < ω / 2) (by linarith)).ne'
  have hd := frameError_derivative hω hT hs
  have hb := (norm_linear_taylor_remainder (frameError_contDiffAt hω hT) hd
    (frameError_zero ω T)).const_mul_left (T : ℝ)
  have hc := tendsto_nhds_unique (frameError_normalized_limit hω hT hs)
    (precessing_spin_every_width hω hω2 hT m hodd)
  convert hb using 1
  funext θ
  rw [← hc]
  field_simp


end UnitaryProducts.PaperProof.Spin
