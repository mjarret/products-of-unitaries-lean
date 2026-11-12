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


end UnitaryProducts.PaperProof.Spin
