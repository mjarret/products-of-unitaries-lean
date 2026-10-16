/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # The zero-frequency limit of the cell corrector -/

@[expose] public section
open Complex Real Set Filter MeasureTheory
open UnitaryProducts.Corrector
open scoped Topology
noncomputable section
namespace UnitaryProducts.PaperProof

/-- Section 4.1: the entire scalar corrector converges to its selected
zero-frequency solution, for every position in the cell and every input entry. -/
theorem closedCellMultiplier_zero_limit (τ : ℝ) (a : ℂ) :
    Tendsto (fun x : ℝ ↦ closedCellMultiplier τ x * a) (𝓝[≠] 0)
      (𝓝 (((τ : ℂ) ^ 2 / 2 - 1 / 24) * a)) := by
  let F : ℝ → ℂ := fun x ↦ Complex.exp (-(I * x * τ)) *
    (Complex.exp (I * x * (-1 / 2 : ℝ)) * (frameMult x : ℂ) +
      ∫ t in (-1 / 2 : ℝ)..τ, Complex.exp (I * x * t) * (t : ℂ))
  have heq (x : ℝ) (hx : |x| < 2 * π) : closedCellMultiplier τ x = F x := by
    have hd (t : ℝ) : HasDerivAt
        (fun u : ℝ ↦ Complex.exp (I * x * u) * closedCellMultiplier u x)
        (Complex.exp (I * x * t) * (t : ℂ)) t := by
      have ht : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
        simpa using (hasDerivAt_id' t).ofReal_comp
      have he := (ht.const_mul (I * x)).cexp
      convert he.mul (closedCellMultiplier_derivative x t) using 1
      ring
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-1 / 2 : ℝ)) (b := τ) (fun t _ ↦ hd t)
      ((show Continuous (fun t : ℝ ↦ Complex.exp (I * x * t) * (t : ℂ)) by
        fun_prop).intervalIntegrable _ _)
    rw [(closedCellMultiplier_endpoints hx).2] at hint
    have hinv : Complex.exp (-(I * x * τ)) * Complex.exp (I * x * τ) = 1 := by
      rw [← Complex.exp_add]
      simp
    dsimp only [F]
    rw [hint]
    calc
      closedCellMultiplier τ x =
          (Complex.exp (-(I * x * τ)) * Complex.exp (I * x * τ)) *
            closedCellMultiplier τ x := by rw [hinv, one_mul]
      _ = _ := by ring
  have hi : Continuous (fun x : ℝ ↦
      ∫ t in (-1 / 2 : ℝ)..τ, Complex.exp (I * x * t) * (t : ℂ)) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (by fun_prop) (-1 / 2) τ
  have hc : ContinuousAt F 0 := by
    have hframe : ContinuousAt (fun x : ℝ ↦ (frameMult x : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt.comp
        UnitaryProducts.Separation.analyticAt_frameMult_zero.continuousAt
    exact (show ContinuousAt (fun x : ℝ ↦ Complex.exp (-(I * x * τ))) 0 by
      fun_prop).mul (((show ContinuousAt
        (fun x : ℝ ↦ Complex.exp (I * x * (-1 / 2 : ℝ))) 0 by
          fun_prop).mul hframe).add hi.continuousAt)
  have hnear : (fun x : ℝ ↦ closedCellMultiplier τ x) =ᶠ[𝓝 0] F := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < 2 * π)] with x hx
    exact heq x (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx)
  have hzero : F 0 = (τ : ℂ) ^ 2 / 2 - 1 / 24 := by
    rw [← heq 0 (by simp [pi_pos]), closedCellMultiplier, if_pos rfl]
  have hlimit := (hc.tendsto.congr' hnear.symm).mul_const a
  simpa only [hzero] using hlimit.mono_left nhdsWithin_le_nhds

end UnitaryProducts.PaperProof
