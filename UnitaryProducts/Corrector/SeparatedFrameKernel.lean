/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# A Schwartz extension of $\mathcal N$, and Fourier inversion

## Declarations

- `analyticAt_frameMult_zero`
- `analyticOnNhd_positiveFrameSeries`
- `zero_or_sin_half_ne_zero`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ContDiff FourierTransform Manifold
open Complex MeasureTheory Set Filter Function

noncomputable section
namespace UnitaryProducts.Separation

/-- Analyticity of the positive partial-fraction series inside its convergence disk. -/
theorem analyticOnNhd_positiveFrameSeries : AnalyticOnNhd ℂ
    (UnitaryProducts.Corrector.positiveFrameSeries : ℂ → ℂ) (Metric.ball 0 (2 * Real.pi)) := by
  refine UnitaryProducts.Corrector.analyticOnNhd_tsum_coeff (by positivity) fun r hr0 hr ↦ ?_
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (UnitaryProducts.Corrector.frameCoeff_nonneg _)] using
    UnitaryProducts.Corrector.summable_frameBound_majorant hr0 hr

/-- The apparent singularity of the scalar frame multiplier at zero is removable analytically. -/
theorem analyticAt_frameMult_zero : AnalyticAt ℝ UnitaryProducts.Corrector.frameMult 0 := by
  have hi : AnalyticAt ℝ (fun x : ℝ ↦ (x : ℂ)) 0 := Complex.ofRealCLM.analyticAt 0
  apply ((Complex.reCLM.analyticAt _).comp ((analyticOnNhd_positiveFrameSeries 0
    (by simp [Real.pi_pos])).restrictScalars.comp_of_eq hi (by simp))).congr
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
    (by simpa using Real.pi_pos : |(0 : ℝ)| < 2 * Real.pi)] with x hx
  change (UnitaryProducts.Corrector.positiveFrameSeries (x : ℂ)).re =
    UnitaryProducts.Corrector.frameMult x
  rw [UnitaryProducts.Corrector.positiveFrameSeries_ofReal, Complex.ofReal_re,
    UnitaryProducts.Corrector.frameBound_abs_eq_frameMult hx]

/-- Nonresonance excludes the nonzero zeros of the half-angle sine. -/
theorem zero_or_sin_half_ne_zero {x : ℝ}
    (hnr : ∀ n : ℤ, n ≠ 0 → x ≠ 2 * Real.pi * n) :
    x = 0 ∨ Real.sin (x / 2) ≠ 0 := by
  refine or_iff_not_imp_left.mpr fun hx hs ↦ ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  exact hnr n (fun h ↦ hx (by subst h; simp only [Int.cast_zero, zero_mul] at hn; linarith))
    (by linarith)

end UnitaryProducts.Separation
