/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ClosedCellConstruction
public import UnitaryProducts.Prose.ChainSteps
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.WalkScalarCut
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-! # Literal intermediate steps in Appendix A.1–A.2 -/
@[expose] public section
open Real Complex Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Prose
noncomputable section
namespace UnitaryProducts.PaperProof

/-- The local phase bound in Lemma A.2: shift the moving spectral window
by the fixed midpoint at the base point. -/
theorem moving_window_center_bound {θ a a₀ w : ℝ}
    (hθ : θ ∈ Icc a (a + w)) :
    |θ - (a₀ + w / 2)| ≤ |a - a₀| + w / 2 := by
  have hcenter : |θ - (a + w / 2)| ≤ w / 2 :=
    abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  calc
    _ = |(θ - (a + w / 2)) + (a - a₀)| := by congr 1; ring
    _ ≤ |θ - (a + w / 2)| + |a - a₀| := abs_add_le _ _
    _ ≤ |a - a₀| + w / 2 := by linarith


end UnitaryProducts.PaperProof
