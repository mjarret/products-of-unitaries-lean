/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.MaxEntryError
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import UnitaryProducts.Approximation.JRSComparison
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Evolution.RoundedTransfer
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmBranch
public import Mathlib.Data.Matrix.Basis
public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Evolution.RegulatedDuhamel
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# Symmetry and derivative of $\mathcal N$

## Declarations

- `frameBound_abs`
- `frameLip_zero`
- `hasDerivAt_frameMult`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real
noncomputable section

namespace UnitaryProducts.Corrector

/-- `frameBound` is even: its odd terms vanish. -/
theorem frameBound_abs (x : ℝ) : frameBound |x| = frameBound x := by
  unfold frameBound
  refine tsum_congr fun n ↦ ?_
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [(even_two_mul k).pow_abs]
  · simp only [frameCoeff_odd, zero_mul]

/-- The derivative of the even cotangent multiplier vanishes at zero.
Only the linear coefficient can contribute, and that odd coefficient is zero. -/
theorem frameLip_zero : frameLip 0 = 0 := by
  unfold frameLip
  refine (tsum_congr fun n ↦ ?_).trans (tsum_zero (α := ℝ))
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp [show frameCoeff 1 = 0 by simpa using frameCoeff_odd 0]
  · simp

/-- The closed form of $\mathcal N$ has derivative `frameLip` on $|x| < 2\pi$. -/
theorem hasDerivAt_frameMult {x : ℝ} (hx : |x| < 2 * π) :
    HasDerivAt frameMult (frameLip x) x := by
  apply (hasDerivAt_frameBound hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
  exact (frameBound_abs_eq_frameMult hy).symm.trans (frameBound_abs y)

end UnitaryProducts.Corrector
