/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.MaxEntryError
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
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
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
public import UnitaryProducts.Evolution.RegulatedDuhamel

/-!
# Mean-value inequality on an interval

## Declarations

- `norm_sub_le_of_derivWithin_le`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real UnitaryProducts.Corrector
noncomputable section
namespace UnitaryProducts

/-- A bound on the derivative within an interval is a Lipschitz constant there:
$\|H(t) - H(s)\| \le L|t - s|$ on $[a, b]$. A restatement of Mathlib's
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`. -/
theorem norm_sub_le_of_derivWithin_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H Hd : ℝ → E} {a b L : ℝ}
    (hH : ∀ t ∈ Icc a b, HasDerivWithinAt H (Hd t) (Icc a b) t)
    (hL : ∀ t ∈ Icc a b, ‖Hd t‖ ≤ L) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖H t - H s‖ ≤ L * |t - s| := fun s hs t ht => by
  simpa [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hH hL hs ht

end UnitaryProducts
