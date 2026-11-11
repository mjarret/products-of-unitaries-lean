/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Comparison.EndpointFrame
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Comparison.UnitStepPathDAT
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative
public import UnitaryProducts.Corrector.PowerSeries

/-!
# The residual on one piece of the rounded clock

## Declarations

- `norm_frameExtension_le_center_profile`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real
noncomputable section
namespace UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- the proof of Lemma A.1 from a center bound: if $\|D\|\le L$ and $\|Y(0)\|\le qL$, then
$\|Y(s)\|\le(q+s^2/2)L$, with $s$ the offset from the center. -/
theorem norm_frameExtension_le_center_profile {h D Ybar : 𝕄} (hh : h.IsHermitian)
    {q L : ℝ} (hD : ‖D‖ ≤ L)
    (hcenter : ‖frameExtension h D Ybar (1 / 2)‖ ≤ q * L) (s : ℝ) :
    ‖frameExtension h D Ybar (s+1/2)‖ ≤ (q+s^2/2)*L := by
  have hb := norm_frameExtension_le_center h D Ybar hh (s+1/2)
  rw [add_sub_cancel_right] at hb
  exact (hb.trans (add_le_add hcenter
    (mul_le_mul_of_nonneg_left hD (by positivity)))).trans_eq (by ring)

end UnitaryProducts.Dressed
