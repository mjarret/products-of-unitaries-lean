/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Walks.Logarithm

/-!
# Gauges for a schedule

## Declarations

- `Gauge`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator
open Set MeasureTheory
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **A gauge for a schedule.**  A nondecreasing `φ` whose increments dominate those of `H`:
`‖H(t) - H(s)‖ ≤ φ(t) - φ(s)` for `s ≤ t` in `[a, b]`.  The cumulative total variation
(Remark 3.9) is the canonical example, and a gauge is all the checkpoint bound of
the variation bound of Remark 3.9 needs — the schedule itself is arbitrary. -/
structure Gauge (H : ℝ → 𝕄) (φ : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- The gauge is nondecreasing on `[a, b]`. -/
  mono : MonotoneOn φ (Icc a b)
  /-- Increments of `H` are dominated by increments of the gauge. -/
  dominates : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → ‖H t - H s‖ ≤ φ t - φ s

end UnitaryProducts
