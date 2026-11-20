/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Evolution.ExplicitSchedule
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Evolution.Regulated
public import UnitaryProducts.Evolution.RegulatedExistence
public import UnitaryProducts.Evolution.Pieces

/-!
# Entry errors in the maximum norm

## Declarations

- `norm_le_sparsity_mul_maxEntryNorm`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set WithLp
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The sparse Hermitian estimate in the entrywise maximum norm: $\|A\|\le s\|A\|_{\max}$ for a
Hermitian $s$-sparse $A$ (§3.1, the Schur test). -/
theorem norm_le_sparsity_mul_maxEntryNorm {A : 𝕄} (hA : A.IsHermitian)
    {s : ℕ} (hs : RowSparse s A) : ‖A‖ ≤ s * (maxEntryNorm A : ℝ) :=
  norm_le_sparsity_mul_of_entry_le hA (maxEntryNorm A).coe_nonneg hs
    (norm_entry_le_maxEntryNorm A)

end UnitaryProducts
