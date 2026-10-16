/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps

/-!
# Unit-step comparison with separate corrector jumps

## Declarations

- `cubic_mesh_subset`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Real Set Complex UnitaryProducts.Corrector UnitaryProducts

noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Mesh cells lie in $[0, 1]$. -/
theorem cubic_mesh_subset {N i : ℕ} :
    meshInterval N i ⊆ Icc (0 : ℝ) 1 := mesh_subset

end UnitaryProducts.Paper
