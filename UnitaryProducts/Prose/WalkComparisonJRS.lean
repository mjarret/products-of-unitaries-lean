/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsWalks
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Separate derivative coefficients for the walk comparison

## Declarations

- `walkJRSFirst`
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory UnitaryProducts.Corrector
open UnitaryProducts.Paper UnitaryProducts.Dressed
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

namespace UnitaryProducts.Prose

/-- The coefficient of the uniform first derivative bound in the walk comparison. -/
def walkJRSFirst (w : ℝ) : ℝ :=
  2 * (frameBound w - frameBound (w / 2) / 2) * walkLogSlope w

end UnitaryProducts.Prose

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.walkConstantChord
