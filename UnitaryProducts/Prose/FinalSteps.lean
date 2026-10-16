/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Prose.Preliminaries

/-!
# The operator norm of a matrix

## Declarations

- `matrix_norm_eq_operator_norm`
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.Prose

/-- Section 2, opening norm convention: the matrix norm used in every statement
is the operator norm of its action on Euclidean space. -/
theorem matrix_norm_eq_operator_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A‖ = ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A‖ :=
  (Matrix.l2_opNorm_toEuclideanCLM A).symm

end UnitaryProducts.Prose
