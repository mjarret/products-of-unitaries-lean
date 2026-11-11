/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogHessian

/-!
# Derivative bounds for the walk logarithm on $[0,1]$

## Declarations

- `Prose.evol_sub_scalar_one`
-/

@[expose] public section

open Real Set Complex Filter NormedSpace
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace UnitaryProducts
-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements); see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace Prose

omit [NeZero d] in
/-- Section 4, the scalar shift identifying the fixed-turn integral with the
rotated walk in the logarithm and transfer arguments. -/
theorem evol_sub_scalar_one (H : 𝕄) (c : ℝ) :
    evol (H - (c : ℂ) • 1) 1 = Complex.exp (I * (c : ℂ)) • evol H 1 := by
  have he : -I • (H - (c : ℂ) • (1 : 𝕄)) =
      algebraMap ℂ 𝕄 (I * (c : ℂ)) + (-I) • H := by
    rw [Algebra.algebraMap_eq_smul_one]
    module
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol, one_smul, he, NormedSpace.exp_add_of_commute (Algebra.commutes _ _)]
  rw [← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  simp only [evol, one_smul]

end Prose

end UnitaryProducts
