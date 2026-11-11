/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.SeriesIdentity
public import UnitaryProducts.Walks.LogarithmBranch

/-!
# Eigenvectors of matrix exponentials

## Declarations

- `hasSum_exp_scalar`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open scoped Matrix
open NormedSpace Complex Set Real

namespace UnitaryProducts

open UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The complex exponential as a sum of its power series, in the form the matrix series uses. -/
theorem hasSum_exp_scalar (z : ℂ) :
    HasSum (fun n : ℕ ↦ ((n.factorial : ℂ)⁻¹ * z ^ n)) (Complex.exp z) := by
  simpa only [div_eq_inv_mul, Complex.exp_eq_exp_ℂ] using
    NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) z

end UnitaryProducts
