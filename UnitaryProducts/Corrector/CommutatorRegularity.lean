/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmSmoothness

/-!
# The commutator as a continuous bilinear map

## Declarations

- `adLCLM`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace UnitaryProducts

/-- The adjoint map `ad_X` as a continuous linear map in `X` as well. -/
noncomputable def adLCLM (d : ℕ) : Matrix (Fin d) (Fin d) ℂ →L[ℂ]
    (Matrix (Fin d) (Fin d) ℂ →L[ℂ] Matrix (Fin d) (Fin d) ℂ) :=
  ContinuousLinearMap.mul ℂ (Matrix (Fin d) (Fin d) ℂ)
    - (ContinuousLinearMap.mul ℂ (Matrix (Fin d) (Fin d) ℂ)).flip

end UnitaryProducts
