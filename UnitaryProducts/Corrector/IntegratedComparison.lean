/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.CommutatorRegularity

/-!
# Two elementary integrals

## Declarations

- `integral_affine`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Set UnitaryProducts.Corrector Real Complex MeasureTheory

/-- The integral of an affine function from its zero of reference. -/
theorem integral_affine (a t p q : ℝ) :
    (∫ s in a..t, (p * (s - a) + q)) = p * (t - a) ^ 2 / 2 + q * (t - a) := by
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        (intervalIntegrable_const (c := a)), integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
  ring

end UnitaryProducts
