/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-!
# The exponential averaging series in a Banach algebra

## Declarations

- `phiSeries`
- `summable_norm_phiSeries_term`
-/

@[expose] public section

open scoped BigOperators
open Real

noncomputable section

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `phiSeries a = ∑ aⁿ/(n+1)!`, i.e. `(exp a - 1)/a`: the averaging operator. It converges
absolutely for every `a` (`summable_norm_phiSeries_term`). -/
def phiSeries (a : A) : A := ∑' n : ℕ, ((Nat.factorial (n + 1) : ℂ)⁻¹) • a ^ n

omit [CompleteSpace A] in
/-- The exponential averaging series converges absolutely in every normed algebra. -/
theorem summable_norm_phiSeries_term (a : A) :
    Summable (fun n : ℕ ↦ ‖((Nat.factorial (n + 1) : ℂ)⁻¹) • a ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (Real.summable_pow_div_factorial ‖a‖)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le n.le_succ))
    (norm_pow_le a n) (norm_nonneg _) (by positivity)

end UnitaryProducts.Corrector
