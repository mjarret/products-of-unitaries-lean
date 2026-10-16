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

- `exp_smul_mul_of_eigen`
- `hasSum_exp_scalar`
- `mul_exp_smul_of_eigen`
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

/-- **Right eigenvectors of the exponential.**  If `X E = c E` then `e^{zX} E = e^{zc} E`. -/
theorem exp_smul_mul_of_eigen {X E : 𝕄} {c : ℂ} (h : X * E = c • E) (z : ℂ) :
    exp (z • X) * E = Complex.exp (z * c) • E := by
  have hpow (n : ℕ) : X ^ n * E = c ^ n • E := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, pow_succ, mul_comm]
  refine HasSum.unique (((hasSum_exp_smul X z).mul_right E).congr_fun fun n ↦ ?_)
    ((hasSum_exp_scalar (z * c)).smul_const E)
  rw [smul_mul_assoc, hpow n, smul_smul, mul_pow, mul_assoc]

/-- **Left eigenvectors of the exponential.**  If `E X = c E` then `E e^{zX} = e^{zc} E`. -/
theorem mul_exp_smul_of_eigen {X E : 𝕄} {c : ℂ} (h : E * X = c • E) (z : ℂ) :
    E * exp (z • X) = Complex.exp (z * c) • E := by
  have hpow (n : ℕ) : E * X ^ n = c ^ n • E := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ' X, ← mul_assoc, h, smul_mul_assoc, ih, smul_smul, pow_succ, mul_comm]
  refine HasSum.unique (((hasSum_exp_smul X z).mul_left E).congr_fun fun n ↦ ?_)
    ((hasSum_exp_scalar (z * c)).smul_const E)
  rw [mul_smul_comm, hpow n, smul_smul, mul_pow, mul_assoc]

end UnitaryProducts
