/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PowerSeries

/-!
# Two facts about the corrector series

## Declarations

- `corrBoundC`
- `corrBoundC_eq_tsum_abs_bernoulli`
- `adL_sub`
- `norm_I_smul_adL_sub_le`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Real

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The majorant $\sum_n |B^+_{n+1}|w^n/(n+1)!$ of the correction series (`bernoulli'`, with
$B^+_1 = +1/2$). The series converges for $|w| < 2\pi$; outside, `tsum` returns `0`. -/
noncomputable def corrBoundC (w : ℝ) : ℝ :=
  ∑' n : ℕ, |((bernoulli' (n + 1) : ℚ) : ℝ)| * w ^ n / (Nat.factorial (n + 1))

/-- The majorant of the correction series, written with the ordinary Bernoulli numbers. -/
theorem corrBoundC_eq_tsum_abs_bernoulli (w : ℝ) :
    corrBoundC w = ∑' n : ℕ, |((bernoulli (n + 1) : ℚ) : ℝ)| * w ^ n / (Nat.factorial (n + 1)) :=
  tsum_congr fun n ↦ by rw [abs_bernoulli'_eq_abs_bernoulli]

end UnitaryProducts.Corrector

namespace UnitaryProducts

open UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- $\mathrm{ad}_H - \mathrm{ad}_{H'} = \mathrm{ad}_{H - H'}$. -/
theorem adL_sub (H H' : 𝕄) : adL H - adL H' = adL (H - H') :=
  ContinuousLinearMap.ext fun E ↦ by
    simp only [ContinuousLinearMap.sub_apply, adL_apply, sub_mul, mul_sub]; abel

/-- $X \mapsto i\,\mathrm{ad}_X$ is $2$-Lipschitz: the bound
$\|\mathrm{ad}_{\tilde h} - \mathrm{ad}_h\| \le 2\|\tilde h - h\|$ in the proof of Lemma A.1(ii).
-/
theorem norm_I_smul_adL_sub_le (H H' : 𝕄) : ‖I • adL H - I • adL H'‖ ≤ 2 * ‖H - H'‖ := by
  simpa [← adL_sub, smul_sub] using norm_I_smul_adL_le (H - H') (0 : ℂ)

end UnitaryProducts
