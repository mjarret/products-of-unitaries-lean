/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib

/-! # The noncommutative power derivative used by Appendix A -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace UnitaryProducts.Corrector
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The derivative of $a \mapsto a^n$ in direction $b$, $\sum_{j<n} a^{n-1-j}ba^j$ (`0` for
$n = 0$). -/
def cubicPowDerivative (a b : A) (n : ℕ) : A :=
  ∑ j ∈ Finset.range n, a ^ (n - 1 - j) * b * a ^ j

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- $\|\partial(a^n)[b]\| \le n r^{n-1}\|b\|$ for $\|a\| \le r$. -/
theorem norm_cubicPowDerivative_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (n : ℕ) :
    ‖cubicPowDerivative a b n‖ ≤ n * r ^ (n - 1) * ‖b‖ := by
  have hr : 0 ≤ r := (norm_nonneg (a)).trans ha
  unfold cubicPowDerivative
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤ r ^ (n - 1) * ‖b‖ := by
    have hjn := Finset.mem_range.mp hj
    have hp : (n - 1 - j) + j = n - 1 := by omega
    calc
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤
          ‖a ^ (n - 1 - j)‖ * ‖b‖ * ‖a ^ j‖ := norm_mul₃_le
      _ ≤ r ^ (n - 1 - j) * ‖b‖ * r ^ j := by
        gcongr <;> exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
      _ = r ^ (n - 1) * ‖b‖ := by
        rw [mul_right_comm, ← pow_add, hp]
  refine (norm_sum_le_of_le _ hterm).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end UnitaryProducts.Corrector
