/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.FrameOperator

/-!
# Reindexed sums of the corrector series

## Declarations

- `summable_frameBound_tail_div`
- `summable_frameBound_tail_div_nonneg`
- `summable_frameLip_shifted`
- `tsum_frameBound_tail_div`
- `tsum_frameBound_tail_div_nonneg`
- `tsum_frameLip_shifted`
- `frameBound_tail_zero`
-/

@[expose] public section

open Real
noncomputable section

namespace UnitaryProducts.Corrector

/-- The shifted series of `tsum_frameLip_shifted` converges on $[0, 2\pi)$. -/
theorem summable_frameLip_shifted {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦ |((bernoulli (n + 3) : ℚ) : ℝ)| * ((n : ℝ) + 1) * x ^ n /
      (Nat.factorial (n + 3) : ℝ)) := by
  have hs := (summable_nat_add_iff 1).mpr (summable_frameLip_majorant hx0 hx)
  simpa only [Nat.add_assoc, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using hs

/-- $\sum_n |B_{n+3}|(n+1)w^n/(n+3)! = \mathcal N'(w)$ = `frameLip w`: the sum of the
diagonal-variation row in the proof of the spectral comparison. -/
theorem tsum_frameLip_shifted {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    (∑' n : ℕ, |((bernoulli (n + 3) : ℚ) : ℝ)| * ((n : ℝ) + 1) * x ^ n /
      (Nat.factorial (n + 3) : ℝ)) = frameLip x := by
  rw [frameLip, (summable_frameLip_majorant hx0 hx).tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, zero_add,
    Nat.add_assoc, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]

/-- The series of `tsum_frameBound_tail_div` converges on $(0, 2\pi)$. -/
theorem summable_frameBound_tail_div {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦
      |((bernoulli (n + 3) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 3) : ℝ)) := by
  refine (((summable_nat_add_iff 1).mpr (summable_frameBound_majorant hx0.le hx)).div_const
    x).congr fun n ↦ ?_
  simp only [Nat.add_assoc, pow_succ]
  field_simp

/-- $\sum_n |B_{n+3}|w^n/(n+3)! = (\mathcal N(w) - 1/12)/w$ for $0 < w < 2\pi$. -/
theorem tsum_frameBound_tail_div {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    (∑' n : ℕ, |((bernoulli (n + 3) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 3) : ℝ)) =
      (frameBound x - 1 / 12) / x := by
  have hzero : |((bernoulli (0 + 2) : ℚ) : ℝ)| * x ^ 0 / (Nat.factorial (0 + 2) : ℝ) = 1 / 12 := by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_two, Nat.factorial]
  rw [eq_div_iff hx0.ne', ← tsum_mul_right, frameBound,
    (summable_frameBound_majorant hx0.le hx).tsum_eq_zero_add, hzero, add_sub_cancel_left]
  exact tsum_congr fun n ↦ by simp only [Nat.add_assoc, pow_succ]; ring

private theorem frameBound_tail_zero (n : ℕ) :
    |((bernoulli (n + 3) : ℚ) : ℝ)| * (0 : ℝ) ^ n / (Nat.factorial (n + 3) : ℝ) = 0 := by
  cases n <;> simp [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_three]

/-- `summable_frameBound_tail_div` on $[0, 2\pi)$; at $w = 0$ every term vanishes. -/
theorem summable_frameBound_tail_div_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦
      |((bernoulli (n + 3) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 3) : ℝ)) := by
  rcases eq_or_lt_of_le hx0 with rfl | hp
  · exact summable_zero.congr fun n ↦ (frameBound_tail_zero n).symm
  · exact summable_frameBound_tail_div hp hx

/-- $\sum_n |B_{n+3}|w^n/(n+3)! = (\mathcal N(w) - \mathcal N(0))/w$ on $[0, 2\pi)$, the sum of the
off-diagonal row in the proof of the spectral comparison; at $w = 0$ both sides are $0$ (`x / 0 =
0`, the
paper's reading of the quotient). -/
theorem tsum_frameBound_tail_div_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    (∑' n : ℕ, |((bernoulli (n + 3) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 3) : ℝ)) =
      (frameBound x - 1 / 12) / x := by
  rcases eq_or_lt_of_le hx0 with rfl | hp
  · simp only [frameBound_tail_zero, tsum_zero, div_zero]
  · exact tsum_frameBound_tail_div hp hx

end UnitaryProducts.Corrector
