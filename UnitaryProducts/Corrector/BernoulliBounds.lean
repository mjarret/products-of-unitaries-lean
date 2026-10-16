/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.MaxEntryError
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.IntegralDressedCell
public import UnitaryProducts.Comparison.IntegralUnitSteps
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Corrector.SeparatedStein
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Evolution.RegulatedDuhamel
public import UnitaryProducts.Evolution.RoundedClock
public import UnitaryProducts.Walks.LogarithmConstruction

/-!
# Symmetry and derivative of $\mathcal N$

## Declarations

- `bernBound_eq_one_add_half_add_sq_mul_frameBound`
- `frameBound_abs`
- `hasDerivAt_frameMult`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real
noncomputable section

namespace UnitaryProducts.Corrector

/-- `frameBound` is even: its odd terms vanish. -/
theorem frameBound_abs (x : ℝ) : frameBound |x| = frameBound x := by
  unfold frameBound
  refine tsum_congr fun n ↦ ?_
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [(even_two_mul k).pow_abs]
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by omega),
      bernoulli'_eq_zero_of_odd ⟨k+1, by ring⟩ (by omega)]
    simp

/-- The closed form of $\mathcal N$ has derivative `frameLip` on $|x| < 2\pi$. -/
theorem hasDerivAt_frameMult {x : ℝ} (hx : |x| < 2 * π) :
    HasDerivAt frameMult (frameLip x) x := by
  apply (hasDerivAt_frameBound hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
  exact (frameBound_abs_eq_frameMult hy).symm.trans (frameBound_abs y)

/-- The full Bernoulli majorant in terms of $\mathcal N$: `bernBound w = 1 + w/2 + w² frameBound w`
for $|w| < 2\pi$. -/
theorem bernBound_eq_one_add_half_add_sq_mul_frameBound {w : ℝ} (hw : |w| < 2 * π) :
    UnitaryProducts.bernBound w = 1+w/2+w^2*frameBound w := by
  have hs : Summable (fun n : ℕ ↦ |((bernoulli n : ℚ) : ℝ)| * w^n / (Nat.factorial n)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs, abs_div, abs_mul, abs_abs, abs_pow,
      Nat.abs_cast] using summable_bernoulli_majorant (abs_nonneg w) hw)
  have hs1 := (summable_nat_add_iff 1).mpr hs
  rw [UnitaryProducts.bernBound, hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
  simp only [bernoulli_zero, bernoulli_one, Rat.cast_one, abs_one, pow_zero,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_one, Nat.zero_add, pow_one,
    Nat.factorial_one]
  rw [frameBound, ← tsum_mul_left]
  have ht : (∑' n : ℕ, |((bernoulli (n+1+1) : ℚ) : ℝ)| * w^(n+1+1) /
      (Nat.factorial (n+1+1))) =
      ∑' n : ℕ, w^2*(|((bernoulli (n+2) : ℚ) : ℝ)| * w^n / (Nat.factorial (n+2))) := by
    refine tsum_congr fun n ↦ ?_
    rw [show n+1+1=n+2 by omega, pow_add]
    ring
  rw [ht]
  norm_num
  ring

end UnitaryProducts.Corrector
