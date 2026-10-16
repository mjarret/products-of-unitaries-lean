/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.Walks.WalkScalarCut

/-! # Complex multiplier series for the appendix's equation `eq:N-series`

The Bernoulli generating series gives the cotangent multiplier. After an
imaginary rotation, the coefficient signs give its nonnegative power series
throughout the complex disk of radius `2 * π`.
-/
@[expose] public section

open Complex Real Set
open UnitaryProducts.Corrector
noncomputable section
namespace UnitaryProducts.WalkCut

/-- The first two Bernoulli coefficients, separated from the frame series. -/
theorem bernSeries_eq_frame_tail {z : ℂ} (hz : ‖z‖ < 2 * π) :
    bernSeries z = 1 - z / 2 + z ^ 2 * frameSeries z := by
  have hs := (summable_norm_bernSeries_term z hz).of_norm
  rw [bernSeries, ← hs.sum_add_tsum_nat_add 2]
  have htail : (∑' n : ℕ,
      (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • z ^ (n + 2)) =
      z ^ 2 * frameSeries z := by
    rw [frameSeries, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [smul_eq_mul, pow_add]
    ring
  rw [htail]
  norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one]
  ring

/-- The frame series at a complex imaginary multiple has nonnegative real coefficients. -/
theorem frameSeries_mul_I_positive (x : ℂ) :
    frameSeries (x * I) = ∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) * x ^ n := by
  rw [frameSeries]
  apply tsum_congr
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have hsign := neg_one_pow_mul_bernoulli_two_mul_add_two k
    have hpow : (x * I) ^ (k + k) = (-1 : ℂ) ^ k * x ^ (k + k) := by
      rw [mul_pow, show I ^ (k + k) = (-1 : ℂ) ^ k by
        rw [← two_mul, pow_mul, I_sq]]
      ring
    rw [smul_eq_mul, hpow, show k + k + 2 = 2 * k + 2 by ring, ← hsign]
    push_cast
    ring
  · subst hk
    rw [bernoulli_eq_bernoulli'_of_ne_one (by omega),
      bernoulli'_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]
    simp

/-- The complex-domain version of the nonnegative power series in equation `eq:N-series`. -/
theorem complexFrameMult_positive_power_series {x : ℂ} (hx : ‖x‖ < 2 * π) :
    complexFrameMult x = ∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) * x ^ n := by
  rw [← frameSeries_mul_I_positive]
  by_cases hx0 : x = 0
  · subst x
    simpa [complexFrameMult, frameBound_zero] using (frameSeries_ofReal_mul_I 0).symm
  have hz : ‖x * I‖ < 2 * π := by simpa using hx
  have hz0 : x * I ≠ 0 := mul_ne_zero hx0 I_ne_zero
  have he : Complex.exp (x * I) - 1 ≠ 0 := by
    intro h
    have hp := phiSeries_complex_mul_self (x * I)
    rw [h] at hp
    rcases mul_eq_zero.mp hp with hp | hp
    · have hi := bernSeries_mul_phiSeries (x * I) hz
      rw [hp, mul_zero] at hi
      exact zero_ne_one hi
    · exact hz0 hp
  have hmul : bernSeries (x * I) * (Complex.exp (x * I) - 1) = x * I := by
    rw [← phiSeries_complex_mul_self, ← mul_assoc, bernSeries_mul_phiSeries _ hz, one_mul]
  rw [bernSeries_eq_frame_tail hz] at hmul
  have hphase : 2 * I * (x / 2) = x * I := by ring
  have hc : Complex.exp (x * I) ≠ 1 := sub_ne_zero.mp he
  rw [complexFrameMult, if_neg hx0, Complex.cot_eq_exp_ratio, hphase]
  field_simp [hx0, I_ne_zero, sub_ne_zero.mpr hc, sub_ne_zero.mpr hc.symm] at *
  simp only [I_sq] at hmul
  linear_combination (norm := ring_nf) -I * hmul
  simp [I_sq]

end UnitaryProducts.WalkCut
