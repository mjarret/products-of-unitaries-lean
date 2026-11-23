/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Positive series for the Appendix multiplier

This file proves the positive Taylor expansions used immediately before Lemma A.1.  The
coefficients come from the cotangent partial fractions; pairing consecutive cosecant poles gives
the positivity needed for the cell-center estimate.
-/

@[expose] public section

open scoped BigOperators Real
open Real

noncomputable section

namespace RoundedClocks

/-- The coefficient of `x ^ (2 * k)` in the partial-fraction expansion of `𝒩`. -/
def multiplierEvenCoeff (k : ℕ) : ℝ :=
  ∑' m : ℕ, 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)

/-- The Taylor coefficients of `𝒩`; all odd coefficients vanish. -/
def multiplierCoeff (n : ℕ) : ℝ :=
  if Even n then multiplierEvenCoeff (n / 2) else 0

/-- Each inverse-power sum defining an even coefficient converges. -/
theorem summable_multiplierEvenCoeff (k : ℕ) :
    Summable (fun m : ℕ ↦ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)) := by
  have hs := (summable_pow_div_add (2 / (2 * π) ^ (2 * k + 2) : ℝ)
    (2 * k + 2) 1 (by omega)).of_norm
  simpa only [Nat.cast_one, mul_pow, div_div] using hs

/-- Every coefficient of the multiplier series is nonnegative. -/
theorem multiplierCoeff_nonneg (n : ℕ) : 0 ≤ multiplierCoeff n := by
  unfold multiplierCoeff multiplierEvenCoeff
  split_ifs
  · exact tsum_nonneg fun _ ↦ by positivity
  · exact le_rfl

/-- The even coefficients have their defining partial-fraction form. -/
theorem multiplierCoeff_even (k : ℕ) :
    multiplierCoeff (2 * k) = multiplierEvenCoeff k := by
  simp [multiplierCoeff]

/-- The odd coefficients vanish. -/
theorem multiplierCoeff_odd (k : ℕ) : multiplierCoeff (2 * k + 1) = 0 := by
  simp [multiplierCoeff]

/-- A single pole has the geometric expansion used in the manuscript. -/
theorem hasSum_multiplier_geometric {x b : ℝ} (hb : 0 < b) (hx : |x| < b) :
    HasSum (fun k : ℕ ↦ 2 / b ^ (2 * k + 2) * x ^ (2 * k))
      (2 / (b ^ 2 - x ^ 2)) := by
  have hr : |x / b| < 1 := by
    rw [abs_div, abs_of_pos hb]
    exact (div_lt_one hb).mpr hx
  have hr2 : (x / b) ^ 2 < 1 := by
    simpa only [one_pow, sq_abs] using
      pow_lt_pow_left₀ hr (abs_nonneg (x / b)) (by decide : 2 ≠ 0)
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg (x / b)) hr2).mul_left (2 / b ^ 2)
  have ht (k : ℕ) : 2 / b ^ 2 * ((x / b) ^ 2) ^ k =
      2 / b ^ (2 * k + 2) * x ^ (2 * k) := by
    rw [← pow_mul, div_pow, pow_add]
    ring
  have he : 2 / b ^ 2 * (1 - (x / b) ^ 2)⁻¹ = 2 / (b ^ 2 - x ^ 2) := by
    rw [div_pow, one_sub_div (pow_ne_zero _ hb.ne'), inv_div]
    field_simp
  exact he ▸ hs.congr_fun (fun k ↦ (ht k).symm)

/-- The even coefficient at order `k` is bounded by its constant term and the first pole. -/
theorem multiplierEvenCoeff_le (k : ℕ) :
    multiplierEvenCoeff k ≤ multiplierEvenCoeff 0 / (2 * π) ^ (2 * k) := by
  have hterms (m : ℕ) :
      2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) ≤
        (2 / (2 * π * (m + 1 : ℝ)) ^ 2) / (2 * π) ^ (2 * k) := by
    have hb : 0 < 2 * π * (m + 1 : ℝ) := by positivity
    have hbase : 2 * π ≤ 2 * π * (m + 1 : ℝ) := by
      calc
        2 * π = 2 * π * 1 := by ring
        _ ≤ 2 * π * (m + 1 : ℝ) := by
          gcongr
          linarith [Nat.cast_nonneg (α := ℝ) m]
    calc
      _ = (2 / (2 * π * (m + 1 : ℝ)) ^ 2) /
          (2 * π * (m + 1 : ℝ)) ^ (2 * k) := by
        rw [pow_add, div_mul_eq_div_div, div_right_comm]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ Real.two_pi_pos.le hbase _)
  have hsum := (summable_multiplierEvenCoeff k).tsum_le_tsum hterms
    ((summable_multiplierEvenCoeff 0).div_const ((2 * π) ^ (2 * k)))
  simpa only [multiplierEvenCoeff, Nat.mul_zero, zero_add, tsum_div_const] using hsum

/-- The even multiplier series converges for `|x| < 2π`. -/
theorem summable_multiplierEvenCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun k : ℕ ↦ multiplierEvenCoeff k * x ^ (2 * k)) := by
  have hr : |x / (2 * π)| < 1 := by
    rw [abs_div, abs_of_pos Real.two_pi_pos]
    exact (div_lt_one Real.two_pi_pos).mpr hx
  have hr2 : (x / (2 * π)) ^ 2 < 1 := by
    simpa only [one_pow, sq_abs] using
      pow_lt_pow_left₀ hr (abs_nonneg (x / (2 * π))) (by decide : 2 ≠ 0)
  have hsum := (summable_geometric_of_lt_one (sq_nonneg (x / (2 * π))) hr2).mul_left
    (multiplierEvenCoeff 0)
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (tsum_nonneg fun _ ↦ by positivity)
      (Even.pow_nonneg (even_two_mul k) x))
    (fun k ↦ ?_) hsum
  calc
    _ ≤ (multiplierEvenCoeff 0 / (2 * π) ^ (2 * k)) * x ^ (2 * k) :=
      mul_le_mul_of_nonneg_right (multiplierEvenCoeff_le k)
        (Even.pow_nonneg (even_two_mul k) x)
    _ = multiplierEvenCoeff 0 * ((x / (2 * π)) ^ 2) ^ k := by
      rw [← pow_mul, div_pow]
      ring

/-- Absolute convergence justifies interchanging the pole and Taylor sums. -/
theorem summable_multiplier_partialFraction_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun p : ℕ × ℕ ↦
      2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1)) := by
  apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ ↦
    2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1))
    (fun p ↦ mul_nonneg (by positivity) ((even_two_mul p.1).pow_nonneg x))).mpr
  constructor
  · intro k
    exact (summable_multiplierEvenCoeff k).mul_right (x ^ (2 * k))
  apply (summable_multiplierEvenCoeff_power hx).congr
  intro k
  change multiplierEvenCoeff k * x ^ (2 * k) = _
  exact tsum_mul_right.symm

/-- Summing the geometric expansions recovers the cotangent pole sum. -/
theorem multiplierEvenCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' k : ℕ, multiplierEvenCoeff k * x ^ (2 * k)) =
      ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  let f : ℕ → ℕ → ℝ := fun k m ↦
    2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k)
  have hrow (k : ℕ) : (∑' m, f k m) = multiplierEvenCoeff k * x ^ (2 * k) :=
    tsum_mul_right
  have hprod : Summable (Function.uncurry f) := summable_multiplier_partialFraction_power hx
  calc
    _ = ∑' k, ∑' m, f k m := tsum_congr fun k ↦ (hrow k).symm
    _ = ∑' m, ∑' k, f k m := hprod.tsum_comm.symm
    _ = _ := tsum_congr fun m ↦ (hasSum_multiplier_geometric (by positivity)
      (hx.trans_le (by
        calc
          2 * π = 2 * π * 1 := by ring
          _ ≤ 2 * π * (m + 1 : ℝ) := by
            gcongr
            linarith [Nat.cast_nonneg (α := ℝ) m]))).tsum_eq

/-- NIST Digital Library of Mathematical Functions, §4.22, equation 4.22.3.

Source statement, quoted verbatim:
`cot z = 1/z + 2z ∑_{n=1}^∞ 1/(z²-n²π²)`.

Mathlib proves this as `cot_series_rep`. The paper substitutes `z=x/2` to obtain the positive
partial-fraction series for `𝒩(x)`. -/
def DLMF_4_22_3 : Prop :=
  ∀ z : ℂ, (∀ n : ℤ, z ≠ n * (π : ℂ)) →
    Complex.cot z = 1 / z + 2 * z *
      ∑' n : ℕ, 1 / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)

/-- The cotangent partial fractions are Mathlib's `cot_series_rep`, rescaled by `π`. -/
theorem dlmf_4_22_3 : DLMF_4_22_3 := by
  intro z hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  let x : ℂ := z / π
  have hx : x ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    exact hz n ((div_eq_iff hπ).mp hn.symm)
  have hπx : (π : ℂ) * x = z := by
    dsimp [x]
    field_simp
  have hterm (n : ℕ) :
      (1 / (x - ((n : ℂ) + 1)) + 1 / (x + ((n : ℂ) + 1))) / π =
        2 * z * (1 / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) := by
    have hm : x - ((n : ℂ) + 1) ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hz (n + 1)
      rw [← hπx, he]
      push_cast
      ring
    have hp : x + ((n : ℂ) + 1) ≠ 0 := by
      intro he
      apply hz (-(n + 1 : ℤ))
      rw [← hπx, eq_neg_of_add_eq_zero_left he]
      push_cast
      ring
    have he :
        ((π : ℂ) * x) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 =
          (π : ℂ) ^ 2 * (x - ((n : ℂ) + 1)) * (x + ((n : ℂ) + 1)) := by
      push_cast
      ring
    have hd : z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 ≠ 0 := by
      rw [← hπx, he]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπ) hm) hp
    rw [← hπx, he]
    field_simp [hπ, hm, hp, hd]
    ring
  have hsum :
      (∑' n : ℕ, (1 / (x - ((n : ℂ) + 1)) + 1 / (x + ((n : ℂ) + 1)))) / π =
        2 * z * ∑' n : ℕ,
          1 / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) := by
    rw [← tsum_div_const, tsum_congr hterm, tsum_mul_left]
  have hc := cot_series_rep hx
  have hc' := cot_series_rep' hx
  have hreindex :
      (∑' n : ℕ+, (1 / (x - (n : ℂ)) + 1 / (x + (n : ℂ)))) =
        ∑' n : ℕ, (1 / (x - ((n : ℂ) + 1)) + 1 / (x + ((n : ℂ) + 1))) := by
    rw [← hc', hc]
    ring
  calc
    Complex.cot z = 1 / z + ((π : ℂ) * Complex.cot ((π : ℂ) * x) - 1 / x) / π := by
      rw [hπx]
      dsimp [x]
      field_simp [hπ, hz0]
      ring
    _ = 1 / z +
        (∑' n : ℕ+, (1 / (x - (n : ℂ)) + 1 / (x + (n : ℂ)))) / π := by
      rw [hc]
      ring
    _ = 1 / z +
        (∑' n : ℕ, (1 / (x - ((n : ℂ) + 1)) + 1 / (x + ((n : ℂ) + 1)))) / π := by
      rw [hreindex]
    _ = _ := by rw [hsum]

/-- The real cotangent partial fractions, transferred from `dlmf_4_22_3`. -/
private theorem real_cot_partialFractions {z : ℝ} (hz : ∀ n : ℤ, z ≠ n) :
    π * Real.cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz 0
  have hpoles : ∀ n : ℤ, (π : ℂ) * (z : ℂ) ≠ n * (π : ℂ) := by
    intro n hn
    apply hz n
    have he : (z : ℂ) = (n : ℂ) := mul_left_cancel₀ hπ (by simpa [mul_comm] using hn)
    exact_mod_cast he
  have hc := dlmf_4_22_3 ((π : ℂ) * (z : ℂ)) hpoles
  have hterm (n : ℕ) :
      (π : ℂ) * (2 * ((π : ℂ) * (z : ℂ)) *
        (1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
          ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2))) =
        1 / ((z : ℂ) - ((n : ℂ) + 1)) + 1 / ((z : ℂ) + ((n : ℂ) + 1)) := by
    have hm : (z : ℂ) - ((n : ℂ) + 1) ≠ 0 := by
      rw [sub_ne_zero]
      intro he
      apply hz (n + 1)
      exact_mod_cast he
    have hp : (z : ℂ) + ((n : ℂ) + 1) ≠ 0 := by
      intro he
      apply hz (-(n + 1 : ℤ))
      exact_mod_cast eq_neg_of_add_eq_zero_left he
    have he :
        ((π : ℂ) * (z : ℂ)) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 =
          (π : ℂ) ^ 2 * ((z : ℂ) - ((n : ℂ) + 1)) *
            ((z : ℂ) + ((n : ℂ) + 1)) := by
      push_cast
      ring
    have hd :
        ((π : ℂ) * (z : ℂ)) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 ≠ 0 := by
      rw [he]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπ) hm) hp
    rw [he]
    field_simp [hπ, hm, hp, hd]
    ring
  have hsum :
      (π : ℂ) * (2 * ((π : ℂ) * (z : ℂ)) *
        ∑' n : ℕ, 1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
          ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) =
        ∑' n : ℕ,
          (1 / ((z : ℂ) - ((n : ℂ) + 1)) + 1 / ((z : ℂ) + ((n : ℂ) + 1))) := by
    calc
      _ = ((π : ℂ) * (2 * ((π : ℂ) * (z : ℂ)))) *
          (∑' n : ℕ, 1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
            ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) := by ring
      _ = (∑' n : ℕ, ((π : ℂ) * (2 * ((π : ℂ) * (z : ℂ)))) *
          (1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
            ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2))) := tsum_mul_left.symm
      _ = _ := tsum_congr fun n ↦ by simpa only [mul_assoc] using hterm n
  have hreindex :
      (∑' n : ℕ,
        (1 / ((z : ℂ) - ((n : ℂ) + 1)) + 1 / ((z : ℂ) + ((n : ℂ) + 1)))) =
        ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / ((z : ℂ) + n)) := by
    rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm
      (fun n : ℕ+ ↦ 1 / ((z : ℂ) - n) + 1 / ((z : ℂ) + n))]
    apply tsum_congr
    intro n
    simp only [Equiv.pnatEquivNat_symm_apply]
    norm_cast
  have hfirst : (π : ℂ) * (1 / ((π : ℂ) * (z : ℂ))) = 1 / (z : ℂ) := by
    field_simp [hπ, hz0]
  have hcomplex :
      (π : ℂ) * Complex.cot ((π : ℂ) * (z : ℂ)) =
        1 / (z : ℂ) + ∑' n : ℕ+, (1 / ((z : ℂ) - n) + 1 / ((z : ℂ) + n)) := by
    calc
      _ = (π : ℂ) * (1 / ((π : ℂ) * (z : ℂ)) +
          2 * ((π : ℂ) * (z : ℂ)) *
            ∑' n : ℕ, 1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
              ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) := by rw [hc]
      _ = (π : ℂ) * (1 / ((π : ℂ) * (z : ℂ))) +
          (π : ℂ) * (2 * ((π : ℂ) * (z : ℂ)) *
            ∑' n : ℕ, 1 / (((π : ℂ) * (z : ℂ)) ^ 2 -
              ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) := by ring
      _ = _ := by rw [hfirst, hsum, hreindex]
  apply Complex.ofReal_injective
  convert hcomplex using 1 <;>
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_tsum,
      Real.cot_eq_cos_div_sin, Complex.cot, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_natCast]

/-- Rescaling the cotangent partial fractions gives the manuscript's multiplier. -/
theorem cot_form_eq_multiplier_partialFractions {x : ℝ}
    (hx : ∀ n : ℤ, x ≠ 2 * π * n) :
    (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 =
      ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2) := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hp : 2 * π ≠ 0 := mul_ne_zero (by norm_num) pi_ne_zero
  let z := x / (2 * π)
  have hz : ∀ n : ℤ, z ≠ n := fun n hn ↦
    hx n (by simpa only [mul_comm] using (div_eq_iff hp).mp hn)
  have hz0 : z ≠ 0 := div_ne_zero hx0 hp
  have hc := real_cot_partialFractions hz
  have ht (n : ℕ+) : -(1 / (z - n) + 1 / (z + n)) / (2 * π * x) =
      2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2) := by
    have hm : z - (n : ℝ) ≠ 0 := sub_ne_zero.mpr (hz (n : ℕ))
    have ha : z + (n : ℝ) ≠ 0 := fun he ↦
      hz (-(n : ℤ)) (by push_cast; exact eq_neg_of_add_eq_zero_left he)
    have he : 4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2 =
        -(2 * π) ^ 2 * (z - n) * (z + n) := by
      dsimp [z]
      field_simp
      ring
    have hxe : x = 2 * π * z := by
      dsimp [z]
      field_simp
    rw [he, hxe]
    field_simp [hm, ha, hz0, pi_ne_zero]
    ring
  rw [← tsum_congr ht, tsum_div_const, tsum_neg,
    (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hc.symm)),
    show π * z = x / 2 by dsimp [z]; field_simp]
  dsimp [z]
  field_simp
  ring

/-- The full multiplier coefficient series converges on the same interval. -/
theorem summable_multiplierCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun n : ℕ ↦ multiplierCoeff n * x ^ n) := by
  apply Summable.even_add_odd
  · simpa only [multiplierCoeff_even] using summable_multiplierEvenCoeff_power hx
  · simp only [multiplierCoeff_odd, zero_mul, summable_zero]

/-- The multiplier Taylor series is the pole sum. -/
theorem multiplierCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' n : ℕ, multiplierCoeff n * x ^ n) =
      ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  have he : Summable (fun k : ℕ ↦ multiplierCoeff (2 * k) * x ^ (2 * k)) := by
    simpa only [multiplierCoeff_even] using summable_multiplierEvenCoeff_power hx
  have ho : Summable (fun k : ℕ ↦
      multiplierCoeff (2 * k + 1) * x ^ (2 * k + 1)) := by
    simp only [multiplierCoeff_odd, zero_mul, summable_zero]
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ ↦ multiplierCoeff n * x ^ n) he ho
  simp only [multiplierCoeff_even, multiplierCoeff_odd, zero_mul, tsum_zero, add_zero] at hsplit
  exact hsplit.symm.trans (multiplierEvenCoeff_power_eq_partialFractions hx)

/-- The cotangent formula equals the positive Taylor series away from zero. -/
theorem multiplierCoeff_series_eq_cot {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    (∑' n : ℕ, multiplierCoeff n * x ^ n) =
      (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 := by
  have hn (n : ℤ) : x ≠ 2 * π * n := by
    by_cases hzero : n = 0
    · simpa only [hzero, Int.cast_zero, mul_zero] using hx0
    · rintro rfl
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hzero
      rw [abs_mul, abs_of_pos Real.two_pi_pos] at hx
      exact hx.not_ge (le_mul_of_one_le_right Real.two_pi_pos.le h1)
  have hcot := cot_form_eq_multiplier_partialFractions hn
  rw [hcot, multiplierCoeff_power_eq_partialFractions hx,
    tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ ↦ 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2))]
  apply tsum_congr
  intro m
  push_cast
  congr 2
  ring

/-- The constant coefficient is `𝒩(0) = 1/12`. -/
theorem multiplierCoeff_zero : multiplierCoeff 0 = 1 / 12 := by
  have hz := hasSum_zeta_two.mul_left (2 / (2 * π) ^ 2)
  have hs : HasSum (fun m : ℕ ↦ 2 / (2 * π * (m : ℝ)) ^ 2) (1 / 12) := by
    convert hz using 1
    · funext m
      rw [mul_pow]
      ring
    · field_simp
      ring
  have ht := (hasSum_nat_add_iff
    (f := fun m : ℕ ↦ 2 / (2 * π * (m : ℝ)) ^ 2) 1).mpr (by simpa using hs)
  rw [show (0 : ℕ) = 2 * 0 by omega, multiplierCoeff_even]
  simpa only [multiplierEvenCoeff, Nat.mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
    one_div] using ht.tsum_eq

/-- On `|x| < 2π`, the positive series sums to the manuscript's multiplier `𝒩(x)`. -/
theorem multiplierCoeff_series_eq (x : ℝ) (hx : |x| < 2 * π) :
    (∑' n : ℕ, multiplierCoeff n * x ^ n) = 𝒩 x := by
  by_cases hx0 : x = 0
  · subst x
    rw [tsum_eq_single 0]
    · simp [𝒩, multiplierCoeff_zero]
    · intro n hn
      simp [zero_pow hn]
  · rw [multiplierCoeff_series_eq_cot hx0 hx, 𝒩, if_neg hx0]

end RoundedClocks
