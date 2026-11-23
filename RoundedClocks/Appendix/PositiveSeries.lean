/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # The positive series of `𝒩`

The preamble of Appendix A: by the partial fractions of the cotangent (DLMF 4.22.3),
`𝒩(x) = ∑_{m ≥ 1} 2/(4π²m² - x²)` for `|x| < 2π`, so `𝒩(x) = ∑ₙ νₙ xⁿ` with every coefficient
`νₙ ≥ 0`. Here `multiplierCoeff n` is `νₙ`.
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

/-- Every pole `2π(m+1)` lies at or beyond `2π`. -/
theorem two_pi_le_pole (m : ℕ) : 2 * π ≤ 2 * π * (m + 1 : ℝ) := by
  calc
    2 * π = 2 * π * 1 := by ring
    _ ≤ 2 * π * (m + 1 : ℝ) := by
      gcongr
      linarith [Nat.cast_nonneg (α := ℝ) m]

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

/-- A single pole has the geometric expansion `2/(b² - x²) = ∑ₖ 2 x^{2k}/b^{2k+2}`. -/
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
    have hbase : 2 * π ≤ 2 * π * (m + 1 : ℝ) := two_pi_le_pole m
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

/-- Absolute convergence permits the common pole/Taylor sum swap, with an arbitrary weight on
each pole. -/
theorem weighted_partialFraction_sum_swap (a : ℕ → ℝ) {x : ℝ} (hx : |x| < 2 * π)
    (hprod : Summable (fun p : ℕ × ℕ ↦ a p.2 *
      (2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1)))) :
    (∑' k : ℕ, (∑' m : ℕ,
      a m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))) * x ^ (2 * k)) =
      ∑' m : ℕ, a m * (2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2)) := by
  let f : ℕ → ℕ → ℝ := fun k m ↦ a m *
    (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k))
  have hrow (k : ℕ) : (∑' m, f k m) =
      (∑' m, a m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))) * x ^ (2 * k) := by
    simp only [f, ← mul_assoc, tsum_mul_right]
  calc
    _ = ∑' k, ∑' m, f k m := tsum_congr fun k ↦ (hrow k).symm
    _ = ∑' m, ∑' k, f k m := hprod.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro m
      have hm : |x| < 2 * π * (m + 1 : ℝ) := hx.trans_le (two_pi_le_pole m)
      exact ((hasSum_multiplier_geometric (by positivity) hm).mul_left (a m)).tsum_eq

/-- Summing the geometric expansions recovers the cotangent pole sum. -/
theorem multiplierEvenCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' k : ℕ, multiplierEvenCoeff k * x ^ (2 * k)) =
      ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  simpa only [multiplierEvenCoeff, one_mul] using
    weighted_partialFraction_sum_swap (fun _ ↦ 1) hx (by
      simpa only [one_mul] using summable_multiplier_partialFraction_power hx)

/-- NIST Digital Library of Mathematical Functions, §4.22, equation 4.22.3.

Source statement, quoted verbatim:
`cot z = 1/z + 2z ∑_{n=1}^∞ 1/(z²-n²π²)`.

Mathlib proves this as `cot_series_rep'`. The paper substitutes `z=x/2` to obtain the positive
partial-fraction series for `𝒩(x)`. -/
def DLMF_4_22_3 : Prop :=
  ∀ z : ℂ, (∀ n : ℤ, z ≠ n * (π : ℂ)) →
    Complex.cot z = 1 / z + 2 * z *
      ∑' n : ℕ, 1 / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)

/-- The cotangent partial fractions are Mathlib's `cot_series_rep'`, rescaled by `π`. -/
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
  calc
    Complex.cot z = 1 / z + ((π : ℂ) * Complex.cot ((π : ℂ) * x) - 1 / x) / π := by
      rw [hπx]
      dsimp [x]
      field_simp [hπ, hz0]
      ring
    _ = _ := by rw [cot_series_rep' hx, ← tsum_div_const, tsum_congr hterm, tsum_mul_left]

/-- DLMF 4.22.5: the cosecant partial-fraction series, obtained from the cotangent series
by `csc z = cot (z/2) - cot z` and the even/odd decomposition. -/
theorem dlmf_4_22_5 :
    ∀ z : ℂ, (∀ n : ℤ, z ≠ n * (π : ℂ)) →
      (Complex.sin z)⁻¹ = 1 / z + 2 * z *
        ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) /
          (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) := by
  intro z hz
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz0 : z ≠ 0 := by simpa using hz 0
  let a : ℕ → ℂ := fun m ↦ 1 / (z ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)
  -- the terms are summable, from Mathlib's cotangent terms
  have hden (m : ℕ) : z ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 ≠ 0 := by
    intro h
    have h' : (z - ((m + 1 : ℕ) : ℂ) * π) * (z + ((m + 1 : ℕ) : ℂ) * π) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact hz (m + 1) (by push_cast at h1 ⊢; linear_combination h1)
    · exact hz (-(m + 1)) (by push_cast at h1 ⊢; linear_combination h1)
  have ha : Summable a := by
    have hx : z / π ∈ Complex.integerComplement := by
      rintro ⟨n, hn⟩
      exact hz n ((div_eq_iff hπ).mp hn.symm)
    refine ((summable_cotTerm hx).mul_left (1 / (2 * (z / π) * (π : ℂ) ^ 2))).congr fun m ↦ ?_
    have hd := hden m
    have key : (z / π + ((m : ℂ) + 1)) * (z / π - ((m : ℂ) + 1)) =
        (z ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) / (π : ℂ) ^ 2 := by
      push_cast
      field_simp
      ring
    rw [cotTerm_identity hx m, key]
    simp only [a]
    field_simp
  have hae : Summable fun m ↦ a (2 * m) :=
    ha.comp_injective (i := fun m ↦ 2 * m) fun m n (h : 2 * m = 2 * n) ↦ by omega
  have hao : Summable fun m ↦ a (2 * m + 1) :=
    ha.comp_injective (i := fun m ↦ 2 * m + 1) fun m n (h : 2 * m + 1 = 2 * n + 1) ↦ by omega
  have hsplit : ∑' m, a m = ∑' m, a (2 * m) + ∑' m, a (2 * m + 1) :=
    (tsum_even_add_odd hae hao).symm
  -- the cotangent at `z` and at `z/2`
  have hcot : Complex.cot z = 1 / z + 2 * z * ∑' m, a m := dlmf_4_22_3 z hz
  have hz2 : ∀ n : ℤ, z / 2 ≠ n * (π : ℂ) := by
    intro n h
    exact hz (2 * n) (by push_cast; linear_combination 2 * h)
  have hcot2 : Complex.cot (z / 2) = 2 / z + 4 * z * ∑' m, a (2 * m + 1) := by
    have hterm (n : ℕ) : 1 / ((z / 2) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) =
        4 * a (2 * n + 1) := by
      simp only [a]
      rw [show (z / 2) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2 =
        (z ^ 2 - ((2 * n + 1 + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) / 4 by push_cast; ring, one_div_div]
      ring
    rw [dlmf_4_22_3 (z / 2) hz2, tsum_congr hterm, tsum_mul_left]
    generalize (∑' m, a (2 * m + 1)) = s
    field_simp
  -- `csc z = cot (z/2) - cot z`
  have hsin : Complex.sin z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h
    exact hz n hn
  have hsin2 : Complex.sin (z / 2) ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h
    exact hz2 n hn
  have hs : Complex.sin z = 2 * Complex.sin (z / 2) * Complex.cos (z / 2) := by
    rw [← Complex.sin_two_mul]
    congr 1
    ring
  have hc : Complex.cos z = 2 * Complex.cos (z / 2) ^ 2 - 1 := by
    rw [← Complex.cos_two_mul]
    congr 1
    ring
  have hcos2 : Complex.cos (z / 2) ≠ 0 := by
    intro h
    exact hsin (by rw [hs, h, mul_zero])
  have hcsc : (Complex.sin z)⁻¹ = Complex.cot (z / 2) - Complex.cot z := by
    rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, hs, hc]
    field_simp
    ring
  -- the alternating series, split into even and odd terms
  have hbe (m : ℕ) : (-1 : ℂ) ^ (2 * m + 1) /
      (z ^ 2 - ((2 * m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) = -a (2 * m) := by
    simp only [a]
    rw [pow_succ, pow_mul, neg_one_sq, one_pow]
    ring
  have hbo (m : ℕ) : (-1 : ℂ) ^ (2 * m + 1 + 1) /
      (z ^ 2 - ((2 * m + 1 + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) = a (2 * m + 1) := by
    simp only [a]
    rw [pow_succ, pow_succ, pow_mul, neg_one_sq, one_pow]
    ring
  have hb : ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2) =
      ∑' m, a (2 * m + 1) - ∑' m, a (2 * m) := by
    have h := tsum_even_add_odd
      (f := fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) / (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2))
      (hae.neg.congr fun m ↦ (hbe m).symm) (hao.congr fun m ↦ (hbo m).symm)
    rw [← h, tsum_congr hbe, tsum_congr hbo, tsum_neg]
    ring
  rw [hcsc, hcot2, hcot, hsplit, hb]
  ring


/-- For `0 < |x| < 2π`, the half-argument `x/2` is not an integer multiple of `π`. -/
theorem div_two_ne_int_mul_pi {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) (n : ℤ) :
    (x : ℂ) / 2 ≠ n * (π : ℂ) := by
  have hn : x / 2 ≠ n * π := by
    intro he
    have he' : x = 2 * π * n := by linarith
    by_cases hz : n = 0
    · simp only [hz, Int.cast_zero, mul_zero] at he'
      exact hx0 he'
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hz
      rw [he', abs_mul, abs_of_pos Real.two_pi_pos] at hx
      exact hx.not_ge (le_mul_of_one_le_right Real.two_pi_pos.le h1)
  exact_mod_cast hn

/-- Substituting `z = x/2` in DLMF 4.22.3 gives `𝒩(x) = ∑_{m ≥ 1} 2/(4π²m² - x²)`. -/
theorem 𝒩_eq_partialFractions {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    𝒩 x = ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  have hc := dlmf_4_22_3 ((x : ℂ) / 2) (div_two_ne_int_mul_pi hx0 hx)
  have ht (m : ℕ) :
      2 / ((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2) =
      -(1 / (((x : ℂ) / 2) ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) / 2 := by
    push_cast
    have he : ((x : ℂ) / 2) ^ 2 - (m + 1 : ℂ) ^ 2 * (π : ℂ) ^ 2 =
        -((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2) / 4 := by ring
    rw [he]
    field_simp
    all_goals ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [tsum_congr ht, tsum_div_const, tsum_neg]
  generalize hs : (∑' n : ℕ, 1 /
    (((x : ℂ) / 2) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) = s at hc ⊢
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  simp only [𝒩, if_neg hx0]
  push_cast
  rw [hc]
  field_simp [hxC]
  all_goals ring

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

/-- For `|x| < 2π`, the positive series sums to `𝒩(x)`: `𝒩(x) = ∑ₙ νₙ xⁿ`. -/
theorem multiplierCoeff_series_eq (x : ℝ) (hx : |x| < 2 * π) :
    (∑' n : ℕ, multiplierCoeff n * x ^ n) = 𝒩 x := by
  by_cases hx0 : x = 0
  · subst x
    rw [tsum_eq_single 0]
    · simp [𝒩, multiplierCoeff_zero]
    · intro n hn
      simp [zero_pow hn]
  · rw [multiplierCoeff_power_eq_partialFractions hx]
    exact (𝒩_eq_partialFractions hx0 hx).symm

end RoundedClocks
