/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-!
# The Bernoulli generating function in a Banach algebra

## Declarations

- `abs_bernoulli_div_factorial_le`
- `abs_bernoulli_term_eq`
- `abs_bernoulli_two_mul`
- `abs_bernoulli_two_mul_div_factorial`
- `bernSeries`
- `bernSeries_mul_I`
- `bernSeries_mul_phiSeries`
- `cot_closed_form_mul`
- `mul_comm_tsum_pow`
- `norm_bernSeries_le`
- `phiSeries`
- `phiSeries_complex_mul_self`
- `phiSeries_mul_bernSeries`
- `sum_bernoulli_div_factorial`
- `sum_bernoulli_div_factorial_complex`
- `summable_bernoulli_majorant`
- `summable_norm_bernSeries_term`
- `summable_norm_phiSeries_term`
- `tsum_abs_bernoulli_eq`
- `tsum_one_div_pow_le_two`
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

/-- `bernSeries a = ∑ Bₙ aⁿ/n!`, i.e. `a/(exp a - 1)` (Mathlib's `bernoulli`, `B₁ = -1/2`). It
converges absolutely for $\|a\| < 2\pi$ (`summable_norm_bernSeries_term`) and is the `tsum` junk
value $0$ when the series is not summable. -/
def bernSeries (a : A) : A :=
  ∑' n : ℕ, (((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • a ^ n

/-- `ζ(2k) ≤ 2` for `k ≥ 1`. -/
theorem tsum_one_div_pow_le_two {k : ℕ} (hk : k ≠ 0) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) ≤ 2 := by
  have h1 : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * k)) := (hasSum_zeta_nat hk).summable
  have h2 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  have hle (n : ℕ) : 1 / (n : ℝ) ^ (2 * k) ≤ 1 / (n : ℝ) ^ 2 := by
    match n with
    | 0 => simp [zero_pow (show 2 * k ≠ 0 by omega)]
    | 1 => simp
    | (m + 2) =>
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (Nat.one_le_cast.mpr (by omega)) (by omega))
  calc ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
        h1.tsum_le_tsum hle h2.summable
    _ = π ^ 2 / 6 := h2.tsum_eq
    _ ≤ 2 := by linarith [mul_lt_mul'' pi_lt_d2 pi_lt_d2 pi_pos.le pi_pos.le]

/-- The sign of the nonzero Bernoulli numbers: `|B_{2k}| = (-1)^{k+1} B_{2k}` for `k ≥ 1`. -/
theorem abs_bernoulli_two_mul {k : ℕ} (hk : k ≠ 0) :
    |((bernoulli (2 * k) : ℚ) : ℝ)| = (-1 : ℝ) ^ (k + 1) * ((bernoulli (2 * k) : ℚ) : ℝ) := by
  set B : ℝ := ((bernoulli (2 * k) : ℚ) : ℝ) with hB
  have hpos : (0 : ℝ) < 2 ^ (2 * k - 1) * π ^ (2 * k) / (Nat.factorial (2 * k)) := by positivity
  have hS' : ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)
      = ((-1 : ℝ) ^ (k + 1) * B) *
        (2 ^ (2 * k - 1) * π ^ (2 * k) / (Nat.factorial (2 * k))) := by
    rw [(hasSum_zeta_nat hk).tsum_eq]; ring
  have hS0 : (0 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) :=
    tsum_nonneg (fun n : ℕ ↦ div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg n) (2 * k)))
  have hc : 0 ≤ (-1 : ℝ) ^ (k + 1) * B := (mul_nonneg_iff_of_pos_right hpos).mp (hS' ▸ hS0)
  rw [← abs_of_nonneg hc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- For `k ≥ 1`, `|B_{2k}|/(2k)! = 2 ζ(2k)/(2π)^{2k}`. -/
theorem abs_bernoulli_two_mul_div_factorial {k : ℕ} (hk : k ≠ 0) :
    |((bernoulli (2 * k) : ℚ) : ℝ)| / (Nat.factorial (2 * k)) =
      2 * (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)) / (2 * π) ^ (2 * k) := by
  set B : ℝ := ((bernoulli (2 * k) : ℚ) : ℝ) with hB
  have hfac : (0 : ℝ) < (Nat.factorial (2 * k)) := by exact_mod_cast Nat.factorial_pos _
  have hpi : (0 : ℝ) < π ^ (2 * k) := by positivity
  have hpow : (0 : ℝ) < 2 ^ (2 * k - 1) := by positivity
  have hS' : ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)
      = ((-1 : ℝ) ^ (k + 1) * B) *
        (2 ^ (2 * k - 1) * π ^ (2 * k) / (Nat.factorial (2 * k))) := by
    rw [(hasSum_zeta_nat hk).tsum_eq]; ring
  have h2 : (2 : ℝ) ^ (2 * k) = 2 * 2 ^ (2 * k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)]
  rw [abs_bernoulli_two_mul hk, hS', mul_pow, h2]
  field_simp
  exact hB.symm

/-- The basic coefficient bound `|Bₙ|/n! ≤ 4/(2π)ⁿ`. -/
theorem abs_bernoulli_div_factorial_le (n : ℕ) :
    |((bernoulli n : ℚ) : ℝ)| / (Nat.factorial n) ≤ 4 / (2 * π) ^ n := by
  have hpi := pi_pos
  have hp : (0 : ℝ) < (2 * π) ^ n := by positivity
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · norm_num
    · rw [abs_bernoulli_two_mul_div_factorial (by omega)]
      have h2 := tsum_one_div_pow_le_two (k := k) (by omega)
      gcongr
      linarith
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · norm_num [Nat.factorial]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith [pi_le_four]
    · rw [bernoulli_eq_zero_of_odd (odd_two_mul_add_one k) (by omega)]
      simp only [Rat.cast_zero, abs_zero, zero_div, ge_iff_le]
      positivity

/-- The Bernoulli majorant converges strictly inside the disc of radius `2π`. -/
theorem summable_bernoulli_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦ |((bernoulli n : ℚ) : ℝ)| * x ^ n / (Nat.factorial n)) := by
  have hpi := pi_pos
  have hr0 : 0 ≤ x / (2 * π) := by positivity
  have hr1 : x / (2 * π) < 1 := by rw [div_lt_one (by positivity)]; exact hx
  have hg : Summable (fun n : ℕ ↦ 4 * (x / (2 * π)) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left 4
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hg
  have h := abs_bernoulli_div_factorial_le n
  have hxn : (0 : ℝ) ≤ x ^ n := pow_nonneg hx0 n
  calc |((bernoulli n : ℚ) : ℝ)| * x ^ n / (Nat.factorial n)
      = (|((bernoulli n : ℚ) : ℝ)| / (Nat.factorial n)) * x ^ n := by ring
    _ ≤ (4 / (2 * π) ^ n) * x ^ n := by gcongr
    _ = 4 * (x / (2 * π)) ^ n := by rw [div_pow]; ring

omit [CompleteSpace A] in
theorem summable_norm_bernSeries_term (a : A) (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦ ‖(((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • a ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_bernoulli_majorant (norm_nonneg a) ha)
  rw [norm_smul, norm_div, Complex.norm_ratCast, Complex.norm_natCast, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le a n) (abs_nonneg _)

omit [CompleteSpace A] in
theorem summable_norm_phiSeries_term (a : A) :
    Summable (fun n : ℕ ↦ ‖((Nat.factorial (n + 1) : ℂ)⁻¹) • a ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (Real.summable_pow_div_factorial ‖a‖)
  rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le n.le_succ))
    (norm_pow_le a n) (norm_nonneg _) (by positivity)

/-- `∑_{k ≤ n} B_k / (k! (n-k+1)!) = [n = 0]`. -/
theorem sum_bernoulli_div_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (bernoulli k) / ((Nat.factorial k : ℚ) * (Nat.factorial (n - k + 1) : ℚ))
      = if n = 0 then 1 else 0 := by
  have key := sum_bernoulli (n + 1)
  have hstep : ∀ k ∈ Finset.range (n + 1),
      (bernoulli k) / ((Nat.factorial k : ℚ) * (Nat.factorial (n - k + 1) : ℚ))
        = ((n + 1).choose k : ℚ) * bernoulli k / (Nat.factorial (n + 1) : ℚ) := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hch : ((n + 1).choose k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k + 1) : ℚ)
        = (Nat.factorial (n + 1) : ℚ) := by
      rw [show n - k + 1 = n + 1 - k by omega]
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show k ≤ n + 1 by omega)
    rw [div_eq_div_iff (by positivity) (by positivity), ← hch]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, key]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

/-- Complex version of `sum_bernoulli_div_factorial`. -/
theorem sum_bernoulli_div_factorial_complex (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (((bernoulli k : ℚ) : ℂ) / (Nat.factorial k : ℂ)) *
          ((Nat.factorial (n - k + 1) : ℂ))⁻¹
      = if n = 0 then 1 else 0 := by
  have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (sum_bernoulli_div_factorial n)
  push_cast at h
  rw [show ((if n = 0 then (1 : ℚ) else 0 : ℚ) : ℂ) = (if n = 0 then (1 : ℂ) else 0) from by
    split_ifs <;> norm_num] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  field_simp

omit [CompleteSpace A] [NormOneClass A] in
/-- Two power series in the same element commute. No convergence is needed: Mathlib's
`Commute.tsum_left` and `Commute.tsum_right` hold for every `tsum`. -/
theorem mul_comm_tsum_pow (c e : ℕ → ℂ) (a : A) :
    (∑' n : ℕ, c n • a ^ n) * (∑' n : ℕ, e n • a ^ n)
      = (∑' n : ℕ, e n • a ^ n) * (∑' n : ℕ, c n • a ^ n) :=
  (Commute.tsum_left _ fun m ↦ Commute.tsum_right _ fun n ↦
    (((Commute.refl a).pow_pow m n).smul_left _).smul_right _).eq

/-- `bernSeries` is a left inverse of `phiSeries` for `‖a‖ < 2π`. -/
theorem bernSeries_mul_phiSeries (a : A) (ha : ‖a‖ < 2 * π) :
    bernSeries a * phiSeries a = 1 := by
  rw [bernSeries, phiSeries, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_norm_bernSeries_term a ha) (summable_norm_phiSeries_term a)]
  have key : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
        ((((bernoulli k : ℚ) : ℂ) / (Nat.factorial k : ℂ)) • a ^ k) *
          ((Nat.factorial (n - k + 1) : ℂ)⁻¹ • a ^ (n - k)))
        = if n = 0 then (1 : A) else 0 := by
    intro n
    have hterm : ∀ k ∈ Finset.range (n + 1),
        ((((bernoulli k : ℚ) : ℂ) / (Nat.factorial k : ℂ)) • a ^ k) *
          ((Nat.factorial (n - k + 1) : ℂ)⁻¹ • a ^ (n - k))
          = ((((bernoulli k : ℚ) : ℂ) / (Nat.factorial k : ℂ)) *
              (Nat.factorial (n - k + 1) : ℂ)⁻¹) • a ^ n := by
      intro k hk
      rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp hk)]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, sum_bernoulli_div_factorial_complex]
    split_ifs with h <;> simp [h]
  rw [tsum_congr key, tsum_ite_eq]

/-- `bernSeries` is a right inverse of `phiSeries` for `‖a‖ < 2π`. -/
theorem phiSeries_mul_bernSeries (a : A) (ha : ‖a‖ < 2 * π) :
    phiSeries a * bernSeries a = 1 :=
  (mul_comm_tsum_pow _ _ a).trans (bernSeries_mul_phiSeries a ha)

omit [CompleteSpace A] in
/-- The dimension-free bound on the inverse. -/
theorem norm_bernSeries_le (a : A) (ha : ‖a‖ < 2 * π) :
    ‖bernSeries a‖ ≤ ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * ‖a‖ ^ n / (Nat.factorial n) := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_bernSeries_term a ha)) ?_
  refine Summable.tsum_le_tsum (fun n ↦ ?_) (summable_norm_bernSeries_term a ha)
    (summable_bernoulli_majorant (norm_nonneg a) ha)
  rw [norm_smul, norm_div, Complex.norm_ratCast, Complex.norm_natCast, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le a n) (abs_nonneg _)

/-- `phiSeries z · z = exp z - 1` over `ℂ`. -/
theorem phiSeries_complex_mul_self (z : ℂ) : phiSeries z * z = Complex.exp z - 1 := by
  have hexp : HasSum (fun n : ℕ ↦ z ^ n / (Nat.factorial n : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ ↦ z ^ n / (Nat.factorial n : ℂ)) 1).mpr hexp
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h2
  rw [phiSeries, ← tsum_mul_right,
    tsum_congr (fun n : ℕ ↦ show ((Nat.factorial (n + 1) : ℂ)⁻¹) • z ^ n * z
      = z ^ (n + 1) / (Nat.factorial (n + 1) : ℂ) by
        simp only [smul_eq_mul, pow_succ]; ring)]
  exact h2.tsum_eq

/-- The closed form `w = (x/2) cot(x/2) - i x/2` satisfies `w · (e^{ix} - 1) = i x`. -/
theorem cot_closed_form_mul {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    (((x / 2 * Real.cot (x / 2) : ℝ) : ℂ) - ((x / 2 : ℝ) : ℂ) * Complex.I)
      * (Complex.exp ((x : ℂ) * Complex.I) - 1) = (x : ℂ) * Complex.I := by
  have hs : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hpy : Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]; ring_nf
  have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    rw [show x = 2 * (x / 2) by ring, Real.sin_two_mul]; ring_nf
  rw [Complex.exp_mul_I, Real.cot_eq_cos_div_sin,
    show Complex.cos (x : ℂ) = ((Real.cos x : ℝ) : ℂ) by rw [Complex.ofReal_cos],
    show Complex.sin (x : ℂ) = ((Real.sin x : ℝ) : ℂ) by rw [Complex.ofReal_sin], hcos, hsin]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  set S : ℂ := ((Real.sin (x / 2) : ℝ) : ℂ) with hSdef
  set C : ℂ := ((Real.cos (x / 2) : ℝ) : ℂ) with hCdef
  have hS : S ≠ 0 := by rw [hSdef]; exact_mod_cast hs
  have hpyC : S ^ 2 + C ^ 2 = 1 := by
    rw [hSdef, hCdef]; exact_mod_cast congrArg (fun r : ℝ ↦ (r : ℂ)) hpy
  field_simp
  linear_combination (2 * (x : ℂ) * C) * hpyC + (-(2 * (x : ℂ) * C * S ^ 2)) * Complex.I_sq

/-- Evaluation of `bernSeries` on the imaginary axis. -/
theorem bernSeries_mul_I {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    bernSeries ((x : ℂ) * Complex.I)
      = ((x / 2 * Real.cot (x / 2) : ℝ) : ℂ) - ((x / 2 : ℝ) : ℂ) * Complex.I := by
  have hnorm : ‖((x : ℂ) * Complex.I)‖ = x := by simp [abs_of_pos hx0]
  have h1 : bernSeries ((x : ℂ) * Complex.I) * phiSeries ((x : ℂ) * Complex.I) = 1 :=
    bernSeries_mul_phiSeries _ (by rw [hnorm]; exact hx)
  have h2 := phiSeries_complex_mul_self ((x : ℂ) * Complex.I)
  have h3 : bernSeries ((x : ℂ) * Complex.I) * (Complex.exp ((x : ℂ) * Complex.I) - 1)
      = (x : ℂ) * Complex.I := by rw [← h2, ← mul_assoc, h1, one_mul]
  have h4 := cot_closed_form_mul hx0 hx
  exact mul_right_cancel₀ (fun h ↦ by rw [h, mul_zero] at h4; simp [hx0.ne'] at h4)
    (h3.trans h4.symm)

/-- Termwise comparison between the majorant and the real part of the imaginary-axis series. -/
theorem abs_bernoulli_term_eq (x : ℝ) (n : ℕ) :
    |((bernoulli n : ℚ) : ℝ)| * x ^ n / (Nat.factorial n)
      = -(((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n).re)
        + (if n = 0 then (2 : ℝ) else 0) + (if n = 1 then x / 2 else 0) := by
  have hterm : (((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n
      = ((((bernoulli n : ℚ) : ℝ) * x ^ n / (Nat.factorial n) : ℝ) : ℂ) * Complex.I ^ n := by
    push_cast
    rw [smul_eq_mul, mul_pow]
    ring
  rw [hterm]
  set r : ℝ := ((bernoulli n : ℚ) : ℝ) * x ^ n / (Nat.factorial n) with hr
  have hre : (((r : ℝ) : ℂ) * Complex.I ^ n).re = r * (Complex.I ^ n).re := by
    simp [Complex.mul_re]
  rw [hre]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hI : (Complex.I ^ (2 * k)).re = (-1 : ℝ) ^ k := by
      rw [show Complex.I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) by
        rw [pow_mul, Complex.I_sq]; push_cast; ring, Complex.ofReal_re]
    rw [hI]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · norm_num [hr]
    · rw [if_neg (by omega), if_neg (by omega), abs_bernoulli_two_mul (by omega), hr,
        show ((-1 : ℝ)) ^ (k + 1) = -((-1 : ℝ) ^ k) by rw [pow_succ]; ring]
      ring
  · have hI : (Complex.I ^ (2 * k + 1)).re = 0 := by
      rw [show Complex.I ^ (2 * k + 1) = (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I by
        rw [pow_succ, pow_mul, Complex.I_sq]; push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hI]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · norm_num [hr]; ring
    · rw [if_neg (by omega), if_neg (by omega),
        bernoulli_eq_zero_of_odd ⟨k, by ring⟩ (by omega)]
      simp

/-- Closed form of the majorant: `∑ |Bₙ| xⁿ/n! = x/2 + 2 - (x/2) cot(x/2)` for `0 < x < 2π`. -/
theorem tsum_abs_bernoulli_eq {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * x ^ n / (Nat.factorial n)
      = x / 2 + 2 - (x / 2) * Real.cot (x / 2) := by
  have hnorm : ‖((x : ℂ) * Complex.I)‖ = x := by simp [abs_of_pos hx0]
  have hsumc : Summable (fun n : ℕ ↦
      (((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n) :=
    (summable_norm_bernSeries_term ((x : ℂ) * Complex.I) (by rw [hnorm]; exact hx)).of_norm
  have hsumre : Summable (fun n : ℕ ↦
      ((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n).re) :=
    hsumc.map Complex.reAddGroupHom Complex.continuous_re
  have hretsum := Complex.re_tsum hsumc
  have hval : (∑' n : ℕ,
      (((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n).re
      = x / 2 * Real.cot (x / 2) := by
    rw [show (∑' n : ℕ,
        (((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • ((x : ℂ) * Complex.I) ^ n)
        = bernSeries ((x : ℂ) * Complex.I) from rfl, bernSeries_mul_I hx0 hx]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hsumA : Summable (fun n : ℕ ↦ if n = 0 then (2 : ℝ) else 0) :=
    (hasSum_ite_eq 0 (2 : ℝ)).summable
  have hsumB : Summable (fun n : ℕ ↦ if n = 1 then x / 2 else 0) :=
    (hasSum_ite_eq 1 (x / 2)).summable
  rw [tsum_congr (abs_bernoulli_term_eq x), Summable.tsum_add (hsumre.neg.add hsumA) hsumB,
    Summable.tsum_add hsumre.neg hsumA, tsum_neg, ← hretsum, hval]
  simp only [tsum_ite_eq]
  ring

end UnitaryProducts.Corrector
