/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.BernoulliSeries

/-!
# The first-moment series and the correction series

## Declarations

- `abs_bernoulli'_eq_abs_bernoulli`
- `corrSeries`
- `corrSeries_eq_half_add`
- `corrSeries_eq_psiSeries_mul_bernSeries`
- `corrSeries_mul_phiSeries`
- `psiSeries`
- `sum_bernoulli'_succ_div_factorial`
- `sum_bernoulli'_succ_div_factorial_complex`
- `summable_bernoulli'_succ_majorant`
- `summable_norm_corrSeries_terms`
- `tsum_abs_bernoulli'_succ_eq`
-/

@[expose] public section

open scoped BigOperators
open Real

noncomputable section

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `psiSeries a = ∑ aⁿ/(n!(n+2))`, i.e. `∫₀¹ τ exp(τa) dτ`. It converges absolutely for every
`a` (`summable_norm_psiSeries_term`). -/
def psiSeries (a : A) : A :=
  ∑' n : ℕ, (((Nat.factorial n : ℂ) * ((n : ℂ) + 2))⁻¹) • a ^ n

/-- `corrSeries a = ∑ B⁺ₙ₊₁ aⁿ/(n+1)!`, i.e. `exp a/(exp a - 1) - 1/a`. It converges absolutely
for $\|a\| < 2\pi$ (`summable_norm_corrSeries_terms`) and is the `tsum` junk value $0$ when the
series is not summable. -/
def corrSeries (a : A) : A :=
  ∑' n : ℕ, (((bernoulli' (n + 1) : ℚ) : ℂ) / (Nat.factorial (n + 1) : ℂ)) • a ^ n

/-- `|B⁺ₙ| = |Bₙ|`: the two Bernoulli conventions differ only by a sign. -/
theorem abs_bernoulli'_eq_abs_bernoulli (n : ℕ) :
    |((bernoulli' n : ℚ) : ℝ)| = |((bernoulli n : ℚ) : ℝ)| := by
  rw [bernoulli'_eq_bernoulli n]; push_cast
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The Cauchy-product coefficient identity
`∑_{k≤n} B⁺_{k+1}/((k+1)!(n-k+1)!) = 1/(n!(n+2))`, over `ℚ`. -/
theorem sum_bernoulli'_succ_div_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (bernoulli' (k + 1) : ℚ) /
          ((Nat.factorial (k + 1) : ℚ) * (Nat.factorial (n - k + 1) : ℚ))
      = 1 / ((Nat.factorial n : ℚ) * ((n : ℚ) + 2)) := by
  have key : ∀ k ∈ Finset.range (n + 1),
      (bernoulli' (k + 1) : ℚ) /
          ((Nat.factorial (k + 1) : ℚ) * (Nat.factorial (n - k + 1) : ℚ))
        = ((Nat.choose (n + 2) (k + 1) : ℚ) * bernoulli' (k + 1)) /
            (Nat.factorial (n + 2) : ℚ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hle : k + 1 ≤ n + 2 := by omega
    have hfac := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : n + 2 - (k + 1) = n - k + 1 := by omega
    rw [hsub] at hfac
    have hq : ((Nat.choose (n + 2) (k + 1) : ℚ)) * (Nat.factorial (k + 1) : ℚ) *
        (Nat.factorial (n - k + 1) : ℚ) = (Nat.factorial (n + 2) : ℚ) := by exact_mod_cast hfac
    rw [← hq]
    have h3 : ((Nat.choose (n + 2) (k + 1) : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hle).ne'
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  have hsum : ∑ k ∈ Finset.range (n + 1),
      ((Nat.choose (n + 2) (k + 1) : ℚ) * bernoulli' (k + 1)) = (n : ℚ) + 1 := by
    have h := Finset.sum_range_succ' (fun j ↦ ((Nat.choose (n + 2) j : ℚ) * bernoulli' j)) (n + 1)
    rw [sum_bernoulli' (n + 2)] at h
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.choose_zero_right,
      Nat.cast_one, bernoulli'_zero, mul_one] at h
    linarith [h]
  rw [hsum]
  have hf : (Nat.factorial (n + 2) : ℚ) = ((n : ℚ) + 2) * ((n : ℚ) + 1) * (Nat.factorial n : ℚ) :=
    by push_cast [Nat.factorial_succ]; ring
  rw [hf]
  have h1 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  field_simp

/-- The same coefficient identity, in the form needed for the Cauchy product over `ℂ`. -/
theorem sum_bernoulli'_succ_div_factorial_complex (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((((bernoulli' (k + 1) : ℚ) : ℂ) / (Nat.factorial (k + 1) : ℂ)) *
          ((Nat.factorial (n - k + 1) : ℂ))⁻¹)
      = (((Nat.factorial n : ℂ)) * ((n : ℂ) + 2))⁻¹ := by
  have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (sum_bernoulli'_succ_div_factorial n)
  push_cast at h
  rw [← one_div, ← h]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- Summability of the majorant of the correction series. -/
theorem summable_bernoulli'_succ_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦
      |((bernoulli' (n + 1) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 1))) := by
  set y : ℝ := (x + 2 * π) / 2 with hy_def
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hy0 : 0 < y := by simp only [hy_def]; linarith
  have hxy : x ≤ y := by simp only [hy_def]; linarith
  have hy : y < 2 * π := by simp only [hy_def]; linarith
  have hs : Summable (fun n : ℕ ↦ |((bernoulli n : ℚ) : ℝ)| * y ^ n / (Nat.factorial n)) :=
    summable_bernoulli_majorant hy0.le hy
  have hs1 : Summable
      (fun n : ℕ ↦ |((bernoulli (n + 1) : ℚ) : ℝ)| * y ^ (n + 1) / (Nat.factorial (n + 1))) :=
    (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) (hs1.mul_right y⁻¹)
  have hrw : |((bernoulli (n + 1) : ℚ) : ℝ)| * y ^ (n + 1) / (Nat.factorial (n + 1)) * y⁻¹
      = |((bernoulli (n + 1) : ℚ) : ℝ)| * y ^ n / (Nat.factorial (n + 1)) := by
    field_simp; ring
  rw [hrw, abs_bernoulli'_eq_abs_bernoulli]
  gcongr

omit [CompleteSpace A] in
/-- Norms of the terms of `corrSeries` are summable. -/
theorem summable_norm_corrSeries_terms (a : A) (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      ‖(((bernoulli' (n + 1) : ℚ) : ℂ) / (Nat.factorial (n + 1) : ℂ)) • a ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_bernoulli'_succ_majorant (norm_nonneg a) ha)
  rw [norm_smul, norm_div, Complex.norm_ratCast, Complex.norm_natCast, div_mul_eq_mul_div]
  gcongr
  exact norm_pow_le a n

/-- The correction series without the second Bernoulli numbers: its constant term is `1/2`, and
from the first power on its coefficients are the ordinary Bernoulli numbers. -/
theorem corrSeries_eq_half_add (a : A) (ha : ‖a‖ < 2 * π) :
    corrSeries a = (2⁻¹ : ℂ) • (1 : A)
      + ∑' n : ℕ, (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • a ^ (n + 1) := by
  have hsum := (summable_norm_corrSeries_terms a ha).of_norm
  rw [corrSeries, hsum.tsum_eq_zero_add]
  congr 1
  · norm_num [bernoulli'_one]
  · refine tsum_congr fun n ↦ ?_
    rw [bernoulli_eq_bernoulli'_of_ne_one (by omega : n + 2 ≠ 1)]

/-- The correction map composed with the averaging operator is `Ψ`. -/
theorem corrSeries_mul_phiSeries (a : A) (ha : ‖a‖ < 2 * π) :
    corrSeries a * phiSeries a = psiSeries a := by
  rw [corrSeries, phiSeries, psiSeries,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (summable_norm_corrSeries_terms a ha) (summable_norm_phiSeries_term a)]
  refine tsum_congr fun n ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l ↦ ((((bernoulli' (k + 1) : ℚ) : ℂ) / (Nat.factorial (k + 1) : ℂ)) • a ^ k) *
      (((Nat.factorial (l + 1) : ℂ)⁻¹) • a ^ l)) n]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((((bernoulli' (k + 1) : ℚ) : ℂ) / (Nat.factorial (k + 1) : ℂ)) • a ^ k) *
        (((Nat.factorial (n - k + 1) : ℂ)⁻¹) • a ^ (n - k))
        = (((((bernoulli' (k + 1) : ℚ) : ℂ) / (Nat.factorial (k + 1) : ℂ)) *
            ((Nat.factorial (n - k + 1) : ℂ))⁻¹)) • a ^ n := by
    intro k hk
    rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_of_le (Finset.mem_range_succ_iff.mp hk)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul,
    sum_bernoulli'_succ_div_factorial_complex n]

/-- Hence the correction map is `Ψ Φ⁻¹`. -/
theorem corrSeries_eq_psiSeries_mul_bernSeries (a : A) (ha : ‖a‖ < 2 * π) :
    corrSeries a = psiSeries a * bernSeries a := by
  rw [← corrSeries_mul_phiSeries a ha, mul_assoc, phiSeries_mul_bernSeries a ha, mul_one]

/-- Closed form of that majorant: `1/2 + (1 - (x/2) cot(x/2))/x` for `0 < x < 2π`. -/
theorem tsum_abs_bernoulli'_succ_eq {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    ∑' n : ℕ, |((bernoulli' (n + 1) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 1))
      = 1 / 2 + (1 - (x / 2) * Real.cot (x / 2)) / x := by
  set f : ℕ → ℝ := fun n ↦ |((bernoulli n : ℚ) : ℝ)| * x ^ n / (Nat.factorial n) with hf
  have hsf : Summable f := summable_bernoulli_majorant hx0.le hx
  have hsplit := hsf.sum_add_tsum_nat_add 1
  have hf0 : ∑ i ∈ Finset.range 1, f i = 1 := by
    simp [hf, bernoulli_zero]
  have hshift (n : ℕ) : f (n + 1)
      = x * (|((bernoulli' (n + 1) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 1))) := by
    simp only [hf, abs_bernoulli'_eq_abs_bernoulli, pow_succ]
    field_simp
  rw [hf0, tsum_congr hshift, tsum_mul_left, tsum_abs_bernoulli_eq hx0 hx] at hsplit
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hT : x * (∑' n : ℕ, |((bernoulli' (n + 1) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 1)))
      = x / 2 + 1 - (x / 2) * Real.cot (x / 2) := by linarith
  field_simp
  linarith [hT]

end UnitaryProducts.Corrector
