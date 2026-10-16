/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.InverseOperator

/-!
# The bound $\|\Phi^{-1}(i\,\mathrm{ad}_h)\| \le (w/2)/\sin(w/2)$

## Declarations

- `bernSeries_two_smul_eq_mul_exp_neg`
- `bernSeries_two_smul_mul_exp_add_one`
- `commute_exp_add_one_phiSeries`
- `cot_half_sub_cot`
- `norm_two_smul_bernSeries_sub_le`
- `sum_inv_factorial_succ_mul`
- `summable_exp_terms_smul`
- `tsum_exp_terms_smul`
- `tsum_exp_terms_smul'`
- `tsum_sin_majorant_eq`
- `two_smul_bernSeries_sub_eq`
- `two_smul_phiSeries_two_smul`
- `norm_bernSeries_I_adL_le_sinBound`
- `norm_tsum_smul_adL_pow_apply_le`
- `sinBound`
- `sinBound_nonneg`
-/

@[expose] public section

open scoped BigOperators
open Real

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] [NormOneClass A] in
/-- The exponential series of `c • a`, as a series in `a`. -/
theorem tsum_exp_terms_smul (c : ℂ) (a : A) :
    (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • (c • a) ^ n)
      = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * c ^ n) • a ^ n :=
  tsum_congr fun n ↦ by rw [smul_pow, smul_smul]

omit [CompleteSpace A] [NormOneClass A] in
theorem tsum_exp_terms_smul' (c e : ℂ) (a : A) :
    (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * e ^ n) • (c • a) ^ n)
      = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (e * c) ^ n) • a ^ n :=
  tsum_congr fun n ↦ by rw [smul_pow, smul_smul, mul_pow, mul_assoc]

omit [NormOneClass A] in
theorem summable_exp_terms_smul (c : ℂ) (a : A) :
    Summable (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ * c ^ n) • a ^ n) := by
  refine ((NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (c • a)).of_norm).congr fun n ↦ ?_
  rw [smul_pow, smul_smul]

/-- `∑_{k ≤ n} 1/((k+1)! (n-k)!) = (2^{n+1} - 1)/(n+1)!`. -/
theorem sum_inv_factorial_succ_mul (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial (k + 1) : ℂ)⁻¹ * (Nat.factorial (n - k) : ℂ)⁻¹
      = ((2 : ℂ) ^ (n + 1) - 1) * (Nat.factorial (n + 1) : ℂ)⁻¹ := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (Nat.factorial (k + 1) : ℂ)⁻¹ * (Nat.factorial (n - k) : ℂ)⁻¹
        = ((n + 1).choose (k + 1) : ℂ) * (Nat.factorial (n + 1) : ℂ)⁻¹ := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.cast_choose ℂ (show k + 1 ≤ n + 1 by omega), show n + 1 - (k + 1) = n - k by omega,
      div_mul_eq_mul_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
      one_div, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  have h := Nat.sum_range_choose (n + 1)
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at h
  linear_combination (by exact_mod_cast h :
    ∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℂ) + 1 = 2 ^ (n + 1))

/-- **The averaging series at twice the argument**: `2 Φ(2b) = Φ(b) e^b + Φ(b)`. -/
theorem two_smul_phiSeries_two_smul (b : A) :
    (2 : ℂ) • phiSeries ((2 : ℂ) • b) = phiSeries b * NormedSpace.exp b + phiSeries b := by
  have hP := summable_norm_phiSeries_term b
  have hE := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) b
  have hprod : phiSeries b * NormedSpace.exp b
      = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (((Nat.factorial (k + 1) : ℂ)⁻¹) • b ^ k) * (((Nat.factorial (n - k) : ℂ)⁻¹) • b ^ (n -
            k)) := by
    rw [phiSeries, ← (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) b).tsum_eq]
    exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hP hE
  have hsum1 : Summable (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1),
      (((Nat.factorial (k + 1) : ℂ)⁻¹) • b ^ k) * (((Nat.factorial (n - k) : ℂ)⁻¹) • b ^ (n - k)))
        :=
    (summable_norm_sum_mul_range_of_summable_norm hP hE).of_norm
  have hsum2 : Summable (fun n : ℕ ↦ ((Nat.factorial (n + 1) : ℂ)⁻¹) • b ^ n) := hP.of_norm
  have hL : (2 : ℂ) • phiSeries ((2 : ℂ) • b)
      = ∑' n : ℕ, ((2 : ℂ) * ((Nat.factorial (n + 1) : ℂ)⁻¹ * (2 : ℂ) ^ n)) • b ^ n := by
    rw [phiSeries, ← (summable_norm_phiSeries_term ((2 : ℂ) • b)).of_norm.tsum_const_smul (2 : ℂ)]
    refine tsum_congr fun n ↦ ?_
    rw [smul_pow, smul_smul, smul_smul]; congr 1; ring
  have hR : phiSeries b * NormedSpace.exp b + phiSeries b
      = ∑' n : ℕ, ((∑ k ∈ Finset.range (n + 1),
          (Nat.factorial (k + 1) : ℂ)⁻¹ * (Nat.factorial (n - k) : ℂ)⁻¹)
          + (Nat.factorial (n + 1) : ℂ)⁻¹) • b ^ n := by
    rw [hprod, phiSeries, ← Summable.tsum_add hsum1 hsum2]
    refine tsum_congr fun n ↦ ?_
    rw [add_smul, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [smul_mul_smul_comm, ← pow_add, Nat.add_sub_cancel' hk]
  rw [hL, hR]
  refine tsum_congr fun n ↦ ?_
  congr 1
  rw [sum_inv_factorial_succ_mul]
  ring

omit [NormOneClass A] in
/-- `e^b + 1` commutes with `Φ(b)`: both are power series in `b`. -/
theorem commute_exp_add_one_phiSeries (b : A) :
    Commute (NormedSpace.exp b + 1) (phiSeries b) := by
  refine Commute.add_left ?_ (Commute.one_left _)
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) b).tsum_eq]
  exact mul_comm_tsum_pow _ _ b

/-- **The Bernoulli series at twice the argument**: `Φ⁻¹(2b) (e^b + 1) = 2 Φ⁻¹(b)` for `‖b‖ < π`. -/
theorem bernSeries_two_smul_mul_exp_add_one {b : A} (hb : ‖b‖ < π) :
    bernSeries ((2 : ℂ) • b) * (NormedSpace.exp b + 1) = (2 : ℂ) • bernSeries b := by
  have h2b : ‖(2 : ℂ) • b‖ < 2 * π := by rw [norm_smul, Complex.norm_ofNat]; linarith
  have hb' : ‖b‖ < 2 * π := by linarith [Real.pi_pos]
  have hPB := phiSeries_mul_bernSeries b hb'
  have hBP := bernSeries_mul_phiSeries ((2 : ℂ) • b) h2b
  have hkey : phiSeries b * (NormedSpace.exp b + 1) = (2 : ℂ) • phiSeries ((2 : ℂ) • b) := by
    rw [two_smul_phiSeries_two_smul, mul_add, mul_one]
  calc bernSeries ((2 : ℂ) • b) * (NormedSpace.exp b + 1)
      = bernSeries ((2 : ℂ) • b) * ((NormedSpace.exp b + 1) * phiSeries b) * bernSeries b := by
        rw [mul_assoc, mul_assoc, hPB, mul_one]
    _ = (2 : ℂ) • ((bernSeries ((2 : ℂ) • b) * phiSeries ((2 : ℂ) • b)) * bernSeries b) := by
        rw [(commute_exp_add_one_phiSeries b).eq, hkey, mul_smul_comm, smul_mul_assoc]
    _ = (2 : ℂ) • bernSeries b := by rw [hBP, one_mul]

/-- The coefficients of `2 Φ⁻¹(b) - Φ⁻¹(2b)` are `(2 - 2ⁿ) Bₙ/n!`. -/
theorem two_smul_bernSeries_sub_eq {b : A} (hb : ‖b‖ < π) :
    (2 : ℂ) • bernSeries b - bernSeries ((2 : ℂ) • b)
      = ∑' n : ℕ, ((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) * ((2 : ℂ) - (2 : ℂ) ^ n))
          • b ^ n := by
  have hb' : ‖b‖ < 2 * π := by linarith [Real.pi_pos]
  have h2b : ‖(2 : ℂ) • b‖ < 2 * π := by rw [norm_smul, Complex.norm_ofNat]; linarith
  have hs1 := (summable_norm_bernSeries_term b hb').of_norm
  have hs2 := (summable_norm_bernSeries_term ((2 : ℂ) • b) h2b).of_norm
  rw [bernSeries, bernSeries, ← hs1.tsum_const_smul (2 : ℂ),
    ← Summable.tsum_sub (hs1.const_smul (2 : ℂ)) hs2]
  refine tsum_congr fun n ↦ ?_
  rw [smul_pow, smul_smul, smul_smul, ← sub_smul]; congr 1; ring

omit [CompleteSpace A] in
/-- The majorant of the even series: `‖2 Φ⁻¹(b) - Φ⁻¹(2b)‖ ≤ ∑ |Bₙ| |2 - 2ⁿ| (w/2)ⁿ/n!` when
`‖b‖ ≤ w/2 < π`. -/
theorem norm_two_smul_bernSeries_sub_le [CompleteSpace A] {b : A} {w : ℝ} (hbw : ‖b‖ ≤ w / 2)
    (hw : w < 2 * π) :
    ‖(2 : ℂ) • bernSeries b - bernSeries ((2 : ℂ) • b)‖
      ≤ ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n
          / (Nat.factorial n) := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := by linarith [norm_nonneg b]
  have hb : ‖b‖ < π := by linarith
  rw [two_smul_bernSeries_sub_eq hb]
  have hle : ∀ n : ℕ, ‖((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ))
      * ((2 : ℂ) - (2 : ℂ) ^ n)) • b ^ n‖
      ≤ |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n / (Nat.factorial n) := by
    intro n
    have h3 : ‖(2 : ℂ) - (2 : ℂ) ^ n‖ = |2 - (2 : ℝ) ^ n| := by
      rw [show (2 : ℂ) - (2 : ℂ) ^ n = ((2 - (2 : ℝ) ^ n : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [norm_smul, norm_mul, norm_div, Complex.norm_ratCast, Complex.norm_natCast, h3]
    have hbn : ‖b ^ n‖ ≤ (w / 2) ^ n :=
      (norm_pow_le b n).trans (pow_le_pow_left₀ (norm_nonneg b) hbw n)
    calc |((bernoulli n : ℚ) : ℝ)| / (Nat.factorial n) * |2 - (2 : ℝ) ^ n| * ‖b ^ n‖
        ≤ |((bernoulli n : ℚ) : ℝ)| / (Nat.factorial n) * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n := by
          gcongr
      _ = _ := by ring
  have hmaj : ∀ n : ℕ, |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n
      / (Nat.factorial n) ≤ |((bernoulli n : ℚ) : ℝ)| * w ^ n / (Nat.factorial n) := by
    intro n
    have h2n : |2 - (2 : ℝ) ^ n| ≤ (2 : ℝ) ^ n := abs_sub_le_iff.mpr
      ⟨by linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)], by linarith⟩
    have hwn : (w / 2) ^ n * (2 : ℝ) ^ n = w ^ n := by
      rw [← mul_pow, div_mul_cancel₀ w two_ne_zero]
    calc |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n / (Nat.factorial n)
        ≤ |((bernoulli n : ℚ) : ℝ)| * (2 : ℝ) ^ n * (w / 2) ^ n / (Nat.factorial n) := by
          gcongr
      _ = |((bernoulli n : ℚ) : ℝ)| * w ^ n / (Nat.factorial n) := by
          rw [mul_assoc, mul_comm ((2 : ℝ) ^ n), hwn]
  have hsummaj : Summable (fun n : ℕ ↦ |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n|
      * (w / 2) ^ n / (Nat.factorial n)) :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity) hmaj (summable_bernoulli_majorant hw0 hw)
  have hsumnorm : Summable (fun n : ℕ ↦ ‖((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ))
      * ((2 : ℂ) - (2 : ℂ) ^ n)) • b ^ n‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hsummaj
  exact (norm_tsum_le_tsum_norm hsumnorm).trans (Summable.tsum_le_tsum hle hsumnorm hsummaj)

/-- `cot(y/2) - cot y = 1/sin y` for `0 < y < π`. -/
theorem cot_half_sub_cot {y : ℝ} (hy0 : 0 < y) (hy : y < π) :
    Real.cot (y / 2) - Real.cot y = 1 / Real.sin y := by
  have hs : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy0 hy).ne'
  have hs2 : Real.sin (y / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsub := Real.sin_sub y (y / 2)
  rw [show y - y / 2 = y / 2 by ring] at hsub
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp
  linear_combination (-1 : ℝ) * hsub

/-- **The majorant of the even series in closed form**: for `0 < w < 2π`,
`∑ |Bₙ| |2 - 2ⁿ| (w/2)ⁿ/n! = bernBound w - 2 bernBound (w/2) + 2 = (w/2)/sin(w/2)`. -/
theorem tsum_sin_majorant_eq {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) :
    ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n / (Nat.factorial n)
      = (w / 2) / Real.sin (w / 2) := by
  have hg := summable_bernoulli_majorant hw0.le hw
  have hh := summable_bernoulli_majorant (show 0 ≤ w / 2 by linarith) (by linarith)
  have hind : Summable (fun n : ℕ ↦ if n = 0 then (2 : ℝ) else 0) :=
    (hasSum_ite_eq 0 (2 : ℝ)).summable
  have hterm : ∀ n : ℕ,
      |((bernoulli n : ℚ) : ℝ)| * |2 - (2 : ℝ) ^ n| * (w / 2) ^ n / (Nat.factorial n)
        = (|((bernoulli n : ℚ) : ℝ)| * w ^ n / (Nat.factorial n)
          - 2 * (|((bernoulli n : ℚ) : ℝ)| * (w / 2) ^ n / (Nat.factorial n)))
          + (if n = 0 then (2 : ℝ) else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h2 : (2 : ℝ) ≤ 2 ^ n := le_self_pow₀ (by norm_num) hn.ne'
      rw [if_neg hn.ne', abs_of_nonpos (show (2 : ℝ) - 2 ^ n ≤ 0 by linarith), add_zero]
      have hwn : (w / 2) ^ n * (2 : ℝ) ^ n = w ^ n := by
        rw [← mul_pow, div_mul_cancel₀ w two_ne_zero]
      rw [← hwn]
      ring
  rw [tsum_congr hterm, Summable.tsum_add (hg.sub (hh.mul_left 2)) hind,
    Summable.tsum_sub hg (hh.mul_left 2), tsum_mul_left, tsum_ite_eq,
    tsum_abs_bernoulli_eq hw0 hw, tsum_abs_bernoulli_eq (show 0 < w / 2 by linarith) (by linarith)]
  have hcot := cot_half_sub_cot (show 0 < w / 2 by linarith) (by linarith)
  rw [show w / 2 / 2 = w / 4 by ring] at hcot
  rw [show w / 2 / 2 = w / 4 by ring]
  rw [div_eq_mul_one_div (w / 2) (Real.sin (w / 2)), ← hcot]
  ring

/-- `Φ⁻¹(2b) = (2Φ⁻¹(b) - Φ⁻¹(2b)) e^{-b}` for `‖b‖ < π`, with `e^{-b}` written as its series. -/
theorem bernSeries_two_smul_eq_mul_exp_neg {b : A} (hb : ‖b‖ < π) :
    bernSeries ((2 : ℂ) • b)
      = ((2 : ℂ) • bernSeries b - bernSeries ((2 : ℂ) • b))
          * ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (-1 : ℂ) ^ n) • b ^ n := by
  rw [← tsum_exp_terms_smul, (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((-1 : ℂ) • b)).tsum_eq,
    neg_one_smul]
  have h2 : bernSeries ((2 : ℂ) • b) * NormedSpace.exp b
      = (2 : ℂ) • bernSeries b - bernSeries ((2 : ℂ) • b) := by
    rw [← bernSeries_two_smul_mul_exp_add_one hb, mul_add, mul_one, add_sub_cancel_right]
  rw [← h2, mul_assoc, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (Commute.refl b).neg_right ((NormedSpace.expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _), add_neg_cancel,
    NormedSpace.exp_zero, mul_one]

end UnitaryProducts.Corrector

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open UnitaryProducts.Corrector Complex NormedSpace

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The sharper majorant of the inverse averaging operator, `(w/2)/sin(w/2)`: the constant $S$ of
Lemma A.2 for $0 < w < 2\pi$. At $w = 0$ it is $0/0 = 0$ in Lean, not the paper's $g(0)=1$;
`walkLogSlope` is the version continuous at $0$. -/
noncomputable def sinBound (w : ℝ) : ℝ := (w / 2) / Real.sin (w / 2)

theorem sinBound_nonneg {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) : 0 ≤ sinBound w :=
  div_nonneg (by linarith) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le

/-- **The series `∑ τⁿ/n! (i·ad_H)ⁿ` is the conjugation `E ↦ e^{iτH} E e^{-iτH}`**
(`conj_eq_tsum`), so it does not increase norms. -/
theorem norm_tsum_smul_adL_pow_apply_le {H : 𝕄} (hH : H.IsHermitian) (E : 𝕄)
    (τ : ℝ) :
    ‖(∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ n) • (I • adL H) ^ n) E‖ ≤ ‖E‖ := by
  rw [tsum_apply_of_summable (summable_exp_terms_smul (A := 𝕄 →L[ℂ] 𝕄) (τ : ℂ) (I • adL H))]
  have hconj : (∑' n : ℕ, (((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ n) • (I • adL H) ^ n) E)
      = evol H (-τ) * E * evol H τ := by
    rw [conj_eq_tsum H E τ]
    exact tsum_congr fun n ↦ by rw [ContinuousLinearMap.smul_apply]
  rw [hconj, CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hH τ),
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hH (-τ))]

/-- **The sharper dimension-free bound on `Φ⁻¹`.**  For Hermitian `H` with `‖i·ad_H‖ ≤ w`,
`0 < w < 2π`: `‖Φ⁻¹‖ ≤ (w/2)/sin(w/2)`.  Indeed `Φ⁻¹ = (2Φ⁻¹(a/2) - Φ⁻¹(a)) e^{-a/2}` with
`a = i·ad_H`, where `e^{-a/2}` is the conjugation by `e^{-iH/2}`, an isometry, and the even series
is dominated by `(w/2)/sin(w/2)`. -/
theorem norm_bernSeries_I_adL_le_sinBound [NeZero d] {H : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw0 : 0 < w) (hw : w < 2 * π) (ha : ‖I • adL H‖ ≤ w) :
    ‖bernSeries (I • adL H)‖ ≤ sinBound w := by
  obtain ⟨b, hb⟩ : ∃ b : 𝕄 →L[ℂ] 𝕄, b = ((1 / 2 : ℝ) : ℂ) • (I • adL H) := ⟨_, rfl⟩
  have hab : I • adL H = (2 : ℂ) • b := by
    rw [hb, smul_smul, show (2 : ℂ) * ((1 / 2 : ℝ) : ℂ) = 1 by push_cast; norm_num, one_smul]
  have hbn : ‖b‖ ≤ w / 2 := by
    rw [hb]
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    norm_num; linarith
  have hsplit := bernSeries_two_smul_eq_mul_exp_neg (A := 𝕄 →L[ℂ] 𝕄) (by linarith : ‖b‖ < π)
  rw [← hab] at hsplit
  have hconj : ∀ E : 𝕄,
      ‖(∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (-1 : ℂ) ^ n) • b ^ n) E‖ ≤ ‖E‖ := by
    intro E
    have hser : (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (-1 : ℂ) ^ n) • b ^ n)
        = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (((-(1 / 2) : ℝ)) : ℂ) ^ n) • (I • adL H) ^ n := by
      rw [hb, tsum_exp_terms_smul' (A := 𝕄 →L[ℂ] 𝕄)]
      exact tsum_congr fun n ↦ by push_cast; ring_nf
    rw [hser]
    exact norm_tsum_smul_adL_pow_apply_le hH E (-(1 / 2))
  have hdiff := norm_two_smul_bernSeries_sub_le (A := 𝕄 →L[ℂ] 𝕄) hbn hw
  rw [← hab, tsum_sin_majorant_eq hw0 hw] at hdiff
  refine ContinuousLinearMap.opNorm_le_bound _ (sinBound_nonneg hw0 hw) fun E ↦ ?_
  rw [hsplit, ContinuousLinearMap.mul_apply]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul hdiff (hconj E) (norm_nonneg _) (sinBound_nonneg hw0 hw))

end UnitaryProducts
