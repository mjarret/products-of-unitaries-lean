/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib

/-! # Positive coefficients from the cotangent partial fractions

The cotangent poles define the coefficients. Geometric expansion gives the
convergence interval, and pairing cosecant poles gives the center coefficient signs.
-/
@[expose] public section
open Real
open scoped BigOperators
noncomputable section
namespace UnitaryProducts.Corrector

/-- The coefficient of `x^(2*k)` in `∑ m≥1, 2/((2πm)^2-x^2)`. -/
def frameEvenCoeff (k : ℕ) : ℝ :=
  ∑' m : ℕ, 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)

/-- The Taylor coefficients of the cotangent multiplier, including the zero odd coefficients. -/
def frameCoeff (n : ℕ) : ℝ :=
  if Even n then frameEvenCoeff (n / 2) else 0

/-- Each even coefficient is a convergent positive inverse-power sum. -/
theorem summable_frameEvenCoeff (k : ℕ) :
    Summable (fun m : ℕ ↦ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)) := by
  have hs := (summable_pow_div_add (2 / (2 * π) ^ (2 * k + 2) : ℝ)
    (2 * k + 2) 1 (by omega)).of_norm
  simpa only [Nat.cast_one, mul_pow, div_div] using hs

/-- The coefficient signs follow directly from the positive denominators. -/
theorem frameCoeff_nonneg (n : ℕ) : 0 ≤ frameCoeff n := by
  unfold frameCoeff frameEvenCoeff
  split_ifs
  · exact tsum_nonneg fun _ ↦ by positivity
  · exact le_rfl

/-- The even-indexed coefficients have their partial-fraction form. -/
theorem frameCoeff_even (k : ℕ) : frameCoeff (2 * k) = frameEvenCoeff k := by
  simp [frameCoeff]

/-- The odd coefficients vanish. -/
theorem frameCoeff_odd (k : ℕ) : frameCoeff (2 * k + 1) = 0 := by
  simp [frameCoeff]

/-- Each summand has the geometric expansion used in Appendix A. -/
theorem hasSum_partialFraction_geometric {x b : ℝ} (hb : 0 < b) (hx : |x| < b) :
    HasSum (fun k : ℕ ↦ 2 / b ^ (2 * k + 2) * x ^ (2 * k))
      (2 / (b ^ 2 - x ^ 2)) := by
  have hr : |x / b| < 1 := by
    rw [abs_div, abs_of_pos hb]
    exact (div_lt_one hb).mpr hx
  have hr2 : (x / b) ^ 2 < 1 := by
    simpa only [one_pow, sq_abs] using pow_lt_pow_left₀ hr (abs_nonneg (x / b)) (by decide : 2 ≠ 0)
  have hs := (hasSum_geometric_of_lt_one (sq_nonneg (x / b)) hr2).mul_left (2 / b ^ 2)
  have ht (k : ℕ) : 2 / b ^ 2 * ((x / b) ^ 2) ^ k =
      2 / b ^ (2 * k + 2) * x ^ (2 * k) := by
    rw [← pow_mul, div_pow, pow_add]
    ring
  have he : 2 / b ^ 2 * (1 - (x / b) ^ 2)⁻¹ = 2 / (b ^ 2 - x ^ 2) := by
    rw [div_pow, one_sub_div (pow_ne_zero _ hb.ne'), inv_div]
    field_simp
  exact he ▸ hs.congr_fun (fun k ↦ (ht k).symm)

/-- The inverse-power coefficient is bounded by its constant coefficient times
`(2π)^(-2k)`, since each pole has modulus at least `2π`. -/
theorem frameEvenCoeff_le (k : ℕ) :
    frameEvenCoeff k ≤ frameEvenCoeff 0 / (2 * π) ^ (2 * k) := by
  have hterms (m : ℕ) :
      2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) ≤
        (2 / (2 * π * (m + 1 : ℝ)) ^ 2) / (2 * π) ^ (2 * k) := by
    have hb : 0 < 2 * π * (m + 1 : ℝ) := by positivity
    have hbase : 2 * π ≤ 2 * π * (m + 1 : ℝ) := by
      calc 2 * π = 2 * π * 1 := by ring
           _ ≤ 2 * π * (m + 1 : ℝ) := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) m]
    calc
      _ = (2 / (2 * π * (m + 1 : ℝ)) ^ 2) /
          (2 * π * (m + 1 : ℝ)) ^ (2 * k) := by rw [pow_add, div_mul_eq_div_div, div_right_comm]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ Real.two_pi_pos.le hbase _)
  have hsum := (summable_frameEvenCoeff k).tsum_le_tsum hterms
    ((summable_frameEvenCoeff 0).div_const ((2 * π) ^ (2 * k)))
  simpa only [frameEvenCoeff, Nat.mul_zero, zero_add, tsum_div_const] using hsum

/-- The even Taylor series converges throughout the open disc of radius `2π`. -/
theorem summable_frameEvenCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun k : ℕ ↦ frameEvenCoeff k * x ^ (2 * k)) := by
  have hr : |x / (2 * π)| < 1 := by
    rw [abs_div, abs_of_pos Real.two_pi_pos]
    exact (div_lt_one Real.two_pi_pos).mpr hx
  have hr2 : (x / (2 * π)) ^ 2 < 1 := by
    simpa only [one_pow, sq_abs] using
      pow_lt_pow_left₀ hr (abs_nonneg (x / (2 * π))) (by decide : 2 ≠ 0)
  have hsum := (summable_geometric_of_lt_one (sq_nonneg (x / (2 * π))) hr2).mul_left
    (frameEvenCoeff 0)
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (tsum_nonneg fun m ↦ by positivity) (Even.pow_nonneg (even_two_mul k) x))
    (fun k ↦ ?_) hsum
  calc
    _ ≤ (frameEvenCoeff 0 / (2 * π) ^ (2 * k)) * x ^ (2 * k) :=
      mul_le_mul_of_nonneg_right (frameEvenCoeff_le k) (Even.pow_nonneg (even_two_mul k) x)
    _ = frameEvenCoeff 0 * ((x / (2 * π)) ^ 2) ^ k := by
      rw [← pow_mul, div_pow]
      ring

/-- Absolute convergence allows the pole sum and the Taylor sum to be interchanged. -/
theorem summable_partialFraction_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun p : ℕ × ℕ ↦
      2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1)) := by
  apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ ↦
    2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1))
    (fun p ↦ mul_nonneg (by positivity) ((even_two_mul p.1).pow_nonneg x))).mpr
  constructor
  · intro k
    exact (summable_frameEvenCoeff k).mul_right (x ^ (2 * k))
  apply (summable_frameEvenCoeff_power hx).congr
  intro k
  change frameEvenCoeff k * x ^ (2 * k) = _
  exact tsum_mul_right.symm

/-- Summing the geometric expansions recovers the cotangent partial fractions. -/
theorem frameEvenCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' k : ℕ, frameEvenCoeff k * x ^ (2 * k)) =
      ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  let f : ℕ → ℕ → ℝ := fun k m ↦
    2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k)
  have hrow_sum (k : ℕ) : (∑' m, f k m) = frameEvenCoeff k * x ^ (2 * k) := by
    exact tsum_mul_right
  have hprod : Summable (Function.uncurry f) := summable_partialFraction_power hx
  calc
    _ = ∑' k, ∑' m, f k m := tsum_congr fun k ↦ (hrow_sum k).symm
    _ = ∑' m, ∑' k, f k m := hprod.tsum_comm.symm
    _ = _ := tsum_congr fun m ↦ (hasSum_partialFraction_geometric (by positivity)
      (hx.trans_le (by calc
        2 * π = 2 * π * 1 := by ring
        _ ≤ 2 * π * (m + 1 : ℝ) := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) m]))).tsum_eq

/-- The coefficient sequence, with zero odd terms, converges at every `|x|<2π`. -/
theorem summable_frameCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun n : ℕ ↦ frameCoeff n * x ^ n) := by
  apply Summable.even_add_odd
  · simpa only [frameCoeff_even] using summable_frameEvenCoeff_power hx
  · simp only [frameCoeff_odd, zero_mul, summable_zero]

set_option maxHeartbeats 800000 in
-- Reindexing two infinite sums requires additional elaboration steps.
/-- The Taylor series of the cotangent partial fractions. -/
theorem frameCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' n : ℕ, frameCoeff n * x ^ n) =
      ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  have he : Summable (fun k : ℕ ↦ frameCoeff (2 * k) * x ^ (2 * k)) := by
    simpa only [frameCoeff_even] using summable_frameEvenCoeff_power hx
  have ho : Summable (fun k : ℕ ↦ frameCoeff (2 * k + 1) * x ^ (2 * k + 1)) := by
    simp only [frameCoeff_odd, zero_mul, summable_zero]
  have hsplit := tsum_even_add_odd (f := fun n : ℕ ↦ frameCoeff n * x ^ n) he ho
  simp only [frameCoeff_even, frameCoeff_odd, zero_mul, tsum_zero, add_zero] at hsplit
  exact hsplit.symm.trans (frameEvenCoeff_power_eq_partialFractions hx)

/-- The even coefficients of the negative center multiplier, directly from the
alternating cosecant partial fractions. The index `m=0` represents the first pole. -/
def centerEvenCoeff (k : ℕ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))

/-- The cosecant coefficient sum converges absolutely. -/
theorem summable_centerEvenCoeff (k : ℕ) :
    Summable (fun m : ℕ ↦ (-1 : ℝ) ^ m *
      (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))) :=
  (summable_frameEvenCoeff k).alternating

/-- Pairing consecutive poles of the cosecant gives a strictly positive difference. -/
theorem centerEvenCoeff_pair_pos (k m : ℕ) :
    0 < 2 / (2 * π * (2 * m + 1 : ℝ)) ^ (2 * k + 2) -
      2 / (2 * π * (2 * m + 2 : ℝ)) ^ (2 * k + 2) := by
  apply sub_pos.mpr
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  apply pow_lt_pow_left₀ _ (by positivity) (by omega)
  gcongr
  linarith

set_option maxHeartbeats 800000 in
-- Reindexing alternating infinite sums requires additional elaboration steps.
/-- Consecutive pairing expresses each alternating coefficient as a sum of
positive differences, exactly the sign argument in Lemma A.1. -/
theorem centerEvenCoeff_eq_paired (k : ℕ) :
    centerEvenCoeff k = ∑' m : ℕ,
      (2 / (2 * π * (2 * m + 1 : ℝ)) ^ (2 * k + 2) -
        2 / (2 * π * (2 * m + 2 : ℝ)) ^ (2 * k + 2)) := by
  let f : ℕ → ℝ := fun m ↦ (-1 : ℝ) ^ m *
    (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))
  have he := (summable_centerEvenCoeff k).comp_injective
    (show Function.Injective (fun m : ℕ ↦ 2 * m) from fun _ _ h ↦ by simp only at h; omega)
  have ho := (summable_centerEvenCoeff k).comp_injective
    (show Function.Injective (fun m : ℕ ↦ 2 * m + 1) from fun _ _ h ↦ by simp only at h; omega)
  calc
    centerEvenCoeff k = (∑' m, f (2 * m)) + ∑' m, f (2 * m + 1) :=
      (tsum_even_add_odd he ho).symm
    _ = ∑' m, (f (2 * m) + f (2 * m + 1)) := (he.tsum_add ho).symm
    _ = _ := by
      apply tsum_congr
      intro m
      simp only [f, even_two_mul, Even.neg_one_pow, pow_add, pow_one, one_mul,
        neg_one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      congr 2; ring

/-- Every even coefficient of the negative center multiplier is positive. -/
theorem centerEvenCoeff_pos (k : ℕ) : 0 < centerEvenCoeff k := by
  rw [centerEvenCoeff_eq_paired]
  have hs := ((summable_frameEvenCoeff k).comp_injective
    (show Function.Injective (fun m : ℕ ↦ 2 * m) from fun _ _ h ↦ by simp only at h; omega)).sub
      ((summable_frameEvenCoeff k).comp_injective
        (show Function.Injective (fun m : ℕ ↦ 2 * m + 1) from fun _ _ h ↦ by simp only at h; omega))
  have hs' : Summable (fun m : ℕ ↦
      2 / (2 * π * (2 * m + 1 : ℝ)) ^ (2 * k + 2) -
        2 / (2 * π * (2 * m + 2 : ℝ)) ^ (2 * k + 2)) := by
    convert hs using 1
    funext m
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    congr 2; ring
  exact (centerEvenCoeff_pair_pos k 0).trans_le
    (hs'.le_tsum 0 (fun m _ ↦ (centerEvenCoeff_pair_pos k m).le))

/-- Separating the even poles identifies the alternating coefficient. -/
theorem centerEvenCoeff_eq_frameEvenCoeff (k : ℕ) :
    centerEvenCoeff k = (1 - (1 / 2 : ℝ) ^ (2 * k + 1)) * frameEvenCoeff k := by
  let a : ℕ → ℝ := fun m ↦ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)
  have he : Summable (fun m ↦ a (2 * m)) := (summable_frameEvenCoeff k).comp_injective
    (fun _ _ h ↦ by omega)
  have ho : Summable (fun m ↦ a (2 * m + 1)) := (summable_frameEvenCoeff k).comp_injective
    (fun _ _ h ↦ by omega)
  have ht (m : ℕ) : a (2 * m + 1) = a m * (1 / 2 : ℝ) ^ (2 * k + 2) := by
    dsimp [a]
    push_cast
    rw [show 2 * π * (2 * (m : ℝ) + 1 + 1) = 2 * (2 * π * (m + 1)) by ring,
      mul_pow, one_div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hodd : (∑' m, a (2 * m + 1)) = frameEvenCoeff k * (1 / 2 : ℝ) ^ (2 * k + 2) := by
    simp_rw [ht]
    exact tsum_mul_right
  have htotal : (∑' m, a (2 * m)) + (∑' m, a (2 * m + 1)) = frameEvenCoeff k :=
    tsum_even_add_odd (f := a) he ho
  have hcenter : centerEvenCoeff k = (∑' m, a (2 * m)) - ∑' m, a (2 * m + 1) := by
    rw [centerEvenCoeff_eq_paired, ← he.tsum_sub ho]
    apply tsum_congr
    intro m
    simp only [a, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    congr 2; ring
  rw [hcenter, hodd]
  rw [hodd] at htotal
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ] at htotal ⊢
  linarith

/-- The Taylor coefficients of the negative cosecant center multiplier. -/
def centerCoeff (n : ℕ) : ℝ := (1 - (1 / 2 : ℝ) ^ (n + 1)) * frameCoeff n

/-- The even center coefficients are the alternating pole sums. -/
theorem centerCoeff_even (k : ℕ) : centerCoeff (2 * k) = centerEvenCoeff k := by
  rw [centerCoeff, frameCoeff_even, centerEvenCoeff_eq_frameEvenCoeff]

/-- The odd center coefficients vanish. -/
theorem centerCoeff_odd (k : ℕ) : centerCoeff (2 * k + 1) = 0 := by
  rw [centerCoeff, frameCoeff_odd, mul_zero]

/-- The center coefficient signs are supplied by the alternating partial fractions. -/
theorem centerCoeff_nonneg (n : ℕ) : 0 ≤ centerCoeff n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [centerCoeff_even]
    exact (centerEvenCoeff_pos k).le
  · rw [centerCoeff_odd]

/-- The center coefficients are dominated term by term by the cotangent coefficients. -/
theorem centerCoeff_le_frameCoeff (n : ℕ) : centerCoeff n ≤ frameCoeff n := by
  unfold centerCoeff
  exact mul_le_of_le_one_left (frameCoeff_nonneg n) (sub_le_self _ (by positivity))

/-- The center series has radius at least `2π`. -/
theorem summable_centerCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun n : ℕ ↦ centerCoeff n * x ^ n) := by
  apply (summable_frameCoeff_power hx).of_norm_bounded
  intro n
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (centerCoeff_nonneg _),
      abs_pow, (even_two_mul k).pow_abs]
    exact mul_le_mul_of_nonneg_right (centerCoeff_le_frameCoeff _) ((even_two_mul k).pow_nonneg x)
  · simp only [centerCoeff_odd, frameCoeff_odd, zero_mul, norm_zero, le_refl]

/-- Summing the center coefficients separates the full cotangent series and its half argument. -/
theorem centerCoeff_power_eq_difference {x : ℝ} (hx : |x| < 2 * π) :
    (∑' n : ℕ, centerCoeff n * x ^ n) =
      (∑' n : ℕ, frameCoeff n * x ^ n) - (∑' n : ℕ, frameCoeff n * (x / 2) ^ n) / 2 := by
  have hh : |x / 2| < 2 * π := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [pi_pos]
  rw [← tsum_div_const, ← (summable_frameCoeff_power hx).tsum_sub
    ((summable_frameCoeff_power hh).div_const 2)]
  apply tsum_congr
  intro n
  simp only [centerCoeff, pow_succ, div_pow]
  ring

/-- The center Taylor series is exactly the alternating cosecant partial fractions. -/
theorem centerCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' n : ℕ, centerCoeff n * x ^ n) =
      ∑' m : ℕ, (-1 : ℝ) ^ m * (2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2)) := by
  let f : ℕ → ℕ → ℝ := fun k m ↦
    (-1 : ℝ) ^ m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k))
  have hprod : Summable (Function.uncurry f) := by
    apply (summable_partialFraction_power hx).of_norm_bounded
    intro p
    change ‖(-1 : ℝ) ^ p.2 *
      (2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1))‖ ≤ _
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (show 0 ≤ 2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) from by positivity),
      (even_two_mul p.1).pow_abs, le_refl]
  have he : Summable (fun k : ℕ ↦ centerCoeff (2 * k) * x ^ (2 * k)) :=
    (summable_centerCoeff_power hx).comp_injective
      (fun _ _ h ↦ by omega)
  have ho : Summable (fun k : ℕ ↦ centerCoeff (2 * k + 1) * x ^ (2 * k + 1)) := by
    simp only [centerCoeff_odd, zero_mul, summable_zero]
  have hsplit := tsum_even_add_odd (f := fun n : ℕ ↦ centerCoeff n * x ^ n) he ho
  simp only [centerCoeff_even, centerCoeff_odd, zero_mul, tsum_zero, add_zero] at hsplit
  calc
    _ = ∑' k, centerEvenCoeff k * x ^ (2 * k) := hsplit.symm
    _ = ∑' k, ∑' m, f k m := by
      apply tsum_congr
      intro k
      rw [centerEvenCoeff, ← tsum_mul_right]
      apply tsum_congr
      intro m
      dsimp [f]
      ring
    _ = ∑' m, ∑' k, f k m := hprod.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro m
      rw [show (∑' k, f k m) = (-1 : ℝ) ^ m *
        (∑' k : ℕ, 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k)) from tsum_mul_left]
      rw [(hasSum_partialFraction_geometric (by positivity)
        (hx.trans_le (by calc
          2 * π = 2 * π * 1 := by ring
          _ ≤ 2 * π * (m + 1 : ℝ) := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) m]))).tsum_eq]

/-- The real cotangent expansion, transferred from Mathlib's complex expansion. -/
private theorem partialFractions_real_cot_series {z : ℝ} (hz : ∀ n : ℤ, z ≠ n) :
    π * Real.cot (π*z) = 1/z + ∑' n : ℕ+, (1/(z-n)+1/(z+n)) := by
  have hc : (z : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    exact hz n (by exact_mod_cast hn.symm)
  apply Complex.ofReal_injective
  convert cot_series_rep hc using 1 <;>
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_tsum,
      Real.cot_eq_cos_div_sin, Complex.cot, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_natCast]

/-- Partial fractions of the frame multiplier away from all integral resonances: for
$x \notin 2\pi\mathbb Z$, $(1 - (x/2)\cot(x/2))/x^2 = \sum_{n \ge 1} 2/(4\pi^2 n^2 - x^2)$,
the partial-fraction series of $\mathcal N$. It is Mathlib's `cot_series_rep` rescaled. -/
theorem cot_form_eq_partialFractions {x : ℝ} (hx : ∀ n : ℤ, x ≠ 2*π*n) :
    (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 = ∑' n : ℕ+, 2/(4*π^2*(n : ℝ)^2-x^2) := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hp : 2*π ≠ 0 := mul_ne_zero (by norm_num) pi_ne_zero
  let z := x/(2*π)
  have hz : ∀ n : ℤ, z ≠ n := fun n hn ↦
    hx n (by simpa only [mul_comm] using (div_eq_iff hp).mp hn)
  have hz0 : z ≠ 0 := div_ne_zero hx0 hp
  have hc := partialFractions_real_cot_series hz
  have ht (n : ℕ+) : -(1/(z-n)+1/(z+n))/(2*π*x) =
      2/(4*π^2*(n : ℝ)^2-x^2) := by
    have hm : z-(n : ℝ) ≠ 0 := sub_ne_zero.mpr (hz (n : ℕ))
    have ha : z+(n : ℝ) ≠ 0 := fun he ↦
      hz (-(n : ℤ)) (by push_cast; exact eq_neg_of_add_eq_zero_left he)
    have he : 4*π^2*(n : ℝ)^2-x^2 = -(2*π)^2*(z-n)*(z+n) := by
      dsimp [z]
      field_simp
      ; ring
    have hxe : x = 2*π*z := by dsimp [z]; field_simp
    rw [he, hxe]
    field_simp [hm, ha, hz0, pi_ne_zero]
    ; ring
  rw [← tsum_congr ht, tsum_div_const, tsum_neg,
    (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hc.symm)), show π*z=x/2 by dsimp [z]; field_simp]
  dsimp [z]; field_simp
  ; ring

/-- The cotangent formula follows from its partial fractions and the positive series. -/
theorem frameCoeff_series_eq_cot {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    (∑' n : ℕ, frameCoeff n * x ^ n) = (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 := by
  have hn (n : ℤ) : x ≠ 2 * π * n := by
    by_cases hzero : n = 0
    · simpa only [hzero, Int.cast_zero, mul_zero] using hx0
    · rintro rfl
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hzero
      rw [abs_mul, abs_of_pos Real.two_pi_pos] at hx
      exact hx.not_ge (le_mul_of_one_le_right Real.two_pi_pos.le h1)
  rw [cot_form_eq_partialFractions hn, frameCoeff_power_eq_partialFractions hx,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2))]
  apply tsum_congr
  intro m
  push_cast
  congr 2
  ring

/-- The constant coefficient is the Basel sum with its pole scaling. -/
theorem frameCoeff_zero : frameCoeff 0 = 1 / 12 := by
  have hz := hasSum_zeta_two.mul_left (2 / (2 * π) ^ 2)
  have hs : HasSum (fun m : ℕ ↦ 2 / (2 * π * (m : ℝ)) ^ 2) (1 / 12) := by
    convert hz using 1
    · funext m
      rw [mul_pow]
      ring
    · field_simp
      ring
  have ht := (hasSum_nat_add_iff (f := fun m : ℕ ↦ 2 / (2 * π * (m : ℝ)) ^ 2) 1).mpr
    (by simpa using hs)
  rw [show (0 : ℕ) = 2 * 0 by omega, frameCoeff_even]
  simpa only [frameEvenCoeff, Nat.mul_zero, zero_add, Nat.cast_add, Nat.cast_one, one_div]
    using ht.tsum_eq

end UnitaryProducts.Corrector
