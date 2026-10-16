/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.LocalSteps
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.RoundedClockQuarter

/-!
# Justifications of the paper's displayed chains

## Declarations

- `bit_fraction_lt_one`
- `chord_arctan_antiderivative`
- `chord_change_variable`
- `chord_cube_antiderivative`
- `integral_quadratic_clock`
- `quadratic_endpoints`
- `rounded_clock_mean_quarter`
- `sum_sample_squares`
- `unitary_difference_norm`
-/

@[expose] public section

open Real Set Filter MeasureTheory
open UnitaryProducts.Corrector UnitaryProducts.Paper
open UnitaryProducts.Paper.UnitStepsProse
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.Prose

/-- Section 1, rounded-clock Duhamel paragraph: the mean of `|t-q(t)|` on an
integer time interval is exactly `1/4`. -/
theorem rounded_clock_mean_quarter {T : ℕ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) / T = 1 / 4 := by
  have hp := clock_error_periodic.intervalIntegral_add_zsmul_eq (T : ℤ) 0
    clock_error_integrable
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one,
    integral_clock_error_one] at hp
  have he : (∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) = (T : ℝ) * (1 / 4) := by
    simpa only [clock, abs_sub_comm] using hp
  rw [he]; field_simp

/-- Section 4's Duhamel computation: every integer cell has area one quarter.
Periodicity gives the stronger identity for every real left endpoint. -/
theorem rounded_clock_cell_quarter (k : ℝ) :
    (∫ t in k..k + 1, |t - (⌊t + 1 / 2⌋ : ℝ)|) = 1 / 4 := by
  have hperiod := clock_error_periodic.intervalIntegral_add_eq k 0
  rw [zero_add, integral_clock_error_one] at hperiod
  simpa only [clock, abs_sub_comm] using hperiod

/-- Section 3, bit-truncation proof: the discarded fractional part is less than one. -/
theorem bit_fraction_lt_one (k : ℕ) (x : ℝ) :
    (2 : ℝ) ^ k * |x| - (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ) < 1 := by
  linarith [Int.lt_floor_add_one ((2 : ℝ) ^ k * |x|)]

/-- Section 4, Theorem 4.2 proof, first equality in the unit-split chain:
left multiplication by `U†` turns the difference into `U†V-1` without changing its norm. -/
theorem unitary_difference_norm {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    (U : unitary A) (V : A) :
    ‖V - (U : A)‖ = ‖star (U : A) * V - 1‖ := by
  have he : star (U : A) * (V - U) = star (U : A) * V - 1 := by
    rw [mul_sub, (Unitary.mem_iff.mp U.property).1]
  rw [← he, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem U.property)]

/-- Section 4, quadratic example: the raw sum of sample squares used in the exponent. -/
theorem sum_sample_squares (T : ℕ) :
    (∑ j ∈ Finset.range T, (j : ℝ) ^ 2) =
      ((T : ℝ) - 1) * T * (2 * T - 1) / 6 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

/-- Section 4, quadratic example: the integrated scalar Hamiltonian is `T/3`. -/
theorem integral_quadratic_clock {T : ℝ} :
    (∫ t in (0 : ℝ)..T, (t / T) ^ 2) = T / 3 := by
  simp_rw [div_pow]; rw [intervalIntegral.integral_div, integral_pow]
  norm_num
  by_cases hT : T = 0
  · simp [hT]
  · field_simp

/-- Section 4, quadratic example: the two endpoint Hamiltonians are zero and `Z`. -/
theorem quadratic_endpoints :
    sharpFamily 0 = 0 ∧ sharpFamily 1 = Matrix.diagonal ![(1 : ℂ), -1] := by
  simp [sharpFamily]


/-- Section 4, Lemma A.2 (`lem:walk-log`) proof: `v=2u-1` contributes the Jacobian factor `1/2`
and changes the integration interval from `[0,1]` to `[-1,1]`. -/
theorem chord_change_variable (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v in (-1 : ℝ)..1, f v := by
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    f (by norm_num : (2 : ℝ) ≠ 0) (-1)
  simpa only [mul_zero, zero_add, mul_one, show (2 : ℝ) + -1 = 1 by norm_num,
    sub_eq_add_neg, smul_eq_mul, one_div] using h

/-- Auxiliary antiderivative for the first standard integral in Lemma A.2,
in the variable `v=2u-1`. This formula assumes positive width; the integral theorem
`walk_slope_quadrature_with_zero` also covers zero width. -/
theorem chord_arctan_antiderivative {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ Real.arctan (v * Real.tan (w / 4)) /
        (Real.sin (w / 4) * Real.cos (w / 4)))
      (1 / (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2)) v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hs : 0 < Real.sin (w / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have h := ((Real.hasDerivAt_arctan (v * Real.tan (w / 4))).comp v
    ((hasDerivAt_id v).mul_const (Real.tan (w / 4)))).div_const
      (Real.sin (w / 4) * Real.cos (w / 4))
  convert h using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- Auxiliary antiderivative for the second standard integral in Lemma A.2: `v/(cos²(w/4) r)`
has derivative `r⁻³`, with `r²=cos²(w/4)+sin²(w/4)v²`. -/
theorem chord_cube_antiderivative {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ v / (Real.cos (w / 4) ^ 2 *
        Real.sqrt (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2)))
      (1 / Real.sqrt (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2) ^ 3) v := by
  let A := Real.cos (w / 4) ^ 2
  let B := Real.sin (w / 4) ^ 2
  let q : ℝ → ℝ := fun v ↦ A + B * v ^ 2
  have hA : 0 < A := sq_pos_of_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩)
  have hq : 0 < q v := add_pos_of_pos_of_nonneg hA (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : 0 < Real.sqrt (q v) := Real.sqrt_pos.mpr hq
  have hd : HasDerivAt q (B * (2 * v)) v := by
    convert (((hasDerivAt_id v).pow 2).const_mul B).const_add A using 1
    simp
  have h := (hasDerivAt_id v).div ((hd.sqrt hq.ne').const_mul A) (by positivity)
  change HasDerivAt (fun v ↦ v / (A * Real.sqrt (q v))) (1 / Real.sqrt (q v) ^ 3) v
  convert h using 1
  have he := Real.sq_sqrt hq.le
  simp only [id_eq]; field_simp [hA.ne', hs.ne']
  ring_nf; rw [he]
  dsimp [q]; ring


end UnitaryProducts.Prose
