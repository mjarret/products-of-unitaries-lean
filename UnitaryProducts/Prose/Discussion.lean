/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.FineSteps
public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# Rounding assertions in Section 5

The constant example records that truncation error need not change sign.
Alternating strictly below and above the input reverses the error's sign.
-/

@[expose] public section

namespace UnitaryProducts.Prose

open Paper.UnitStepsProse in
/-- Section 5: inside an open centered cell, the clock error is the displacement
from the integer sample and changes sign under reflection in that sample. -/
theorem full_cell_clock_error (j : ℤ) {t : ℝ} (ht : |t - (j : ℝ)| < 1 / 2) :
    t - (clock t : ℝ) = t - (j : ℝ) ∧
      (2 * (j : ℝ) - t) - (clock (2 * (j : ℝ) - t) : ℝ) =
        -(t - (clock t : ℝ)) := by
  have hReflection : |2 * (j : ℝ) - t - j| < 1 / 2 := by
    have hDisplacement : 2 * (j : ℝ) - t - j = -(t - j) := by ring
    rwa [hDisplacement, abs_neg]
  have hClock := clock_eq_of_abs_sub_lt ht
  have hReflectedClock := clock_eq_of_abs_sub_lt hReflection
  rw [hClock, hReflectedClock]
  constructor
  · rfl
  · ring

open Paper.UnitStepsProse in
/-- Section 5: every full centered cell contains both signs of the rounded-clock
error. The two quarter points lie strictly inside the cell; endpoint half-cells
are not asserted to contain both signs. -/
theorem full_cell_opposite_signs (j : ℤ) :
    ∃ tMinus tPlus : ℝ,
      |tMinus - (j : ℝ)| < 1 / 2 ∧ |tPlus - (j : ℝ)| < 1 / 2 ∧
      tMinus - (clock tMinus : ℝ) < 0 ∧ 0 < tPlus - (clock tPlus : ℝ) := by
  have hLeftMem : |((j : ℝ) - 1 / 4) - j| < 1 / 2 := by
    rw [sub_sub_cancel_left]
    norm_num
  have hRightMem : |((j : ℝ) + 1 / 4) - j| < 1 / 2 := by
    rw [add_sub_cancel_left]
    norm_num
  have hLeftClock : clock ((j : ℝ) - 1 / 4) = j :=
    clock_eq_of_abs_sub_lt hLeftMem
  have hRightClock : clock ((j : ℝ) + 1 / 4) = j :=
    clock_eq_of_abs_sub_lt hRightMem
  refine ⟨(j : ℝ) - 1 / 4, (j : ℝ) + 1 / 4, hLeftMem, hRightMem, ?_, ?_⟩
  · rw [hLeftClock, sub_sub_cancel_left]
    norm_num
  · rw [hRightClock, add_sub_cancel_left]
    norm_num

open Paper.UnitStepsProse MeasureTheory Set in
/-- Section 5: the signed clock error has zero integral over every full centered
cell. The single tie at the right endpoint has measure zero. -/
theorem full_cell_clock_integral (j : ℤ) :
    (∫ t in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), t - (clock t : ℝ)) = 0 := by
  have he : (∫ t in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), t - (clock t : ℝ)) =
      ∫ t in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), t - (j : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne ((j : ℝ) + 1 / 2)] with t ht
    intro hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have habs : |t - (j : ℝ)| < 1 / 2 := abs_lt.mpr
      ⟨by linarith [hmem.1], by
        rcases lt_or_eq_of_le hmem.2 with h | h
        · linarith
        · exact (ht h).elim⟩
    rw [clock_eq_of_abs_sub_lt habs]
  rw [he, intervalIntegral.integral_sub
    (f := fun t : ℝ ↦ t) (g := fun _ : ℝ ↦ (j : ℝ))
    (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

open Paper.UnitStepsProse MeasureTheory Set in
/-- Section 5: the first-order term has zero integral on the open full cell.
Removing the endpoints does not change the integral, and its matrix coefficient
is constant on the cell. -/
theorem full_cell_first_order_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (j : ℤ) (D : E) :
    (∫ t in Ioo ((j : ℝ) - 1 / 2) ((j : ℝ) + 1 / 2),
      (t - (clock t : ℝ)) • D) = 0 := by
  have hScalar : (∫ t in Ioo ((j : ℝ) - 1 / 2) ((j : ℝ) + 1 / 2),
      t - (clock t : ℝ)) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : (j : ℝ) - 1 / 2 ≤ j + 1 / 2)]
    exact full_cell_clock_integral j
  rw [integral_smul_const, hScalar, zero_smul]

/-- Section 5: a constant positive input can have strictly positive truncation error
at every time. At zero binary places, the constant input `1/2` truncates to zero. -/
theorem constant_truncation_error_positive :
    ∃ x : ℝ, ∀ _t : ℝ, 0 < x - truncBits 0 x := by
  refine ⟨1 / 2, fun _t ↦ ?_⟩
  have htrunc : truncBits 0 (1 / 2) = 0 := by
    norm_num [truncBits, level]
  rw [htrunc]
  norm_num



open UnitaryProducts.Paper in
/-- Section 5: dividing the Hamiltonian by a positive integer and multiplying
its duration by that integer preserves the evolution after the corresponding
change of time, including its final value. -/
theorem subdivided_evolution {d : ℕ}
    {H U : ℝ → Matrix (Fin d) (Fin d) ℂ} {T : ℝ}
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    {n : ℕ} (hn : 0 < n) :
    IsEvolution (fun t ↦ (n : ℝ)⁻¹ • H (t / ((n : ℝ) * T)))
      (fun t ↦ U (t / n)) 0 ((n : ℝ) * T) ∧
      U (((n : ℝ) * T) / n) = U T := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hscale := rescaled_evolution hU (inv_pos.mpr hnpos)
  have htime : T / (n : ℝ)⁻¹ = (n : ℝ) * T := by
    rw [div_inv_eq_mul, mul_comm]
  constructor
  · simpa only [htime, div_eq_mul_inv, mul_comm] using hscale
  · congr 1
    exact mul_div_cancel_left₀ T hnpos.ne'

open UnitaryProducts.Paper in
/-- Section 5: every eigenvalue difference of the divided Hamiltonian is an
original eigenvalue difference divided by the same positive integer. Eigenvalues
may be enumerated differently, so the matching indices are existential. -/
theorem subdivided_eigenvalue_difference {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    {n : ℕ} (hn : 0 < n) (p q : Fin d) :
    ∃ i j, (Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues p -
      (Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues q =
        (hA.eigenvalues i - hA.eigenvalues j) / n ∧
      |(Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues p -
        (Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues q| =
        |hA.eigenvalues i - hA.eigenvalues j| / n := by
  obtain ⟨i, hi⟩ := scaled_eigenvalue hA (n : ℝ)⁻¹ p
  obtain ⟨j, hj⟩ := scaled_eigenvalue hA (n : ℝ)⁻¹ q
  have hdiff : (Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues p -
      (Separation.isHermitian_real_smul hA (n : ℝ)⁻¹).eigenvalues q =
      (hA.eigenvalues i - hA.eigenvalues j) / n := by
    rw [hi, hj, ← mul_sub, div_eq_mul_inv, mul_comm]
  refine ⟨i, j, hdiff, ?_⟩
  rw [hdiff, abs_div, abs_of_pos (show (0 : ℝ) < (n : ℝ) from Nat.cast_pos.mpr hn)]

end UnitaryProducts.Prose
