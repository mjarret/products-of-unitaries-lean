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

/-- Section 5: the inclusive sample indices `0,...,T` give `T+1` cells.
The partition and its endpoint half-cells are identified by
`Paper.rounded_clock_partition` and `PaperProof.uniform_cell_domains`. -/
theorem sample_cell_count (T : ℕ) :
    (Finset.range (T + 1)).card = T + 1 :=
  Finset.card_range (T + 1)

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

/-- Section 5: a constant positive input can have strictly positive truncation error
at every time. At zero binary places, the constant input `1/2` truncates to zero. -/
theorem constant_truncation_error_positive :
    ∃ x : ℝ, ∀ _t : ℝ, 0 < x - truncBits 0 x := by
  refine ⟨1 / 2, fun _t ↦ ?_⟩
  have htrunc : truncBits 0 (1 / 2) = 0 := by
    norm_num [truncBits, level]
  rw [htrunc]
  norm_num

/-- Section 5: rounding a real component strictly below and strictly above its
input gives errors of opposite signs, by `sub_pos` and `sub_neg`. -/
theorem alternating_rounding_error_signs {x yBelow yAbove : ℝ}
    (hBelow : yBelow < x) (hAbove : x < yAbove) :
    0 < x - yBelow ∧ x - yAbove < 0 := by
  have hPositive : 0 < x - yBelow := sub_pos.mpr hBelow
  have hNegative : x - yAbove < 0 := sub_neg.mpr hAbove
  exact ⟨hPositive, hNegative⟩

/-- Section 5: choosing the lower rounding before each cell center and the upper rounding
after it makes the entry error change sign at that center. -/
theorem alternating_rounding_in_time {x yBelow yAbove : ℝ}
    (hBelow : yBelow < x) (hAbove : x < yAbove) (j : ℝ) :
    let y := fun t : ℝ ↦ if t < j then yBelow else yAbove
    (∀ t < j, 0 < x - y t) ∧ (∀ t > j, x - y t < 0) := by
  intro y
  have hsigns := alternating_rounding_error_signs hBelow hAbove
  constructor
  · intro t ht
    simpa only [y, if_pos ht] using hsigns.1
  · intro t ht
    simpa only [y, if_neg (not_lt.mpr ht.le)] using hsigns.2

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
