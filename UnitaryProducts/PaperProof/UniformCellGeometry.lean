/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# UniformCellGeometry

## Declarations

- `sum_Icc_one_eq_sum_range`
- `uniform_local_hamiltonian_derivative`
-/
@[expose] public section
open Set Real
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof

/-- Reindex the N jumps by their right sample, j = 1,...,N. -/
theorem sum_Icc_one_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, f j = ∑ k ∈ Finset.range N, f (k + 1) := by
  simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm] using
    Finset.sum_Ico_eq_sum_range f 1 (N + 1)

/-- Section 4.1: the rounded cell includes its left tie and excludes its right tie. -/
theorem rounded_cell_iff (t : ℝ) (j : ℤ) :
    clock t = j ↔ -(1 / 2 : ℝ) ≤ t - j ∧ t - j < 1 / 2 := by
  rw [clock, Int.floor_eq_iff]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Section 4.1: the exact preimage cell, restricted to the evolution interval,
and the constant Hamiltonian on that cell. -/
theorem rounded_cell_description {E : Type*} (H : ℝ → E) (T : ℝ) (j : ℤ) :
    clock ⁻¹' {j} ∩ Icc 0 T =
      {t : ℝ | -(1 / 2 : ℝ) ≤ t - j ∧ t - j < 1 / 2} ∩ Icc 0 T ∧
    ∀ t ∈ clock ⁻¹' {j} ∩ Icc 0 T, H ((clock t : ℝ) / T) = H ((j : ℝ) / T) := by
  constructor
  · ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_setOf_eq,
      rounded_cell_iff]
  · intro t ht
    have hclock : clock t = j := ht.1
    rw [hclock]

/-- Section 4.1: the first and last rounded cells are exactly half-cells;
the final endpoint belongs to the last cell. -/
theorem rounded_endpoint_cells {T : ℕ} (hT : 1 ≤ T) :
    clock ⁻¹' {(0 : ℤ)} ∩ Icc (0 : ℝ) T = Ico 0 (1 / 2) ∧
    clock ⁻¹' {(T : ℤ)} ∩ Icc (0 : ℝ) T = Icc ((T : ℝ) - 1 / 2) T := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  constructor
  · ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, rounded_cell_iff,
      Int.cast_zero, sub_zero, mem_Icc, mem_Ico]
    constructor
    · intro h
      exact ⟨h.2.1, h.1.2⟩
    · intro h
      exact ⟨⟨by linarith [h.1], h.2⟩, ⟨h.1, by linarith [h.2]⟩⟩
  · ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, rounded_cell_iff,
      Int.cast_natCast, mem_Icc]
    constructor
    · intro h
      exact ⟨by linarith [h.1.1], h.2.2⟩
    · intro h
      exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩,
        ⟨by linarith [h.1], h.2⟩⟩

end UnitaryProducts.PaperProof
