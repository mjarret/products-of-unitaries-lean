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
- `uniform_cell_domains`
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


/-- Intersecting the centered cells with [0,1] leaves a full cell at each
interior sample and exactly a half-cell at each endpoint sample. -/
theorem uniform_cell_domains {N : ℕ} (hN : 0 < N) :
    let δ : ℝ := 1/(2*N)
    Icc (-δ) δ ∩ Icc (0 : ℝ) 1 = Icc 0 δ ∧
    Icc (1-δ) (1+δ) ∩ Icc (0 : ℝ) 1 = Icc (1-δ) 1 ∧
    ∀ j : ℕ, 0 < j → j < N →
      Icc (((j : ℝ)-1/2)/N) (((j : ℝ)+1/2)/N) ⊆ Icc (0 : ℝ) 1 := by
  intro δ
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · rw [Icc_inter_Icc, sup_eq_right.mpr (neg_nonpos.mpr hδ0), inf_eq_left.mpr hδ1]
  · rw [Icc_inter_Icc, sup_eq_left.mpr (sub_nonneg.mpr hδ1),
      inf_eq_right.mpr (le_add_of_nonneg_right hδ0)]
  · intro j hj hjN
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    have hjN1 : (j : ℝ)+1 ≤ N := by exact_mod_cast (show j+1 ≤ N by omega)
    exact Icc_subset_Icc (div_nonneg (by linarith) hn.le)
      ((div_le_one hn).mpr (by linarith))

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
