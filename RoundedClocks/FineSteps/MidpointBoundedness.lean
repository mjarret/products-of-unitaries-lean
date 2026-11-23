/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.FineStepEstimates

/-! # Bounded midpoint-product errors

Theorem 3.6 uses boundedness of the Hamiltonian and its derivative to control the local
midpoint-product error uniformly over all fine steps.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Theorem 3.6: boundedness from Lemma 3.4 makes the midpoint error nonnegative
and bounds the error on every open cell. -/
theorem fine_steps_error_control_of_bounded {F : ℝ → ℝ} {H : ℝ → 𝕄}
    (hbounded : BddAbove ((fun x ↦ ‖H x‖) '' Icc (0 : ℝ) 1)) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) :
    0 ≤ midpointApproximationError F H N s ∧
      ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ‖H x - entrywise F (H ((s j + s (j + 1)) / 2))‖ ≤
          midpointApproximationError F H N s := by
  classical
  obtain ⟨B, hB⟩ := hbounded
  have hB0 : 0 ≤ B := (norm_nonneg (H 0)).trans (hB ⟨0, by simp, rfl⟩)
  let C := ∑ j ∈ Finset.range N,
    ‖entrywise F (H ((s j + s (j + 1)) / 2))‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hMbdd : BddAbove ({0} ∪ {r : ℝ | ∃ j < N,
      ∃ x ∈ Ioo (s j) (s (j + 1)),
        r = ‖H x - entrywise F (H ((s j + s (j + 1)) / 2))‖}) := by
    refine ⟨B + C, ?_⟩
    rintro r (rfl | ⟨j, hj, x, hx, rfl⟩)
    · positivity
    · have hxI : x ∈ Icc (0 : ℝ) 1 := by
        constructor
        · rw [← hs.2.1]
          exact (checkpoints_mono hs (Nat.zero_le j) hj.le).trans hx.1.le
        · rw [← hs.2.2]
          exact hx.2.le.trans (checkpoints_mono hs (Nat.succ_le_of_lt hj) le_rfl)
      have hsample := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range N) ↦
          norm_nonneg (entrywise F (H ((s i + s (i + 1)) / 2))))
        (Finset.mem_range.mpr hj)
      exact (norm_sub_le _ _).trans (add_le_add (hB ⟨x, hxI, rfl⟩) hsample)
  exact ⟨le_csSup hMbdd (Or.inl rfl), fun j hj x hx ↦
    le_csSup hMbdd (Or.inr ⟨j, hj, x, hx, rfl⟩)⟩

/-- Theorem 3.6: the held midpoint family, using the bound supplied by Lemma 3.4. -/
theorem fine_steps_held_family_of_bounded [NeZero d] {F : ℝ → ℝ} (hF : Function.Odd F)
    {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    (hbounded : BddAbove ((fun x ↦ ‖H x‖) '' Icc (0 : ℝ) 1)) {T : ℝ} (hT : 0 < T)
    {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    ∃ K : ℝ → 𝕄, IsRegulated K 0 1 ∧ IsHermitianFamily K 0 1 ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        K x = T • entrywise F (H ((s j + s (j + 1)) / 2))) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        ‖T • H x - K x‖ ≤ T * midpointApproximationError F H N s) := by
  classical
  obtain ⟨hM0, hpoint⟩ := fine_steps_error_control_of_bounded (F := F) hbounded hs
  let A : ℕ → 𝕄 := fun j ↦ T • entrywise F (H ((s j + s (j + 1)) / 2))
  let cell := fun x j ↦ j < N ∧ x ∈ Ioo (s j) (s (j + 1))
  let K : ℝ → 𝕄 := fun x ↦ if h : ∃ j, cell x j then A h.choose else T • H x
  have hpieces : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), K x = A j := by
    intro j hj x hx
    have hex : ∃ q, cell x q := ⟨j, hj, hx⟩
    have hc := hex.choose_spec
    have he : hex.choose = j := by
      rcases lt_trichotomy hex.choose j with hlt | he | hgt
      · have hord := checkpoints_mono hs (Nat.succ_le_of_lt hlt) hj.le
        exact False.elim (by linarith [hc.2.2, hx.1])
      · exact he
      · have hord := checkpoints_mono hs (Nat.succ_le_of_lt hgt) hc.1.le
        exact False.elim (by linarith [hc.2.1, hx.2])
    simp only [K, dif_pos hex, he]
  have hA : ∀ j < N, (A j).IsHermitian := by
    intro j hj
    have hm := checkpoint_midpoint_mem hs hj
    have hsample := (entrywise_and_error_isHermitian F hF (hH _ hm)).1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hsample.eq]
  have hKreg : IsRegulated K 0 1 := by
    simpa only [hs.2.1, hs.2.2] using piecewise_regulated_of_cells K s A N hpieces
  have hKherm : IsHermitianFamily K 0 1 := by
    intro x hx
    by_cases hc : ∃ j, cell x j
    · rw [hpieces hc.choose hc.choose_spec.1 x hc.choose_spec.2]
      exact hA hc.choose hc.choose_spec.1
    · change (K x).IsHermitian
      simp only [K, dif_neg hc]
      rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (hH x hx).eq]
  refine ⟨K, hKreg, hKherm, hpieces, ?_⟩
  intro x hx
  by_cases hc : ∃ j, cell x j
  · have hp := hpoint hc.choose hc.choose_spec.1 x hc.choose_spec.2
    simpa only [K, dif_pos hc, A, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hT] using mul_le_mul_of_nonneg_left hp hT.le
  · simp only [K, dif_neg hc, sub_self, norm_zero]
    positivity

end RoundedClocks
