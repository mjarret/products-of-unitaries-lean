/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps.BitTruncation
public import RoundedClocks.FineSteps.Checkpoints

/-! # The piecewise-constant family in the proof of Theorem 3.6

"The piecewise-constant family `G(s) = H^{(F)}(s_{j+1/2})` for `sⱼ < s < sⱼ₊₁` is Hermitian, as
`F` is odd." This file constructs the family `T G(s)` for `s ∈ [0,1]`, shows that it is regulated
and Hermitian, and bounds `‖T H(s) - T G(s)‖` by `T` times the supremum in the statement of
Theorem 3.6.
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

/-- The truncated midpoint samples `T H^{(F)}(s_{j+1/2})` are Hermitian, as `F` is odd. -/
theorem midpoint_sample_isHermitian {F : ℝ → ℝ} (hF : Function.Odd F) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) (T : ℝ) {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {j : ℕ} (hj : j < N) : (T • entrywise F (H ((s j + s (j + 1)) / 2))).IsHermitian := by
  have hsample :=
    (Function.Odd.entrywise_and_sub_isHermitian hF
      (hH (checkpoint_midpoint_mem hs hj))).1
  exact isHermitian_real_smul hsample T

/-- The supremum in Theorem 3.6. When `H` is bounded for `s ∈ [0,1]`, as every regulated `H` is,
the norms `‖H(x) - H^{(F)}(s_{j+1/2})‖` with `sⱼ < x < sⱼ₊₁` are bounded, so their supremum
`max_j sup_{sⱼ < x < sⱼ₊₁} ‖H(x) - H^{(F)}(s_{j+1/2})‖` is nonnegative and at least each of
them. -/
theorem le_midpointApproximationError {F : ℝ → ℝ} {H : ℝ → 𝕄}
    (hbounded : BddAbove ((fun x ↦ ‖H x‖) '' Icc (0 : ℝ) 1)) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) :
    0 ≤ midpointApproximationError F H N s ∧
      ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ‖H x - entrywise F (H ((s j + s (j + 1)) / 2))‖ ≤
          midpointApproximationError F H N s := by
  classical
  obtain ⟨B, hB⟩ := hbounded
  have hB0 : 0 ≤ B := (norm_nonneg (H 0)).trans (hB ⟨0, by simp, rfl⟩)
  -- Each norm is at most `B` plus the sum `C` of the norms of the truncated midpoint samples.
  let C := ∑ j ∈ Finset.range N,
    ‖entrywise F (H ((s j + s (j + 1)) / 2))‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hMbdd : BddAbove ({0} ∪ {r : ℝ | ∃ j < N,
      ∃ x ∈ Ioo (s j) (s (j + 1)),
        r = ‖H x - entrywise F (H ((s j + s (j + 1)) / 2))‖}) := by
    refine ⟨B + C, ?_⟩
    rintro r (rfl | ⟨j, hj, x, hx, rfl⟩)
    · positivity
    · have hxI : x ∈ Icc (0 : ℝ) 1 :=
        ⟨(checkpoint_mem hs hj.le).1.trans hx.1.le,
          hx.2.le.trans (checkpoint_mem hs (Nat.succ_le_of_lt hj)).2⟩
      have hsample := Finset.single_le_sum
        (fun i (_ : i ∈ Finset.range N) ↦
          norm_nonneg (entrywise F (H ((s i + s (i + 1)) / 2))))
        (Finset.mem_range.mpr hj)
      exact (norm_sub_le _ _).trans (add_le_add (hB ⟨x, hxI, rfl⟩) hsample)
  exact ⟨le_csSup hMbdd (Or.inl rfl), fun j hj x hx ↦
    le_csSup hMbdd (Or.inr ⟨j, hj, x, hx, rfl⟩)⟩

/-- Proof of Theorem 3.6, first sentence. For an odd `F`, a time-dependent Hamiltonian `H` that is
bounded for `s ∈ [0,1]`, and `T > 0`, there is a regulated Hermitian family `G` with
`G(x) = T H^{(F)}(s_{j+1/2})` for `sⱼ < x < sⱼ₊₁` and
`‖T H(x) - G(x)‖ ≤ T max_j sup_{sⱼ < x < sⱼ₊₁} ‖H(x) - H^{(F)}(s_{j+1/2})‖` for every `x ∈ [0,1]`.
At the checkpoints, where the paper leaves the family unspecified, `G = T H`, so that the bound
holds there too. -/
theorem exists_midpoint_family [NeZero d] {F : ℝ → ℝ} (hF : Function.Odd F)
    {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    (hbounded : BddAbove ((fun x ↦ ‖H x‖) '' Icc (0 : ℝ) 1)) {T : ℝ} (hT : 0 < T)
    {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    ∃ G : ℝ → 𝕄, IsRegulated G 0 1 ∧ IsHermitianFamily G 0 1 ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        G x = T • entrywise F (H ((s j + s (j + 1)) / 2))) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        ‖T • H x - G x‖ ≤ T * midpointApproximationError F H N s) := by
  classical
  obtain ⟨hM0, hpoint⟩ := le_midpointApproximationError (F := F) hbounded hs
  -- The samples `Aⱼ = T H^{(F)}(s_{j+1/2})`, and the family `G`: equal to `Aⱼ` strictly between
  -- the checkpoints `sⱼ` and `sⱼ₊₁`, and to `T H` at the checkpoints.
  let A : ℕ → 𝕄 := fun j ↦ T • entrywise F (H ((s j + s (j + 1)) / 2))
  let between := fun x j ↦ j < N ∧ x ∈ Ioo (s j) (s (j + 1))
  let G : ℝ → 𝕄 := fun x ↦ if h : ∃ j, between x j then A h.choose else T • H x
  -- The open intervals between consecutive checkpoints are disjoint, so `G = Aⱼ` on the `j`th.
  have hpieces : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), G x = A j := by
    intro j hj x hx
    have hex : ∃ q, between x q := ⟨j, hj, hx⟩
    have hc := hex.choose_spec
    have he : hex.choose = j := by
      rcases lt_trichotomy hex.choose j with hlt | he | hgt
      · have hord := checkpoints_mono hs (Nat.succ_le_of_lt hlt) hj.le
        exact False.elim (by linarith [hc.2.2, hx.1])
      · exact he
      · have hord := checkpoints_mono hs (Nat.succ_le_of_lt hgt) hc.1.le
        exact False.elim (by linarith [hc.2.1, hx.2])
    simp only [G, dif_pos hex, he]
  -- The samples are Hermitian, as `F` is odd.
  have hA : ∀ j < N, (A j).IsHermitian := fun j hj ↦
    midpoint_sample_isHermitian hF hH T hs hj
  -- A piecewise-constant family is regulated.
  have hGreg : IsRegulated G 0 1 := by
    simpa only [hs.zero, hs.last] using isRegulated_of_piecewise_constant G s A N hpieces
  have hGherm : IsHermitianFamily G 0 1 := by
    intro x hx
    by_cases hc : ∃ j, between x j
    · rw [hpieces hc.choose hc.choose_spec.1 x hc.choose_spec.2]
      exact hA hc.choose hc.choose_spec.1
    · change (G x).IsHermitian
      simp only [G, dif_neg hc]
      exact isHermitian_real_smul (hH hx) T
  refine ⟨G, hGreg, hGherm, hpieces, ?_⟩
  -- Between checkpoints `‖T H(x) - G(x)‖ = T ‖H(x) - H^{(F)}(s_{j+1/2})‖`, and at a checkpoint
  -- `T H(x) - G(x) = 0`.
  intro x hx
  by_cases hc : ∃ j, between x j
  · have hp := hpoint hc.choose hc.choose_spec.1 x hc.choose_spec.2
    simpa only [G, dif_pos hc, A, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hT] using mul_le_mul_of_nonneg_left hp hT.le
  · simp only [G, dif_neg hc, sub_self, norm_zero]
    positivity

end RoundedClocks
