/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.FineStepEstimates

/-! # Regularity of fine-step approximations

Theorem 3.6 obtains measurability and integrability for the midpoint and truncated Hamiltonians
from their regulated, piecewise-constant structure.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

/-- The supplied Lemma 3.4 partitions bound the family on the unit interval. -/
theorem fine_steps_bounded_of_checkpoints {H : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε) :
    BddAbove ((fun t ↦ ‖H t‖) '' Icc (0 : ℝ) 1) := by
  obtain ⟨N, s, hs, -, herr⟩ := hpart 1 one_pos
  let B := 1 + ∑ j ∈ Finset.range (N + 1), ‖H (s j)‖ +
    ∑ j ∈ Finset.range N, ‖H ((s j + s (j + 1)) / 2)‖
  refine ⟨B, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rcases checkpoint_or_mem_cell hs.1.1 ⟨hs.1.2.1 ▸ hx.1, hs.1.2.2 ▸ hx.2⟩ with
    ⟨j, hj, rfl⟩ | ⟨j, hj, hxj⟩
  · have hnode := Finset.single_le_sum
      (fun i (_ : i ∈ Finset.range (N + 1)) ↦ norm_nonneg (H (s i)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have hmid : 0 ≤ ∑ i ∈ Finset.range N, ‖H ((s i + s (i + 1)) / 2)‖ :=
      Finset.sum_nonneg fun i _ ↦ norm_nonneg _
    dsimp [B]
    linarith
  · have hmid := Finset.single_le_sum
      (fun i (_ : i ∈ Finset.range N) ↦
        norm_nonneg (H ((s i + s (i + 1)) / 2))) (Finset.mem_range.mpr hj)
    have hdist := herr j hj x hxj
    have hnorm : ‖H x‖ ≤ ‖H x - H ((s j + s (j + 1)) / 2)‖ +
        ‖H ((s j + s (j + 1)) / 2)‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (H x - H ((s j + s (j + 1)) / 2))
          (H ((s j + s (j + 1)) / 2))
    dsimp [B]
    linarith [hdist, hmid, Finset.sum_nonneg
      (fun i (_ : i ∈ Finset.range (N + 1)) ↦ norm_nonneg (H (s i)))]

/-- The supplied Lemma 3.4 partitions place relative discontinuities in a countable set. -/
theorem fine_steps_countable_discontinuities_of_checkpoints {H : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε) :
    {t ∈ Icc (0 : ℝ) 1 | ¬ ContinuousWithinAt H (Icc 0 1) t}.Countable := by
  classical
  choose N s hs hosc herr using fun n : ℕ ↦
    hpart (1 / (n + 1)) (by positivity)
  let S : Set ℝ := ⋃ n : ℕ, Set.range (s n)
  have hS : S.Countable := Set.countable_iUnion fun _ ↦ Set.countable_range _
  refine hS.mono fun t ht ↦ Classical.byContradiction fun hn ↦ ht.2
    (ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.mpr fun ε hε ↦ ?_))
  obtain ⟨n, hnε⟩ := exists_nat_one_div_lt hε
  have hno : ∀ j, t ≠ s n j := fun j hj ↦ hn (Set.mem_iUnion.mpr ⟨n, j, hj.symm⟩)
  rcases checkpoint_or_mem_cell (hs n).1.1
      ⟨(hs n).1.2.1 ▸ ht.1.1, (hs n).1.2.2 ▸ ht.1.2⟩ with hnode | ⟨j, hj, htj⟩
  · obtain ⟨j, -, hj⟩ := hnode
    exact absurd hj (hno j)
  · filter_upwards [Ioo_mem_nhds htj.1 htj.2] with x hx
    rw [dist_eq_norm]
    exact (hosc n j hj x hx t htj).trans_lt hnε

/-- The supplied Lemma 3.4 partitions make the family interval integrable. -/
theorem fine_steps_integrable_of_checkpoints {H : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε) :
    IntervalIntegrable H MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  let S := {t ∈ Icc (0 : ℝ) 1 | ¬ ContinuousWithinAt H (Icc 0 1) t}
  have hS : S.Countable := fine_steps_countable_discontinuities_of_checkpoints hpart
  have hc : ContinuousOn H (Icc (0 : ℝ) 1 \ S) := fun x hx ↦
    ContinuousWithinAt.mono (not_not.mp fun hn ↦ hx.2 ⟨hx.1, hn⟩) Set.diff_subset
  have hm := hc.aestronglyMeasurable (μ := MeasureTheory.volume)
    (measurableSet_Icc.diff hS.measurableSet)
  have hmeas : AEStronglyMeasurable H (MeasureTheory.volume.restrict (Icc 0 1)) := by
    rwa [Measure.restrict_congr_set
      (diff_null_ae_eq_self (hS.measure_zero MeasureTheory.volume))] at hm
  obtain ⟨B, hB⟩ := fine_steps_bounded_of_checkpoints hpart
  exact Integrable.of_bound hmeas B
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hB ⟨t, ht, rfl⟩)

end RoundedClocks
