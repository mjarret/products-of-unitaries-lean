/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic

/-!
# Checkpoints

Checkpoints `0 = s₀ ≤ ⋯ ≤ s_N = 1` (Section 3.2) are nondecreasing in the index, so every
checkpoint and every midpoint `s_{j+1/2} = (sⱼ + sⱼ₊₁)/2` lies in `[0,1]`, where a time-dependent
Hamiltonian is defined.
-/

@[expose] public section

open Set

namespace RoundedClocks

/-- Checkpoints are nondecreasing in the index: `sᵢ ≤ sⱼ` for `i ≤ j ≤ N`. -/
theorem checkpoints_mono {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : s i ≤ s j :=
  partition_mono hs.le_succ hij hj

/-- Every checkpoint lies in `[0,1]`. -/
theorem checkpoint_mem {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {j : ℕ} (hj : j ≤ N) : s j ∈ Icc (0 : ℝ) 1 := by
  have h0 := checkpoints_mono hs (Nat.zero_le j) hj
  have h1 := checkpoints_mono hs hj le_rfl
  rw [hs.zero] at h0
  rw [hs.last] at h1
  exact ⟨h0, h1⟩

/-- Every midpoint `s_{j+1/2} = (sⱼ + sⱼ₊₁)/2` lies in `[0,1]`. -/
theorem checkpoint_midpoint_mem {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {j : ℕ} (hj : j < N) : (s j + s (j + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
  have h0 := (checkpoint_mem hs hj.le).1
  have h1 := (checkpoint_mem hs (Nat.succ_le_of_lt hj)).2
  constructor <;> linarith [hs.le_succ j hj]

end RoundedClocks
