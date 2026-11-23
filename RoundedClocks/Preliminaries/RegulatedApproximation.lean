/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Citations

/-! # Piecewise-constant approximation of regulated families

Theorem 2.2 approximates a regulated matrix family on each partition cell and uses the finite
image of the approximation to obtain regularity bounds.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2 / Dieudonné (7.6.1): a partition point is a checkpoint or in an open cell. -/
private lemma comparison_checkpoint_or_open_cell (t : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (t 0) (t n)) :
    (∃ j ≤ n, x = t j) ∨ ∃ j < n, x ∈ Ioo (t j) (t (j + 1)) := by
  induction n with
  | zero => exact Or.inl ⟨0, le_rfl, le_antisymm hx.2 hx.1⟩
  | succ n ih =>
    rcases le_or_gt x (t n) with hle | hgt
    · rcases ih ⟨hx.1, hle⟩ with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ n), he⟩
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, he⟩
    · rcases hx.2.eq_or_lt with he | hlt
      · exact Or.inl ⟨n + 1, le_rfl, he⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hgt, hlt⟩

/-- Section 2 / Dieudonné (7.6.1): step functions have finite image, including checkpoints. -/
lemma comparison_step_finite_image {G : ℝ → 𝕄} {a b : ℝ}
    (hG : IsPiecewiseConstant G a b) : (G '' Icc a b).Finite := by
  rcases hG with ⟨n, t, A, ha, hb, _, hA⟩
  have hfinite : (A '' Iio n ∪ (fun j ↦ G (t j)) '' Iic n).Finite :=
    ((finite_Iio n).image A).union ((finite_Iic n).image (fun j ↦ G (t j)))
  apply hfinite.subset
  rintro _ ⟨x, hx, rfl⟩
  rw [← ha, ← hb] at hx
  rcases comparison_checkpoint_or_open_cell t n hx with ⟨j, hj, he⟩ | ⟨j, hj, hxj⟩
  · exact Or.inr ⟨j, hj, congrArg G he.symm⟩
  · exact Or.inl ⟨j, hj, (hA j hj x hxj).symm⟩

/-- Section 2 / Dieudonné (7.6.1): step functions are continuous off finitely many checkpoints. -/
lemma comparison_step_continuous_off_finite {G : ℝ → 𝕄} {a b : ℝ}
    (hG : IsPiecewiseConstant G a b) :
    ∃ D : Set ℝ, D.Finite ∧ ∀ x ∈ Icc a b, x ∉ D → ContinuousAt G x := by
  rcases hG with ⟨n, t, A, ha, hb, _, hA⟩
  refine ⟨t '' (↑(Finset.range (n + 1)) : Set ℕ),
    (Finset.finite_toSet _).image t, ?_⟩
  intro x hx hxD
  rw [← ha, ← hb] at hx
  rcases comparison_checkpoint_or_open_cell t n hx with ⟨j, hj, he⟩ | ⟨j, hj, hxj⟩
  · apply False.elim
    apply hxD
    refine ⟨j, ?_, he.symm⟩
    simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hj
  · apply continuousAt_const.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhds hxj.1 hxj.2] with y hy
      exact hA j hj y hy

end RoundedClocks
