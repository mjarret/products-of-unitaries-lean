/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps

/-! # Transfer estimates for truncated products

Example 4.5 compares the bit-truncated product with the rounded evolution through the Duhamel
formula and the fine-step truncation bound.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- An odd entrywise real map preserves Hermitian matrices. -/
theorem entrywise_isHermitian {F : ℝ → ℝ} (hF : Function.Odd F) {A : 𝕄}
    (hA : IsHermitian A) : IsHermitian (entrywise F A) := by
  ext i j
  change star (⟨F (A j i).re, F (A j i).im⟩ : ℂ) =
    ⟨F (A i j).re, F (A i j).im⟩
  rw [← hA.apply i j]
  exact Complex.ext rfl (hF _).symm

/-- The exponential `e^{-iuA}` is unitary for Hermitian `A`. -/
theorem phase_isUnitary {A : 𝕄} (hA : IsHermitian A) (u : ℝ) :
    IsUnitary (exp ((u : ℂ) • (-I • A))) := by
  letI : NormedAlgebra ℚ 𝕄 := NormedAlgebra.restrictScalars ℚ ℂ 𝕄
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact Unitary.star_mul_self_of_mem <| NormedSpace.exp_mem_unitary_of_mem_skewAdjoint <|
    skewAdjoint.smul_mem u (hA.isSelfAdjoint.smul_mem_skewAdjoint hI)

/-- A unitary matrix has operator norm at most one. -/
theorem unitary_norm_le_one [NeZero d] {A : 𝕄} (hA : IsUnitary A) : ‖A‖ ≤ 1 := by
  nontriviality 𝕄
  exact (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff'.2 hA)).le

end RoundedClocks
