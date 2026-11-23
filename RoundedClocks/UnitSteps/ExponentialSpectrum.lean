/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Spectrum of a matrix phase

Corollary 4.7 identifies the spectrum of a unitary exponential with the exponential image of the
Hermitian spectrum and locates phases on the chosen open turn.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section

namespace RoundedClocks.WalkLeakageSpectrum

/-- Operator-norm matrices form a C-star algebra. -/
private def matrixCStarAlgebra (d : ℕ) :
    CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}

/-- The spectrum of the matrix phase is the phase image of its real spectrum. -/
theorem spectrum_phase_image {A : Matrix (Fin d) (Fin d) ℂ} (hA : IsHermitian A) :
    spectrum ℂ (NormedSpace.exp (-I • A)) =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ A := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hn : IsStarNormal A := hsa.isStarNormal
  have he : NormedSpace.exp (-I • A) =
      cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A := by
    have hh : cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A =
        cfc Complex.exp (cfc (fun z : ℂ ↦ -I * z) A) :=
      cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I * z) A hn
        Complex.continuous_exp.continuousOn (continuousOn_const.mul continuousOn_id)
    rw [hh, cfc_const_mul_id (-I) A, CFC.complex_exp_eq_normedSpace_exp]
  rw [he, cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) A hn
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn]
  rw [← hsa.spectrumRestricts.algebraMap_image, Set.image_image]
  rfl

/-- Two phases in the same open turn have distinct exponentials unless they coincide. -/
theorem phase_inj {α θ φ : ℝ}
    (hθ : θ ∈ Ioo α (α + 2 * π)) (hφ : φ ∈ Ioo α (α + 2 * π))
    (he : Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (φ : ℂ))) : θ = φ := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hi := congrArg Complex.im hk
  simp at hi
  have hklo : (-1 : ℝ) < k := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h)
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
    simp only [neg_mul] at hm
    linarith [hθ.2, hφ.1]
  have hkhi : (k : ℝ) < 1 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h)
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
    linarith [hθ.1, hφ.2]
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hkzero : k = 0 := by omega
  subst k
  simpa using hi

/-- Within an open turn, membership in the phase arc is membership in its real interval. -/
theorem phase_mem_arc_iff {α β θ : ℝ} (hβ : β < α + 2 * π)
    (hθ : θ ∈ Ioo α (α + 2 * π)) :
    Complex.exp (-I * (θ : ℂ)) ∈ arc α β ↔ θ ∈ Ioo α β := by
  constructor
  · rintro ⟨φ, hφ, he⟩
    have heq := phase_inj ⟨hφ.1, hφ.2.trans hβ⟩ hθ he
    exact heq ▸ hφ
  · intro h
    exact ⟨θ, h, rfl⟩

end RoundedClocks.WalkLeakageSpectrum
