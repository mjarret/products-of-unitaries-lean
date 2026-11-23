/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Citations
public import RoundedClocks.Preliminaries.Basic

/-! # The least eigenvalue of a continuous Hermitian family

The least eigenvalue of a continuous Hermitian family `H(s)` for `s ∈ [0,1]` is continuous, by the
Loewner-order spectral bound (`continuousOn_sInf_spectrum`). Theorem 4.6 uses it for the
`a` of (4.7), and the proof of Theorem 4.7 for its `ℓ`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator MatrixOrder
open Set Matrix

noncomputable section
namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The least eigenvalues of Hermitian `A` and `B` differ by at most `‖A - B‖`. -/
theorem abs_sInf_spectrum_sub_le
    [NeZero d] {A B : 𝕄} (hA : IsHermitian A) (hB : IsHermitian B) :
    |sInf (spectrum ℝ A) - sInf (spectrum ℝ B)| ≤ ‖A - B‖ := by
  have hleast : ∀ {X : 𝕄}, X.IsHermitian → IsLeast (spectrum ℝ X) (sInf (spectrum ℝ X)) := by
    intro X hX
    rw [hX.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).isCompact.isLeast_sInf (Set.range_nonempty _)
  have key : ∀ {A B : 𝕄}, A.IsHermitian → B.IsHermitian →
      sInf (spectrum ℝ B) - ‖A - B‖ ≤ sInf (spectrum ℝ A) := by
    intro A B hA hB
    have h1 : algebraMap ℝ 𝕄 (sInf (spectrum ℝ B)) ≤ B :=
      (algebraMap_le_iff_le_spectrum hB.isSelfAdjoint).mpr fun x hx ↦ (hleast hB).2 hx
    have h2 : B - A ≤ algebraMap ℝ 𝕄 ‖B - A‖ :=
      (le_algebraMap_iff_spectrum_le (hB.isSelfAdjoint.sub hA.isSelfAdjoint)).mpr fun x hx ↦
        (le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx)
    have h3 : algebraMap ℝ 𝕄 (sInf (spectrum ℝ B) - ‖A - B‖) ≤ A := by
      rw [map_sub, norm_sub_rev]
      simpa using sub_le_sub h1 h2
    exact (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp h3 _ (hleast hA).1
  rw [abs_le]
  constructor
  · have := key hA hB
    linarith
  · have := key hB hA
    rw [norm_sub_rev] at this
    linarith

/-- The least eigenvalue of a continuous Hermitian family `H(s)` is continuous for `s ∈ [0,1]`. -/
theorem continuousOn_sInf_spectrum
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) (hHc : ContinuousOn H (Icc (0 : ℝ) 1)) :
    IsContinuousFamily (fun s ↦ sInf (spectrum ℝ (H s))) := by
  have hL : LipschitzOnWith 1 (fun X : 𝕄 ↦ sInf (spectrum ℝ X)) {X | X.IsHermitian} :=
    LipschitzOnWith.of_dist_le_mul fun A hA B hB ↦ by
      simpa [Real.dist_eq, dist_eq_norm] using abs_sInf_spectrum_sub_le hA hB
  exact hL.continuousOn.comp hHc fun s hs ↦ @hH s hs

end RoundedClocks
