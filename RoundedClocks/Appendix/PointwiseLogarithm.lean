/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.WalkLeakage.LogarithmUniqueness

/-! # Lemma A.2: the logarithm of one unitary matrix

The first two sentences of the proof of Lemma A.2, for one unitary `W` with spectrum in
`{e^{-iθ} : θ ∈ [a, a+w]}`. The spectral theorem gives `W = ∑_j e^{-iθ_j} P_j` with
`θ_j ∈ [a, a+w]`, so `H = ∑_j θ_j P_j` is Hermitian with spectrum in `[a, a+w]` and `e^{-iH} = W`
(`walk_log_pointwise`). As `θ ↦ e^{-iθ}` is injective for `θ ∈ [a, a+w]`, `H` is the only such
matrix (`walk_log_unique`).
-/

@[expose] public section

open Real Complex Set Matrix
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The first sentence of the proof of Lemma A.2: if every eigenvalue of the unitary `U` is
`e^{-iθ}` with `θ ∈ [a, a+w]`, then `H = ∑_j θ_j P_j`, constructed by continuous functional
calculus, is Hermitian with spectrum in `[a, a+w]` and `e^{-iH} = U`. -/
theorem walk_log_pointwise (a w : ℝ)
    (U : 𝕄) (hu : IsUnitary U)
    (harc : ∀ z ∈ spectrum ℂ U,
      ∃ θ ∈ Icc a (a + w), z = Complex.exp (-I * (θ : ℂ))) :
    ∃ H : 𝕄, ∃ _hH : H.IsHermitian,
      HasRealSpectrumIn H (Icc a (a + w)) ∧ NormedSpace.exp (-I • H) = U := by
  classical
  have hn : IsStarNormal U := isStarNormal_of_mem_unitary hu
  let θ : ℂ → ℝ := fun z ↦ if hz : z ∈ spectrum ℂ U then (harc z hz).choose else a
  have hθ (z : ℂ) (hz : z ∈ spectrum ℂ U) :
      θ z ∈ Icc a (a + w) ∧ z = Complex.exp (-I * (θ z : ℂ)) := by
    simpa only [θ, dif_pos hz] using (harc z hz).choose_spec
  let f : ℂ → ℂ := fun z ↦ (θ z : ℂ)
  have hc := (Matrix.finite_spectrum U).continuousOn f
  refine ⟨cfc f U, ?_, ?_, ?_⟩
  · change star (cfc f U) = cfc f U
    rw [← cfc_star]
    exact cfc_congr fun z _ ↦ by simp [f]
  · intro x hx
    have hspec : (x : ℂ) ∈ spectrum ℂ (cfc f U) := (spectrum.algebraMap_mem_iff ℂ).mpr hx
    rw [cfc_map_spectrum f U hn hc] at hspec
    obtain ⟨z, hz, heq⟩ := hspec
    rw [← Complex.ofReal_injective heq]
    exact (hθ z hz).1
  · rw [← cfc_smul (-I) f U hc, ← CFC.complex_exp_eq_normedSpace_exp,
      ← cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I • f z) U hn
        Complex.continuous_exp.continuousOn (hc.const_smul (-I))]
    conv_rhs => rw [← cfc_id ℂ U]
    exact cfc_congr fun z hz ↦ ((hθ z hz).2).symm

/-- `e^{-iH}` is the functional calculus of `z ↦ e^{-iz}` at a Hermitian `H`. -/
theorem exp_eq_cfc (H : 𝕄) (hH : H.IsHermitian) :
    NormedSpace.exp (-I • H) = cfc (fun z : ℂ ↦ Complex.exp (-I * z)) H := by
  have := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  rw [cfc_comp_const_mul (-I) Complex.exp H Complex.continuous_exp.continuousOn,
    CFC.complex_exp_eq_normedSpace_exp]

/-- The second sentence of the proof of Lemma A.2: as `θ ↦ e^{-iθ}` is injective for `θ ∈ [a, a+w]`,
a Hermitian matrix with spectrum in `[a, a+w]` is determined by its exponential. -/
theorem walk_log_unique {A B : 𝕄} {a w : ℝ} (hw : w < 2 * π)
    (hA : IsHermitian A) (hAw : HasRealSpectrumIn A (Icc a (a + w)))
    (hB : IsHermitian B) (hBw : HasRealSpectrumIn B (Icc a (a + w)))
    (he : NormedSpace.exp (-I • A) = NormedSpace.exp (-I • B)) : A = B := by
  let δ := (2 * π - w) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  apply WalkLeakage.logarithm_unique (α := a - δ) hA hB
  · intro x hx
    exact ⟨(sub_lt_self a hδ).trans_le (hAw hx).1, by
      dsimp only [δ]
      linarith [(hAw hx).2]⟩
  · intro x hx
    exact ⟨(sub_lt_self a hδ).trans_le (hBw hx).1, by
      dsimp only [δ]
      linarith [(hBw hx).2]⟩
  · exact he

end RoundedClocks.WalkLog
