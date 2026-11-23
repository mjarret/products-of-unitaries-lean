/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.Spectral
public import RoundedClocks.UnitSteps.ExponentialCoordinates
public import RoundedClocks.UnitSteps.TruncatedProductBounds
public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-! # Endpoint projectors and phases

Corollary 4.7 identifies the spectral projectors at the endpoints and matches their phase factors
with the Hermitian logarithm.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

/-- A selected-eigenspace projector keeps exactly the selected basis vectors. -/
theorem walk_starProjection_basis
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (ev : Fin d → ℂ)
    (T : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) (S : Set ℂ)
    (hdiag : ∀ j v, ⟪b j, T v⟫_ℂ = ev j * ⟪b j, v⟫_ℂ) (j : Fin d) :
    (⨆ z ∈ S, Module.End.eigenspace T.toLinearMap z).starProjection (b j) =
      if ev j ∈ S then b j else 0 := by
  classical
  let E : Submodule ℂ (EuclideanSpace ℂ (Fin d)) := ⨆ z ∈ S, Module.End.eigenspace T.toLinearMap z
  have hvec (j : Fin d) : T (b j) = ev j • b j := by
    apply walk_ext_basis b
    intro k
    rw [hdiag, inner_smul_right]
    simp only [orthonormal_iff_ite.mp b.orthonormal]
    by_cases hkj : k = j <;> simp [hkj]
  have hproj (j : Fin d) : E.starProjection (b j) =
      if ev j ∈ S then b j else 0 := by
    by_cases hj : ev j ∈ S
    · rw [if_pos hj]
      apply Submodule.starProjection_eq_self_iff.mpr
      have hle : Module.End.eigenspace T.toLinearMap (ev j) ≤ E :=
        le_iSup_of_le (ev j) (le_iSup_of_le hj le_rfl)
      exact hle (Module.End.mem_eigenspace_iff.mpr (hvec j))
    · rw [if_neg hj]
      apply (Submodule.starProjection_apply_eq_zero_iff E).mpr
      have hker : E ≤ LinearMap.ker (innerSL ℂ (b j)).toLinearMap := by
        refine iSup_le fun z ↦ iSup_le fun hz ↦ ?_
        intro u hu
        change ⟪b j, u⟫_ℂ = 0
        have he := congrArg (fun u : (EuclideanSpace ℂ (Fin d)) ↦ ⟪b j, u⟫_ℂ)
          (Module.End.mem_eigenspace_iff.mp hu)
        change ⟪b j, T u⟫_ℂ = ⟪b j, z • u⟫_ℂ at he
        rw [hdiag, inner_smul_right] at he
        by_contra hn
        have hzj := mul_right_cancel₀ hn he
        exact hj (hzj.symm ▸ hz)
      apply (Submodule.mem_orthogonal' E (b j)).mpr
      intro u hu
      exact hker hu
  exact hproj j

/-- In one open turn, the phase arc and real interval select the same projector. -/
theorem walk_arcBandProjector_exp {H : 𝕄} (hH : IsHermitian H) {α β : ℝ}
    (hβ : β < α + 2 * Real.pi)
    (hturn : ∀ j, hH.eigenvalues j ∈ Set.Ioo α (α + 2 * Real.pi)) :
    arcBandProjector (exp (-I • H)) α β = bandProjector H α β := by
  classical
  unfold arcBandProjector bandProjector spectralProjector
  apply congrArg (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
  apply ContinuousLinearMap.coe_injective
  apply hH.eigenvectorBasis.toBasis.ext
  intro j
  change (⨆ z ∈ arc α β, Module.End.eigenspace
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (exp (-I • H))).toLinearMap z
    ).starProjection (hH.eigenvectorBasis j) =
      (⨆ z ∈ interval α β, Module.End.eigenspace
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) H).toLinearMap z
      ).starProjection (hH.eigenvectorBasis j)
  rw [walk_starProjection_basis hH.eigenvectorBasis
      (fun j ↦ Complex.exp (-I * (hH.eigenvalues j : ℂ))) _ _
      (walk_inner_phase_eigenvectorBasis hH),
    walk_starProjection_basis hH.eigenvectorBasis
      (fun j ↦ (hH.eigenvalues j : ℂ)) _ _ (walk_inner_eigenvectorBasis hH)]
  have hi : (hH.eigenvalues j : ℂ) ∈ interval α β ↔
      hH.eigenvalues j ∈ Set.Ioo α β := by
    simp [interval]
  rw [WalkLeakageSpectrum.phase_mem_arc_iff hβ (hturn j), hi]

/-- An arc spectral projector is orthogonal, without a normality assumption. -/
theorem walk_arcProjector_isOrthogonal (W : 𝕄) (a b : ℝ) :
    IsOrthogonalProjector (arcBandProjector W a b) := by
  exact spectralProjector_isOrthogonal W (arc a b)

/-- Every scalar exponential of a Hermitian matrix commutes with its band projector. -/
theorem walk_phase_commute_bandProjector {H : 𝕄} (hH : IsHermitian H)
    (a b : ℝ) (z : ℂ) : Commute (exp (z • H)) (bandProjector H a b) := by
  exact ((spectralProjector_commute hH (interval a b)).symm.smul_left z).exp_left

/-- The final negative half-step phase is unitary. -/
theorem walk_negative_halfPhase_isUnitary {H : 𝕄} (hH : IsHermitian H) :
    IsUnitary (exp (-(I / 2) • H)) := by
  have he : -(I / 2) • H = ((1 / 2 : ℝ) : ℂ) • (-I • H) := by module
  rw [he]
  exact phase_isUnitary hH (1 / 2)

/-- The initial positive half-step phase is unitary. -/
theorem walk_positive_halfPhase_isUnitary {H : 𝕄} (hH : IsHermitian H) :
    IsUnitary (exp ((I / 2) • H)) := by
  have he : (I / 2) • H = ((-(1 / 2) : ℝ) : ℂ) • (-I • H) := by module
  rw [he]
  exact phase_isUnitary hH (-(1 / 2))

end RoundedClocks
