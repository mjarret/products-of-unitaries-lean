/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic
public import RoundedClocks.UnitSteps.WalkLeakage.ExponentialCoordinates
public import RoundedClocks.UnitSteps.Basic
public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-! # The endpoint projectors of Theorem 4.7

Proof of Theorem 4.7: "As `W(s) = e^{-iH(s)}`, `P` and `Q` are the spectral projectors of `H(0)`
and `H(1)` for their eigenvalues in `(α(0), β(0))` and `(α(1), β(1))`
(`walk_arcBandProjector_exp`), and they commute with `e^{iH(0)/2}` and `e^{-iH(1)/2}`
(`walk_phase_commute_bandProjector`)."
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

/-- If an orthonormal basis `b_j` diagonalizes `T` with eigenvalues `ev_j`, the spectral projector
of `T` for the eigenvalues in `S` maps `b_j` to itself when `ev_j ∈ S` and to `0` otherwise. -/
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
  change E.starProjection (b j) = if ev j ∈ S then b j else 0
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

/-- If the eigenvalues of a Hermitian `H` lie in `(α, α + 2π)` and `β < α + 2π`, the spectral
projector of `e^{-iH}` for the arc `{e^{-iθ} : α < θ < β}` is the spectral projector of `H` for
its eigenvalues in `(α, β)`. -/
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
  rw [phase_mem_arc_iff hβ (hturn j), hi]

/-- `e^{zH}` commutes with the spectral projector of a Hermitian `H` for its eigenvalues in
`(a, b)`. -/
theorem walk_phase_commute_bandProjector {H : 𝕄} (hH : IsHermitian H)
    (a b : ℝ) (z : ℂ) : Commute (exp (z • H)) (bandProjector H a b) := by
  exact ((spectralProjector_commute hH (interval a b)).symm.smul_left z).exp_left

end RoundedClocks
