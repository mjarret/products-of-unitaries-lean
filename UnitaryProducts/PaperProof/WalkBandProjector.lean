/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Paper.SpectralWindow
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Spectral.SinTheta

/-! # The unitary window projector in the Hermitian logarithm's eigenbasis -/
@[expose] public section
noncomputable section
open Complex Real Set Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace BigOperators
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝔼" => EuclideanSpace ℂ (Fin d)
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- Exponentiation acts on every coordinate of a Hermitian eigenbasis by the
corresponding scalar phase, including repeated eigenvalues. -/
theorem inner_evol_eigenvectorBasis {A : 𝕄} (hA : A.IsHermitian)
    (j : Fin d) (v : 𝔼) :
    ⟪hA.eigenvectorBasis j, 𝒯 (evol A 1) v⟫_ℂ =
      Complex.exp (-I * (hA.eigenvalues j : ℂ)) * ⟪hA.eigenvectorBasis j, v⟫_ℂ := by
  have hp (n : ℕ) (u : 𝔼) :
      ⟪hA.eigenvectorBasis j, 𝒯 (A ^ n) u⟫_ℂ =
        (hA.eigenvalues j : ℂ) ^ n * ⟪hA.eigenvectorBasis j, u⟫_ℂ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, ContinuousLinearMap.mul_apply,
        isDiag_eigenvectorBasis hA j, ih, pow_succ]
      ring
  let L : 𝕄 →L[ℂ] ℂ := (innerSL ℂ (hA.eigenvectorBasis j)).comp (evalCLM v)
  have hs := L.hasSum (hasSum_exp_smul A (-I))
  have ht := (hasSum_exp_scalar (-I * (hA.eigenvalues j : ℂ))).mul_right
    ⟪hA.eigenvectorBasis j, v⟫_ℂ
  have he : L (NormedSpace.exp (-I • A)) =
      Complex.exp (-I * (hA.eigenvalues j : ℂ)) * ⟪hA.eigenvectorBasis j, v⟫_ℂ := by
    apply HasSum.unique (hs.congr_fun fun n ↦ ?_) ht
    simp only [L, ContinuousLinearMap.comp_apply, map_smul, evalCLM_apply,
      innerSL_apply_apply, smul_eq_mul, hp, mul_pow]
    ring
  simpa only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply, evalCLM_apply,
    evol, one_smul] using he

/-- For an operator diagonal in an orthonormal basis, the orthogonal projector
onto selected eigenspaces keeps exactly the coordinates with selected eigenvalue.
No injectivity of the scalar function is required. -/
theorem starProjection_eigenspaces_eq_proj
    (b : OrthonormalBasis (Fin d) ℂ 𝔼) (ev : Fin d → ℝ) (f : ℝ → ℂ)
    (T : 𝔼 →L[ℂ] 𝔼) (S : Set ℂ)
    (hdiag : ∀ j v, ⟪b j, T v⟫_ℂ = f (ev j) * ⟪b j, v⟫_ℂ) :
    (⨆ z ∈ S, Module.End.eigenspace T.toLinearMap z).starProjection =
      proj b ev {x | f x ∈ S} := by
  classical
  let E : Submodule ℂ 𝔼 := ⨆ z ∈ S, Module.End.eigenspace T.toLinearMap z
  have hvec (j : Fin d) : T (b j) = f (ev j) • b j := by
    apply ext_basis b
    intro k
    rw [hdiag, inner_smul_right]
    simp only [orthonormal_iff_ite.mp b.orthonormal]
    by_cases hkj : k = j <;> simp [hkj]
  have hproj (j : Fin d) : E.starProjection (b j) =
      if f (ev j) ∈ S then b j else 0 := by
    by_cases hj : f (ev j) ∈ S
    · rw [if_pos hj]
      apply Submodule.starProjection_eq_self_iff.mpr
      have hle : Module.End.eigenspace T.toLinearMap (f (ev j)) ≤ E :=
        le_iSup_of_le (f (ev j)) (le_iSup_of_le hj le_rfl)
      exact hle (Module.End.mem_eigenspace_iff.mpr (hvec j))
    · rw [if_neg hj]
      apply (Submodule.starProjection_apply_eq_zero_iff E).mpr
      have hker : E ≤ LinearMap.ker (innerSL ℂ (b j)).toLinearMap := by
        refine iSup_le fun z ↦ iSup_le fun hz ↦ ?_
        intro u hu
        change ⟪b j, u⟫_ℂ = 0
        have he := congrArg (fun u : 𝔼 ↦ ⟪b j, u⟫_ℂ)
          (Module.End.mem_eigenspace_iff.mp hu)
        change ⟪b j, T u⟫_ℂ = ⟪b j, z • u⟫_ℂ at he
        rw [hdiag, inner_smul_right] at he
        by_contra hn
        have hzj := mul_right_cancel₀ hn he
        exact hj (hzj.symm ▸ hz)
      apply (Submodule.mem_orthogonal' E (b j)).mpr
      intro u hu
      exact hker hu
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro j
  change E.starProjection (b j) = proj b ev {x | f x ∈ S} (b j)
  rw [hproj]
  apply ext_basis b
  intro k
  rw [inner_proj]
  simp only [Set.mem_setOf_eq]
  by_cases hj : f (ev j) ∈ S
  · rw [if_pos hj]
    by_cases hkj : k = j
    · subst k; rw [if_pos hj]
    · simp [orthonormal_iff_ite.mp b.orthonormal, hkj]
  · rw [if_neg hj]
    by_cases hkj : k = j
    · subst k; simp [hj]
    · simp [orthonormal_iff_ite.mp b.orthonormal, hkj]

/-- The endpoint projector of Definition 2.5 for a unitary exponential is the
Hermitian spectral projector selecting exactly its phases in the stated arc.
This equality retains phase coincidences and needs no choice of logarithm branch. -/
theorem spectralWindowProjector_evol {A : 𝕄} (hA : A.IsHermitian) (α β : ℝ) :
    Paper.spectralWindowProjector true (evol A 1) α β =
      specProj hA {x : ℝ | ∃ θ ∈ Ioo α β,
        Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ))} := by
  unfold Paper.spectralWindowProjector specProj
  apply congrArg (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
  have hp := starProjection_eigenspaces_eq_proj hA.eigenvectorBasis hA.eigenvalues
    (fun x : ℝ ↦ Complex.exp (-I * (x : ℂ))) (𝒯 (evol A 1))
    (Paper.spectralWindowSet true α β) (inner_evol_eigenvectorBasis hA)
  simpa only [Paper.spectralWindowSet, Bool.true_eq, ↓reduceIte, Set.mem_image,
    Set.mem_setOf_eq] using hp

end UnitaryProducts.PaperProof
