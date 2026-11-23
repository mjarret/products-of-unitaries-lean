/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.Basic

/-! # `e^{-iH}` in an eigenbasis of `H`

For an orthonormal eigenbasis `ψ_j` of a Hermitian `H` with eigenvalues `λ_j`,
`ψ_j† H v = λ_j ψ_j† v` (`walk_inner_eigenvectorBasis`) and
`ψ_j† e^{-iH} v = e^{-iλ_j} ψ_j† v` (`walk_inner_phase_eigenvectorBasis`). The proof of
Theorem 4.7 uses these for the uniqueness of the logarithm and for the endpoint projectors.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝔼" => EuclideanSpace ℂ (Fin d)
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- Vectors with equal coordinates `b_j† x = b_j† y` in an orthonormal basis `b` are equal. -/
theorem walk_ext_basis (b : OrthonormalBasis (Fin d) ℂ 𝔼) {x y : 𝔼}
    (h : ∀ j, ⟪b j, x⟫_ℂ = ⟪b j, y⟫_ℂ) : x = y := by
  exact InnerProductSpace.ext_inner_left_basis b.toBasis (by simpa using h)

/-- `ψ_j† H v = λ_j ψ_j† v` for an eigenbasis `ψ_j` of a Hermitian `H` with eigenvalues `λ_j`. -/
theorem walk_inner_eigenvectorBasis {H : 𝕄} (hH : H.IsHermitian)
    (j : Fin d) (v : 𝔼) :
    ⟪hH.eigenvectorBasis j, 𝒯 H v⟫_ℂ =
      (hH.eigenvalues j : ℂ) * ⟪hH.eigenvectorBasis j, v⟫_ℂ := by
  have h := (Matrix.isHermitian_iff_isSymmetric.1 hH).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace v ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)
  simpa [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
    Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.repr_apply_apply] using h

/-- The map `X ↦ X v` from matrices to vectors, for a fixed vector `v`, is continuous and
linear. -/
def walk_evalCLM (v : 𝔼) : 𝕄 →L[ℂ] 𝔼 :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.applyₗ v) ∘ₗ ContinuousLinearMap.coeLM ℂ ∘ₗ
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearMap)

/-- `walk_evalCLM v X = X v`. -/
theorem walk_evalCLM_apply (v : 𝔼) (X : 𝕄) : walk_evalCLM v X = 𝒯 X v := rfl

/-- The exponential series `e^{zX} = Σ_n (z^n/n!) X^n`. -/
theorem walk_hasSum_exp_smul (X : 𝕄) (z : ℂ) :
    HasSum (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ * z ^ n) • X ^ n)
      (NormedSpace.exp (z • X)) := by
  simpa [smul_pow, smul_smul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z • X)

/-- The exponential series `e^z = Σ_n z^n/n!`. -/
theorem walk_hasSum_exp_scalar (z : ℂ) :
    HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ * z ^ n) (Complex.exp z) := by
  simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z

/-- `ψ_j† e^{-iH} v = e^{-iλ_j} ψ_j† v` for an eigenbasis `ψ_j` of a Hermitian `H` with
eigenvalues `λ_j`, from the exponential series. -/
theorem walk_inner_phase_eigenvectorBasis {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (j : Fin d) (v : EuclideanSpace ℂ (Fin d)) :
    ⟪hH.eigenvectorBasis j,
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (NormedSpace.exp (-Complex.I • H)) v⟫_ℂ =
      Complex.exp (-Complex.I * (hH.eigenvalues j : ℂ)) *
        ⟪hH.eigenvectorBasis j, v⟫_ℂ := by
  have hp (n : ℕ) (u : 𝔼) :
      ⟪hH.eigenvectorBasis j, 𝒯 (H ^ n) u⟫_ℂ =
        (hH.eigenvalues j : ℂ) ^ n * ⟪hH.eigenvectorBasis j, u⟫_ℂ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, ContinuousLinearMap.mul_apply,
        walk_inner_eigenvectorBasis hH j, ih, pow_succ]
      ring
  let L : 𝕄 →L[ℂ] ℂ := (innerSL ℂ (hH.eigenvectorBasis j)).comp (walk_evalCLM v)
  have hs := L.hasSum (walk_hasSum_exp_smul H (-Complex.I))
  have ht := (walk_hasSum_exp_scalar (-Complex.I * (hH.eigenvalues j : ℂ))).mul_right
    ⟪hH.eigenvectorBasis j, v⟫_ℂ
  have he : L (NormedSpace.exp (-Complex.I • H)) =
      Complex.exp (-Complex.I * (hH.eigenvalues j : ℂ)) *
        ⟪hH.eigenvectorBasis j, v⟫_ℂ := by
    apply HasSum.unique (hs.congr_fun fun n ↦ ?_) ht
    simp only [L, ContinuousLinearMap.comp_apply, map_smul, walk_evalCLM_apply,
      innerSL_apply_apply, smul_eq_mul, hp, mul_pow]
    ring
  simpa only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    walk_evalCLM_apply] using he

end RoundedClocks
