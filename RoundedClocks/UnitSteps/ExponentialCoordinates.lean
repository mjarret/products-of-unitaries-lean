/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-! # Eigenbasis coordinates for the exponential

Corollary 4.7 diagonalizes the two Hermitian logarithms in orthonormal eigenbases and compares
their unitary exponentials coordinate by coordinate.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝔼" => EuclideanSpace ℂ (Fin d)
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- Equal coordinates in an orthonormal basis determine equal vectors. -/
theorem walk_ext_basis (b : OrthonormalBasis (Fin d) ℂ 𝔼) {x y : 𝔼}
    (h : ∀ j, ⟪b j, x⟫_ℂ = ⟪b j, y⟫_ℂ) : x = y := by
  rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [h]

/-- A Hermitian matrix multiplies each eigenbasis coordinate by its eigenvalue. -/
theorem walk_inner_eigenvectorBasis {H : 𝕄} (hH : H.IsHermitian)
    (j : Fin d) (v : 𝔼) :
    ⟪hH.eigenvectorBasis j, 𝒯 H v⟫_ℂ =
      (hH.eigenvalues j : ℂ) * ⟪hH.eigenvectorBasis j, v⟫_ℂ := by
  have hsa : IsSelfAdjoint (𝒯 H) := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).map 𝒯
  have hev : 𝒯 H (hH.eigenvectorBasis j) =
      (hH.eigenvalues j : ℂ) • hH.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, hH.mulVec_eigenvectorBasis j,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hsym := hsa.isSymmetric (hH.eigenvectorBasis j) v
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [← hsym, hev, inner_smul_left, Complex.conj_ofReal]

/-- Matrix evaluation at a fixed vector is continuous and complex linear. -/
def walk_evalCLM (v : 𝔼) : 𝕄 →L[ℂ] 𝔼 :=
  LinearMap.mkContinuous
    { toFun := fun X ↦ 𝒯 X v
      map_add' := by intro X Y; simp
      map_smul' := by intro c X; simp }
    ‖v‖ fun X ↦ by
      rw [mul_comm, ← Matrix.l2_opNorm_toEuclideanCLM X]
      exact ContinuousLinearMap.le_opNorm (𝒯 X) v

/-- Continuous matrix evaluation agrees with the matrix operator action. -/
theorem walk_evalCLM_apply (v : 𝔼) (X : 𝕄) : walk_evalCLM v X = 𝒯 X v := rfl

/-- The matrix exponential series separates a scalar multiple from matrix powers. -/
theorem walk_hasSum_exp_smul (X : 𝕄) (z : ℂ) :
    HasSum (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ * z ^ n) • X ^ n)
      (NormedSpace.exp (z • X)) := by
  simpa [NormedSpace.expSeries_apply_eq, smul_pow, smul_smul] using
    NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (z • X)

/-- The scalar exponential series uses the same coefficients as the matrix series. -/
theorem walk_hasSum_exp_scalar (z : ℂ) :
    HasSum (fun n : ℕ ↦ (n.factorial : ℂ)⁻¹ * z ^ n) (Complex.exp z) := by
  simpa only [div_eq_inv_mul, Complex.exp_eq_exp_ℂ] using
    NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) z

/-- Exponentiation multiplies each Hermitian eigenbasis coordinate by its scalar phase. -/
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
