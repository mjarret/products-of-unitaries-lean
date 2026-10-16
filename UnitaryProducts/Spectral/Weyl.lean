/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.SinTheta

/-!
# Weyl's inequality

## Declarations

- `abs_eigenvalues_sub_le`
- `abs_eigenvalues₀_sub_le`
- `eigenvalues_sortIdx`
- `eigenvalues₀_sub_le`
- `hasGap_of_norm_sub_le`
- `norm_sq_sum_smul_eq`
- `re_inner_sum_smul_eq`
- `sortIdx`
- `toEuclideanCLM_eigenvectorBasis`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator InnerProductSpace
open Finset Matrix Module

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
local notation "𝔼" => EuclideanSpace ℂ (Fin d)

section Rayleigh

variable {ι : Type*} [Fintype ι]

/-- `‖∑ cᵢ wᵢ‖² = ∑ |cᵢ|²` for an orthonormal family. -/
theorem norm_sq_sum_smul_eq {w : ι → 𝔼} (hw : Orthonormal ℂ w) (c : ι → ℂ) :
    ‖∑ i, c i • w i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, hw.inner_sum c c univ, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- The quadratic form of `T` on `∑ cᵢ wᵢ`, when `T wᵢ = μᵢ wᵢ`: `∑ μᵢ |cᵢ|²`. -/
theorem re_inner_sum_smul_eq {w : ι → 𝔼} (hw : Orthonormal ℂ w) {μ : ι → ℝ} {T : 𝔼 →L[ℂ] 𝔼}
    (hT : ∀ i, T (w i) = ((μ i : ℝ) : ℂ) • w i) (c : ι → ℂ) :
    RCLike.re ⟪∑ i, c i • w i, T (∑ i, c i • w i)⟫_ℂ = ∑ i, μ i * ‖c i‖ ^ 2 := by
  have hTx : T (∑ i, c i • w i) = ∑ i, (c i * ((μ i : ℝ) : ℂ)) • w i := by
    rw [map_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hT i, smul_smul]
  rw [hTx, hw.inner_sum c (fun i ↦ c i * ((μ i : ℝ) : ℂ)) univ, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Rayleigh

/-- Eigenvectors of a Hermitian matrix, as eigenvectors of the operator `𝒯 A`. -/
theorem toEuclideanCLM_eigenvectorBasis {A : 𝕄} (hA : A.IsHermitian) (j : Fin d) :
    𝒯 A (hA.eigenvectorBasis j) = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j := by
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, hA.mulVec_eigenvectorBasis j,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The re-indexing behind `Matrix.IsHermitian.eigenvalues`: sorted position to matrix index. -/
noncomputable def sortIdx (d : ℕ) : Fin (Fintype.card (Fin d)) ≃ Fin d :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- Mathlib's `eigenvalues` at `sortIdx d j` is the `j`-th sorted eigenvalue `eigenvalues₀ j`. -/
theorem eigenvalues_sortIdx {A : 𝕄} (hA : A.IsHermitian) (j : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues (sortIdx d j) = hA.eigenvalues₀ j :=
  congrArg hA.eigenvalues₀ ((sortIdx d).symm_apply_apply j)

/-- **Weyl, one side.**  `λ_k(A) − λ_k(B) ≤ ‖A − B‖` for the sorted eigenvalues. -/
theorem eigenvalues₀_sub_le {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues₀ k - hB.eigenvalues₀ k ≤ ‖A - B‖ := by
  classical
  -- the span of the first `k+1` eigenvectors of `A` and of the last `d−k` eigenvectors of `B`
  let wU : Finset.Iic k → 𝔼 := fun j ↦ hA.eigenvectorBasis (sortIdx d j)
  let wW : Finset.Ici k → 𝔼 := fun j ↦ hB.eigenvectorBasis (sortIdx d j)
  have hwU : Orthonormal ℂ wU :=
    hA.eigenvectorBasis.orthonormal.comp _ ((sortIdx d).injective.comp Subtype.val_injective)
  have hwW : Orthonormal ℂ wW :=
    hB.eigenvectorBasis.orthonormal.comp _ ((sortIdx d).injective.comp Subtype.val_injective)
  let U : Submodule ℂ 𝔼 := Submodule.span ℂ (Set.range wU)
  let W : Submodule ℂ 𝔼 := Submodule.span ℂ (Set.range wW)
  have hU : finrank ℂ U = k + 1 := by
    rw [finrank_span_eq_card hwU.linearIndependent, Fintype.card_coe, Fin.card_Iic]
  have hW : finrank ℂ W = Fintype.card (Fin d) - k := by
    rw [finrank_span_eq_card hwW.linearIndependent, Fintype.card_coe, Fin.card_Ici]
  -- they meet nontrivially
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
  have hle : finrank ℂ ↥(U ⊔ W) ≤ finrank ℂ 𝔼 := Submodule.finrank_le _
  rw [finrank_euclideanSpace] at hle
  have hne : U ⊓ W ≠ ⊥ := fun h0 ↦ by
    rw [h0, finrank_bot, hU, hW] at hsum; have := k.isLt; omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨cU, hcU⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Submodule.mem_inf.mp hx).1
  obtain ⟨cW, hcW⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (Submodule.mem_inf.mp hx).2
  -- the two Rayleigh bounds
  have hTU : ∀ j : Finset.Iic k, 𝒯 A (wU j) = ((hA.eigenvalues₀ j : ℝ) : ℂ) • wU j := fun j ↦ by
    rw [← eigenvalues_sortIdx hA]; exact toEuclideanCLM_eigenvectorBasis hA (sortIdx d j)
  have hTW : ∀ j : Finset.Ici k, 𝒯 B (wW j) = ((hB.eigenvalues₀ j : ℝ) : ℂ) • wW j := fun j ↦ by
    rw [← eigenvalues_sortIdx hB]
    exact toEuclideanCLM_eigenvectorBasis hB (sortIdx d j)
  have h1 : hA.eigenvalues₀ k * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, 𝒯 A x⟫_ℂ := by
    rw [← hcU, re_inner_sum_smul_eq hwU hTU, norm_sq_sum_smul_eq hwU, mul_sum]
    exact sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone (Finset.mem_Iic.mp j.2)) (sq_nonneg _)
  have h2 : RCLike.re ⟪x, 𝒯 B x⟫_ℂ ≤ hB.eigenvalues₀ k * ‖x‖ ^ 2 := by
    rw [← hcW, re_inner_sum_smul_eq hwW hTW, norm_sq_sum_smul_eq hwW, mul_sum]
    exact sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (hB.eigenvalues₀_antitone (Finset.mem_Ici.mp j.2)) (sq_nonneg _)
  -- the difference is controlled by the operator norm
  have h3 : RCLike.re ⟪x, 𝒯 A x⟫_ℂ - RCLike.re ⟪x, 𝒯 B x⟫_ℂ ≤ ‖A - B‖ * ‖x‖ ^ 2 := by
    rw [← map_sub, ← inner_sub_right, show 𝒯 A x - 𝒯 B x = 𝒯 (A - B) x by
      rw [map_sub, ContinuousLinearMap.sub_apply]]
    calc RCLike.re ⟪x, 𝒯 (A - B) x⟫_ℂ ≤ ‖⟪x, 𝒯 (A - B) x⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖𝒯 (A - B) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖𝒯 (A - B)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((𝒯 (A - B)).le_opNorm x) (norm_nonneg x)
      _ = ‖A - B‖ * ‖x‖ ^ 2 := by rw [Matrix.l2_opNorm_toEuclideanCLM]; ring
  exact le_of_mul_le_mul_right (by rw [sub_mul]; linarith) (pow_pos (norm_pos_iff.mpr hx0) 2)

/-- **Weyl's inequality.**  For Hermitian `A`, `B` with eigenvalues sorted in decreasing order,
`|λ_k(A) − λ_k(B)| ≤ ‖A − B‖`. -/
theorem abs_eigenvalues₀_sub_le {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (k : Fin (Fintype.card (Fin d))) :
    |hA.eigenvalues₀ k - hB.eigenvalues₀ k| ≤ ‖A - B‖ :=
  abs_sub_le_iff.mpr ⟨eigenvalues₀_sub_le hA hB k,
    (eigenvalues₀_sub_le hB hA k).trans_eq (norm_sub_rev B A)⟩

/-- Weyl's inequality with Mathlib's indexing of `eigenvalues` by the matrix index (the same
re-indexing of the sorted list for `A` and for `B`). -/
theorem abs_eigenvalues_sub_le {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin d) :
    |hA.eigenvalues i - hB.eigenvalues i| ≤ ‖A - B‖ :=
  abs_eigenvalues₀_sub_le hA hB ((sortIdx d).symm i)

/-- **A gap survives a perturbation.**  If `A` has no eigenvalues in the collar
`c < |λ − m| < c + δ` and `‖A − B‖ ≤ η`, then `B` has none in `c + η < |λ − m| < c + δ − η`:
a gap `δ − 2η` around the window widened by `η`. The separation step of the unnumbered endpoint
projector estimate uses
it (`endpoint_complement_separation`). -/
theorem hasGap_of_norm_sub_le {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {m c δ η : ℝ} (hgap : HasGap hA m c δ) (hη : ‖A - B‖ ≤ η) :
    HasGap hB m (c + η) (δ - 2 * η) := by
  intro i
  have key : |(|hA.eigenvalues i - m|) - (|hB.eigenvalues i - m|)| ≤ η :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans
      (by rw [sub_sub_sub_cancel_right]; exact (abs_eigenvalues_sub_le hA hB i).trans hη)
  rw [abs_le] at key
  exact (hgap i).imp (fun h ↦ by linarith [key.1]) (fun h ↦ by linarith [key.2])

end UnitaryProducts
