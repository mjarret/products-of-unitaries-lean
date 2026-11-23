/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import RoundedClocks.Definitions

/-! # The rank of a spectral projector (Remark 3.8)

The spectral projector of a Hermitian `A` for the eigenvalues in a set `S` has rank equal to the
number of eigenvalues of `A` in `S`, counted with multiplicity. Remark 3.8 uses this count to
conclude that `P_s` and `P̃_s` have equal rank.
-/

@[expose] public section

noncomputable section

namespace RoundedClocks

open Classical in
/-- The rank of the spectral projector of a Hermitian `A` for the eigenvalues in `S` is the number
of eigenvalues of `A` in `S`, counted with multiplicity. -/
theorem rank_spectralProjector {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (S : Set ℂ) :
    (spectralProjector A S).rank =
      (Finset.univ.filter (fun j : Fin d => (hA.eigenvalues j : ℂ) ∈ S)).card := by
  classical
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let E := ⨆ z ∈ S, Module.End.eigenspace (T A).toLinearMap z
  let b := hA.eigenvectorBasis.toBasis
  let s := Finset.univ.filter (fun j : Fin d => (hA.eigenvalues j : ℂ) ∈ S)
  -- An orthonormal eigenbasis `b` of `A`: `A bⱼ = λⱼ bⱼ`, so `A` multiplies the `j`th coordinate
  -- of every vector by `λⱼ`.
  have hb (j : Fin d) : T A (b j) = (hA.eigenvalues j : ℂ) • b j := by
    apply WithLp.ofLp_injective
    simpa [T, b, Matrix.ofLp_toEuclideanCLM] using hA.mulVec_eigenvectorBasis j
  have hcoord (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
      b.repr (T A x) j = (hA.eigenvalues j : ℂ) * b.repr x j := by
    have h := (Matrix.isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace x ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)
    simpa [T, b, Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
      Matrix.IsHermitian.eigenvalues₀, OrthonormalBasis.repr_apply_apply] using h
  -- The span of the eigenvectors of `A` with eigenvalues in `S` is the span of the `bⱼ` with
  -- `λⱼ ∈ S`: an eigenvector for `z ∈ S` has zero coordinate along every `bⱼ` with `λⱼ ≠ z`.
  have hspan : E = Submodule.span ℂ (Set.range (fun j : s => b j)) := by
    apply le_antisymm
    · refine iSup_le fun z => iSup_le fun hz => ?_
      intro x hx
      have heig : T A x = z • x := Module.End.mem_eigenspace_iff.mp hx
      rw [← b.sum_repr x]
      apply Submodule.sum_mem
      intro j hj
      by_cases hjs : j ∈ s
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hjs⟩, rfl⟩)
      · have hne : (hA.eigenvalues j : ℂ) ≠ z := by
          intro heq
          exact hjs (by simp [s, heq, hz])
        have hc := hcoord x j
        rw [heig, map_smul] at hc
        have hzj : b.repr x j = 0 := by
          have hp : ((hA.eigenvalues j : ℂ) - z) * b.repr x j = 0 := by
            simpa [sub_mul] using sub_eq_zero.mpr hc.symm
          exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)
        simp [hzj]
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply Submodule.mem_iSup_of_mem (hA.eigenvalues j : ℂ)
      apply Submodule.mem_iSup_of_mem ((Finset.mem_filter.mp j.property).2)
      exact Module.End.mem_eigenspace_iff.mpr (hb j)
  have hmap : (T (spectralProjector A S)).toLinearMap = E.starProjection.toLinearMap := by
    change (T (T.symm E.starProjection)).toLinearMap = _
    rw [T.apply_symm_apply]
  -- The rank of the projector is the dimension of its range, which the `bⱼ` with `λⱼ ∈ S` span.
  calc
    (spectralProjector A S).rank =
        Module.finrank ℂ (LinearMap.range (T (spectralProjector A S)).toLinearMap) := by
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        Matrix.toEuclideanLin_eq_toLin_orthonormal]
      exact Matrix.rank_eq_finrank_range_toLin _ _ _
    _ = Module.finrank ℂ E := by rw [hmap, Submodule.range_starProjection]
    _ = Fintype.card s := by
      rw [hspan]
      exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)
    _ = s.card := Fintype.card_coe s

end RoundedClocks
