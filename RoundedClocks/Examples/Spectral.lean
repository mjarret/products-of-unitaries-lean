/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import RoundedClocks.Definitions

/-! Spectral-projector facts used by the examples. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set
open NormedSpace (exp)
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : Nat}

local notation "Mat" => Matrix (Fin d) (Fin d) Complex

/-- A spectral projector is an orthogonal projector. -/
theorem spectralProjector_isOrthogonal (A : Mat) (S : Set Complex) :
    IsOrthogonalProjector (spectralProjector A S) := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex)
  let E := ⨆ z ∈ S, Module.End.eigenspace (T A).toLinearMap z
  have hE : IsStarProjection E.starProjection := isStarProjection_starProjection
  have hmap : Matrix.toEuclideanCLM.toRingEquiv (spectralProjector A S) =
      E.starProjection := by
    change T (T.symm E.starProjection) = E.starProjection
    exact T.apply_symm_apply E.starProjection
  constructor
  · apply Matrix.toEuclideanCLM.injective
    rw [map_mul, hmap]
    exact hE.isIdempotentElem.eq
  · apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    change IsSelfAdjoint (T.symm E.starProjection)
    exact (isSelfAdjoint_starProjection E).map T.symm

/-- A spectral projector of a Hermitian matrix commutes with that matrix. -/
theorem spectralProjector_commute {A : Mat} (hA : IsHermitian A) (S : Set Complex) :
    Commute (spectralProjector A S) A := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := Complex)
  let E := ⨆ z ∈ S, Module.End.eigenspace (T A).toLinearMap z
  have hEinvariant : ∀ {v : EuclideanSpace Complex (Fin d)}, v ∈ E → T A v ∈ E := by
    intro v hv
    refine Submodule.iSup_induction
      (motive := fun v ↦ T A v ∈ E)
      (fun z : Complex ↦ ⨆ _ : z ∈ S, Module.End.eigenspace (T A).toLinearMap z)
      hv ?_ (by simp) ?_
    · intro z v hv
      refine Submodule.iSup_induction
        (motive := fun v ↦ T A v ∈ E)
        (fun _ : z ∈ S ↦ Module.End.eigenspace (T A).toLinearMap z)
        hv ?_ (by simp) ?_
      · intro hz v hvz
        apply Submodule.mem_iSup_of_mem z
        apply Submodule.mem_iSup_of_mem hz
        rw [Module.End.mem_eigenspace_iff] at hvz ⊢
        calc
          T A (T A v) = T A (z • v) := congrArg (T A) hvz
          _ = z • T A v := map_smul (T A) z v
      · intro x y hx hy
        simpa only [map_add] using E.add_mem hx hy
    · intro x y hx hy
      simpa only [map_add] using E.add_mem hx hy
  have hAself : IsSelfAdjoint (T A) :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map Matrix.toEuclideanCLM
  have horthogonal : ∀ {v : EuclideanSpace Complex (Fin d)},
      v ∈ Submodule.orthogonal E → T A v ∈ Submodule.orthogonal E := by
    intro v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    have hsym := hAself.isSymmetric u v
    simp only [ContinuousLinearMap.coe_coe] at hsym
    rw [← hsym]
    exact hv (T A u) (hEinvariant hu)
  have hmap : Matrix.toEuclideanCLM.toRingEquiv (spectralProjector A S) =
      E.starProjection := by
    change T (T.symm E.starProjection) = E.starProjection
    exact T.apply_symm_apply E.starProjection
  apply Matrix.toEuclideanCLM.injective
  rw [map_mul, map_mul, hmap]
  apply ContinuousLinearMap.ext
  intro x
  have hPx : E.starProjection x ∈ E := E.starProjection_apply_mem x
  have hxperp : x - E.starProjection x ∈ Submodule.orthogonal E :=
    E.sub_starProjection_mem_orthogonal x
  have hAPx : T A (E.starProjection x) ∈ E := hEinvariant hPx
  have hAperp : T A (x - E.starProjection x) ∈ Submodule.orthogonal E :=
    horthogonal hxperp
  calc
    E.starProjection (T A x) = E.starProjection
        (T A (E.starProjection x) + T A (x - E.starProjection x)) := by
          apply congrArg E.starProjection
          rw [map_sub]
          module
    _ = E.starProjection (T A (E.starProjection x)) +
        E.starProjection (T A (x - E.starProjection x)) := map_add _ _ _
    _ = T A (E.starProjection x) + 0 := by
      rw [E.starProjection_eq_self_iff.mpr hAPx,
        (Submodule.starProjection_apply_eq_zero_iff E).mpr hAperp]
    _ = T A (E.starProjection x) := add_zero _

/-- Removing one point from the unit interval leaves a set dense in that interval. -/
theorem crossing_interval_dense (s₀ : Real) :
    Icc (0 : Real) 1 ⊆ closure (Icc (0 : Real) 1 \ {s₀}) := by
  have hinner : Ioo (0 : Real) 1 ⊆ closure (Icc (0 : Real) 1 \ {s₀}) := by
    apply ((dense_compl_singleton s₀).open_subset_closure_inter isOpen_Ioo).trans
    apply closure_mono
    intro s hs
    exact ⟨⟨hs.1.1.le, hs.1.2.le⟩, hs.2⟩
  have hclosed := closure_minimal hinner isClosed_closure
  simpa only [closure_Ioo (show (0 : Real) ≠ 1 by norm_num)] using hclosed

/-- A continuous spectral projector away from one point remains an orthogonal projector
commuting with the Hamiltonian at that point. -/
theorem crossing_projectors_extend (H P : Real → Mat) (hH : IsTimeDepHamiltonian H)
    (hcH : ContinuousOn H (Icc (0 : Real) 1)) (hcP : IsContinuousFamily P) (s₀ : Real)
    (hP : ∀ s ∈ Icc (0 : Real) 1, s ≠ s₀ → IsOneEigenvalueProjector (P s) (H s)) :
    ∀ s ∈ Icc (0 : Real) 1, IsOrthogonalProjector (P s) ∧ Commute (P s) (H s) := by
  have hoff : ∀ s ∈ Icc (0 : Real) 1 \ {s₀},
      IsOrthogonalProjector (P s) ∧ Commute (P s) (H s) := by
    intro s hs
    obtain ⟨mu, heq⟩ := hP s hs.1 (by simpa using hs.2)
    rw [IsSpectralProjector] at heq
    rw [heq]
    exact ⟨spectralProjector_isOrthogonal _ _,
      spectralProjector_commute (hH s hs.1) _⟩
  have hsub : Icc (0 : Real) 1 \ {s₀} ⊆ Icc (0 : Real) 1 := diff_subset
  have hid : EqOn (fun s ↦ P s * P s) P (Icc (0 : Real) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isIdempotentElem.eq)
      (hcP.mul hcP) hcP hsub (crossing_interval_dense s₀)
  have hstar : EqOn (fun s ↦ star (P s)) P (Icc (0 : Real) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isSelfAdjoint.star_eq)
      hcP.star hcP hsub (crossing_interval_dense s₀)
  have hcomm : EqOn (fun s ↦ P s * H s) (fun s ↦ H s * P s)
      (Icc (0 : Real) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).2.eq)
      (hcP.mul hcH) (hcH.mul hcP) hsub (crossing_interval_dense s₀)
  intro s hs
  exact ⟨⟨hid hs, hstar hs⟩, hcomm hs⟩

/-- The exponential `exp (-iuG)` of a Hermitian matrix is unitary. -/
theorem exp_neg_I_smul_isUnitary {G : Mat} (hG : IsHermitian G) (u : Real) :
    IsUnitary (exp ((u : Complex) • (-I • G))) := by
  let +nondep : NormedAlgebra ℚ Mat := .restrictScalars ℚ Complex Mat
  have hI : -I ∈ skewAdjoint Complex := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact Unitary.star_mul_self_of_mem <|
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem u (hG.isSelfAdjoint.smul_mem_skewAdjoint hI))

end RoundedClocks
