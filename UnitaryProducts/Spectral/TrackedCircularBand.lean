/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogarithmConstruction

/-!
# Continuous spectral minima and exponential spectral mapping

## Declarations

- `continuous_spectralBottom`
- `isLeast_spectralBottom`
- `spectralBottom`
- `spectrum_evol_image`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Complex Set Real NormedSpace Filter
noncomputable section
namespace UnitaryProducts
-- `Unitary.argSelfAdjoint` and the C*-algebra spectral lemmas need `CStarAlgebra 𝕄`; the instance
-- is built from the ℓ²-operator-norm instances, so the norm is unchanged.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The least Hermitian eigenvalue, written as a continuous expression in the matrix:
$\|A\| - \|\,\|A\| \cdot 1 - A\|$. This closed form is chosen because it is visibly continuous in
$A$ (`continuous_spectralBottom`); `isLeast_spectralBottom` proves that it is the least eigenvalue
of a Hermitian $A$. The walk transfer (§4.3) uses it for the continuous extreme eigenvalue $l$ of
the logarithm, the endpoint $a = l$ of the spectral arc. For non-Hermitian $A$ the value has no
spectral meaning. -/
def spectralBottom (A : 𝕄) : ℝ := ‖A‖-‖algebraMap ℝ 𝕄 ‖A‖-A‖

/-- `spectralBottom` is continuous. -/
theorem continuous_spectralBottom : Continuous (spectralBottom (d := d)) := by
  unfold spectralBottom
  exact continuous_norm.sub (((continuous_algebraMap ℝ 𝕄).comp continuous_norm).sub
    continuous_id).norm

/-- For Hermitian $A$, `spectralBottom A` is the least point of the real spectrum: the spectrum of
$\|A\| - A$ lies in $[0, \|\,\|A\| - A\|]$ and contains its top end. -/
theorem isLeast_spectralBottom [NeZero d] {A : 𝕄} (hA : A.IsHermitian) :
    IsLeast (spectrum ℝ A) (spectralBottom A) := by
  let D := algebraMap ℝ 𝕄 ‖A‖-A
  have hD : IsSelfAdjoint D :=
    (show IsSelfAdjoint (algebraMap ℝ 𝕄 ‖A‖) from by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (show IsSelfAdjoint ‖A‖ from rfl).smul (show IsSelfAdjoint (1:𝕄) from by simp
        [isSelfAdjoint_iff])).sub
      (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)
  have hnonneg : ∀ y ∈ spectrum ℝ D, 0≤y := by
    intro y hy
    rw [← spectrum.singleton_sub_eq] at hy
    obtain ⟨m,hm,x,hx,rfl⟩ := hy
    have hm' : m=‖A‖ := Set.mem_singleton_iff.mp hm
    rw [hm']
    exact sub_nonneg.mpr ((le_abs_self x).trans (spectrum.norm_le_norm_of_mem hx))
  have hmem : ‖D‖ ∈ spectrum ℝ D := by
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum hD with h | h
    · exact h
    · have hz : ‖D‖=0 := le_antisymm (by linarith [hnonneg _ h]) (norm_nonneg _)
      simpa only [hz,neg_zero] using h
  have hbottom : spectralBottom A ∈ spectrum ℝ A := by
    rw [← spectrum.singleton_sub_eq] at hmem
    obtain ⟨m,hm,x,hx,he⟩ := hmem
    have hm' : m=‖A‖ := Set.mem_singleton_iff.mp hm
    have hx' : spectralBottom A = x := by
      dsimp [spectralBottom]
      dsimp [D] at he
      rw [hm'] at he
      linarith
    exact hx' ▸ hx
  refine ⟨hbottom,?_⟩
  intro x hx
  have hm : ‖A‖-x ∈ spectrum ℝ D := by
    rw [← spectrum.singleton_sub_eq]
    exact ⟨‖A‖,Set.mem_singleton _,x,hx,rfl⟩
  have hb : ‖A‖-x ≤ ‖D‖ := (le_abs_self _).trans (spectrum.norm_le_norm_of_mem hm)
  dsimp [spectralBottom]
  dsimp [D] at hb
  linarith

/-- Spectral mapping for the unit-time evolution: for Hermitian $A$, the spectrum of
$e^{-iA}$ is $\{e^{-i\theta} : \theta \in \operatorname{spec} A\}$. -/
theorem spectrum_evol_image {A : 𝕄} (hA : A.IsHermitian) :
    spectrum ℂ (evol A 1) = (fun θ : ℝ ↦ Complex.exp (-I*(θ:ℂ))) '' spectrum ℝ A := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hn : IsStarNormal A := hsa.isStarNormal
  have he : evol A 1 = cfc (fun z : ℂ ↦ Complex.exp (-I*z)) A := by
    have hh : cfc (fun z : ℂ ↦ Complex.exp (-I*z)) A =
        cfc Complex.exp (cfc (fun z : ℂ ↦ -I*z) A) :=
      cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I*z) A hn
        Complex.continuous_exp.continuousOn (continuousOn_const.mul continuousOn_id)
    rw [evol,one_smul,hh,cfc_const_mul_id (-I) A,CFC.complex_exp_eq_normedSpace_exp]
  rw [he, cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I*z)) A hn
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn]
  rw [← hsa.spectrumRestricts.algebraMap_image,Set.image_image]
  rfl

private theorem phase_unitary (c : ℝ) : Complex.exp (I*(c:ℂ)) ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
    Complex.norm_exp_I_mul_ofReal]
  norm_num


private theorem evol_scalar_sub (c : ℝ) (A : 𝕄) :
    evol (((c:ℂ) • 1)-A) 1 = Complex.exp (-I*(c:ℂ)) • NormedSpace.exp (I • A) := by
  have he : -I • (((c:ℂ) • (1:𝕄))-A) = algebraMap ℂ 𝕄 (-I*(c:ℂ))+I • A := by
    rw [Algebra.algebraMap_eq_smul_one]; module
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol,one_smul,he,NormedSpace.exp_add_of_commute (Algebra.commutes _ _)]
  rw [← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]


/-- A continuously moving cut outside the spectrum selects the continuous open-interval logarithm:
if $e^{-i\alpha(s)}$ is never an eigenvalue of $W(s)$, there is a continuous Hermitian $G$ with
$e^{-iG(s)} = W(s)$ and $\|G(s) - (\alpha(s) + \pi)\| < \pi$, so that the spectrum of $G(s)$ lies
in $(\alpha(s), \alpha(s) + 2\pi)$ (§4.3, "cutting at $\alpha(s)$ selects a logarithm
with spectrum in $(\alpha(s),\alpha(s)+2\pi)$"). -/
theorem continuous_log_of_cut {X : Type*} [TopologicalSpace X] [NeZero d]
    (W : X → unitary 𝕄) (α : X → ℝ) (hW : Continuous W) (hα : Continuous α)
    (hcut : ∀ s, Complex.exp (-I * (α s : ℂ)) ∉ spectrum ℂ (W s : 𝕄)) :
    ∃ G : X → 𝕄, Continuous G ∧ (∀ s, (G s).IsHermitian) ∧
      ∀ s, evol (G s) 1 = (W s:𝕄) ∧ ‖G s-((α s+π:ℝ):ℂ) • 1‖ < π := by
  -- Step 1: rotate by `e^{i(α+π)}`; the cut moves to `-1`, so `u = e^{i(α+π)} W` avoids `-1`.
  let z : X → ℂ := fun s ↦ Complex.exp (I*((α s+π:ℝ):ℂ))
  let u : X → unitary 𝕄 := fun s ↦ ⟨z s • (W s:𝕄),
    Unitary.smul_mem_of_mem (phase_unitary (α s+π)) (W s).property⟩
  have huc : Continuous u := ((Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (hα.add continuous_const)))).smul
      (continuous_subtype_val.comp hW)).subtype_mk _
  have hu : ∀ s, ‖((u s:unitary 𝕄):𝕄)-1‖ < 2 := by
    intro s
    apply (Unitary.norm_sub_one_lt_two_iff (u s).property).mpr
    intro hneg
    have hs : (-1:ℂ) ∈ z s • spectrum ℂ (W s:𝕄) := by
      rwa [← spectrum.smul_eq_smul (z s) (W s:𝕄) (spectrum.nonempty _)]
    obtain ⟨y,hy,he⟩ := hs
    have hz : z s*Complex.exp (-I*(α s:ℂ)) = -1 := by
      dsimp only [z]; rw [← Complex.exp_add]
      convert Complex.exp_pi_mul_I using 1 ; push_cast ; ring_nf
    have hye : y=Complex.exp (-I*(α s:ℂ)) :=
      mul_left_cancel₀ (Complex.exp_ne_zero _) (he.trans hz.symm)
    exact hcut s (hye ▸ hy)
  have hu' : ∀ s, u s ∈ Metric.ball (1:unitary 𝕄) 2 := fun s ↦ by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, OneMemClass.coe_one] using hu s
  -- Step 2: Mathlib's principal logarithm, `u = e^{iA}` with `A` continuous and `‖A‖ < π`.
  let A : X → selfAdjoint 𝕄 := fun s ↦ Unitary.argSelfAdjoint (u s)
  have hAc : Continuous A := Unitary.continuousOn_argSelfAdjoint.comp_continuous huc hu'
  have hAn : ∀ s, ‖(A s:𝕄)‖ < π := fun s ↦ by
    simpa only [Unitary.openPartialHomeomorph_target,Metric.mem_ball,dist_zero_right,
      AddSubgroupClass.coe_norm] using (Unitary.openPartialHomeomorph (A := 𝕄)).map_source' (hu' s)
  -- Step 3: undo the rotation, `G = (α + π) - A`; it is continuous, Hermitian, and `e^{-iG} = W`.
  let G : X → 𝕄 := fun s ↦ ((α s+π:ℝ):ℂ) • 1-(A s:𝕄)
  refine ⟨G, ?_, ?_, ?_⟩
  · exact ((Complex.continuous_ofReal.comp (hα.add continuous_const)).smul continuous_const).sub
      (continuous_subtype_val.comp hAc)
  · refine fun s ↦ Matrix.isHermitian_iff_isSelfAdjoint.mpr (IsSelfAdjoint.sub ?_ (A s).property)
    exact (show IsSelfAdjoint ((α s+π:ℝ):ℂ) from by simp [isSelfAdjoint_iff]).smul
      (show IsSelfAdjoint (1:𝕄) from by simp [isSelfAdjoint_iff])
  · intro s
    refine ⟨?_, ?_⟩
    · have he : NormedSpace.exp (I • (A s:𝕄)) = (u s:𝕄) := by
        exact congrArg (fun v : unitary 𝕄 ↦ (v:𝕄)) (expUnitary_argSelfAdjoint (hu s))
      change evol (((α s+π:ℝ):ℂ) • 1-(A s:𝕄)) 1 = _
      rw [evol_scalar_sub,he]
      change Complex.exp (-I*((α s+π:ℝ):ℂ)) • (Complex.exp (I*((α s+π:ℝ):ℂ)) • (W s:𝕄)) = _
      rw [smul_smul, ← Complex.exp_add, show -I*((α s+π:ℝ):ℂ)+I*((α s+π:ℝ):ℂ)=0 by ring,
        Complex.exp_zero, one_smul]
    · rw [show G s-((α s+π:ℝ):ℂ) • 1 = -(A s:𝕄) by dsimp [G]; abel, norm_neg]
      exact hAn s

end UnitaryProducts
