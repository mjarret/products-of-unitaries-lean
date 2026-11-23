/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.WalkLeakage.Band

/-! # The continuous logarithm of Theorem 4.7

First sentence of the proof of Theorem 4.7: "As `α` and `W` are continuous,
`H = α + π + i Log(e^{i(α+π)} W)` is continuous, for the principal logarithm `Log`." This `H` is
Hermitian, `e^{-iH} = W`, and `H(s)` has spectrum in `(α(s), α(s) + 2π)`
(`exists_continuous_logarithm`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Complex Set Real NormedSpace Filter
noncomputable section
namespace RoundedClocks
namespace WalkLeakage

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `e^{ic}` has modulus one for real `c`. -/
private theorem phase_unitary (c : ℝ) : Complex.exp (I*(c:ℂ)) ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
    Complex.norm_exp_I_mul_ofReal]
  norm_num

/-- `e^{-i(c - A)} = e^{-ic} e^{iA}` for real `c`. -/
private theorem evol_scalar_sub (c : ℝ) (A : 𝕄) :
    NormedSpace.exp (-I • (((c:ℂ) • 1)-A)) = Complex.exp (-I*(c:ℂ)) • NormedSpace.exp (I • A) := by
  have he : -I • (((c:ℂ) • (1:𝕄))-A) = algebraMap ℂ 𝕄 (-I*(c:ℂ))+I • A := by
    rw [Algebra.algebraMap_eq_smul_one]; module
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [he,NormedSpace.exp_add_of_commute (Algebra.commutes _ _)]
  rw [← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]

/-- If `α` and the unitary `W` are continuous and `e^{-iα(s)}` is never an eigenvalue of `W(s)`,
then `G = α + π + i Log(e^{i(α+π)} W)`, for the principal logarithm `Log`, is continuous and
Hermitian, `e^{-iG(s)} = W(s)`, and `‖G(s) - (α(s) + π)‖ < π`. -/
theorem continuous_log_of_cut {X : Type*} [TopologicalSpace X] [NeZero d]
    (W : X → unitary 𝕄) (α : X → ℝ) (hW : Continuous W) (hα : Continuous α)
    (hcut : ∀ s, Complex.exp (-I * (α s : ℂ)) ∉ spectrum ℂ (W s : 𝕄)) :
    ∃ G : X → 𝕄, Continuous G ∧ (∀ s, (G s).IsHermitian) ∧
      ∀ s, NormedSpace.exp (-I • G s) = (W s:𝕄) ∧ ‖G s-((α s+π:ℝ):ℂ) • 1‖ < π := by
  -- Step 1: `u = e^{i(α+π)} W` does not have the eigenvalue `-1`, as `e^{-iα}` is not an
  -- eigenvalue of `W`.
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
  -- Step 2: the principal logarithm gives `u = e^{iA}` with `A` continuous, Hermitian, and
  -- `‖A‖ < π`.
  let A : X → selfAdjoint 𝕄 := fun s ↦ Unitary.argSelfAdjoint (u s)
  have hAc : Continuous A := Unitary.continuousOn_argSelfAdjoint.comp_continuous huc hu'
  have hAn : ∀ s, ‖(A s:𝕄)‖ < π := fun s ↦ by
    simpa only [Unitary.openPartialHomeomorph_target,Metric.mem_ball,dist_zero_right,
      AddSubgroupClass.coe_norm] using (Unitary.openPartialHomeomorph (A := 𝕄)).map_source' (hu' s)
  -- Step 3: `G = (α + π) - A` is continuous and Hermitian, and `e^{-iG} = W`.
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
      change NormedSpace.exp (-I • (((α s+π:ℝ):ℂ) • 1-(A s:𝕄))) = _
      rw [evol_scalar_sub,he]
      change Complex.exp (-I*((α s+π:ℝ):ℂ)) • (Complex.exp (I*((α s+π:ℝ):ℂ)) • (W s:𝕄)) = _
      rw [smul_smul, ← Complex.exp_add, show -I*((α s+π:ℝ):ℂ)+I*((α s+π:ℝ):ℂ)=0 by ring,
        Complex.exp_zero, one_smul]
    · rw [show G s-((α s+π:ℝ):ℂ) • 1 = -(A s:𝕄) by dsimp [G]; abel, norm_neg]
      exact hAn s

/-- If `‖G - (α + π)‖ < π`, the spectrum of `G` lies in `(α, α + 2π)`. -/
theorem spectrum_open_turn [NeZero d] {G : 𝕄} {α : ℝ}
    (h : ‖G - ((α + π : ℝ) : ℂ) • 1‖ < π) :
    HasRealSpectrumIn G (Ioo α (α + 2 * π)) := by
  intro x hx
  have hm : x - (α + π) ∈ spectrum ℝ (G - algebraMap ℝ 𝕄 (α + π)) := by
    rw [← spectrum.sub_singleton_eq]
    exact ⟨x, hx, α + π, Set.mem_singleton _, rfl⟩
  have hn := spectrum.norm_le_norm_of_mem hm
  have he : algebraMap ℝ 𝕄 (α + π) = ((α + π : ℝ) : ℂ) • (1 : 𝕄) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (IsScalarTower.algebraMap_smul ℂ (α + π) (1 : 𝕄)).symm
  rw [he, Real.norm_eq_abs] at hn
  have hb := abs_lt.mp (hn.trans_lt h)
  constructor <;> linarith

/-- First sentence of the proof of Theorem 4.7: a continuous unitary family `W` with a band
`{e^{-iθ} : α(s) < θ < β(s)}` has a continuous logarithm `H` with spectrum in
`(α(s), α(s) + 2π)`, namely `H = α + π + i Log(e^{i(α+π)} W)`. -/
theorem exists_continuous_logarithm [NeZero d] {W : ℝ → 𝕄} {α β : ℝ → ℝ}
    (hband : IsArcBandFamily W α β) (hW : IsContinuousFamily W) :
    ∃ H, IsLogarithm W α H ∧ IsContinuousFamily H := by
  classical
  let S := Icc (0 : ℝ) 1
  let V : S → unitary 𝕄 := fun s ↦ ⟨W s, (hband.isArcBand s.property).isUnitary⟩
  have hc : Continuous V := (continuousOn_iff_continuous_restrict.mp hW).subtype_mk _
  obtain ⟨G, hGc, hGh, hG⟩ := continuous_log_of_cut V
    (fun s ↦ α s) hc (continuousOn_iff_continuous_restrict.mp hband.continuous_left)
    (fun s ↦ (hband.isArcBand s.property).left_notMem)
  let H : ℝ → 𝕄 := fun s ↦ if hs : s ∈ S then G ⟨s, hs⟩ else 0
  have hH (s : S) : H s = G s := by simp [H, s.property]
  refine ⟨H, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s hs
    rw [hH ⟨s, hs⟩]
    exact hGh ⟨s, hs⟩
  · intro s hs
    rw [hH ⟨s, hs⟩]
    exact (hG ⟨s, hs⟩).1
  · intro s hs
    rw [hH ⟨s, hs⟩]
    exact spectrum_open_turn (hG ⟨s, hs⟩).2
  · apply continuousOn_iff_continuous_restrict.mpr
    exact hGc.congr (fun s ↦ (hH s).symm)

end WalkLeakage
end RoundedClocks
