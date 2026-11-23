/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.LogarithmIntegral

/-! # Lemma A.2: equation (A.3) near a point

Fix `s₀ ∈ [0,1]`. The paper multiplies `W` by a constant phase so that `a(s₀) = -w/2`. Here the
phase is `c = e^{iμ}` with `μ = a(s₀) + w/2`, and `V = cW`. For `s` near `s₀`,
`H = μ + i∫₀¹ (V-1) S_u du` with `S_u = (1+u(V-1))⁻¹`, which is the first line of (A.3).
Differentiating twice under the integral gives the second and third lines and shows that `H` is
twice continuously differentiable.
-/

@[expose] public section

open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `e^{iμ} e^{-iH}` is the functional calculus of `z ↦ e^{iμ} e^{-iz}` at a Hermitian `H`. -/
theorem phase_exp_eq_cfc (H : 𝕄) (hH : H.IsHermitian) (μ : ℝ) :
    Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H) =
      cfc (fun z : ℂ ↦ Complex.exp (I * (μ : ℂ)) * Complex.exp (-I * z)) H := by
  rw [exp_eq_cfc H hH, ← cfc_smul (Complex.exp (I * (μ : ℂ))) _ H
    ((Matrix.finite_spectrum H).continuousOn _)]
  rfl

/-- The first line of (A.3) at one point: if the spectrum of the Hermitian `H` lies in `(μ-π, μ+π)`,
then `H = μ + i∫₀¹ (V-1) S_u du` for `V = e^{iμ} e^{-iH}`. -/
theorem walkLogIntegral_phase_recovery {H : 𝕄} {μ : ℝ} (hH : H.IsHermitian)
    (hwin : HasRealSpectrumIn H (Ioo (μ - π) (μ + π))) :
    H = (μ : ℂ) • 1 + I • walkLogIntegral
      (Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H)) := by
  let f : ℂ → ℂ := fun z ↦ Complex.exp (I * (μ : ℂ)) * Complex.exp (-I * z)
  letI : IsStarNormal H := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  have hf := (Matrix.finite_spectrum H).continuousOn f
  have hphase (θ : ℝ) : f (θ : ℂ) = Complex.exp (-I * ((θ - μ : ℝ) : ℂ)) := by
    dsimp [f]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hreal (z : ℂ) (hz : z ∈ spectrum ℂ H) :
      ∃ θ : ℝ, z = (θ : ℂ) ∧ θ ∈ Ioo (μ - π) (μ + π) := by
    have he := IsSelfAdjoint.mem_spectrum_eq_re
      (Matrix.isHermitian_iff_isSelfAdjoint.mp hH) hz
    refine ⟨z.re, he, hwin ?_⟩
    apply (spectrum.algebraMap_mem_iff ℂ).mp
    change (z.re : ℂ) ∈ spectrum ℂ H
    rwa [← he]
  have hslit : spectrum ℂ (cfc f H) ⊆ Complex.slitPlane := by
    rw [cfc_map_spectrum f H (inferInstance : IsStarNormal H) hf]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl, hθ⟩ := hreal z hz
    rw [hphase]
    apply phase_mem_slitPlane
    constructor <;> linarith [hθ.1, hθ.2]
  letI : IsStarNormal (cfc f H) := cfc_predicate f H
  rw [phase_exp_eq_cfc H hH μ, walkLogIntegral_eq_cfc _ hslit,
    ← cfc_comp (R := ℂ) Complex.log f H (inferInstance : IsStarNormal H)
      (((Matrix.finite_spectrum H).image f).continuousOn _) hf,
    ← cfc_smul I _ H ((Matrix.finite_spectrum H).continuousOn _)]
  have hc : (μ : ℂ) • (1 : 𝕄) = cfc (fun _ : ℂ ↦ (μ : ℂ)) H := by
    rw [cfc_const (p := IsStarNormal) (μ : ℂ) H inferInstance]
    exact (Algebra.algebraMap_eq_smul_one (μ : ℂ)).symm
  rw [hc, ← cfc_add H _ _ ((Matrix.finite_spectrum H).continuousOn _)
    ((Matrix.finite_spectrum H).continuousOn _)]
  conv_lhs => rw [← cfc_id' ℂ H]
  apply cfc_congr
  intro z hz
  obtain ⟨θ, rfl, hθ⟩ := hreal z hz
  change (θ : ℂ) = (μ : ℂ) + I * Complex.log (f (θ : ℂ))
  rw [hphase, Complex.log_exp]
  · push_cast
    rw [← mul_assoc, mul_neg, I_mul_I]
    simp
  · simp only [neg_mul, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
    linarith [hθ.2]
  · simp only [neg_mul, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
    linarith [hθ.1]

/-- Equation (A.3) for `s` near `s₀`. On an interval `K` that contains `s₀` and is a neighbourhood
of `s₀` in `[0,1]`, with `μ = a(s₀) + w/2` and `V = e^{iμ} W`: `H = μ + i∫₀¹ (V-1) S_u du` (first
line), this function is `C²`, and its first and second derivatives are `i∫₀¹ S_u V' S_u du` and
`i∫₀¹ (S_u V'' S_u - 2u S_u V' S_u V' S_u) du` (second and third lines). -/
theorem exists_local_walkLogIntegral_contDiffOn {H W : ℝ → 𝕄} {a : ℝ → ℝ} {w : ℝ}
    (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hc : IsC2Family W) (hW : IsUnitaryFamily W 0 1)
    (harc : HasSpectrumInPhaseInterval W a w)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (he : ∀ s ∈ Icc (0 : ℝ) 1, NormedSpace.exp (-I • H s) = W s)
    (hwindow : ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Icc (a s) (a s + w)))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0,
      let K := Icc (max 0 (s₀ - δ)) (min 1 (s₀ + δ))
      let μ := a s₀ + w / 2
      let V := fun s ↦ Complex.exp (I * (μ : ℂ)) • W s
      let D := derivWithin V K
      let E := derivWithin D K
      let F := fun s ↦ (μ : ℂ) • (1 : 𝕄) + I • walkLogIntegral (V s)
      max 0 (s₀ - δ) < min 1 (s₀ + δ) ∧
      K ∈ 𝓝[Icc (0 : ℝ) 1] s₀ ∧ s₀ ∈ K ∧
      ContDiffOn ℝ 2 F K ∧ EqOn H F K ∧
      ContinuousOn (fun s ↦ I • walkLogSecondIntegral (V s) (D s) (E s)) K ∧
      (∀ s ∈ K, HasDerivWithinAt F (I • walkLogFirstIntegral (V s) (D s)) K s) ∧
      (∀ s ∈ K, HasDerivWithinAt (fun t ↦ I • walkLogFirstIntegral (V t) (D t))
        (I • walkLogSecondIntegral (V s) (D s) (E s)) K s) := by
  obtain ⟨ρ, hρ, heρ⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_isUnit_phase_chord hw (ha s₀ hs₀) hW harc)
  let δ := ρ / 2
  have hδ : 0 < δ := half_pos hρ
  let l := max 0 (s₀ - δ)
  let r := min 1 (s₀ + δ)
  let K := Icc l r
  let μ := a s₀ + w / 2
  let V := fun s ↦ Complex.exp (I * (μ : ℂ)) • W s
  have hlr : l < r := by
    dsimp [l, r]
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    constructor <;> constructor <;> linarith [hs₀.1, hs₀.2]
  have hsub : K ⊆ Icc (0 : ℝ) 1 := fun s hs ↦
    ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  have hdist (s : ℝ) (hs : s ∈ K) : dist s s₀ < ρ := by
    rw [Real.dist_eq, abs_lt]
    have hl := (le_max_right _ _).trans hs.1
    have hr := hs.2.trans (min_le_right _ _)
    dsimp [δ] at hl hr
    constructor <;> linarith
  have hu : ∀ s ∈ K, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1)) := by
    intro s hs
    exact (heρ ⟨hdist s hs, hsub hs⟩).2
  have hcV : ContDiffOn ℝ 2 V K := (hc.mono hsub).const_smul _
  obtain ⟨hF, hcont, hd, hdd⟩ := walkLogIntegral_contDiffOn_of_contDiffOn hlr hcV hu
  have hmem : K ∈ 𝓝[Icc (0 : ℝ) 1] s₀ := by
    apply mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith : s₀ - δ < s₀)
        (by linarith : s₀ < s₀ + δ))))
    intro s hs
    exact ⟨max_le hs.1.1 hs.2.1, le_min hs.1.2 hs.2.2⟩
  refine ⟨δ, hδ, hlr, hmem, ?_, contDiffOn_const.add (hF.const_smul I), ?_,
    hcont.const_smul I, ?_, ?_⟩
  · exact ⟨max_le hs₀.1 (by linarith), le_min hs₀.2 (by linarith)⟩
  · intro s hs
    have hwin : HasRealSpectrumIn (H s) (Ioo (μ - π) (μ + π)) := by
      intro θ hθ
      have ht := hwindow s (hsub hs) hθ
      have hb := abs_lt.mp (heρ ⟨hdist s hs, hsub hs⟩).1
      dsimp [μ]
      constructor <;> linarith [ht.1, ht.2]
    have hi := walkLogIntegral_phase_recovery (hH s (hsub hs)) hwin
    rw [he s (hsub hs)] at hi
    exact hi
  · intro s hs
    exact ((hd s hs).const_smul I).const_add _
  · intro s hs
    exact (hdd s hs).const_smul I

/-- `H` is twice continuously differentiable for `s ∈ [0,1]`. -/
theorem walk_log_isC2Family {H W : ℝ → 𝕄} {a : ℝ → ℝ} {w : ℝ}
    (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hc : IsC2Family W) (hW : IsUnitaryFamily W 0 1)
    (harc : HasSpectrumInPhaseInterval W a w)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (he : ∀ s ∈ Icc (0 : ℝ) 1, NormedSpace.exp (-I • H s) = W s)
    (hwindow : ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Icc (a s) (a s + w))) :
    IsC2Family H := by
  intro s hs
  obtain ⟨δ, hδ, hlr, hmem, hsK, hF, hEq, hcont, hd, hdd⟩ :=
    exists_local_walkLogIntegral_contDiffOn hw ha hc hW harc hH he hwindow hs
  exact ((hF s hsK).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
    (mem_of_superset hmem fun t ht ↦ hEq ht) (hEq hsK)

/-- The second and third lines of (A.3) at `s₀`, with `c = e^{i(a(s₀)+w/2)}` and
`S_u = (1+u(cW(s₀)-1))⁻¹`: `H'(s₀) = i∫₀¹ S_u (cW') S_u du` and
`H''(s₀) = i∫₀¹ (S_u (cW'') S_u - 2u S_u (cW') S_u (cW') S_u) du`. -/
theorem walk_log_local_derivatives {H W : ℝ → 𝕄} {a : ℝ → ℝ} {w : ℝ}
    (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hc : IsC2Family W) (hW : IsUnitaryFamily W 0 1)
    (harc : HasSpectrumInPhaseInterval W a w)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (he : ∀ s ∈ Icc (0 : ℝ) 1, NormedSpace.exp (-I • H s) = W s)
    (hwindow : ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Icc (a s) (a s + w))) :
    IsC2Family H ∧ ∀ s₀ ∈ Icc (0 : ℝ) 1,
      let c := Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ))
      ∂H s₀ = I • walkLogFirstIntegral (c • W s₀) (c • ∂W s₀) ∧
      ∂∂H s₀ = I • walkLogSecondIntegral (c • W s₀) (c • ∂W s₀) (c • ∂∂W s₀) := by
  have hcH := walk_log_isC2Family hw ha hc hW harc hH he hwindow
  refine ⟨hcH, ?_⟩
  intro s₀ hs₀ c
  obtain ⟨δ, hδ, hlr, hmem, hsK, hF, hEq, hcont, hd, hdd⟩ :=
    exists_local_walkLogIntegral_contDiffOn hw ha hc hW harc hH he hwindow hs₀
  let K := Icc (max 0 (s₀ - δ)) (min 1 (s₀ + δ))
  let V := fun s ↦ c • W s
  let D := derivWithin V K
  let E := derivWithin D K
  let G := fun s ↦ I • walkLogFirstIntegral (V s) (D s)
  have hsub : K ⊆ Icc (0 : ℝ) 1 := fun s hs ↦
    ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  have huniq := uniqueDiffOn_Icc hlr
  have huniq01 := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)
  have hWd := hc.differentiableOn (by norm_num)
  have hcD : ContDiffOn ℝ 1 (∂W) (Icc (0 : ℝ) 1) :=
    hc.derivWithin huniq01 (by norm_num)
  have hWdd := hcD.differentiableOn (by norm_num)
  -- On `K`, `V' = cW'` and `V'' = cW''`.
  have hD : EqOn D (fun s ↦ c • ∂W s) K := by
    intro s hs
    exact (((hWd s (hsub hs)).hasDerivWithinAt.const_smul c).mono hsub)
      |>.derivWithin (huniq s hs)
  have hE : EqOn E (fun s ↦ c • ∂∂W s) K := by
    intro s hs
    have ht := ((hWdd s (hsub hs)).hasDerivWithinAt.const_smul c).mono hsub
    exact (ht.congr hD (hD hs)).derivWithin (huniq s hs)
  -- The second line of (A.3) on `K`: `H' = i∫₀¹ S_u V' S_u du`.
  have hG : EqOn (∂H) G K := by
    intro s hs
    have hdH := (hd s hs).congr hEq (hEq hs)
    have hlocal := hdH.derivWithin (huniq s hs)
    have hglobal := derivWithin_subset hsub (huniq s hs)
      (hcH.differentiableOn (by norm_num) s (hsub hs))
    exact hglobal.symm.trans hlocal
  have hfirst : ∂H s₀ = G s₀ := hG hsK
  -- The third line of (A.3) at `s₀`.
  have hsecond : ∂∂H s₀ = I • walkLogSecondIntegral (V s₀) (D s₀) (E s₀) := by
    exact (((hdd s₀ hsK).congr hG (hG hsK)).mono_of_mem_nhdsWithin hmem)
      |>.derivWithin (huniq01 s₀ hs₀)
  dsimp [G] at hfirst
  rw [hD hsK] at hfirst hsecond
  rw [hE hsK] at hsecond
  exact ⟨hfirst, hsecond⟩

end RoundedClocks.WalkLog
