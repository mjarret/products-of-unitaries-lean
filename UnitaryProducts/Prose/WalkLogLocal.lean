/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsWalks
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local integral proof of Lemma A.2(ii)

## Declarations

- `contDiffOn_two_of_integral_derivatives`
- `continuousOn_integral_rectangle`
- `continuousOn_walkLogSecondIntegrand`
- `exists_local_walkLogIntegral_contDiffOn`
- `exists_uniform_walkLog_distance_and_bound`
- `hasDerivWithinAt_Icc_of_continuous_derivative`
- `isUnit_walkLogChord_of_centered`
- `walkLogFirstIntegral`
- `walkLogIntegral_contDiffOn_of_contDiffOn`
- `walkLogIntegral_contDiffOn_two`
- `walkLogSecondIntegral`
-/


@[expose] public section

open Real Complex Set Filter MeasureTheory UnitaryProducts.Corrector
open scoped Topology Matrix.Norms.L2Operator Pointwise

noncomputable section

namespace UnitaryProducts.Prose

section SpectralDistance

attribute [local instance] matrixCStarAlgebra
open UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2(ii), after (log-integral): on one closed relative neighborhood,
the rotated spectrum is uniformly separated from the cut and the resolvents are
uniformly bounded. Compactness supplies the positive distance without changing constants. -/
theorem exists_uniform_walkLog_distance_and_bound (a : ℝ → ℝ) (w : ℝ)
    (W : ℝ → 𝕄) (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hW : ContinuousOn W (Icc (0 : ℝ) 1)) (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ x ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (x : ℂ)))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, ∃ ε > 0, ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, |s - s₀| ≤ δ →
      (∀ z ∈ spectrum ℂ (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s),
        ∀ x : ℝ, x ≤ 0 → ε ≤ ‖z - (x : ℂ)‖) ∧
      (spectrum ℂ (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s) ⊆
        Complex.slitPlane) ∧
      ∀ u ∈ Icc (0 : ℝ) 1,
        ‖walkLogResolvent (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s) u‖ ≤ C := by
  let r := (π + w / 2) / 2
  let K := (fun t : ℝ ↦ Complex.exp (-I * (t : ℂ))) '' Icc (-r) r
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hcut : K ⊆ Complex.slitPlane := by
    rintro z ⟨t, ht, rfl⟩
    apply exp_neg_I_mem_slitPlane
    dsimp [r] at ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨ε, hε, he⟩ := hK.exists_thickening_subset_open Complex.isOpen_slitPlane hcut
  have hsep : ∀ z ∈ K, ∀ x : ℝ, x ≤ 0 → ε ≤ ‖z - (x : ℂ)‖ := by
    intro z hz x hx
    by_contra! hlt
    have hm : (x : ℂ) ∈ Metric.thickening ε K := by
      apply Metric.mem_thickening_iff.mpr
      refine ⟨z, hz, ?_⟩
      simpa only [dist_eq_norm, norm_sub_rev] using hlt
    have hc := Complex.mem_slitPlane_iff.mp (he hm)
    exact (not_lt_of_ge hx) (by simpa using hc)
  have hev : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] s₀,
      |a s - a s₀| < (2 * π - w) / 4 := by
    have ht := ((ha s₀ hs₀).sub (continuousWithinAt_const (b := a s₀))).abs
    exact ht.eventually (gt_mem_nhds (by simp; linarith))
  obtain ⟨ρ, hρ, heρ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  obtain ⟨δ, hδ, C, hC⟩ := exists_uniform_walkLogResolvent_bound a w W hw ha hW
    hunit harc hs₀
  refine ⟨min δ (ρ / 2), lt_min hδ (half_pos hρ), ε, hε, C, ?_⟩
  intro s hs hd
  have hdδ := hd.trans (min_le_left _ _)
  refine ⟨?_, hC s hs hdδ⟩
  intro z hz x hx
  apply hsep z _ x hx
  rw [spectrum.smul_eq_smul _ _ (spectrum.nonempty _)] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := harc s hs y hy
  have hdρ : dist s s₀ < ρ := by
    rw [Real.dist_eq]
    have hh := hd.trans (min_le_right _ _)
    linarith
  have ha' := abs_lt.mp (show |a s - a s₀| < (2 * π - w) / 4 from heρ ⟨hdρ, hs⟩)
  refine ⟨t - (a s₀ + w / 2), ?_, ?_⟩
  · dsimp [r]
    constructor <;> linarith [ht.1, ht.2, ha'.1, ha'.2]
  · dsimp only
    rw [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring

end SpectralDistance

section CompactCalculus

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Lemma A.2(ii), continuity under the integral: a continuous integrand on a
closed rectangle has a continuous parameter integral, including at its endpoints. -/
theorem continuousOn_integral_rectangle {F : ℝ → ℝ → A} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s ↦ ∫ u : ℝ in (0 : ℝ)..1, F s u) (Icc a b) := by
  by_cases hab : a ≤ b
  · let f : ℝ → ℝ → A := fun s u ↦ F (max a (min b s)) (max 0 (min 1 u))
    have hf : Continuous (Function.uncurry f) := by
      apply hF.comp_continuous (f := fun p : ℝ × ℝ ↦
        (max a (min b p.1), max 0 (min 1 p.2))) (by fun_prop)
      intro p
      exact ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩,
        ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
    have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hf 0 1
    apply hi.continuousOn.congr
    intro s hs
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    simp only [f, min_eq_right hs.2, max_eq_right hs.1,
      min_eq_right hu.2, max_eq_right hu.1]
  · simp only [Icc_eq_empty hab, continuousOn_empty]

/-- Lemma A.2(ii), endpoint differentiation: continuous interior derivatives extend
to derivatives within the closed interval. This is used for both integral derivatives. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {F G : ℝ → A} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt F (G s) (Icc a b) s := by
  have ht : Tendsto (fun x ↦ deriv F x) (𝓝[Ioo a b] s) (𝓝 (G s)) := by
    apply ((hG s hs).mono Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hd x hx).deriv.symm
  have ht' : Tendsto (fun x ↦ fderiv ℝ F x) (𝓝[Ioo a b] s)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (G s))) := by
    simp only [← toSpanSingleton_deriv]
    exact (ContinuousLinearMap.toSpanSingletonCLE : A ≃L[ℝ] (ℝ →L[ℝ] A)).continuous
      |>.continuousAt |>.tendsto |>.comp ht
  have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo
    (fun x hx ↦ (hF x (by simpa [closure_Ioo hab.ne] using hx)).mono
      Ioo_subset_Icc_self) ht'
  rw [closure_Ioo hab.ne] at hh
  exact hh

/-- Lemma A.2(ii): two continuous derivatives obtained by integration imply `C²`
on a closed interval, using derivatives within that interval at both endpoints. -/
theorem contDiffOn_two_of_integral_derivatives {F G H : ℝ → A} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hH : ContinuousOn H (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s)
    (hdd : ∀ s ∈ Ioo a b, HasDerivAt G (H s) s) :
    ContDiffOn ℝ 2 F (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt F (G s) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt G (H s) (Icc a b) s) := by
  have hdw := fun (s : ℝ) (hs : s ∈ Icc a b) ↦
    hasDerivWithinAt_Icc_of_continuous_derivative hab hF hG hd hs
  have hddw := fun (s : ℝ) (hs : s ∈ Icc a b) ↦
    hasDerivWithinAt_Icc_of_continuous_derivative hab hG hH hdd hs
  have huniq := uniqueDiffOn_Icc hab
  have he : EqOn (derivWithin F (Icc a b)) G (Icc a b) :=
    fun s hs ↦ (hdw s hs).derivWithin (huniq s hs)
  have he' : EqOn (derivWithin G (Icc a b)) H (Icc a b) :=
    fun s hs ↦ (hddw s hs).derivWithin (huniq s hs)
  have hcG : ContDiffOn ℝ 1 G (Icc a b) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiffOn_succ_iff_derivWithin huniq]
    exact ⟨fun s hs ↦ (hddw s hs).differentiableWithinAt, by simp,
      contDiffOn_zero.mpr (hH.congr (fun s hs ↦ he' hs))⟩
  refine ⟨?_, hdw, hddw⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiffOn_succ_iff_derivWithin huniq]
  exact ⟨fun s hs ↦ (hdw s hs).differentiableWithinAt, by simp,
    hcG.congr (fun s hs ↦ he hs)⟩

end CompactCalculus

section IntegralDerivatives

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Lemma A.2(ii), the first derivative integral following (log-integral), before
multiplication by `i` and addition of the fixed scalar center. -/
def walkLogFirstIntegral (V D : A) : A :=
  ∫ u : ℝ in (0 : ℝ)..1, walkLogResolvent V u * D * walkLogResolvent V u

/-- Lemma A.2(ii), the second derivative integral following (log-integral), before
multiplication by `i`; the two inverse derivatives give the coefficient `2u`. -/
def walkLogSecondIntegral (V D E : A) : A :=
  ∫ u : ℝ in (0 : ℝ)..1, walkLogResolvent V u * E * walkLogResolvent V u -
    (2 * u) • (walkLogResolvent V u * D * walkLogResolvent V u * D * walkLogResolvent V u)

/-- Lemma A.2(ii): the second differentiated integrand is jointly continuous on
the entire parameter rectangle, including its boundary. -/
theorem continuousOn_walkLogSecondIntegrand {V D E : ℝ → A} {S : Set ℝ}
    (hV : ContinuousOn V S) (hD : ContinuousOn D S) (hE : ContinuousOn E S)
    (hu : ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ContinuousOn (fun p : ℝ × ℝ ↦
      walkLogResolvent (V p.1) p.2 * E p.1 * walkLogResolvent (V p.1) p.2 -
        (2 * p.2) • (walkLogResolvent (V p.1) p.2 * D p.1 *
          walkLogResolvent (V p.1) p.2 * D p.1 * walkLogResolvent (V p.1) p.2))
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hD' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hE' : ContinuousOn (fun p : ℝ × ℝ ↦ E p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hE.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  exact ((hZ.mul hE').mul hZ).sub
    ((continuousOn_const.mul continuous_snd.continuousOn).smul
      ((((hZ.mul hD').mul hZ).mul hD').mul hZ))

end IntegralDerivatives

section IntegralCalculus

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2(ii): differentiating under the compact resolvent integral twice
produces continuous first and second derivatives and a `C²` integral on a closed
interval. The formulas use derivatives within the interval at both endpoints. -/
theorem walkLogIntegral_contDiffOn_two {V D E : ℝ → 𝕄} {a b : ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt V (D s) s)
    (hdd : ∀ s ∈ Ioo a b, HasDerivAt D (E s) s)
    (hu : ∀ s ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1)))
    (hZ : ContinuousOn (fun p : ℝ × ℝ ↦ walkLogResolvent (V p.1) p.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hFint : ContinuousOn (fun p : ℝ × ℝ ↦ (V p.1 - 1) * walkLogResolvent (V p.1) p.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (fun s ↦ walkLogIntegral (V s)) (Icc a b) ∧
      ContinuousOn (fun s ↦ walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogIntegral (V t))
        (walkLogFirstIntegral (V s) (D s)) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogFirstIntegral (V t) (D t))
        (walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) s) := by
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hF := continuousOn_integral_rectangle
    (F := fun s u ↦ (V s - 1) * walkLogResolvent (V s) u)
    hFint
  have hG := continuousOn_integral_rectangle
    (F := fun s u ↦ walkLogResolvent (V s) u * D s * walkLogResolvent (V s) u)
    ((hZ.mul hd').mul hZ)
  have hH := continuousOn_integral_rectangle
    (F := fun s u ↦ walkLogResolvent (V s) u * E s * walkLogResolvent (V s) u -
      (2 * u) • (walkLogResolvent (V s) u * D s * walkLogResolvent (V s) u *
        D s * walkLogResolvent (V s) u))
    (continuousOn_walkLogSecondIntegrand hV hD hE hu)
  obtain ⟨hc, hdw, hddw⟩ := contDiffOn_two_of_integral_derivatives hab hF hG hH
    (fun s hs ↦ hasDerivAt_walkLogIntegral hs hV hD hd hu)
    (fun s hs ↦ hasDerivAt_walkLogDerivativeIntegral hs hV hD hE hd hdd hu)
  exact ⟨hc, hH, hdw, hddw⟩

/-- Lemma A.2(ii): the only smoothness hypothesis needed for twice differentiating
the resolvent integral is `C²` of the walk; its within-derivatives supply `D` and `E`. -/
theorem walkLogIntegral_contDiffOn_of_contDiffOn {V : ℝ → 𝕄} {a b : ℝ}
    (hab : a < b) (hc : ContDiffOn ℝ 2 V (Icc a b))
    (hu : ∀ s ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    let D := derivWithin V (Icc a b)
    let E := derivWithin D (Icc a b)
    ContDiffOn ℝ 2 (fun s ↦ walkLogIntegral (V s)) (Icc a b) ∧
      ContinuousOn (fun s ↦ walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogIntegral (V t))
        (walkLogFirstIntegral (V s) (D s)) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogFirstIntegral (V t) (D t))
        (walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) s) := by
  intro D E
  have huniq := uniqueDiffOn_Icc hab
  have hD : ContDiffOn ℝ 1 D (Icc a b) := hc.derivWithin huniq (by norm_num)
  have hE : ContinuousOn E (Icc a b) := hD.continuousOn_derivWithin huniq (by norm_num)
  have hZ := (contDiffOn_walkLogResolvent hc hu).continuousOn
  have hFint := (contDiffOn_walkLogIntegrand hc hu).continuousOn
  apply walkLogIntegral_contDiffOn_two hab hc.continuousOn hD.continuousOn hE _ _ hu hZ hFint
  · intro s hs
    exact ((hc.differentiableOn (by norm_num) s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  · intro s hs
    exact ((hD.differentiableOn (by norm_num) s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)

end IntegralCalculus

section LocalBranch

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2(ii): every chord of a centered exponential with norm below `π` is
invertible, supplying the hypothesis for differentiation of its resolvent integral. -/
theorem isUnit_walkLogChord_of_centered {H : 𝕄} (hH : H.IsHermitian)
    (hn : ‖H‖ < π) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 + u • (evol H 1 - 1)) := by
  letI : IsStarNormal (evol H 1) := ⟨by
    change star (evol H 1) * evol H 1 = evol H 1 * star (evol H 1)
    rw [star_evol_mul_self hH 1, mul_eq_one_comm.mpr (star_evol_mul_self hH 1)]⟩
  rw [← cfc_unit_chord (evol H 1) u]
  apply isUnit_cfc (p := IsStarNormal) (fun z : ℂ ↦ 1 + u • (z - 1)) (evol H 1)
    (by fun_prop) inferInstance
  exact fun z hz ↦ chord_ne_zero_of_slitPlane (spectrum_evol_one_subset_slitPlane hH hn hz) hu

/-- Lemma A.2(ii), the full local integral argument: near each `s₀`, the frozen
integral is `C²`, its derivatives are the differentiated integrals with continuous
second derivative, and it equals the prescribed logarithm. The closed relative
neighborhood includes one-sided neighborhoods at `0` and `1`. No smoothness or
continuity of the logarithm is assumed. -/
theorem exists_local_walkLogIntegral_contDiffOn {H W : ℝ → 𝕄} {a : ℝ → ℝ} {w : ℝ}
    (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (he : ∀ s ∈ Icc (0 : ℝ) 1, evol (H s) 1 = W s)
    (hwindow : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) i,
      (hH s hs).eigenvalues i ∈ Icc (a s) (a s + w))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0,
      let K := Icc (max 0 (s₀ - δ)) (min 1 (s₀ + δ))
      let μ := a s₀ + w / 2
      let V := fun s ↦ Complex.exp (I * (μ : ℂ)) • W s
      let D := derivWithin V K
      let E := derivWithin D K
      let F := fun s ↦ (μ : ℂ) • (1 : 𝕄) + I • walkLogIntegral (V s)
      K ∈ 𝓝[Icc (0 : ℝ) 1] s₀ ∧ s₀ ∈ K ∧
      ContDiffOn ℝ 2 F K ∧ EqOn H F K ∧
      ContinuousOn (fun s ↦ I • walkLogSecondIntegral (V s) (D s) (E s)) K ∧
      (∀ s ∈ K, HasDerivWithinAt F (I • walkLogFirstIntegral (V s) (D s)) K s) ∧
      (∀ s ∈ K, HasDerivWithinAt (fun t ↦ I • walkLogFirstIntegral (V t) (D t))
        (I • walkLogSecondIntegral (V s) (D s) (E s)) K s) := by
  have hev := eventually_window_in_principal_turn (ha s₀ hs₀)
    (show 0 < 2 * π - w by linarith)
  simp only [sub_sub_cancel] at hev
  obtain ⟨ρ, hρ, heρ⟩ := Metric.mem_nhdsWithin_iff.mp hev
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
  have hnorm (s : ℝ) (hs : s ∈ K) : ‖H s - (μ : ℂ) • 1‖ < π := by
    have ht := (heρ ⟨hdist s hs, hsub hs⟩).2
    have hn := norm_center_lt_pi_of_open_turn (hH s (hsub hs)) (α := μ - π) (by
      intro i
      have hh := ht _ (hwindow s (hsub hs) i)
      dsimp [μ]
      constructor <;> linarith [hh.1, hh.2])
    simpa only [sub_add_cancel] using hn
  have hherm (s : ℝ) (hs : s ∈ K) : (H s - (μ : ℂ) • 1).IsHermitian := by
    apply (hH s (hsub hs)).sub
    change star ((μ : ℂ) • (1 : 𝕄)) = (μ : ℂ) • 1
    simp only [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  have hevol (s : ℝ) (hs : s ∈ K) : evol (H s - (μ : ℂ) • 1) 1 = V s := by
    rw [evol_sub_scalar_one, he s (hsub hs)]
  have hu : ∀ s ∈ K, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1)) := by
    intro s hs u hu
    rw [← hevol s hs]
    exact isUnit_walkLogChord_of_centered (hherm s hs) (hnorm s hs) hu
  have hcV : ContDiffOn ℝ 2 V K := (hc.mono hsub).const_smul _
  obtain ⟨hF, hcont, hd, hdd⟩ := walkLogIntegral_contDiffOn_of_contDiffOn hlr hcV hu
  have hmem : K ∈ 𝓝[Icc (0 : ℝ) 1] s₀ := by
    apply mem_of_superset (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith : s₀ - δ < s₀)
        (by linarith : s₀ < s₀ + δ))))
    intro s hs
    exact ⟨max_le hs.1.1 hs.2.1, le_min hs.1.2 hs.2.2⟩
  refine ⟨δ, hδ, hmem, ?_, contDiffOn_const.add (hF.const_smul I), ?_,
    hcont.const_smul I, ?_, ?_⟩
  · exact ⟨max_le hs₀.1 (by linarith), le_min hs₀.2 (by linarith)⟩
  · intro s hs
    have hi := walkLogIntegral_evol (hherm s hs) (hnorm s hs)
    rw [hevol s hs] at hi
    change H s = (μ : ℂ) • 1 + I • walkLogIntegral (V s)
    rw [hi, smul_smul]
    have hI : I * (-I) = (1 : ℂ) := by simp
    rw [hI, one_smul]
    abel
  · intro s hs
    exact ((hd s hs).const_smul I).const_add _
  · intro s hs
    exact (hdd s hs).const_smul I


end LocalBranch

end UnitaryProducts.Prose
