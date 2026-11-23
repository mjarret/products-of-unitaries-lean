/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import RoundedClocks.Appendix.ExponentialDuhamel
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Lemma A.3: the matrices `X` and `Λ`

With `Ω'_σ = e^{iσΩ} Ω' e^{-iσΩ}`, the proof of Lemma A.3 sets `X = ∫_{-1/2}^{1/2} Ω'_τ dτ` and
`Λ = -i∫_{-1/2}^{1/2} ∫₀^τ Ω'_σ dσ dτ`. Then `Ω' = X + [Ω,Λ]`, `‖X‖ = ‖(e^{-iΩ})'‖`, and
`‖Λ‖ ≤ ‖Ω'‖/4`. Here `evol Ω σ` is `e^{-iσΩ}`, `centeredDuhamel Ω D` is `X`, and
`centeredRemainder Ω D` is `Λ`, with `D` in place of `Ω'`.
-/
@[expose] public section
noncomputable section
open Complex Real Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
open RoundedClocks.EndValue
namespace RoundedClocks.EndValue
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `i e^{iΘ/2} V e^{iΘ/2}`. With `Θ = Ω` and `V = (e^{-iΩ})'` this is `X`, as
`(e^{-iΩ})' = -i e^{-iΩ/2} X e^{-iΩ/2}`. -/
def centeredSymmetrize (Θ V : 𝕄) : 𝕄 :=
  I • (evol Θ (-1 / 2) * V * evol Θ (-1 / 2))

/-- `‖i e^{iΘ/2} V e^{iΘ/2}‖ = ‖V‖` for Hermitian `Θ`. -/
theorem norm_centeredSymmetrize {Θ : 𝕄} (hΘ : Θ.IsHermitian) (V : 𝕄) :
    ‖centeredSymmetrize Θ V‖ = ‖V‖ := by
  have hmem (u : ℝ) : evol Θ u ∈ unitary 𝕄 := by
    simpa only [evol, frozenEvolution, Complex.coe_smul] using
      exp_neg_I_smul_isUnitary hΘ u
  rw [centeredSymmetrize, norm_smul, Complex.norm_I, one_mul,
    CStarRing.norm_mul_mem_unitary _ (hmem _),
    CStarRing.norm_mem_unitary_mul _ (hmem _)]

/-- The `X = ∫_{-1/2}^{1/2} Ω'_τ dτ` of the proof of Lemma A.3, with `Ω'_τ = e^{iτΩ} Ω' e^{-iτΩ}`;
here `Θ` is `Ω` and `Ωd` is `Ω'`. -/
def centeredDuhamel (Θ Ωd : 𝕄) : 𝕄 :=
  ∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), evol Θ (-τ) * Ωd * evol Θ τ

/-- Duhamel's formula in the paper's form: `(e^{-iΩ})' = -i∫₀¹ e^{-iσΩ} Ω' e^{-i(1-σ)Ω} dσ`. -/
theorem centered_evolDeriv_duhamel [NeZero d] (Θ Ωd : 𝕄) :
    evolDeriv Θ Ωd = -I • ∫ σ in (0 : ℝ)..1,
      evol Θ σ * Ωd * evol Θ (1 - σ) := by
  rw [evolDeriv_apply]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun σ : ℝ ↦ evol Θ σ * Ωd * evol Θ (1 - σ)) 1
    (a := 0) (b := 1)
  simpa only [sub_self, sub_zero, sub_sub_cancel] using h

/-- `(e^{-iΩ})' = -i e^{-iΩ/2} X e^{-iΩ/2}`, by the substitution `σ = 1/2 - τ`; stated as
`X = i e^{iΩ/2} (e^{-iΩ})' e^{iΩ/2}`. -/
theorem centeredDuhamel_eq_centeredSymmetrize [NeZero d] (Θ Ωd : 𝕄) :
    centeredDuhamel Θ Ωd = centeredSymmetrize Θ (evolDeriv Θ Ωd) := by
  let F : ℝ → 𝕄 := fun σ ↦ evol Θ σ * Ωd * evol Θ (1 - σ)
  let L := ContinuousLinearMap.mulLeftRight ℂ 𝕄 (evol Θ (-1 / 2))
    (evol Θ (-1 / 2))
  have hF : Continuous F := ((continuous_evol Θ).mul continuous_const).mul
    ((continuous_evol Θ).comp (continuous_const.sub continuous_id))
  have hL (σ : ℝ) : L (F σ) =
      evol Θ (-(1 / 2 - σ)) * Ωd * evol Θ (1 / 2 - σ) := by
    change evol Θ (-1 / 2) * (evol Θ σ * Ωd * evol Θ (1 - σ)) *
      evol Θ (-1 / 2) = _
    calc
      _ = (evol Θ (-1 / 2) * evol Θ σ) * Ωd *
          (evol Θ (1 - σ) * evol Θ (-1 / 2)) := by simp only [mul_assoc]
      _ = _ := by
        rw [← evol_add, ← evol_add,
          show -1 / 2 + σ = -(1 / 2 - σ) by ring,
          show (1 - σ) + -1 / 2 = 1 / 2 - σ by ring]
  have hphase : I * -I = (1 : ℂ) := by simp
  rw [centeredSymmetrize, centered_evolDeriv_duhamel, mul_smul_comm, smul_mul_assoc,
    smul_smul, hphase, one_smul]
  change centeredDuhamel Θ Ωd = L (∫ σ in (0 : ℝ)..1, F σ)
  rw [← L.intervalIntegral_comp_comm (hF.intervalIntegrable 0 1)]
  simp_rw [hL]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun τ : ℝ ↦ evol Θ (-τ) * Ωd * evol Θ τ) (1 / 2) (a := 0) (b := 1)
  norm_num at hsub
  simpa only [centeredDuhamel, neg_div, neg_sub] using hsub.symm

/-- `‖X‖ = ‖(e^{-iΩ})'‖`. -/
theorem norm_centeredDuhamel [NeZero d] {Θ : 𝕄} (hΘ : Θ.IsHermitian) (Ωd : 𝕄) :
    ‖centeredDuhamel Θ Ωd‖ = ‖evolDeriv Θ Ωd‖ := by
  rw [centeredDuhamel_eq_centeredSymmetrize, norm_centeredSymmetrize hΘ]

/-- The inner integral `∫₀^τ Ω'_σ dσ` in the definition of `Λ`. -/
def centeredPrimitive (Ω D : 𝕄) (τ : ℝ) : 𝕄 :=
  ∫ σ in (0 : ℝ)..τ, evol Ω (-σ) * D * evol Ω σ

/-- The `Λ = -i∫_{-1/2}^{1/2} ∫₀^τ Ω'_σ dσ dτ` of the proof of Lemma A.3. -/
def centeredRemainder (Ω D : 𝕄) : 𝕄 :=
  -I • ∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), centeredPrimitive Ω D τ

/-- `σ ↦ Ω'_σ` is continuous. -/
theorem continuous_centeredConjugation (Ω D : 𝕄) :
    Continuous (fun τ : ℝ ↦ evol Ω (-τ) * D * evol Ω τ) :=
  (((continuous_evol Ω).comp continuous_neg).mul continuous_const).mul (continuous_evol Ω)

/-- `τ ↦ ∫₀^τ Ω'_σ dσ` is continuous. -/
theorem continuous_centeredPrimitive (Ω D : 𝕄) : Continuous (centeredPrimitive Ω D) :=
  intervalIntegral.continuous_primitive
    (fun a b ↦ (continuous_centeredConjugation Ω D).intervalIntegrable a b) 0

/-- `∂_σ Ω'_σ = i[Ω, Ω'_σ]`. -/
theorem centered_conjugation_hasDerivAt (Ω D : 𝕄) (σ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t)
      (I • adL Ω (evol Ω (-σ) * D * evol Ω σ)) σ := by
  let f : ℝ → 𝕄 := fun t ↦ evol Ω (-t) * D * evol Ω t
  have hcomm (t : ℝ) : Ω * evol Ω t = evol Ω t * Ω :=
    ((((Commute.refl Ω).smul_right (-I)).smul_right t).exp_right).eq
  change HasDerivAt f (I • adL Ω (f σ)) σ
  have hn : HasDerivAt (fun s : ℝ ↦ evol Ω (-s))
      (I • (Ω * evol Ω (-σ))) σ := by
    simpa only [smul_mul_assoc, neg_smul, neg_neg, one_smul, neg_mul] using
      (hasDerivAt_evol Ω (-σ)).scomp σ (hasDerivAt_neg σ)
  convert (hn.mul_const D).mul (hasDerivAt_evol Ω σ) using 1
  simp only [f, adL_apply, smul_mul_assoc, mul_smul_comm, smul_sub,
    neg_smul, neg_mul, mul_neg, mul_assoc]
  rw [hcomm σ]
  module

/-- `[Ω, Ω'_σ] = -i ∂_σ Ω'_σ`. -/
theorem centered_conjugation_commutator_eq_deriv (Ω D : 𝕄) (σ : ℝ) :
    adL Ω (evol Ω (-σ) * D * evol Ω σ) =
      -I • deriv (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t) σ := by
  rw [(centered_conjugation_hasDerivAt Ω D σ).deriv, smul_smul]
  simp

/-- `Ω'_τ - Ω' = i[Ω, ∫₀^τ Ω'_σ dσ]`: the integral of `∂_σ Ω'_σ` from `0` to `τ`. -/
theorem conjugation_sub_eq_commutator_integral (Ω D : 𝕄) (τ : ℝ) :
    evol Ω (-τ) * D * evol Ω τ - D = I • adL Ω (centeredPrimitive Ω D τ) := by
  let f : ℝ → 𝕄 := fun σ ↦ evol Ω (-σ) * D * evol Ω σ
  have hc : Continuous f := continuous_centeredConjugation Ω D
  have hd (σ : ℝ) : HasDerivAt f (I • adL Ω (f σ)) σ :=
    centered_conjugation_hasDerivAt Ω D σ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun σ _ ↦ hd σ) (((adL Ω).continuous.comp hc).const_smul I |>.intervalIntegrable 0 τ)
  rw [intervalIntegral.integral_smul,
    (adL Ω).intervalIntegral_comp_comm (hc.intervalIntegrable 0 τ)] at hFTC
  simpa [f, centeredPrimitive, evol_zero] using hFTC.symm

/-- Line 1 of the display `[Ω,Λ] = Ω' - X`: `[Ω,Λ] = -i∫_{-1/2}^{1/2} ∫₀^τ [Ω, Ω'_σ] dσ dτ`. -/
theorem centeredRemainder_commutator_integral (Ω D : 𝕄) :
    adL Ω (centeredRemainder Ω D) =
      -I • ∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ∫ σ in (0 : ℝ)..τ, adL Ω (evol Ω (-σ) * D * evol Ω σ) := by
  rw [centeredRemainder, map_smul,
    ← (adL Ω).intervalIntegral_comp_comm
      ((continuous_centeredPrimitive Ω D).intervalIntegrable _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro τ _
  exact ((adL Ω).intervalIntegral_comp_comm
    ((continuous_centeredConjugation Ω D).intervalIntegrable 0 τ)).symm

/-- Line 2 of the display: `[Ω,Λ] = -∫_{-1/2}^{1/2} ∫₀^τ ∂_σ Ω'_σ dσ dτ`. -/
theorem centeredRemainder_commutator_deriv (Ω D : 𝕄) :
    adL Ω (centeredRemainder Ω D) =
      -(∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ∫ σ in (0 : ℝ)..τ,
          deriv (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t) σ) := by
  rw [centeredRemainder_commutator_integral]
  simp_rw [centered_conjugation_commutator_eq_deriv,
    intervalIntegral.integral_smul]
  rw [smul_smul, show (-I) * (-I) = (-1 : ℂ) by simp, neg_one_smul]

/-- Line 3 of the display: `[Ω,Λ] = -∫_{-1/2}^{1/2} (Ω'_τ - Ω') dτ`. -/
theorem centeredRemainder_commutator_boundary (Ω D : 𝕄) :
    adL Ω (centeredRemainder Ω D) =
      -(∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        (evol Ω (-τ) * D * evol Ω τ - D)) := by
  rw [centeredRemainder_commutator_deriv]
  congr 1
  apply intervalIntegral.integral_congr
  intro τ _
  simp_rw [(centered_conjugation_hasDerivAt Ω D _).deriv,
    intervalIntegral.integral_smul]
  rw [(adL Ω).intervalIntegral_comp_comm
    ((continuous_centeredConjugation Ω D).intervalIntegrable 0 τ)]
  exact (conjugation_sub_eq_commutator_integral Ω D τ).symm

/-- Line 4 of the display: `[Ω,Λ] = Ω' - X`, together with the definitions of `X` and `Λ` as
integrals. -/
theorem centeredDuhamel_decomposition (Ω D : 𝕄) :
    centeredDuhamel Ω D =
      (∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), evol Ω (-τ) * D * evol Ω τ) ∧
    centeredRemainder Ω D =
      -I • (∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ∫ σ in (0 : ℝ)..τ, evol Ω (-σ) * D * evol Ω σ) ∧
    adL Ω (centeredRemainder Ω D) = D - centeredDuhamel Ω D := by
  refine ⟨rfl, rfl, ?_⟩
  rw [centeredRemainder_commutator_boundary,
    intervalIntegral.integral_sub
      ((continuous_centeredConjugation Ω D).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const]
  norm_num only [show (1 / 2 : ℝ) - -1 / 2 = 1 by norm_num, one_smul]
  simp only [centeredDuhamel, neg_div]
  abel

/-- `Ω' = X + [Ω,Λ]`. -/
theorem centeredDuhamel_add_commutator (Ω D : 𝕄) :
    D = centeredDuhamel Ω D + adL Ω (centeredRemainder Ω D) := by
  rw [(centeredDuhamel_decomposition Ω D).2.2]
  abel

/-- `‖∫₀^τ Ω'_σ dσ‖ ≤ |τ| ‖Ω'‖`, as conjugation by a unitary preserves the norm. -/
theorem norm_centeredPrimitive_le {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄) (τ : ℝ) :
    ‖centeredPrimitive Ω D τ‖ ≤ |τ| * ‖D‖ := by
  have hmem (u : ℝ) : evol Ω u ∈ unitary 𝕄 := by
    simpa only [evol, frozenEvolution, Complex.coe_smul] using
      exp_neg_I_smul_isUnitary hΩ u
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
    (f := fun σ : ℝ ↦ evol Ω (-σ) * D * evol Ω σ) (C := ‖D‖) (fun σ _ ↦ by
      rw [CStarRing.norm_mul_mem_unitary _ (hmem _),
        CStarRing.norm_mem_unitary_mul _ (hmem _)])
  simpa only [centeredPrimitive, sub_zero, mul_comm] using hb

/-- `∫_{-1/2}^{1/2} |τ| dτ = 1/4`. -/
theorem integral_abs_centered_half :
    (∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), |τ|) = 1 / 4 := by
  have hleft : (∫ τ in (-1 / 2 : ℝ)..0, |τ|) = 1 / 8 := by
    rw [intervalIntegral.integral_congr (fun τ hτ ↦ abs_of_nonpos
      (show τ ≤ 0 from (uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 0) ▸ hτ).2)),
      intervalIntegral.integral_neg, integral_id]
    norm_num
  have hright : (∫ τ in (0 : ℝ)..(1 / 2 : ℝ), |τ|) = 1 / 8 := by
    rw [intervalIntegral.integral_congr (fun τ hτ ↦ abs_of_nonneg
      (show 0 ≤ τ from (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2) ▸ hτ).1)), integral_id]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-1 / 2) 0)
    (continuous_abs.intervalIntegrable 0 (1 / 2)), hleft, hright]
  norm_num

/-- `‖Λ‖ ≤ ∫_{-1/2}^{1/2} |τ| dτ ‖Ω'‖ = ‖Ω'‖/4`. -/
theorem norm_centeredRemainder_le {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄) :
    ‖centeredRemainder Ω D‖ ≤ ‖D‖ / 4 := by
  rw [centeredRemainder, norm_smul, norm_neg, Complex.norm_I, one_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm
    (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)).trans ?_
  have hbound := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)
    ((continuous_centeredPrimitive Ω D).norm.intervalIntegrable _ _)
    ((continuous_abs.mul continuous_const).intervalIntegrable _ _)
    (fun τ _ ↦ norm_centeredPrimitive_le hΩ D τ)
  refine hbound.trans_eq ?_
  change (∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), |τ| * ‖D‖) = ‖D‖ / 4
  rw [intervalIntegral.integral_mul_const, integral_abs_centered_half]
  ring

end RoundedClocks.EndValue
