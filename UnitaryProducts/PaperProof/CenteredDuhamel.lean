/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Walks.LogarithmDerivative
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The centered Duhamel decomposition in Lemma A.3 -/
@[expose] public section
noncomputable section
open Complex Real Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The derivative transported by the two positive half evolutions. -/
def centeredSymmetrize (Θ V : 𝕄) : 𝕄 :=
  I • (evol Θ (-1 / 2) * V * evol Θ (-1 / 2))

/-- Both half evolutions are unitary, and the scalar phase has modulus one. -/
theorem norm_centeredSymmetrize {Θ : 𝕄} (hΘ : Θ.IsHermitian) (V : 𝕄) :
    ‖centeredSymmetrize Θ V‖ = ‖V‖ := by
  rw [centeredSymmetrize, norm_smul, Complex.norm_I, one_mul,
    CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hΘ _),
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hΘ _)]

/-- The centered Duhamel average called `X` in the proof of Lemma A.3. -/
def centeredDuhamel (Θ Ωd : 𝕄) : 𝕄 :=
  ∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), evol Θ (-τ) * Ωd * evol Θ τ

/-- Duhamel's formula with the paper's order of the two time arguments. -/
theorem centered_evolDeriv_duhamel [NeZero d] (Θ Ωd : 𝕄) :
    evolDeriv Θ Ωd = -I • ∫ σ in (0 : ℝ)..1,
      evol Θ σ * Ωd * evol Θ (1 - σ) := by
  rw [evolDeriv_apply, evol_mul_phiSeries_eq]
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun σ : ℝ ↦ evol Θ σ * Ωd * evol Θ (1 - σ)) 1
    (a := 0) (b := 1)
  simpa only [sub_self, sub_zero, sub_sub_cancel] using h

/-- The substitution `σ = 1/2 - τ` transports Duhamel's derivative to `X`. -/
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

/-- The two unitary half evolutions preserve the norm of the centered average. -/
theorem norm_centeredDuhamel [NeZero d] {Θ : 𝕄} (hΘ : Θ.IsHermitian) (Ωd : 𝕄) :
    ‖centeredDuhamel Θ Ωd‖ = ‖evolDeriv Θ Ωd‖ := by
  rw [centeredDuhamel_eq_centeredSymmetrize, norm_centeredSymmetrize hΘ]

/-- The inner primitive used to define the commutator remainder. -/
def centeredPrimitive (Ω D : 𝕄) (τ : ℝ) : 𝕄 :=
  ∫ σ in (0 : ℝ)..τ, evol Ω (-σ) * D * evol Ω σ

/-- The double integral called `Λ` in the proof of Lemma A.3. -/
def centeredRemainder (Ω D : 𝕄) : 𝕄 :=
  -I • ∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), centeredPrimitive Ω D τ

/-- The conjugation integrand is continuous on the whole real line. -/
theorem continuous_centeredConjugation (Ω D : 𝕄) :
    Continuous (fun τ : ℝ ↦ evol Ω (-τ) * D * evol Ω τ) :=
  (((continuous_evol Ω).comp continuous_neg).mul continuous_const).mul (continuous_evol Ω)

/-- The inner integral depends continuously on its upper endpoint. -/
theorem continuous_centeredPrimitive (Ω D : 𝕄) : Continuous (centeredPrimitive Ω D) :=
  intervalIntegral.continuous_primitive
    (fun a b ↦ (continuous_centeredConjugation Ω D).intervalIntegrable a b) 0

/-- Lemma A.3: the guessed conjugated derivative satisfies
`∂σ Ω'σ = i[Ω, Ω'σ]`, equivalently the commutator is `-i` times that derivative. -/
theorem centered_conjugation_hasDerivAt (Ω D : 𝕄) (σ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t)
      (I • adL Ω (evol Ω (-σ) * D * evol Ω σ)) σ := by
  let f : ℝ → 𝕄 := fun t ↦ evol Ω (-t) * D * evol Ω t
  have hcomm (t : ℝ) : Ω * evol Ω t = evol Ω t * Ω := by
    have hh := (commute_evol Ω t).eq
    simp only [smul_mul_assoc, mul_smul_comm] at hh
    exact (smul_right_injective 𝕄 (neg_ne_zero.mpr I_ne_zero)) hh
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

/-- Lemma A.3: `[Ω, Ω'σ] = -i ∂σ Ω'σ`, the identity used to check
the double-integral guess for `Λ`. -/
theorem centered_conjugation_commutator_eq_deriv (Ω D : 𝕄) (σ : ℝ) :
    adL Ω (evol Ω (-σ) * D * evol Ω σ) =
      -I • deriv (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t) σ := by
  rw [(centered_conjugation_hasDerivAt Ω D σ).deriv, smul_smul]
  simp

/-- Integrating the verified derivative of conjugation gives the endpoint
identity used in the third line of Lemma A.3's ansatz verification. -/
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

/-- Lemma A.3, first verification line: the commutator passes through the
two integrals defining the guessed `Λ`. -/
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

/-- Lemma A.3, second verification line: substitute the verified derivative
of the conjugated input into the double commutator integral. -/
theorem centeredRemainder_commutator_deriv (Ω D : 𝕄) :
    adL Ω (centeredRemainder Ω D) =
      -(∫ τ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        ∫ σ in (0 : ℝ)..τ,
          deriv (fun t : ℝ ↦ evol Ω (-t) * D * evol Ω t) σ) := by
  rw [centeredRemainder_commutator_integral]
  simp_rw [centered_conjugation_commutator_eq_deriv,
    intervalIntegral.integral_smul]
  rw [smul_smul, show (-I) * (-I) = (-1 : ℂ) by simp, neg_one_smul]

/-- Lemma A.3, third verification line: the inner derivative integral is
the conjugation at `τ` minus its value at zero. -/
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

/-- Lemma A.3: the two integral guesses for `X` and `Λ`, together with the
last verification line `[Ω, Λ] = Ω' - X`. -/
theorem centeredDuhamel_ansatz_verified (Ω D : 𝕄) :
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

/-- The verified integral ansatz gives precisely `D = X + [Ω,Λ]`. -/
theorem centeredDuhamel_add_commutator (Ω D : 𝕄) :
    D = centeredDuhamel Ω D + adL Ω (centeredRemainder Ω D) := by
  rw [(centeredDuhamel_ansatz_verified Ω D).2.2]
  abel

/-- Unitary conjugation gives the sharp length bound for the inner primitive. -/
theorem norm_centeredPrimitive_le {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄) (τ : ℝ) :
    ‖centeredPrimitive Ω D τ‖ ≤ |τ| * ‖D‖ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ)
    (f := fun σ : ℝ ↦ evol Ω (-σ) * D * evol Ω σ) (C := ‖D‖) (fun σ _ ↦ by
      rw [CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hΩ _),
        CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hΩ _)])
  simpa only [centeredPrimitive, sub_zero, mul_comm] using hb

/-- The scalar integral responsible for the coefficient one quarter. -/
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

/-- The commutator remainder has norm at most one quarter of the input norm. -/
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

end UnitaryProducts.PaperProof
