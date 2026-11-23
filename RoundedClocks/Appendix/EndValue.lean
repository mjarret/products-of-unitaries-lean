/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueSeriesDerivative
public import RoundedClocks.Appendix.EndValueBounds
public import RoundedClocks.Appendix.EndValueDuhamel

/-! # End-value derivative bounds

Lemma A.3 follows from the multiplier derivative, its endpoint bounds, and the centered Duhamel
decomposition.
-/

@[expose] public section
noncomputable section
open Set Filter Complex NormedSpace
open scoped Topology Real Matrix.Norms.L2Operator
namespace RoundedClocks
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Dieudonné's theorem and the cotangent expansion give the spectral multiplier's derivative,
including the endpoints. -/
theorem endValue_multiplier_allPoints_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω A Ω' A' : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hdΩ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ω (Ω' t) (Icc 0 1) t)
    (hdA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (A' t) (Icc 0 1) t)
    (hΩ' : ContinuousOn Ω' (Icc 0 1)) (hA' : ContinuousOn A' (Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s ↦ 𝒩ad (Ω s) (A s))
      (∑' n, (multiplierCoeff n : ℂ) • (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))) (Icc 0 1) t := by
  have ha t ht := norm_adL_le_width (hΩ t ht) hw0 (hwidth t ht)
  have hd := endValue_commutator_derivative_cited dieudonne_8_6_4 multiplierCoeff_nonneg
    hw0 zero_le_one (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (summable_multiplierCoeff_deriv hw0 hw) ha hdΩ hdA hΩ' hA'
  have he t ht : 𝒩ad (Ω t) (A t) =
      ∑' n, (multiplierCoeff n : ℂ) • ((adL (Ω t) ^ n) (A t)) :=
    (endValue_matrixSeries_cited (hΩ t ht) hw0 hw (hwidth t ht)).symm
  intro t ht
  exact (hd t ht).congr (fun s hs ↦ he s hs) (he t ht)

/-- The continuous cited derivative makes the spectral multiplier a C¹ family. -/
theorem endValue_multiplier_C1_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω A Ω' A' : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hdΩ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ω (Ω' t) (Icc 0 1) t)
    (hdA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (A' t) (Icc 0 1) t)
    (hΩ' : ContinuousOn Ω' (Icc 0 1)) (hA' : ContinuousOn A' (Icc 0 1)) :
    IsC1Family (fun t ↦ 𝒩ad (Ω t) (A t)) := by
  have hd := endValue_multiplier_allPoints_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth
    hdΩ hdA hΩ' hA'
  have hc := endValue_continuousOn_derivativeSeries multiplierCoeff_nonneg hw0
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (summable_multiplierCoeff_deriv hw0 hw)
    (fun t ht ↦ norm_adL_le_width (hΩ t ht) hw0 (hwidth t ht))
    (fun t ht ↦ (hdΩ t ht).continuousWithinAt)
    (fun t ht ↦ (hdA t ht).continuousWithinAt) hΩ' hA'
  apply (contDiffOn_succ_iff_derivWithin (n := 0) (uniqueDiffOn_Icc zero_lt_one)).2
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.2
  exact hc.congr (fun t ht ↦ (hd t ht).derivWithin
    (uniqueDiffOn_Icc zero_lt_one t ht))

/-- For A = Ω', Dieudonné's theorem and the cotangent expansion yield the endpoint-inclusive
formula and C¹ regularity. -/
theorem endValue_derivative_C1_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hC2 : IsC2Family Ω) :
    IsC1Family (fun t ↦ 𝒩ad (Ω t) (deriv01 Ω t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s ↦ 𝒩ad (Ω s) (deriv01 Ω s))
        (∑' n, (multiplierCoeff n : ℂ) •
          (((adL (Ω t) ^ n) (deriv01 (deriv01 Ω) t)) +
            (powDeriv (adL (Ω t)) (adL (deriv01 Ω t)) n) (deriv01 Ω t)))
        (Icc 0 1) t := by
  have hu := uniqueDiffOn_Icc zero_lt_one
  have hC1 : ContDiffOn ℝ 1 (deriv01 Ω) (Icc (0 : ℝ) 1) :=
    hC2.derivWithin hu (by norm_num)
  have hC0 : ContinuousOn (deriv01 (deriv01 Ω)) (Icc (0 : ℝ) 1) :=
    (hC1.derivWithin hu (m := 0) (by norm_num)).continuousOn
  have hdΩ t ht : HasDerivWithinAt Ω (deriv01 Ω t) (Icc 0 1) t :=
    (hC2.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdA t ht : HasDerivWithinAt (deriv01 Ω) (deriv01 (deriv01 Ω) t)
      (Icc 0 1) t := (hC1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  exact ⟨endValue_multiplier_C1_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hdΩ hdA
      hC1.continuousOn hC0,
    endValue_multiplier_allPoints_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hdΩ hdA
      hC1.continuousOn hC0⟩

/-- Lemma A.3(i) follows from the cited series derivative and its scalar majorants. -/
theorem endValue_part_i_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) :
    IsC1Family (fun s ↦ 𝒩ad (Ω s) (deriv01 Ω s)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖deriv01 (fun t ↦ 𝒩ad (Ω t) (deriv01 Ω t)) s‖ ≤
          𝒩 w * ‖deriv01 (deriv01 Ω) s‖ +
            2 * deriv 𝒩 w * ‖deriv01 Ω s‖ ^ 2 := by
  obtain ⟨hC1, hd⟩ := endValue_derivative_C1_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hC2
  refine ⟨hC1, fun s hs ↦ ?_⟩
  have ha := norm_adL_le_width (hΩ s hs) hw0 (hwidth s hs)
  have hsum := endValue_summable_norm_series multiplierCoeff_nonneg ha
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (A := deriv01 (deriv01 Ω) s)
  have hins := endValue_summable_norm_insertion multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw)
    (B := deriv01 Ω s) (A := deriv01 Ω s)
  rw [deriv01, (hd s hs).derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]
  simp only [smul_add, hsum.of_norm.tsum_add hins.of_norm]
  have hb := EndValueCitedBounds.norm_series_le (hΩ s hs) hw0 hw (hwidth s hs)
    (E := deriv01 (deriv01 Ω) s)
  have hi := endValue_norm_insertionSeries_le multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw)
    (B := deriv01 Ω s) (A := deriv01 Ω s)
  rw [← endValue_scalar_derivative_cited dieudonne_8_6_4 hw0 hw] at hi
  calc
    _ ≤ ‖multiplierSeriesOp (Ω s) (deriv01 (deriv01 Ω) s)‖ +
        ‖∑' n, (multiplierCoeff n : ℂ) •
          ((powDeriv (adL (Ω s)) (adL (deriv01 Ω s)) n) (deriv01 Ω s))‖ :=
      norm_add_le _ _
    _ ≤ 𝒩 w * ‖deriv01 (deriv01 Ω) s‖ +
        2 * deriv 𝒩 w * ‖deriv01 Ω s‖ * ‖deriv01 Ω s‖ := add_le_add hb hi
    _ = _ := by ring


/-- Linearity and the Jacobi telescope give (F-split) for any decomposition. -/
theorem endValue_F_split_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {Ω : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (D E X Λ : 𝕄)
    (hsplit : D = X + adL Ω Λ) :
    ‖multiplierSeriesOp Ω E + endValue_F Ω D D‖ ≤
      𝒩 w * ‖E‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖D‖ +
        4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by
  have ha := norm_adL_le_width hΩ hw0 hwidth
  have hFX := endValue_norm_insertionSeries_le multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw) (B := X) (A := D)
  rw [← endValue_scalar_derivative_cited dieudonne_8_6_4 hw0 hw] at hFX
  have hFΛ := EndValueCitedBounds.norm_F_commutator_le hΩ hw0 hw hwidth Λ D
  have hlinear : endValue_F Ω D D = endValue_F Ω X D + endValue_F Ω (adL Ω Λ) D := by
    conv_lhs => arg 2; rw [hsplit]
    exact endValue_F_add Ω X (adL Ω Λ) D (ha.trans_lt hw)
  calc
    _ ≤ ‖multiplierSeriesOp Ω E‖ + ‖endValue_F Ω D D‖ := norm_add_le _ _
    _ ≤ 𝒩 w * ‖E‖ + (‖endValue_F Ω X D‖ + ‖endValue_F Ω (adL Ω Λ) D‖) := by
      apply add_le_add (EndValueCitedBounds.norm_series_le hΩ hw0 hw hwidth)
      rw [hlinear]
      exact norm_add_le _ _
    _ ≤ 𝒩 w * ‖E‖ +
        (2 * deriv 𝒩 w * ‖X‖ * ‖D‖ + 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖) :=
      add_le_add le_rfl (add_le_add hFX hFΛ)
    _ = _ := by ring

/-- Lemma A.3(ii), with the endpoint derivatives interpreted within the closed interval. -/
theorem endValue_part_ii_assembled [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖deriv01 (fun t ↦ 𝒩ad (Ω t) (deriv01 Ω t)) s‖ ≤
      𝒩 w * ‖deriv01 (deriv01 Ω) s‖ +
        2 * deriv 𝒩 w * ‖deriv01 (fun t ↦ exp (-I • Ω t)) s‖ * ‖deriv01 Ω s‖ +
        (𝒩 w - 𝒩 0) * ‖deriv01 Ω s‖ ^ 2 := by
  have hd := (endValue_derivative_C1_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hC2).2 s hs
  have ha := norm_adL_le_width (hΩ s hs) hw0 (hwidth s hs)
  have hsum := endValue_summable_norm_series multiplierCoeff_nonneg ha
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (A := deriv01 (deriv01 Ω) s)
  have hins := endValue_summable_norm_insertion multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw)
    (B := deriv01 Ω s) (A := deriv01 Ω s)
  -- The cited series derivative is the multiplier on Ω'' plus F(Ω').
  have hderiv : deriv01 (fun t ↦ 𝒩ad (Ω t) (deriv01 Ω t)) s =
      multiplierSeriesOp (Ω s) (deriv01 (deriv01 Ω) s) +
        endValue_F (Ω s) (deriv01 Ω s) (deriv01 Ω s) := by
    rw [deriv01, hd.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]
    simp only [smul_add, hsum.of_norm.tsum_add hins.of_norm,
      multiplierSeriesOp, endValue_F]
  -- Establish the generic F-split before selecting the two centered integrals.
  have hsplit (X Λ : 𝕄) (h : deriv01 Ω s = X + adL (Ω s) Λ) :=
    endValue_F_split_assembled dieudonne_8_6_4 (hΩ s hs) hw0 hw (hwidth s hs)
      (deriv01 Ω s) (deriv01 (deriv01 Ω) s) X Λ h
  let X := EndValue.centeredDuhamel (Ω s) (deriv01 Ω s)
  let Λ := EndValue.centeredRemainder (Ω s) (deriv01 Ω s)
  have hbound := hsplit X Λ (EndValue.centeredDuhamel_add_commutator _ _)
  have hX : ‖X‖ = ‖EndValue.evolDeriv (Ω s) (deriv01 Ω s)‖ :=
    EndValue.norm_centeredDuhamel (hΩ s hs) _
  have hΛ : ‖Λ‖ ≤ ‖deriv01 Ω s‖ / 4 := EndValue.norm_centeredRemainder_le (hΩ s hs) _
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := by
    rw [← EndValueCitedBounds.positive_tail hw0 hw]
    exact tsum_nonneg fun n ↦
      mul_nonneg (multiplierCoeff_nonneg _) (pow_nonneg hw0 _)
  have hdΩ := (hC2.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hU := EndValue.hasDerivWithinAt_evol_curve (hΩ s hs) hdΩ
  have hUeq : deriv01 (fun t ↦ exp (-I • Ω t)) s =
      EndValue.evolDeriv (Ω s) (deriv01 Ω s) :=
    hU.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)
  rw [hderiv]
  calc
    _ ≤ 𝒩 w * ‖deriv01 (deriv01 Ω) s‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖deriv01 Ω s‖ +
        4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖deriv01 Ω s‖ := hbound
    _ ≤ 𝒩 w * ‖deriv01 (deriv01 Ω) s‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖deriv01 Ω s‖ +
        4 * (𝒩 w - 𝒩 0) * (‖deriv01 Ω s‖ / 4) * ‖deriv01 Ω s‖ := by
      gcongr
    _ = _ := by rw [hX, ← hUeq]; ring


end RoundedClocks
