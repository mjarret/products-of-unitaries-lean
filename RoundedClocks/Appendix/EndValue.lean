/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CommutatorTelescope
public import RoundedClocks.Appendix.EndValueDuhamel

/-! # Lemma A.3: the derivative of `𝒩([Ω,·])Ω'`

Part (i) is equation (A.2) with `g = 𝒩` and `A = Ω'` (`endValue_part_i`). For part (ii), the proof
writes `(𝒩([Ω,·])Ω')' = 𝒩([Ω,·])Ω'' + 𝓕(Ω')` (`deriv_endValue_eq`), splits `Ω' = X + [Ω,Λ]` with
`‖X‖ = ‖(e^{-iΩ})'‖` and `‖Λ‖ ≤ ‖Ω'‖/4`, and bounds `𝓕(X)` and `𝓕([Ω,Λ])` separately, which is
equation (A.4) (`endValue_F_split`, `endValue_part_ii`). Here `multiplierSeriesOp Ω E` is the
series `∑ₙ νₙ [Ω,·]ⁿ E` of `𝒩([Ω,·])E`, and `endValue_F Ω B D` is `𝓕(B)` with `D` in place of `Ω'`.
-/

@[expose] public section
noncomputable section
open Set Filter Complex NormedSpace
open scoped Topology Real Matrix.Norms.L2Operator
namespace RoundedClocks
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The first line of (A.2) for `g = 𝒩`, with the series written as the `𝒩([Ω,·])A` of
Definition 4.1: `(𝒩([Ω,·])A)' = 𝒩([Ω,·])A' + ∑ₙ νₙ ∑_{k<n} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} A]`. -/
theorem hasDerivWithinAt_𝒩ad [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω A Ω' A' : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hdΩ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ω (Ω' t) (Icc 0 1) t)
    (hdA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (A' t) (Icc 0 1) t)
    (hΩ' : ContinuousOn Ω' (Icc 0 1)) (hA' : ContinuousOn A' (Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s ↦ 𝒩ad (Ω s) (A s))
      (∑' n, (multiplierCoeff n : ℂ) • (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))) (Icc 0 1) t := by
  have ha t ht := norm_adL_le_width (hΩ ht) hw0 (hwidth t ht)
  have hd := hasDerivWithinAt_adL_series multiplierCoeff_nonneg
    hw0 zero_le_one (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (summable_multiplierCoeff_deriv hw0 hw) ha hdΩ hdA hΩ' hA'
  -- The two meanings of `𝒩([Ω,·])A` agree.
  have he t ht : 𝒩ad (Ω t) (A t) =
      ∑' n, (multiplierCoeff n : ℂ) • ((adL (Ω t) ^ n) (A t)) :=
    (multiplierSeriesOp_eq_𝒩ad (hΩ ht) hw0 hw (hwidth t ht)).symm
  intro t ht
  exact (hd t ht).congr (fun s hs ↦ he s hs) (he t ht)

/-- `𝒩([Ω,·])A` is continuously differentiable: its derivative, the series of (A.2), is
continuous. -/
theorem isC1Family_𝒩ad [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω A Ω' A' : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hdΩ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ω (Ω' t) (Icc 0 1) t)
    (hdA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (A' t) (Icc 0 1) t)
    (hΩ' : ContinuousOn Ω' (Icc 0 1)) (hA' : ContinuousOn A' (Icc 0 1)) :
    IsC1Family (fun t ↦ 𝒩ad (Ω t) (A t)) := by
  have hd := hasDerivWithinAt_𝒩ad hw0 hw hΩ hwidth
    hdΩ hdA hΩ' hA'
  have hc := continuousOn_adL_series_deriv multiplierCoeff_nonneg hw0
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (summable_multiplierCoeff_deriv hw0 hw)
    (fun t ht ↦ norm_adL_le_width (hΩ ht) hw0 (hwidth t ht))
    (fun t ht ↦ (hdΩ t ht).continuousWithinAt)
    (fun t ht ↦ (hdA t ht).continuousWithinAt) hΩ' hA'
  apply (contDiffOn_succ_iff_derivWithin (n := 0) (uniqueDiffOn_Icc zero_lt_one)).2
  refine ⟨fun t ht ↦ (hd t ht).differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.2
  exact hc.congr (fun t ht ↦ (hd t ht).derivWithin
    (uniqueDiffOn_Icc zero_lt_one t ht))

/-- With `A = Ω'` in (A.2): `𝒩([Ω,·])Ω'` is continuously differentiable for `s ∈ [0,1]`, with
derivative `𝒩([Ω,·])Ω'' + ∑ₙ νₙ ∑_{k<n} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} Ω']`. -/
theorem endValue_isC1Family_hasDerivWithinAt [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ t ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω t) w)
    (hC2 : IsC2Family Ω) :
    IsC1Family (fun t ↦ 𝒩ad (Ω t) (∂Ω t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s ↦ 𝒩ad (Ω s) (∂Ω s))
        (∑' n, (multiplierCoeff n : ℂ) •
          (((adL (Ω t) ^ n) (∂∂Ω t)) +
            (powDeriv (adL (Ω t)) (adL (∂Ω t)) n) (∂Ω t)))
        (Icc 0 1) t := by
  have hu := uniqueDiffOn_Icc zero_lt_one
  have hC1 : ContDiffOn ℝ 1 (∂Ω) (Icc (0 : ℝ) 1) :=
    hC2.derivWithin hu (by norm_num)
  have hC0 : ContinuousOn (∂∂Ω) (Icc (0 : ℝ) 1) :=
    (hC1.derivWithin hu (m := 0) (by norm_num)).continuousOn
  have hdΩ t ht : HasDerivWithinAt Ω (∂Ω t) (Icc 0 1) t :=
    (hC2.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdA t ht : HasDerivWithinAt (∂Ω) (∂∂Ω t)
      (Icc 0 1) t := (hC1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  exact ⟨isC1Family_𝒩ad hw0 hw hΩ hwidth hdΩ hdA
      hC1.continuousOn hC0,
    hasDerivWithinAt_𝒩ad hw0 hw hΩ hwidth hdΩ hdA
      hC1.continuousOn hC0⟩

/-- Lemma A.3(i): with `g = 𝒩` and `A = Ω'`, (A.2) gives the continuous differentiability of
`𝒩([Ω,·])Ω'` and `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖Ω'‖²`. -/
theorem endValue_part_i [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) :
    IsC1Family (fun s ↦ 𝒩ad (Ω s) (∂Ω s)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤
          𝒩 w * ‖∂∂Ω s‖ + 2 * deriv 𝒩 w * ‖∂Ω s‖ ^ 2 := by
  obtain ⟨hC1, hd⟩ := endValue_isC1Family_hasDerivWithinAt hw0 hw hΩ hwidth hC2
  refine ⟨hC1, fun s hs ↦ ?_⟩
  -- The second line of (A.2), with `g(w) = 𝒩(w)` and `g'(w) = 𝒩'(w)`.
  have h := norm_adL_series_deriv_le multiplierCoeff_nonneg hw0
    (norm_adL_le_width (hΩ hs) hw0 (hwidth s hs))
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (summable_multiplierCoeff_deriv hw0 hw) (B := ∂Ω s) (A := ∂Ω s) (A' := ∂∂Ω s)
  rw [multiplierCoeff_series_eq w (by rwa [abs_of_nonneg hw0]), ← deriv_𝒩_eq_tsum hw0 hw] at h
  rw [deriv01, (hd s hs).derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]
  exact h.trans_eq (by ring)

/-- `(𝒩([Ω,·])Ω')' = 𝒩([Ω,·])Ω'' + 𝓕(Ω')`, where
`𝓕(A) = ∑ₙ νₙ ∑_{k<n} [Ω,·]^k [A, [Ω,·]^{n-1-k} Ω']`. -/
theorem deriv_endValue_eq [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s =
      multiplierSeriesOp (Ω s) (∂∂Ω s) + endValue_F (Ω s) (∂Ω s) (∂Ω s) := by
  have hd := (endValue_isC1Family_hasDerivWithinAt hw0 hw hΩ hwidth hC2).2 s hs
  have ha := norm_adL_le_width (hΩ hs) hw0 (hwidth s hs)
  have hsum := summable_norm_adL_series multiplierCoeff_nonneg ha
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
    (E := ∂∂Ω s)
  have hins := summable_norm_powDeriv_series multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw)
    (B := ∂Ω s) (A := ∂Ω s)
  rw [deriv01, hd.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]
  simp only [smul_add, hsum.of_norm.tsum_add hins.of_norm,
    multiplierSeriesOp, endValue_F]

/-- Lines 3 and 4 of (A.4), for any decomposition `D = X + [Ω,Λ]`:
`‖𝒩([Ω,·])E + 𝓕(D)‖ ≤ 𝒩(w) ‖E‖ + 2𝒩'(w) ‖X‖ ‖D‖ + 4(𝒩(w) - 𝒩(0)) ‖Λ‖ ‖D‖`. -/
theorem endValue_F_split [NeZero d]
    {Ω : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (D E X Λ : 𝕄)
    (hsplit : D = X + adL Ω Λ) :
    ‖multiplierSeriesOp Ω E + endValue_F Ω D D‖ ≤
      𝒩 w * ‖E‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖D‖ +
        4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by
  have ha := norm_adL_le_width hΩ hw0 hwidth
  -- `‖𝓕(X)‖ ≤ 2𝒩'(w) ‖X‖ ‖D‖`, counting terms as in (A.2).
  have hFX := norm_powDeriv_series_le multiplierCoeff_nonneg hw0 ha
    (summable_multiplierCoeff_deriv hw0 hw) (B := X) (A := D)
  rw [← deriv_𝒩_eq_tsum hw0 hw] at hFX
  -- `‖𝓕([Ω,Λ])‖ ≤ 4(𝒩(w) - 𝒩(0)) ‖Λ‖ ‖D‖`, from lines 1 and 2 of (A.4).
  have hFΛ := norm_endValue_F_commutator_le hΩ hw0 hw hwidth Λ D
  -- `𝓕` is linear.
  have hlinear : endValue_F Ω D D = endValue_F Ω X D + endValue_F Ω (adL Ω Λ) D := by
    conv_lhs => arg 2; rw [hsplit]
    exact endValue_F_add Ω X (adL Ω Λ) D (ha.trans_lt hw)
  calc
    _ ≤ ‖multiplierSeriesOp Ω E‖ + ‖endValue_F Ω D D‖ := norm_add_le _ _
    -- Line 3: split `𝓕(D) = 𝓕(X) + 𝓕([Ω,Λ])` and bound `𝒩([Ω,·])E` by (A.1).
    _ ≤ 𝒩 w * ‖E‖ + (‖endValue_F Ω X D‖ + ‖endValue_F Ω (adL Ω Λ) D‖) := by
      apply add_le_add (norm_multiplierSeriesOp_le hΩ hw0 hw hwidth)
      rw [hlinear]
      exact norm_add_le _ _
    -- Line 4.
    _ ≤ 𝒩 w * ‖E‖ +
        (2 * deriv 𝒩 w * ‖X‖ * ‖D‖ + 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖) :=
      add_le_add le_rfl (add_le_add hFX hFΛ)
    _ = _ := by ring

/-- Lemma A.3(ii): equation (A.4) with the paper's `X` and `Λ`, for which `Ω' = X + [Ω,Λ]`,
`‖X‖ = ‖(e^{-iΩ})'‖`, and `‖Λ‖ ≤ ‖Ω'‖/4`. Derivatives at `s = 0` and `s = 1` are one-sided. -/
theorem endValue_part_ii [NeZero d]
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    {Ω : ℝ → 𝕄} (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤
      𝒩 w * ‖∂∂Ω s‖ +
        2 * deriv 𝒩 w * ‖∂(fun t ↦ exp (-I • Ω t)) s‖ * ‖∂Ω s‖ +
        (𝒩 w - 𝒩 0) * ‖∂Ω s‖ ^ 2 := by
  -- The paper's `X` and `Λ`, with `Ω' = X + [Ω,Λ]`.
  let X := EndValue.centeredDuhamel (Ω s) (∂Ω s)
  let Λ := EndValue.centeredRemainder (Ω s) (∂Ω s)
  have hsplit : ∂Ω s = X + adL (Ω s) Λ := EndValue.centeredDuhamel_add_commutator _ _
  -- `‖X‖ = ‖(e^{-iΩ})'‖`, by Duhamel's formula for `(e^{-iΩ})'`.
  have hX : ‖X‖ = ‖EndValue.evolDeriv (Ω s) (∂Ω s)‖ :=
    EndValue.norm_centeredDuhamel (hΩ hs) _
  have hdΩ := (hC2.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hU := EndValue.hasDerivWithinAt_evol_curve (hΩ hs) hdΩ
  have hUeq : ∂(fun t ↦ exp (-I • Ω t)) s =
      EndValue.evolDeriv (Ω s) (∂Ω s) :=
    hU.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)
  -- `‖Λ‖ ≤ ‖Ω'‖/4`.
  have hΛ : ‖Λ‖ ≤ ‖∂Ω s‖ / 4 := EndValue.norm_centeredRemainder_le (hΩ hs) _
  -- `𝒩(w) - 𝒩(0) = ∑_{n ≥ 1} νₙ wⁿ ≥ 0`.
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := by
    rw [← tsum_multiplierCoeff_tail hw0 hw]
    exact tsum_nonneg fun n ↦
      mul_nonneg (multiplierCoeff_nonneg _) (pow_nonneg hw0 _)
  -- `(𝒩([Ω,·])Ω')' = 𝒩([Ω,·])Ω'' + 𝓕(Ω')`, then (A.4).
  rw [deriv_endValue_eq hw0 hw hΩ hwidth hC2 hs]
  calc
    _ ≤ 𝒩 w * ‖∂∂Ω s‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖∂Ω s‖ +
        4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖∂Ω s‖ :=
      endValue_F_split (hΩ hs) hw0 hw (hwidth s hs) (∂Ω s) (∂∂Ω s) X Λ hsplit
    -- `‖Λ‖ ≤ ‖Ω'‖/4`, with the coefficient `4(𝒩(w) - 𝒩(0)) ≥ 0`.
    _ ≤ 𝒩 w * ‖∂∂Ω s‖ + 2 * deriv 𝒩 w * ‖X‖ * ‖∂Ω s‖ +
        4 * (𝒩 w - 𝒩 0) * (‖∂Ω s‖ / 4) * ‖∂Ω s‖ := by
      gcongr
    _ = _ := by rw [hX, ← hUeq]; ring

end RoundedClocks
