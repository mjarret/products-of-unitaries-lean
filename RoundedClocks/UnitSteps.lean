/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.Appendix
public import RoundedClocks.UnitSteps.TruncatedProductBounds
public import RoundedClocks.UnitSteps.RoundedClockComparison
public import RoundedClocks.UnitSteps.RoundedClockBound
public import RoundedClocks.UnitSteps.unitary_products
public import RoundedClocks.UnitSteps.SpectralGapTransfer
public import RoundedClocks.UnitSteps.HermitianLogarithm
public import RoundedClocks.UnitSteps.ExponentialSpectrum
public import RoundedClocks.UnitSteps.LogarithmWidth
public import RoundedClocks.UnitSteps.DerivativeTransport
public import RoundedClocks.UnitSteps.OrderedEigenvalueContinuity
public import RoundedClocks.UnitSteps.EndpointProjectors
public import RoundedClocks.UnitSteps.SharpnessCalculation
public import RoundedClocks.UnitSteps.UnitTransferDuhamel
public import RoundedClocks.UnitSteps.LogarithmUniqueness
public import RoundedClocks.UnitSteps.WalkLeakageRegularity

/-!
# Section 4: unit steps

The rounded-clock comparison (Theorems 4.2 and 4.4), its examples (Examples 4.3 and 4.5), and
products of given unitaries (Theorems 4.6 and 4.7).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Theorem 4.2.** Assuming Dieudonné (7.6.1), Section 8.7, (10.5.4) and (10.6.3) with the remark
(10.4.6), and DLMF
4.22.5, let `T ≥ 1` be an integer and `H` a time-dependent Hamiltonian whose derivative
`H'` exists on `[0,1]` (one-sided at the ends) with `‖H'(s₁) - H'(s₂)‖ ≤ L |s₁ - s₂|`, and whose
samples `H(j/T)`, `0 ≤ j ≤ T`, have eigenvalue differences of modulus at most a width `w < 2π`.
Then the evolutions `U` of `H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy
`‖V(T) - U(T)‖ ≤ (c₀ (‖H'(0)‖ + ‖H'(1)‖) + L/24 + c₁ ‖H'‖∞²)/T + Σ_{j=1}^T ‖Δ_j‖`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem rounded_clock_comparison (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dlmf_4_22_5 : DLMF_4_22_5) (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
  exact rounded_clock_comparison_main dieudonne_7_6_1 dieudonne_section_8_7
    dlmf_4_22_5 dieudonne_10_5_4 dieudonne_10_6_3
    hT hH hL hw hwidth

/-- **Example 4.3.** Assuming Dieudonné (10.5.4) and (10.6.3) with the remark (10.4.6), for an
integer `T ≥ 2`,
`H(s) = s² Z` with `Z = diag(1,-1)` satisfies the
hypotheses of Theorem 4.2 with `L = 2` and `w = 2`, and its evolutions `U` and `V` satisfy
(i) `‖V(T) - U(T)‖ = 2 sin(1/(12T))`, asymptotic to `1/(6T)`, and
(ii) `‖W_T - U(T)‖ = 2 sin(1/4 - 1/(12T))`, with limit `2 sin(1/4)`. -/
theorem unit_sharp (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (T : ℕ) (hT : 2 ≤ T) :
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s ↦ (s ^ 2 : ℝ) • Matrix.diagonal ![1, -1]
    IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H 2 ∧ HasSampleWidth H T 2 ∧
      ‖roundedEvolution H T T - evolution H T T‖ = 2 * Real.sin (1 / (12 * T)) ∧
      (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * N))) ~[atTop] (fun N : ℕ ↦ 1 / (6 * N)) ∧
      ‖stepProduct H T - evolution H T T‖ = 2 * Real.sin (1 / 4 - 1 / (12 * T)) ∧
      Tendsto (fun N : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * N))) atTop
        (𝓝 (2 * Real.sin (1 / 4))) := by
  change IsTimeDepHamiltonian UnitSharp.H ∧ _
  have hT1 : 1 ≤ T := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT1
  obtain ⟨hH, hL, hwidth⟩ := UnitSharp.regularity T hT1
  -- The integral, left-endpoint sum, and trapezoidal correction.
  have hintegral := UnitSharp.integral_H (T : ℝ) hTr
  have hleftSum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      ((T : ℝ) - 1) * (2 * T - 1) / (6 * T) := by
    rw [UnitSharp.left_sum T hT1]
    field_simp
    ring
  have hsum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (T : ℝ) / 3 - 1 / 2 + 1 / (6 * T) := by
    rw [hleftSum]
    field_simp
    ring
  have hcorrection : (1 / 2 : ℝ) • (UnitSharp.H 1 - UnitSharp.H 0) =
      (1 / 2 : ℝ) • UnitSharp.Z := by simp [UnitSharp.H]
  -- The three endpoint formulas, with existence and uniqueness from Dieudonné.
  have hU : evolution UnitSharp.H T T =
      exp (-I • (∫ t in 0..(T : ℝ), UnitSharp.H (t / T))) := by
    rw [hintegral, smul_comm]
    exact UnitSharp.evolution_end dieudonne_10_5_4 dieudonne_10_6_3 T hT1
  have hevolution : evolution UnitSharp.H T T = UnitSharp.E ((T : ℝ) / 3) := by
    rw [hU, hintegral, smul_comm]
    rfl
  have hproduct := UnitSharp.sharp_stepProduct T hsum
  have hrounded : roundedEvolution UnitSharp.H T T =
      UnitSharp.E ((T : ℝ) / 3 + 1 / (6 * T)) := by
    rw [roundedEvolution_end dieudonne_10_5_4 hH hT1, hproduct]
    have hleft : exp (-(I / 2) • UnitSharp.H 1) = UnitSharp.E (1 / 2) := by
      have hc : (1 / 2 : ℝ) • UnitSharp.H 1 = (1 / 2 : ℝ) • UnitSharp.Z := by
        simp [UnitSharp.H] at hcorrection ⊢
      rw [UnitSharp.E, smul_comm, ← hc]
      congr 1
      module
    have hright : exp ((I / 2) • UnitSharp.H 0) = 1 := by simp [UnitSharp.H]
    rw [hleft, hright, mul_one, ← UnitSharp.E_add]
    congr 1
    ring
  have hcorrected :
      ‖roundedEvolution UnitSharp.H T T - evolution UnitSharp.H T T‖ =
        2 * Real.sin (1 / (12 * T)) := by
    rw [hrounded, hevolution, UnitSharp.norm_reduction, UnitSharp.norm_phase]
    have hx0 : 0 < 1 / (12 * (T : ℝ)) := by positivity
    have hxpi : 1 / (12 * (T : ℝ)) < π := by
      have := Real.pi_gt_three
      have hTreal : (2 : ℝ) ≤ T := by exact_mod_cast hT
      have hb := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 24)
        (show (24 : ℝ) ≤ 12 * T by linarith)
      linarith
    rw [show (((T : ℝ) / 3 + 1 / (6 * T)) - T / 3) / 2 =
      1 / (12 * T) by ring, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)]
  have huncorrected :
      ‖stepProduct UnitSharp.H T - evolution UnitSharp.H T T‖ =
        2 * Real.sin (1 / 4 - 1 / (12 * T)) := by
    rw [hproduct, hevolution, UnitSharp.norm_reduction, UnitSharp.norm_phase]
    have hx0 : 0 < 1 / 4 - 1 / (12 * (T : ℝ)) := by
      have hTreal : (2 : ℝ) ≤ T := by exact_mod_cast hT
      rw [sub_pos, div_lt_iff₀ (by positivity : 0 < 12 * (T : ℝ))]
      linarith [show (2 : ℝ) ≤ T by exact_mod_cast hT]
    have hxpi : 1 / 4 - 1 / (12 * (T : ℝ)) < π := by
      have hinv : 0 < 1 / (12 * (T : ℝ)) := by positivity
      linarith [Real.pi_gt_three]
    rw [show (((T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) - T / 3) / 2 =
      -(1 / 4 - 1 / (12 * T)) by ring, Real.sin_neg, abs_neg,
      abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)]
  exact ⟨hH, hL, hwidth, hcorrected, UnitSharp.asymptotic, huncorrected, UnitSharp.limit⟩

/-- **Theorem 4.4.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3)
with the remark (10.4.6), and DLMF 4.22.5, under the hypotheses of Theorem 4.2, the
evolutions `U` of
`H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy `‖V(T) - U(T)‖ ≤ ℰ_w(H)/T`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem rounded_clock_bound (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤ ℰ w L H / T := by
  have hw0 : 0 ≤ w := width_nonneg hH hwidth
  -- Sum the three-term jump estimate over the T sample intervals.
  have hjumps := sum_norm_Δ_le dieudonne_8_6_4 hT hH hL hw0 hw hwidth
  -- Theorem 4.2 supplies the endpoint and cell terms.
  have hcomparison := rounded_clock_comparison dieudonne_7_6_1 dieudonne_section_8_7 dlmf_4_22_5
    dieudonne_10_5_4 dieudonne_10_6_3 hT hH hL hw hwidth
  calc
    _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := hcomparison
    _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T := add_le_add_right hjumps _
    _ = ℰ w L H / T := by
      unfold ℰ
      ring

/-- **Example 4.5.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3)
with the remark (10.4.6),
and DLMF 4.22.5, under the hypotheses of Theorem 4.2, let `P` and `Q` be orthogonal
projectors
commuting with `H(0)` and `H(1)`, and let `C ≥ 0` and `δ > 0`. If `‖(1 - Q) U(T) P‖ ≤ C/T`,
`T ≥ 2(C + ℰ_w(H))/δ`, and `√2 σ_k 2^{-k} ≤ δ/(2T)`, then the `T`-step product `W^{(k)}_T` of the
truncation `H^{(k)}` satisfies `‖(1 - Q) W^{(k)}_T P‖ ≤ δ`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem unit_transfer (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) {P Q : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hPH : Commute P (H 0)) (hQH : Commute Q (H 1)) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T)
    (hTδ : 2 * (C + ℰ w L H) / δ ≤ T) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T)) :
    ‖(1 - Q) * stepProduct (fun s ↦ entrywise (bitTruncation k) (H s)) T * P‖ ≤ δ := by
  let Hk : ℝ → 𝕄 := fun s ↦ entrywise (bitTruncation k) (H s)
  let W := stepProduct H T
  let Wk := stepProduct Hk T
  let E := ℰ w L H
  let A := exp (-(I / 2) • H 1)
  let B := exp ((I / 2) • H 0)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hA : IsUnitary A := by
    dsimp [A]
    have he : -(I / 2) • H 1 = ((1 / 2 : ℝ) : ℂ) • (-I • H 1) := by module
    rw [he]
    exact phase_isUnitary (hH 1 (by norm_num)) (1 / 2)
  have hB : IsUnitary B := by
    dsimp [B]
    have he : (I / 2) • H 0 = ((-(1 / 2) : ℝ) : ℂ) • (-I • H 0) := by module
    rw [he]
    exact phase_isUnitary (hH 0 (by norm_num)) (-(1 / 2))
  have hAnorm : ‖A‖ ≤ 1 := unitary_norm_le_one hA
  have hBnorm : ‖B‖ ≤ 1 := unitary_norm_le_one hB
  have hAQ : Commute A Q := by
    exact (hQH.symm.smul_left (-(I / 2))).exp_left
  have hBP : Commute B P := by
    exact (hPH.symm.smul_left (I / 2)).exp_left
  have htransfer := transfer hP hQ hP hQ hA hB hAQ hBP
    (U := evolution H T T) (W := Wk)
  have hleak : ‖(1 - Q) * Wk * P‖ ≤ C / T + ‖A * Wk * B - evolution H T T‖ := by
    have hright := (abs_le.1 htransfer).2
    simp only [sub_self, norm_zero, add_zero, mul_zero] at hright
    linarith
  have hround : roundedEvolution H T T = A * W * B :=
    roundedEvolution_end dieudonne_10_5_4 hH hT
  have hsplit : ‖A * Wk * B - evolution H T T‖ ≤
      ‖Wk - W‖ + ‖roundedEvolution H T T - evolution H T T‖ := by
    calc
      _ = ‖A * (Wk - W) * B + (A * W * B - evolution H T T)‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖A * (Wk - W) * B‖ + ‖A * W * B - evolution H T T‖ :=
        norm_add_le _ _
      _ ≤ ‖Wk - W‖ + ‖A * W * B - evolution H T T‖ := by
        gcongr
        exact (norm_mul_le_of_le (norm_mul_le_of_le hAnorm le_rfl) hBnorm).trans_eq
          (by ring)
      _ = _ := by rw [hround]
  have hHk : IsTimeDepHamiltonian Hk := by
    intro s hs
    exact entrywise_isHermitian (truncation_bits (d := d) k).1 (hH s hs)
  have hsample : ‖Wk - W‖ ≤ T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
    calc
      _ ≤ ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖ :=
        unit_transfer_stepProduct_error dieudonne_7_6_1 dieudonne_section_8_7 hT hH hHk
      _ ≤ ∑ _j ∈ Finset.range T, √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (truncation_bits k).2 H hH
        constructor
        · positivity
        · apply (div_le_one hTr).2
          exact_mod_cast (Finset.mem_range.1 hj).le
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hclock : ‖roundedEvolution H T T - evolution H T T‖ ≤ E / T := by
    exact rounded_clock_bound dieudonne_7_6_1 dieudonne_section_8_7 dieudonne_8_6_4
      dlmf_4_22_5 dieudonne_10_5_4 dieudonne_10_6_3
      hT hH hL hw hwidth
  have htime : (C + E) / T ≤ δ / 2 := by
    have h := (div_le_iff₀ hδ).1 hTδ
    apply (div_le_iff₀ hTr).2
    linarith
  have hbits : T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) ≤ δ / 2 := by
    have h := mul_le_mul_of_nonneg_left hk hTr.le
    convert h using 1
    all_goals field_simp
  change ‖(1 - Q) * Wk * P‖ ≤ δ
  calc
    _ ≤ C / T + ‖A * Wk * B - evolution H T T‖ := hleak
    _ ≤ C / T + ‖Wk - W‖ +
        ‖roundedEvolution H T T - evolution H T T‖ := by linarith [hsplit]
    _ ≤ (C + E) / T + T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
      calc
        _ ≤ C / T + T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) + E / T := by
          gcongr
        _ = _ := by ring
    _ ≤ δ / 2 + δ / 2 := add_le_add htime hbits
    _ = δ := by ring

/-- **Theorem 4.6.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3)
with the remark (10.4.6),
DLMF 4.22.5 and Bhatia Corollary III.2.6, let `T`, `H`, `L`, and `w` satisfy the
hypotheses of Theorem 4.2, with `H` twice continuously differentiable and every `H(s)` having
eigenvalue differences of modulus at most `w`, and let `W = e^{-iH}`. Then the evolution `U` of
`H(t/T)` and
`V(T) = e^{-iH(1)/2} W((T-1)/T) ⋯ W(0) e^{iH(0)/2}` satisfy
`‖e^{-iH(1)/2} W((T-1)/T) ⋯ W(0) e^{iH(0)/2} - U(T)‖ ≤ ℰ̃_w(W)/T`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem unitary_products (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hSampleWidth : HasSampleWidth H T w) (hC2 : IsC2Family H)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) w) :
    let W := fun s ↦ exp (-I • H s)
    ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      ℰtilde w W / T := by
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  change ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) -
    evolution H T T‖ ≤ ℰtilde w W / T
  -- Equation (2.5) identifies the rounded endpoint.
  have hendpoint := roundedEvolution_end dieudonne_10_5_4 hH hT
  change roundedEvolution H T T =
    exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) at hendpoint
  rw [← hendpoint]
  have hw0 : 0 ≤ w := by
    have hs := (sorted_eigenvalues (hH 0 (by norm_num))).2.1
    simpa using hwidth 0 (by norm_num) _ hs _ hs
  have hκ : 0 ≤ κ w := by
    unfold κ
    split_ifs with hz
    · norm_num
    · exact div_nonneg (by positivity)
        (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).le
  have hc0 := c₀_nonneg_of_width dlmf_4_22_5 hw0 hw
  have hc1 : 0 ≤ c₁ w := by unfold c₁; positivity
  have hN := 𝒩_nonneg_of_width hw0 hw
  have hN' := deriv_𝒩_nonneg hw0 hw
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := sub_nonneg.mpr (𝒩_zero_le hw0 hw)
  -- Lemma A.2: logarithm bounds, followed by their suprema.
  have hlog := phase_log_derivative_bounds bhatia_corollary_III_2_6 hH hw0 hw hC2 hwidth
  have hW1 : ContinuousOn (∂W) (Icc (0 : ℝ) 1) :=
    hC2.phase.deriv_contDiffOn.continuousOn
  have hW2 : ContinuousOn (∂∂W) (Icc (0 : ℝ) 1) := hC2.phase.continuousOn_deriv2
  have hH0 := supNorm_nonneg_of_continuousOn hC2.deriv_contDiffOn.continuousOn
  have hW0 := supNorm_nonneg_of_continuousOn hW1
  have hfirst : ‖∂H‖∞ ≤ κ w * ‖∂W‖∞ := by
    apply supNorm_le_of_forall
    intro s hs
    exact (hlog s hs).1.trans
      (mul_le_mul_of_nonneg_left (norm_le_supNorm_of_continuousOn hW1 hs) hκ)
  have hsecond : ‖∂∂H‖∞ ≤ κ w * ‖∂∂W‖∞ + ‖∂W‖∞ ^ 2 / Real.cos (w / 4) ^ 2 := by
    apply supNorm_le_of_forall
    intro s hs
    exact (hlog s hs).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (norm_le_supNorm_of_continuousOn hW2 hs) hκ)
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_supNorm_of_continuousOn hW1 hs) 2)
        (sq_nonneg _)))
  have hend : ‖∂H 0‖ + ‖∂H 1‖ ≤ κ w * (‖∂W 0‖ + ‖∂W 1‖) := by
    calc
      _ ≤ κ w * ‖∂W 0‖ + κ w * ‖∂W 1‖ :=
        add_le_add (hlog 0 (by norm_num)).1 (hlog 1 (by norm_num)).1
      _ = _ := by ring
  -- Lemma A.3(ii): integrate each corrector jump and sum the cell estimates.
  have hjump := jump_sum_le dieudonne_8_6_4 hT hH hw0 hw hwidth hC2
  -- Theorem 4.2 with L equal to the second-derivative supremum.
  have hclock := rounded_clock_comparison dieudonne_7_6_1 dieudonne_section_8_7 dlmf_4_22_5
    dieudonne_10_5_4 dieudonne_10_6_3 hT hH
    hC2.hasLipschitzDerivative hw hSampleWidth
  have hcombined : ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + (1 / 24 + 𝒩 w) * ‖∂∂H‖∞ +
        (c₁ w + (𝒩 w - 𝒩 0)) * ‖∂H‖∞ ^ 2 +
        2 * deriv 𝒩 w * ‖∂W‖∞ * ‖∂H‖∞) / T := by
    calc
      _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + ‖∂∂H‖∞ / 24 +
          c₁ w * ‖∂H‖∞ ^ 2) / T +
          (𝒩 w * ‖∂∂H‖∞ + 2 * deriv 𝒩 w * ‖∂W‖∞ * ‖∂H‖∞ +
            (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2) / T :=
        hclock.trans (add_le_add (le_refl _) hjump)
      _ = _ := by ring
  -- Substitute the logarithm estimates and collect the coefficient c₂.
  apply hcombined.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ c₀ w * (κ w * (‖∂W 0‖ + ‖∂W 1‖)) +
        (1 / 24 + 𝒩 w) * (κ w * ‖∂∂W‖∞ + ‖∂W‖∞ ^ 2 / Real.cos (w / 4) ^ 2) +
        (c₁ w + (𝒩 w - 𝒩 0)) * (κ w * ‖∂W‖∞) ^ 2 +
        2 * deriv 𝒩 w * ‖∂W‖∞ * (κ w * ‖∂W‖∞) :=
      add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hend hc0)
          (mul_le_mul_of_nonneg_left hsecond (by positivity)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hfirst 2) (add_nonneg hc1 htail)))
        (mul_le_mul_of_nonneg_left hfirst (by positivity))
    _ = ℰtilde w W := by unfold ℰtilde c₂; ring

/-- **Theorem 4.7.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3)
with the remark (10.4.6),
DLMF 4.22.5 and Bhatia Corollary III.2.6, let `T ≥ 1` be an integer, and let a twice
continuously differentiable unitary family
`W` have a band of `m` eigenvalues `{e^{-iθ} : α(s) < θ < β(s)}` with
`α < β < α + 2π`, eigenphase gap continuous in `s`, and endpoint projectors `P` and `Q`. Let `ϑ`
be the least eigenphase gap over `s ∈ [0,1]`. Let `U` be the evolution of `H(t/T)` for the Hermitian
`H(s)` with `e^{-iH(s)} = W(s)` and spectrum in `(α(s), α(s) + 2π)`. Then, with `w = 2π - ϑ`,
`‖(1 - Q) W((T-1)/T) ⋯ W(0) P‖ ≤ ‖(1 - Q) U(T) P‖ + ℰ̃_w(W)/T`. -/
theorem walk_leakage (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6) [NeZero d]
    {T : ℕ} (hT : 1 ≤ T) {W : ℝ → 𝕄} {α β : ℝ → ℝ}
    (hband : IsArcBandFamily W α β) (m : ℕ)
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, eigenvalueCount (W s) (arc (α s) (β s)) = m)
    (hgap : IsContinuousFamily (fun s ↦ eigenphaseGap (W s) (α s) (β s)))
    (hC2 : IsC2Family W) :
    let ϑ := sInf ((fun s ↦ eigenphaseGap (W s) (α s) (β s)) '' Icc 0 1)
    let P := arcBandProjector (W 0) (α 0) (β 0)
    let Q := arcBandProjector (W 1) (α 1) (β 1)
    ∀ H, IsLogarithm W α H →
      ‖(1 - Q) * sampleProduct W T * P‖ ≤
        ‖(1 - Q) * evolution H T T * P‖ + ℰtilde (2 * π - ϑ) W / T := by
  dsimp only
  intro H hHlog
  obtain ⟨hϑ, hϑ_le⟩ := WalkLeakageGap.gap_minimum hband hgap
  obtain ⟨G, hGlog, hGcont⟩ :=
    WalkLeakageLog.exists_continuous_logarithm hband hC2.continuousOn
  -- Open-turn uniqueness transfers continuity to the given logarithm.
  have hHG : EqOn H G (Icc 0 1) :=
    WalkLeakageUnique.logarithms_eqOn hHlog hGlog
  have hHcont : IsContinuousFamily H := ContinuousOn.congr hGcont hHG
  let ℓ := fun s ↦ sInf (spectrum ℝ (H s))
  have hℓ : IsContinuousFamily ℓ :=
    WalkLeakageBhatia.continuous_sInf bhatia_corollary_III_2_6 hHlog.1 hHcont
  have henclosure : ∀ s ∈ Icc (0 : ℝ) 1,
      IsLeast (spectrum ℝ (H s)) (ℓ s) ∧
        HasRealSpectrumIn (H s) (Icc (ℓ s) (ℓ s + (2 * π -
          sInf ((fun t ↦ eigenphaseGap (W t) (α t) (β t)) '' Icc 0 1)))) := by
    intro s hs
    apply WalkLeakageSpectrum.spectrum_enclosure (hband.2.2 s hs)
    · rw [← hHlog.2.1 s hs]
      exact WalkLeakageSpectrum.spectrum_phase_image (hHlog.1 s hs)
    · exact hHlog.2.2 s hs
    · exact hϑ_le s hs
  let w := 2 * π -
    sInf ((fun t ↦ eigenphaseGap (W t) (α t) (β t)) '' Icc 0 1)
  -- The enclosure contains its least eigenvalue, so its width is nonnegative.
  have hw0 : 0 ≤ w := by
    have hs : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h := (henclosure 0 hs).2 (henclosure 0 hs).1.1
    change ℓ 0 ≤ ℓ 0 ∧ ℓ 0 ≤ ℓ 0 + w at h
    linarith [h.2]
  have hw : w < 2 * π := by
    dsimp [w]
    linarith
  -- Exponentiating the real enclosure gives the phase interval for Lemma A.2.
  have harc : HasSpectrumInPhaseInterval W ℓ w := by
    intro s hs z hz
    rw [← hHlog.2.1 s hs,
      WalkLeakageSpectrum.spectrum_phase_image (hHlog.1 s hs)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact ⟨θ, (henclosure s hs).2 hθ, rfl⟩
  have hW : IsUnitaryFamily W 0 1 := by
    intro s hs
    exact (hband.2.2 s hs).1
  obtain ⟨K, hKherm, hKspec, hKunique, hKC2, hKderiv⟩ :=
    walk_log hw0 hw hℓ hW harc hC2
  have hHK : EqOn H K (Icc 0 1) := by
    intro s hs
    exact hKunique s hs (H s) (hHlog.1 s hs) (henclosure s hs).2 (hHlog.2.1 s hs)
  -- Lemma A.2 gives C² regularity of H by uniqueness on the unit interval.
  have hHC2 : IsC2Family H := ContDiffOn.congr hKC2 hHK
  have hHwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) w := by
    intro s hs x hx y hy
    have hx_bounds := (henclosure s hs).2 hx
    have hy_bounds := (henclosure s hs).2 hy
    apply abs_le.mpr
    constructor <;> linarith [hx_bounds.1, hx_bounds.2, hy_bounds.1, hy_bounds.2]
  have hHsample : HasSampleWidth H T w := by
    intro j hj
    have hTpos : (0 : ℝ) < T := by
      exact_mod_cast (show 0 < T from lt_of_lt_of_le Nat.zero_lt_one hT)
    have hjT : (j : ℝ) ≤ T := by exact_mod_cast hj
    have hs : (j : ℝ) / (T : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one hTpos).mpr hjT
    exact hHwidth _ hs
  -- Compactness turns the C² logarithm into the regularity required by Theorem 4.6.
  obtain ⟨L, hHL⟩ := WalkLeakageRegularity.exists_lipschitz_derivative hHC2
  have hHexp : EqOn (fun s ↦ exp (-I • H s)) W (Icc 0 1) :=
    fun s hs ↦ hHlog.2.1 s hs
  -- Interval agreement transports every sample and both within derivatives.
  have hproducts := WalkLeakageTransport.sampleProduct_eq hHexp hT
  have henergy := WalkLeakageTransport.energy_eq hHexp w
  have hcomparison :
      ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) -
        evolution H T T‖ ≤ ℰtilde w W / T := by
    have h := unitary_products dieudonne_7_6_1 dieudonne_section_8_7 dieudonne_8_6_4
      dlmf_4_22_5 bhatia_corollary_III_2_6 dieudonne_10_5_4 dieudonne_10_6_3
      hT hHlog.1 hHL hw hHsample hHC2 hHwidth
    dsimp only at h
    rw [hproducts, henergy] at h
    exact h
  -- The open-turn logarithm identifies the arc projectors with its real band projectors.
  have hprojectors : ∀ s ∈ Icc (0 : ℝ) 1,
      arcBandProjector (W s) (α s) (β s) = bandProjector (H s) (α s) (β s) := by
    intro s hs
    rw [← hHlog.2.1 s hs]
    apply walk_arcBandProjector_exp (hHlog.1 s hs) (hband.2.2 s hs).2.2.1
    intro j
    exact hHlog.2.2 s hs ((hHlog.1 s hs).eigenvalues_mem_spectrum_real j)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hP := walk_arcProjector_isOrthogonal (W 0) (α 0) (β 0)
  have hQ := walk_arcProjector_isOrthogonal (W 1) (α 1) (β 1)
  have hBP : Commute (exp ((I / 2) • H 0)) (arcBandProjector (W 0) (α 0) (β 0)) := by
    rw [hprojectors 0 h0]
    exact walk_phase_commute_bandProjector (hHlog.1 0 h0) _ _ _
  have hAQ : Commute (exp (-(I / 2) • H 1)) (arcBandProjector (W 1) (α 1) (β 1)) := by
    rw [hprojectors 1 h1]
    exact walk_phase_commute_bandProjector (hHlog.1 1 h1) _ _ _
  -- Proposition 2.4 removes the endpoint phases without moving either projector.
  have htransfer := transfer (U := evolution H T T) (W := sampleProduct W T)
    hP hQ hP hQ (walk_negative_halfPhase_isUnitary (hHlog.1 1 h1))
    (walk_positive_halfPhase_isUnitary (hHlog.1 0 h0)) hAQ hBP
  simp only [sub_self, norm_zero, add_zero, mul_zero] at htransfer
  have hupper := (abs_le.mp htransfer).2
  simpa only [add_comm] using sub_le_iff_le_add.mp (hupper.trans hcomparison)

end RoundedClocks
