/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.Appendix.ConstantsArc
public import RoundedClocks.Appendix.ConstantsPi
public import RoundedClocks.Appendix.LogarithmIntegral
public import RoundedClocks.Appendix.LogarithmEstimates
public import RoundedClocks.Appendix.CellFamily
public import RoundedClocks.Appendix.CellCenterBound
public import RoundedClocks.Appendix.CellGrowth
public import RoundedClocks.Appendix.EndValue

/-!
# Appendices A and B: spectral bounds and constants

The corrector of one cell (Lemma A.1), the Hermitian logarithm (Lemma A.2), the derivative of the
multiplier (Lemma A.3), and the constants (Facts B.1 and B.2).
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

/-- **Lemma A.1.** Assuming DLMF 4.22.5, let `0 ≤ w < 2π`, let `Ω` be a Hermitian matrix with
eigenvalue differences of modulus at most `w`, and let `D` be a matrix. There is a continuously
differentiable matrix-valued `Y(τ)` for `|τ| ≤ 1/2` such that: (i) `Y` solves
`Y' + i[Ω,Y] = τD`, with end values `𝒩([Ω,·])D`; and (ii) `‖Y(0)‖ ≤ c₀ ‖D‖` and
`‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2` for `|τ| ≤ 1/2`. -/
theorem cell (dlmf_4_22_5 : DLMF_4_22_5) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) (hwidth : HasEigenvalueDifferences Ω w) (D : 𝕄) :
    ∃ Y : ℝ → 𝕄, IsC1FamilyOn Y (-1 / 2) (1 / 2) ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
          (Icc (-1 / 2) (1 / 2)) τ) ∧
      Y (-1 / 2) = 𝒩ad Ω D ∧ Y (1 / 2) = 𝒩ad Ω D ∧ ‖Y 0‖ ≤ c₀ w * ‖D‖ ∧
      ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 := by
  -- The spectral multiplier family has the form in Lemma A.1.
  let Y : ℝ → 𝕄 := cellGuess Ω hΩ D
  -- The guess is continuously differentiable on the cell.
  have hC1 : IsC1FamilyOn Y (-1 / 2) (1 / 2) :=
    (cellGuess_contDiff Ω hΩ D).contDiffOn
  -- Differentiating verifies the corrector equation.
  have hODE : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
        (Icc (-1 / 2) (1 / 2)) τ := by
    intro τ hτ
    exact (cellGuess_hasDerivAt Ω hΩ D τ).hasDerivWithinAt
  -- Both endpoints give the correction multiplier.
  have hends : Y (-1 / 2) = 𝒩ad Ω D ∧ Y (1 / 2) = 𝒩ad Ω D :=
    cellGuess_endpoints hΩ D hw hwidth
  -- The cosecant partial fractions bound the centre value.
  have hcenter : ‖Y 0‖ ≤ c₀ w * ‖D‖ := by
    simpa only [Y, cellGuess] using
      norm_cellCenter_le dlmf_4_22_5 hw0 hw hΩ hwidth D
  -- Integrating the conjugated equation gives quadratic growth.
  have hgrowth : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 :=
    norm_le_of_cellEquation hΩ D hODE
  exact ⟨Y, hC1, hODE, hends.1, hends.2, hcenter, hgrowth⟩

/-- **Lemma A.2.** Let `0 ≤ w < 2π`, let `a` be continuous on `[0,1]`, and let `W(s)` for
`s ∈ [0,1]` be a twice continuously differentiable unitary family whose spectrum lies in
`{e^{-iθ} : θ ∈ [a(s), a(s) + w]}`. Then `W = e^{-iH}` for exactly one Hermitian `H(s)` with
spectrum in `[a(s), a(s) + w]`, `H` is twice continuously differentiable, and for `s ∈ [0,1]`,
`‖H'(s)‖ ≤ κ ‖W'(s)‖` and `‖H''(s)‖ ≤ κ ‖W''(s)‖ + ‖W'(s)‖²/cos²(w/4)`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem walk_log [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {a : ℝ → ℝ}
    (ha : IsContinuousFamily a) {W : ℝ → 𝕄} (hW : IsUnitaryFamily W 0 1)
    (harc : HasSpectrumInPhaseInterval W a w)
    (hC2 : IsC2Family W) :
    ∃ H : ℝ → 𝕄, IsTimeDepHamiltonian H ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        exp (-I • H s) = W s ∧ HasRealSpectrumIn (H s) (Icc (a s) (a s + w))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ B : 𝕄, IsHermitian B →
        HasRealSpectrumIn B (Icc (a s) (a s + w)) →
        exp (-I • B) = W s → B = H s) ∧
      IsC2Family H ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ‖∂H s‖ ≤ κ w * ‖∂W s‖ ∧
        ‖∂∂H s‖ ≤ κ w * ‖∂∂W s‖ + ‖∂W s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  classical
  have hex (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    WalkLog.walk_log_pointwise (a s) w (W s) (hW s hs) (harc s hs)
  let H : ℝ → 𝕄 := fun s ↦ if hs : s ∈ Icc (0 : ℝ) 1 then
    (hex s hs).choose else 0
  have hchosen (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (H s).IsHermitian ∧ HasRealSpectrumIn (H s) (Icc (a s) (a s + w)) ∧
        exp (-I • H s) = W s := by
    obtain ⟨hherm, hspec, hexp⟩ := (hex s hs).choose_spec
    exact ⟨by simpa only [H, dif_pos hs] using hherm,
      by simpa only [H, dif_pos hs] using hspec,
      by simpa only [H, dif_pos hs] using hexp⟩
  have hH : IsTimeDepHamiltonian H := fun s hs ↦ (hchosen s hs).1
  have he := fun s hs ↦ (hchosen s hs).2.2
  have hwindow := fun s hs ↦ (hchosen s hs).2.1
  have hunique : ∀ s ∈ Icc (0 : ℝ) 1, ∀ B : 𝕄, IsHermitian B →
      HasRealSpectrumIn B (Icc (a s) (a s + w)) →
      exp (-I • B) = W s → B = H s := by
    intro s hs B hB hBw hBe
    exact WalkLog.walk_log_unique hw hB hBw (hH s hs) (hwindow s hs)
      (hBe.trans (he s hs).symm)
  obtain ⟨hcH, hderiv⟩ :=
    WalkLog.walk_log_local_derivatives hw ha hC2 hW harc hH he hwindow
  refine ⟨H, hH, (fun s hs ↦ ⟨he s hs, hwindow s hs⟩), hunique, hcH, ?_⟩
  intro s₀ hs₀
  let μ := a s₀ + w / 2
  let c := Complex.exp (I * (μ : ℂ))
  have hcenter : HasRealSpectrumIn (H s₀) (Icc (μ - w / 2) (μ + w / 2)) := by
    convert hwindow s₀ hs₀ using 1
    all_goals
      dsimp [μ]
      congr 1
      all_goals ring
  have hphase : ‖c‖ = 1 := by
    dsimp [c]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hnorm (A : 𝕄) : ‖c • A‖ = ‖A‖ := by rw [norm_smul, hphase, one_mul]
  have hbounds := WalkLog.walkLog_integral_norm_bounds (hH s₀ hs₀) hw0 hw hcenter
    (c • ∂W s₀) (c • ∂∂W s₀)
  dsimp only at hbounds
  rw [he s₀ hs₀] at hbounds
  change ‖WalkLogCalculus.walkLogFirstIntegral (c • W s₀) (c • ∂W s₀)‖ ≤ _ ∧
    ‖WalkLogCalculus.walkLogSecondIntegral (c • W s₀) (c • ∂W s₀)
      (c • ∂∂W s₀)‖ ≤ _ at hbounds
  obtain ⟨hfirst, hsecond⟩ := hderiv s₀ hs₀
  constructor
  · rw [hfirst, norm_smul, Complex.norm_I, one_mul]
    simpa only [hnorm] using hbounds.1
  · rw [hsecond, norm_smul, Complex.norm_I, one_mul]
    simpa only [hnorm] using hbounds.2

/-- **Lemma A.3.** Assuming Dieudonné (8.6.4), let `0 ≤ w < 2π`, and let `Ω(s)` be
twice continuously differentiable for `s ∈ [0,1]`, with every `Ω(s)` Hermitian with eigenvalue
differences of modulus at most `w`. Then `𝒩([Ω,·])Ω'` is continuously differentiable, and for every
`s ∈ [0,1]`,
(i) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖Ω'‖²`, and
(ii) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖(e^{-iΩ})'‖ ‖Ω'‖ + (𝒩(w) - 𝒩(0)) ‖Ω'‖²`. -/
theorem end_value (dieudonne_8_6_4 : Dieudonne_8_6_4)
    [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : ℝ → 𝕄}
    (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω s) w)
    (hC2 : IsC2Family Ω) :
    IsC1Family (fun s ↦ 𝒩ad (Ω s) (∂Ω s)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ + 2 * deriv 𝒩 w * ‖∂Ω s‖ ^ 2 ∧
        ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ +
          2 * deriv 𝒩 w * ‖∂(fun t ↦ exp (-I • Ω t)) s‖ * ‖∂Ω s‖ +
          (𝒩 w - 𝒩 0) * ‖∂Ω s‖ ^ 2 := by
  -- The series derivative gives continuous differentiability and part (i).
  have hfirst := endValue_part_i_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hC2
  -- The centered Duhamel decomposition and Jacobi telescope give part (ii).
  exact ⟨hfirst.1, fun s hs ↦
    ⟨hfirst.2 s hs, endValue_part_ii_assembled dieudonne_8_6_4 hw0 hw hΩ hwidth hC2 s hs⟩⟩

/-- **Fact B.1.** At width `π`, `c₀ = 1/(2π) - 1/π²`, `𝒩(π) = 1/π²`, `𝒩'(π) = 1/(4π) - 2/π³`, and
`ℰ_π(H) ≤ 0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²`. -/
theorem constants_at_pi [NeZero d] :
    c₀ π = 1 / (2 * π) - 1 / π ^ 2 ∧ 𝒩 π = 1 / π ^ 2 ∧ deriv 𝒩 π = 1 / (4 * π) - 2 / π ^ 3 ∧
      ∀ (H : ℝ → 𝕄) (L : ℝ), HasLipschitzDerivative H L →
        ℰ π L H ≤ 0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2 := by
  refine ⟨?_, multiplier_values_at_pi.1, multiplier_values_at_pi.2, energy_pi_bound⟩
  simp only [c₀, if_neg Real.pi_ne_zero, Real.sin_pi_div_two]
  ring

/-- **Fact B.2.** As `w → 2π`, with `ϑ = 2π - w`, `c₀ κ ∼ (1/24 + 𝒩(w)) κ ∼ ϑ⁻²` and
`c₂ ∼ (8/π + 5π/2 + 2) ϑ⁻³`, so every coefficient of `ℰ̃_w(W)` is `O(ϑ⁻³)`. -/
theorem constants_near_two_pi :
    (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ (8 / π + 5 * π / 2 + 2) / ϑ ^ 3) ∧
      (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) := by
  exact ⟨free_arc_equivalents.1, free_arc_equivalents.2.1,
    free_arc_equivalents.2.2, free_arc_isBigO.1,
    free_arc_isBigO.2.1, free_arc_isBigO.2.2⟩

end RoundedClocks
