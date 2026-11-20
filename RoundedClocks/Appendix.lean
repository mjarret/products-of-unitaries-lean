/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

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

/-- **Lemma A.1.** Let `0 ≤ w < 2π`, let `Ω` be Hermitian with eigenvalue differences of modulus at
most `w`, and let `D` be a matrix. There is a continuously differentiable `Y(τ)` for `|τ| ≤ 1/2`
that solves `Y' + i[Ω,Y] = τD` with end values `Y(-1/2) = Y(1/2) = 𝒩([Ω,·])D`, and satisfies
`‖Y(0)‖ ≤ c₀ ‖D‖` and `‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2` for `|τ| ≤ 1/2`. -/
theorem cell {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hwidth : HasWidth Ω w) (D : 𝕄) :
    ∃ Y : ℝ → 𝕄, ContDiffOn ℝ 1 Y (Icc (-1 / 2) (1 / 2)) ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ) ∧
      Y (-1 / 2) = 𝒩ad Ω D ∧ Y (1 / 2) = 𝒩ad Ω D ∧ ‖Y 0‖ ≤ c₀ w * ‖D‖ ∧
      ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 := by
  rw [Bridge.𝒩ad_eq]
  exact UnitaryProducts.PaperProof.lem_cell hw0 hw hΩ hwidth D

/-- **Lemma A.2.** Let `0 ≤ w < 2π`, let `a` be continuous on `[0,1]`, and let `W(s)` for
`s ∈ [0,1]` be a twice continuously differentiable unitary family whose spectrum lies in
`{e^{-iθ} : θ ∈ [a(s), a(s) + w]}`. Then `W = e^{-iH}` for exactly one Hermitian `H(s)` with
spectrum in `[a(s), a(s) + w]`, `H` is twice continuously differentiable, and for `s ∈ [0,1]`,
`‖H'(s)‖ ≤ κ ‖W'(s)‖` and `‖H''(s)‖ ≤ κ ‖W''(s)‖ + ‖W'(s)‖²/cos²(w/4)`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem walk_log [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc 0 1)) {W : ℝ → 𝕄} (hW : ∀ s ∈ Icc (0 : ℝ) 1, IsUnitary (W s))
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * θ))
    (hC2 : ContDiffOn ℝ 2 W (Icc 0 1)) :
    ∃ H : ℝ → 𝕄, IsTimeDepHamiltonian H ∧
      (∀ s ∈ Icc (0 : ℝ) 1, exp (-I • H s) = W s ∧ spectrum ℝ (H s) ⊆ Icc (a s) (a s + w)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ B : 𝕄, B.IsHermitian → spectrum ℝ B ⊆ Icc (a s) (a s + w) →
        exp (-I • B) = W s → B = H s) ∧
      ContDiffOn ℝ 2 H (Icc 0 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ‖∂H s‖ ≤ κ w * ‖∂W s‖ ∧
        ‖∂∂H s‖ ≤ κ w * ‖∂∂W s‖ + ‖∂W s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  obtain ⟨H, hH, h1, h2, h3, h4⟩ :=
    UnitaryProducts.PaperProof.lem_walk_log a w hw0 hw W ha hW harc hC2
  have hev (B : 𝕄) : UnitaryProducts.evol B 1 = exp (-I • B) := by
    simp [UnitaryProducts.evol]
  have hspec (B : 𝕄) (hB : B.IsHermitian) (s : ℝ) :
      spectrum ℝ B ⊆ Icc (a s) (a s + w) ↔ ∀ i, hB.eigenvalues i ∈ Icc (a s) (a s + w) := by
    rw [hB.spectrum_real_eq_range_eigenvalues, Set.range_subset_iff]
  refine ⟨H, hH, fun s hs ↦ ⟨(hev _).symm.trans (h1 s hs).2, (hspec _ (hH s hs) s).2 (h1 s hs).1⟩,
    fun s hs B hB hBs hBe ↦ h2 s hs B hB ((hspec B hB s).1 hBs) ((hev B).trans hBe), h3, h4⟩

/-- **Lemma A.3.** Let `0 ≤ w < 2π`, and let `Ω(s)` be twice continuously differentiable for
`s ∈ [0,1]`, with every `Ω(s)` Hermitian with eigenvalue differences of modulus at most `w`. Then
`𝒩([Ω,·])Ω'` is continuously differentiable, and for every `s ∈ [0,1]`,
(i) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖Ω'‖²`, and
(ii) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖(e^{-iΩ})'‖ ‖Ω'‖ + (𝒩(w) - 𝒩(0)) ‖Ω'‖²`. -/
theorem end_value {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : ℝ → 𝕄}
    (hΩ : IsTimeDepHamiltonian Ω) (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasWidth (Ω s) w)
    (hC2 : ContDiffOn ℝ 2 Ω (Icc 0 1)) :
    ContDiffOn ℝ 1 (fun s ↦ 𝒩ad (Ω s) (∂Ω s)) (Icc 0 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ + 2 * deriv 𝒩 w * ‖∂Ω s‖ ^ 2 ∧
        ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ +
          2 * deriv 𝒩 w * ‖∂(fun t ↦ exp (-I • Ω t)) s‖ * ‖∂Ω s‖ +
          (𝒩 w - 𝒩 0) * ‖∂Ω s‖ ^ 2 := by
  have h := UnitaryProducts.PaperProof.canonical_cell_curve hw0 hw hΩ hwidth hC2
  have hev : (fun t ↦ exp (-I • Ω t)) = fun t ↦ UnitaryProducts.evol (Ω t) 1 := by
    funext t
    simp [UnitaryProducts.evol]
  simp only [Bridge.𝒩ad_eq, hev]
  exact h

/-- **Fact B.1.** At width `π`, `c₀ = 1/(2π) - 1/π²`, `𝒩(π) = 1/π²`, `𝒩'(π) = 1/(4π) - 2/π³`, and
`ℰ_π(H) ≤ 0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²`. -/
theorem constants_at_pi :
    c₀ π = 1 / (2 * π) - 1 / π ^ 2 ∧ 𝒩 π = 1 / π ^ 2 ∧ deriv 𝒩 π = 1 / (4 * π) - 2 / π ^ 3 ∧
      ∀ (H : ℝ → 𝕄) (L : ℝ), HasLipschitzDerivative H L →
        ℰ π L H ≤ 0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2 := by
  have h0 := UnitaryProducts.PaperProof.hamiltonianEnergy_pi_le (d := d) (fun _ ↦ 0)
    (fun _ ↦ 0) (L := 0) ⟨fun _ _ ↦ hasDerivWithinAt_const _ _ _, fun _ _ _ _ ↦ by simp⟩
  refine ⟨h0.1, h0.2.1, h0.2.2.1, fun H L hH ↦ ?_⟩
  have h := (UnitaryProducts.PaperProof.hamiltonianEnergy_pi_le H (∂H)
    (Bridge.HasLipschitzDerivative.paper hH)).2.2.2
  rw [Bridge.ℰ_eq, Bridge.supNorm_eq]
  refine h.trans_eq ?_
  norm_num

/-- **Fact B.2.** As `w → 2π`, with `ϑ = 2π - w`, `c₀ κ ∼ (1/24 + 𝒩(w)) κ ∼ ϑ⁻²` and
`c₂ ∼ (8/π + 5π/2 + 2) ϑ⁻³`, so every coefficient of `ℰ̃_w(W)` is `O(ϑ⁻³)`. -/
theorem constants_near_two_pi :
    (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ (8 / π + 5 * π / 2 + 2) / ϑ ^ 3) ∧
      (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := UnitaryProducts.PaperProof.fact_arc
  have hev : ∀ᶠ ϑ in 𝓝[>] (0 : ℝ),
      UnitaryProducts.walkLogSlope (2 * π - ϑ) = κ (2 * π - ϑ) := by
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ϑ hϑ
    rw [← UnitaryProducts.walkLogSlope_closed (by linarith [hϑ.2, Real.pi_pos])
      (by linarith [hϑ.1])]
    rfl
  refine ⟨h1.congr_left ?_, h2.congr_left ?_, h3, h4, h5, h6⟩ <;>
    filter_upwards [hev] with ϑ h <;> rw [h] <;> rfl

end RoundedClocks
