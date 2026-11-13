/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ScalarGapLimits
public import UnitaryProducts.PaperProof.UniformConstants

/-! # Scalar coefficients for the Jacobi end-value estimate -/
@[expose] public section
noncomputable section
open Real Set Filter
open scoped Topology
open UnitaryProducts.Corrector UnitaryProducts.Paper UnitaryProducts.Prose
namespace UnitaryProducts.PaperProof

/-- Appendix B: the squared unitary-derivative coefficient used in Theorem 4.6. -/
def walk_square (w : ℝ) : ℝ :=
  (1 / 24 + frameBound w) / Real.cos (w / 4) ^ 2 +
    uniform_c1 w * walkLogSlope w ^ 2 + 2 * frameLip w * walkLogSlope w +
    (frameBound w - frameBound 0) * walkLogSlope w ^ 2

/-- Substitution of the logarithm derivative bounds collects precisely `c₂`.
This is the last algebraic step of the proof of Theorem 4.6. -/
theorem walk_collect (w E L M : ℝ) :
    uniform_c0 w * (walkLogSlope w * E) +
      (1 / 24 + frameBound w) *
        (walkLogSlope w * M + L ^ 2 / Real.cos (w / 4) ^ 2) +
      (uniform_c1 w + frameBound w - frameBound 0) * (walkLogSlope w * L) ^ 2 +
      2 * frameLip w * L * (walkLogSlope w * L) =
    uniform_c0 w * walkLogSlope w * E + walkUniformSecond w * M +
      walk_square w * L ^ 2 := by
  dsimp [walkUniformSecond, walk_square]
  ring

/-- The scalar estimates consumed by the four leading terms of `c₂`. -/
theorem scalar_edge_limits :
    Tendsto (fun θ ↦ θ * walkLogSlope (2 * π - θ)) (𝓝[>] 0) (𝓝 (2 * π)) ∧
    Tendsto (fun θ ↦ θ * frameBound (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun θ ↦ θ ^ 2 * frameLip (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun θ ↦ θ * uniform_c0 (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun θ ↦ θ * uniform_c1 (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (8 * π))) := by
  obtain ⟨_, _, hS, _, hN, hD, _, _, _⟩ := walk_constant_limit
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply hS.congr'
    filter_upwards [hev] with θ hθ
    rw [walkLogSlope_closed (by linarith [hθ.2, pi_pos]) (by linarith [hθ.1])]
  · apply hN.congr'
    filter_upwards [hev] with θ hθ
    rw [(paper_series_eq (by linarith [hθ.2, pi_pos] : 0 ≤ 2 * π - θ)
      (by linarith [hθ.1] : 2 * π - θ < 2 * π)).1]
  · apply hD.congr'
    filter_upwards [hev] with θ hθ
    rw [(paper_series_eq (by linarith [hθ.2, pi_pos] : 0 ≤ 2 * π - θ)
      (by linarith [hθ.1] : 2 * π - θ < 2 * π)).2]
  · apply uniform_c0_c1_div_frame_limits.1.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    rw [(paper_series_eq hw0 hw).1,
      (paper_series_eq (by positivity : 0 ≤ (2 * π - θ) / 2)
        (by linarith : (2 * π - θ) / 2 < 2 * π)).1]
    rfl
  · apply uniform_c0_c1_div_frame_limits.2.1.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    rw [(paper_series_eq hw0 hw).1,
      (paper_series_eq (by positivity : 0 ≤ (2 * π - θ) / 2)
        (by linarith : (2 * π - θ) / 2 < 2 * π)).1]
    rfl

/-- The four summands in Appendix B's asymptotic proof contribute respectively
`8/π`, `π/2`, `2`, and `2π` after multiplication by the cubed free arc. -/
theorem walk_square_leading_terms :
    Tendsto (fun θ ↦ θ ^ 3 * ((1 / 24 + frameBound (2 * π - θ)) /
      Real.cos ((2 * π - θ) / 4) ^ 2)) (𝓝[>] 0) (𝓝 (8 / π)) ∧
    Tendsto (fun θ ↦ θ ^ 3 * (uniform_c1 (2 * π - θ) *
      walkLogSlope (2 * π - θ) ^ 2)) (𝓝[>] 0) (𝓝 (π / 2)) ∧
    Tendsto (fun θ ↦ θ ^ 3 * (2 * frameLip (2 * π - θ) *
      walkLogSlope (2 * π - θ))) (𝓝[>] 0) (𝓝 2) ∧
    Tendsto (fun θ ↦ θ ^ 3 * ((frameBound (2 * π - θ) - frameBound 0) *
      walkLogSlope (2 * π - θ) ^ 2)) (𝓝[>] 0) (𝓝 (2 * π)) := by
  obtain ⟨hS, hN, hD, _, hC⟩ := scalar_edge_limits
  have hR := tendsto_gap_div_cos
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((hid.div_const 24).add hN).mul (hR.pow 2)
    rw [show (0 / 24 + 1 / (2 * π)) * 4 ^ 2 = 8 / π by ring] at h
    convert h using 1
    exact funext fun θ ↦ by ring
  · have h := hC.mul (hS.pow 2)
    rw [show (1 / (8 * π)) * (2 * π) ^ 2 = π / 2 by field_simp; ring] at h
    convert h using 1
    exact funext fun θ ↦ by ring
  · have h := (hD.const_mul 2).mul hS
    rw [show 2 * (1 / (2 * π)) * (2 * π) = 2 by field_simp] at h
    convert h using 1
    exact funext fun θ ↦ by ring
  · have h := (hN.sub (hid.mul_const (frameBound 0))).mul (hS.pow 2)
    rw [show (1 / (2 * π) - 0 * frameBound 0) * (2 * π) ^ 2 = 2 * π by
      field_simp; ring] at h
    convert h using 1
    exact funext fun θ ↦ by ring

/-- Appendix B: the two inverse-square coefficients and inverse-cube coefficient. -/
theorem walk_coefficient_limits :
    Tendsto (fun θ ↦ uniform_c0 (2 * π - θ) * walkLogSlope (2 * π - θ) * θ ^ 2)
      (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun θ ↦ walkUniformSecond (2 * π - θ) * θ ^ 2)
      (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun θ ↦ walk_square (2 * π - θ) * θ ^ 3)
      (𝓝[>] 0) (𝓝 (8 / π + 5 * π / 2 + 2)) := by
  obtain ⟨hS, hN, _, hC, _⟩ := scalar_edge_limits
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨?_, ?_, ?_⟩
  · have h := hC.mul hS
    rw [show (1 / (2 * π)) * (2 * π) = 1 by field_simp] at h
    convert h using 1
    exact funext fun θ ↦ by ring
  · have h := ((hid.div_const 24).add hN).mul hS
    rw [show (0 / 24 + 1 / (2 * π)) * (2 * π) = 1 by field_simp; ring] at h
    convert h using 1
    exact funext fun θ ↦ by dsimp [walkUniformSecond]; ring
  · obtain ⟨h1, h2, h3, h4⟩ := walk_square_leading_terms
    have h := ((h1.add h2).add h3).add h4
    rw [show 8 / π + π / 2 + 2 + 2 * π = 8 / π + 5 * π / 2 + 2 by ring] at h
    convert h using 1
    exact funext fun θ ↦ by dsimp [walk_square]; ring

/-- The asymptotic equivalents displayed in Appendix B. -/
theorem walk_coefficient_equivalents :
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun θ ↦ uniform_c0 (2 * π - θ) * walkLogSlope (2 * π - θ))
      (fun θ ↦ 1 / θ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walkUniformSecond (2 * π - θ))
      (fun θ ↦ 1 / θ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walk_square (2 * π - θ))
      (fun θ ↦ (8 / π + 5 * π / 2 + 2) / θ ^ 3) := by
  have convert_limit (f : ℝ → ℝ) (p : ℕ) (c : ℝ) (hc : c ≠ 0)
      (h : Tendsto (fun θ ↦ f θ * θ ^ p) (𝓝[>] 0) (𝓝 c)) :
      Asymptotics.IsEquivalent (𝓝[>] 0) f (fun θ ↦ c / θ ^ p) := by
    apply Asymptotics.isEquivalent_of_tendsto_one
    have hh := h.div_const c
    rw [div_self hc] at hh
    simpa only [Pi.div_def, div_div_eq_mul_div] using hh
  obtain ⟨h1, h2, h3⟩ := walk_coefficient_limits
  exact ⟨convert_limit _ 2 1 one_ne_zero h1,
    convert_limit _ 2 1 one_ne_zero h2,
    convert_limit _ 3 _ (by positivity) h3⟩

/-- The leading expression in the final display of Appendix B. -/
def walk_leading (w : ℝ) : ℝ :=
  frameBound w / Real.cos (w / 4) ^ 2 +
    frameBound w / 4 * walkLogSlope w ^ 2 +
    2 * frameLip w * walkLogSlope w + frameBound w * walkLogSlope w ^ 2

/-- The leading expression has the same cubic-order limit as `c₂`. -/
theorem walk_leading_limit :
    Tendsto (fun θ ↦ walk_leading (2 * π - θ) * θ ^ 3)
      (𝓝[>] 0) (𝓝 (8 / π + 5 * π / 2 + 2)) := by
  obtain ⟨hS, hN, hD, _, _⟩ := scalar_edge_limits
  have hR := tendsto_gap_div_cos
  have h1 := hN.mul (hR.pow 2)
  have h2 := (hN.div_const 4).mul (hS.pow 2)
  have h3 := (hD.const_mul 2).mul hS
  have h4 := hN.mul (hS.pow 2)
  have h := ((h1.add h2).add h3).add h4
  rw [show 1 / (2 * π) * 4 ^ 2 + (1 / (2 * π) / 4) * (2 * π) ^ 2 +
      2 * (1 / (2 * π)) * (2 * π) + 1 / (2 * π) * (2 * π) ^ 2 =
      8 / π + 5 * π / 2 + 2 by field_simp; ring] at h
  convert h using 1
  exact funext fun θ ↦ by dsimp [walk_leading]; ring

/-- Both asymptotic equivalences in the final display of Appendix B. -/
theorem walk_leading_equivalents :
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walk_square (2 * π - θ))
      (fun θ ↦ walk_leading (2 * π - θ)) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walk_leading (2 * π - θ))
      (fun θ ↦ (8 / π + 5 * π / 2 + 2) / θ ^ 3) := by
  have hlead : Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun θ ↦ walk_leading (2 * π - θ))
      (fun θ ↦ (8 / π + 5 * π / 2 + 2) / θ ^ 3) := by
    apply Asymptotics.isEquivalent_of_tendsto_one
    have h := walk_leading_limit.div_const (8 / π + 5 * π / 2 + 2)
    rw [div_self (by positivity : (8 / π + 5 * π / 2 + 2 : ℝ) ≠ 0)] at h
    simpa only [Pi.div_def, div_div_eq_mul_div] using h
  exact ⟨walk_coefficient_equivalents.2.2.trans hlead.symm, hlead⟩

end UnitaryProducts.PaperProof
