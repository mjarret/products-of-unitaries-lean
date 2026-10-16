/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UniformConstants

/-! # Scalar coefficients for the Jacobi end-value estimate -/
@[expose] public section
noncomputable section
open Real Set Filter
open scoped Topology
open UnitaryProducts.Corrector UnitaryProducts.Paper UnitaryProducts.Prose
namespace UnitaryProducts.PaperProof

/-- Theorem B's decimal bounds, for `a = 2c₀ + 1/24 + N(π)` and
`b = c₁ + 2N'(π)`. -/
theorem intro_constants :
    1 / π - 1 / π ^ 2 + 1 / 24 ≤ (26 / 100 : ℝ) ∧
    5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 ≤ (61 / 1000 : ℝ) := by
  have hlo : (10000 / 31416 : ℝ) ≤ 1 / π := by
    apply (le_div_iff₀ pi_pos).mpr
    linarith [Real.pi_lt_d4]
  have hhi : 1 / π ≤ (10000 / 31415 : ℝ) := by
    apply (div_le_iff₀ pi_pos).mpr
    linarith [Real.pi_gt_d4]
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 2
  have hcubelo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 3
  have hA : 1 / π - 1 / π ^ 2 + 1 / 24 = 1 / π - (1 / π) ^ 2 + 1 / 24 := by ring
  have hB : 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 =
      5 / 8 * (1 / π) - 1 / 4 * (1 / π) ^ 2 - 4 * (1 / π) ^ 3 + 1 / 64 := by ring
  rw [hA, hB]
  constructor <;> linarith

/-- The squared unitary-derivative coefficient in Theorem 4.5. -/
def walk_square (w : ℝ) : ℝ :=
  (1 / 24 + frameBound w) / Real.cos (w / 4) ^ 2 +
    uniform_c1 w * walkLogSlope w ^ 2 + 2 * frameLip w * walkLogSlope w +
    (frameBound w - frameBound 0) * walkLogSlope w ^ 2

/-- The displayed definition of `c₂`, expressed in the paper's series and
continuous sine quotient. -/
theorem walk_square_eq_paper {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let κ : ℝ → ℝ := fun x ↦ if x = 0 then 1 else (x / 2) / Real.sin (x / 2)
    walk_square w = (1 / 24 + N w) / Real.cos (w / 4) ^ 2 +
      ((N w - N (w / 2) / 2) / 4 + 1 / 64) * κ w ^ 2 +
      2 * deriv N w * κ w + (N w - N 0) * κ w ^ 2 := by
  intro N κ
  rw [show κ w = walkLogSlope w from walkLogSlope_closed hw0 hw]
  dsimp only [N]
  rw [(paper_series_eq hw0 hw).1, (paper_series_eq hw0 hw).2,
    (paper_series_eq (show 0 ≤ w / 2 by positivity)
      (show w / 2 < 2 * π by linarith)).1,
    (paper_series_eq (le_refl 0) (by positivity : (0 : ℝ) < 2 * π)).1]
  rfl

/-- Substitution of the logarithm derivative bounds collects precisely `c₂`.
This is the last algebraic step of the proof of Theorem 4.5. -/
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

/-- The four summands in the proof of Theorem 4.5 contribute respectively
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
  obtain ⟨_, hR, _⟩ := walk_constant_chord_limit
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

/-- Theorem 4.5's two inverse-square coefficients and inverse-cube coefficient. -/
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

/-- The asymptotic equivalents displayed in Theorem 4.5. -/
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

/-- The leading expression displayed in the last line of Theorem 4.5's proof. -/
def walk_leading (w : ℝ) : ℝ :=
  frameBound w / Real.cos (w / 4) ^ 2 +
    frameBound w / 4 * walkLogSlope w ^ 2 +
    2 * frameLip w * walkLogSlope w + frameBound w * walkLogSlope w ^ 2

/-- The leading expression has the same cubic-order limit as `c₂`. -/
theorem walk_leading_limit :
    Tendsto (fun θ ↦ walk_leading (2 * π - θ) * θ ^ 3)
      (𝓝[>] 0) (𝓝 (8 / π + 5 * π / 2 + 2)) := by
  obtain ⟨hS, hN, hD, _, _⟩ := scalar_edge_limits
  obtain ⟨_, hR, _⟩ := walk_constant_chord_limit
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

/-- Both asymptotic equivalences in the final display of Theorem 4.5. -/
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
