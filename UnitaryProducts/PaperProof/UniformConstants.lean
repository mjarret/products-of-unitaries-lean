/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ScalarGapLimits

public import UnitaryProducts.Prose.WalkComparisonJRS
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Prose.SyncSteps

/-!
# Constants for the comparison with a corrector on every rounded-clock cell

## Declarations

- `uniform_c0`
- `uniform_c0_c1_div_frame_limits`
- `uniform_c1`
- `uniform_linear_coefficient`
- `uniform_pi_coefficients`
- `uniform_quadratic_coefficient`
- `walkUniformSecond`
- `walkUniformSquare`
- `walkEta`
- `walk_c2_eq_paper`
- `walk_uniform_coefficient_equivalents`
- `walk_uniform_coefficient_limits`
- `walk_uniform_coefficients_mono`
- `walk_uniform_square_leading_terms`
-/

@[expose] public section
noncomputable section
open Real Set Filter
open UnitaryProducts.Corrector UnitaryProducts.Paper UnitaryProducts.Prose
open scoped Topology
namespace UnitaryProducts.PaperProof

/-- The endpoint coefficient for the periodic corrector. -/
def uniform_c0 (w : ℝ) : ℝ := frameBound w - frameBound (w / 2) / 2

/-- The quadratic residual coefficient when every cell has its corrector. -/
def uniform_c1 (w : ℝ) : ℝ := uniform_c0 w / 4 + 1 / 64

/-- The coefficient of a common bound on the first and second derivatives. -/
def uniform_linear_coefficient (w : ℝ) : ℝ :=
  2 * uniform_c0 w + 1 / 24 + frameBound w

/-- The coefficient of the squared first derivative bound. -/
def uniform_quadratic_coefficient (w : ℝ) : ℝ := uniform_c1 w + 2 * frameLip w


/-- Exact coefficients at width pi, before any numerical relaxation. -/
theorem uniform_pi_coefficients :
    uniform_linear_coefficient π = 1 / π - 1 / π ^ 2 + 1 / 24 ∧
    uniform_quadratic_coefficient π =
      5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 := by
  dsimp [uniform_linear_coefficient, uniform_quadratic_coefficient, uniform_c1, uniform_c0]
  rw [frameBound_center_pi, frameBound_frameLip_pi.1, frameBound_frameLip_pi.2]
  constructor <;> field_simp <;> ring

/-- The new coefficient of the walk's second derivative bound. -/
def walkUniformSecond (w : ℝ) : ℝ := (1 / 24 + frameBound w) * walkLogSlope w

/-- The coefficient `η = (1+S)/(2(π²-w²/4)cos(w/4))` of the spectral comparison and the walk
comparison. -/
def walkEta (w : ℝ) : ℝ :=
  (1 + walkLogSlope w) / (2 * (π ^ 2 - w ^ 2 / 4) * Real.cos (w / 4))


/-- The new coefficient of the walk's squared first derivative bound. -/
def walkUniformSquare (w : ℝ) : ℝ :=
  1 / (24 * Real.cos (w / 4) ^ 2) + uniform_c1 w * walkLogSlope w ^ 2 + walkEta w

/-- The coefficient `c₂ = 1/(24cos²(w/4)) + c₁S² + η` of the walk comparison, with the series
defining `𝒩` and the sine quotient `S`, including the zero-width case. -/
theorem walk_c2_eq_paper {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let S : ℝ → ℝ := fun x ↦ if x = 0 then 1 else (x / 2) / Real.sin (x / 2)
    walkUniformSquare w = 1 / (24 * Real.cos (w / 4) ^ 2) +
      ((Nf w - Nf (w / 2) / 2) / 4 + 1 / 64) * S w ^ 2 +
      (1 + S w) / (2 * (π ^ 2 - w ^ 2 / 4) * Real.cos (w / 4)) := by
  intro Nf S
  have hS : S w = walkLogSlope w := walkLogSlope_closed hw0 hw
  dsimp only [Nf]
  rw [hS, (paper_series_eq hw0 hw).1,
    (paper_series_eq (show 0 ≤ w / 2 by positivity)
      (show w / 2 < 2 * π by linarith)).1]
  rfl

/-- The endpoint and residual coefficients have leading ratios 1 and 1/4 to
`𝒩(w)`. The first two conclusions give their normalized limits as well. -/
theorem uniform_c0_c1_div_frame_limits :
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let c₀ := fun w ↦ N w - N (w / 2) / 2
    let c₁ := fun w ↦ c₀ w / 4 + 1 / 64
    Tendsto (fun θ ↦ θ * c₀ (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (2 * π))) ∧
    Tendsto (fun θ ↦ θ * c₁ (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / (8 * π))) ∧
    Tendsto (fun θ ↦ c₀ (2 * π - θ) / N (2 * π - θ)) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun θ ↦ c₁ (2 * π - θ) / N (2 * π - θ)) (𝓝[>] 0) (𝓝 (1 / 4)) := by
  intro N c₀ c₁
  obtain ⟨_, _, _, _, hN, _, _, hC, _⟩ := walk_constant_limit
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h₀ : Tendsto (fun θ ↦ θ * c₀ (2 * π - θ))
      (𝓝[>] 0) (𝓝 (1 / (2 * π))) := by
    have hh := hC.sub (hid.div_const 24)
    simp only [zero_div, sub_zero] at hh
    simpa only [c₀, N, mul_add, mul_one_div, add_sub_cancel_right] using hh
  have h₁ : Tendsto (fun θ ↦ θ * c₁ (2 * π - θ))
      (𝓝[>] 0) (𝓝 (1 / (8 * π))) := by
    have hh := (h₀.div_const 4).add (hid.div_const 64)
    rw [show (1 / (2 * π) / 4 + 0 / 64 : ℝ) = 1 / (8 * π) by ring] at hh
    simpa only [c₁, mul_add, ← mul_div_assoc, mul_one] using hh
  refine ⟨h₀, h₁, ?_, ?_⟩
  · have hh := h₀.div hN (show (1 / (2 * π) : ℝ) ≠ 0 by positivity)
    rw [div_self (show (1 / (2 * π) : ℝ) ≠ 0 by positivity)] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ using mul_div_mul_left _ _ (ne_of_gt hθ)
  · have hh := h₁.div hN (show (1 / (2 * π) : ℝ) ≠ 0 by positivity)
    rw [show (1 / (8 * π)) / (1 / (2 * π)) = (1 / 4 : ℝ) by field_simp; ring] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ using mul_div_mul_left _ _ (ne_of_gt hθ)

/-- Section 4, the walk comparison (`thm:unit-steps-walk`) proof, last paragraph: with `w = 2π - θ`,
`π² - w²/4 = (θ/2)(2π - θ/2) ∼ πθ`; as `θ → 0`, `1/(24cos²(w/4))` is of order `θ⁻²`, and `c₁S²` and
`η` are asymptotic to `(π/2)/θ³` and `4/θ³`. The functions `N` and `S` are exactly the paper's
series and continuous-extension sine quotient. -/
theorem walk_uniform_square_leading_terms :
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let S : ℝ → ℝ := fun x ↦ if x = 0 then 1 else (x / 2) / Real.sin (x / 2)
    (∀ θ : ℝ, π ^ 2 - (2 * π - θ) ^ 2 / 4 = (θ / 2) * (2 * π - θ / 2)) ∧
    Tendsto (fun θ ↦ (π ^ 2 - (2 * π - θ) ^ 2 / 4) / θ) (𝓝[>] 0) (𝓝 π) ∧
    Tendsto (fun θ ↦ θ ^ 2 * (1 / (24 * Real.cos ((2 * π - θ) / 4) ^ 2))) (𝓝[>] 0)
      (𝓝 (2 / 3)) ∧
    Tendsto (fun θ ↦ θ ^ 3 * (((N (2 * π - θ) - N ((2 * π - θ) / 2) / 2) / 4 + 1 / 64) *
      S (2 * π - θ) ^ 2)) (𝓝[>] 0) (𝓝 (π / 2)) ∧
    Tendsto (fun θ ↦ θ ^ 3 * ((1 + S (2 * π - θ)) /
      (2 * (π ^ 2 - (2 * π - θ) ^ 2 / 4) * Real.cos ((2 * π - θ) / 4)))) (𝓝[>] 0) (𝓝 4) := by
  intro N S
  obtain ⟨_, _, hS, _, _, _, _, _, _⟩ := Paper.walk_constant_limit
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hR := tendsto_gap_div_cos
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  refine ⟨fun θ ↦ by ring, ?_, ?_, ?_, ?_⟩
  · have h := ((tendsto_const_nhds (x := 2 * π)).sub (hid.div_const 2)).div_const 2
    rw [show (2 * π - 0 / 2) / 2 = π by ring] at h
    apply h.congr'
    filter_upwards [hev] with θ hθ
    have hθ0 : θ ≠ 0 := hθ.1.ne'
    field_simp
    ring
  · have h := (hR.pow 2).div_const 24
    rw [show (4 : ℝ) ^ 2 / 24 = 2 / 3 by norm_num] at h
    simpa only [div_pow, div_div, mul_one_div, mul_comm] using h
  · have h := (hS.pow 2).mul uniform_c0_c1_div_frame_limits.2.1
    rw [show (2 * π) ^ 2 * (1 / (8 * π)) = π / 2 by field_simp; norm_num] at h
    convert h using 1
    exact funext fun θ ↦ by dsimp [N, S]; ring
  · have h3 : Tendsto (fun θ : ℝ ↦ 1 / (2 * π - θ / 2)) (𝓝[>] 0) (𝓝 (1 / (2 * π - 0 / 2))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.sub (hid.div_const 2)) (by simp [pi_ne_zero])
    have h := ((hid.add hS).mul hR).mul h3
    rw [show (0 + 2 * π) * 4 * (1 / (2 * π - 0 / 2)) = 4 by field_simp; ring] at h
    apply h.congr'
    filter_upwards [hev] with θ hθ
    have hsin : 0 < Real.sin (θ / 4) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, pi_pos])
    have hc : Real.cos ((2 * π - θ) / 4) ≠ 0 := by
      rw [(free_arc_reflections θ).2.1]; exact hsin.ne'
    have hθ0 : θ ≠ 0 := hθ.1.ne'
    have hd : 2 * π - θ / 2 ≠ 0 := by linarith [hθ.2, pi_pos]
    rw [show π ^ 2 - (2 * π - θ) ^ 2 / 4 = (θ / 2) * (2 * π - θ / 2) by ring]
    dsimp only [S]
    generalize (if 2 * π - θ = 0 then (1 : ℝ) else (2 * π - θ) / 2 / Real.sin ((2 * π - θ) / 2)) = σ
    field_simp

/-- The first two coefficient limits and the sum of the three quadratic contributions
in the final paragraph of the walk comparison. The coefficient limits accompany
the finite-time inequality. -/
theorem walk_uniform_coefficient_limits :
    Tendsto (fun θ ↦ walkJRSFirst (2 * π - θ) * θ ^ 2) (𝓝[>] 0) (𝓝 2) ∧
    Tendsto (fun θ ↦ walkUniformSecond (2 * π - θ) * θ ^ 2) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun θ ↦ walkUniformSquare (2 * π - θ) * θ ^ 3) (𝓝[>] 0)
      (𝓝 (4 + π / 2)) := by
  obtain ⟨_, _, hS, _, _, _, _, _, _⟩ := walk_constant_limit
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  have hs : Tendsto (fun θ ↦ θ * walkLogSlope (2 * π - θ)) (𝓝[>] 0)
      (𝓝 (2 * π)) := by
    apply hS.congr'
    filter_upwards [hev] with θ hθ
    exact congrArg (θ * ·) (walkLogSlope_closed (by linarith [hθ.2, pi_pos])
      (by linarith [hθ.1]))
  have hn : Tendsto (fun θ ↦ θ * frameBound (2 * π - θ)) (𝓝[>] 0)
      (𝓝 (1 / (2 * π))) := by
    have hw : Tendsto (fun θ : ℝ ↦ 2 * π - θ) (𝓝[>] 0) (𝓝 (2 * π)) := by
      simpa using tendsto_const_nhds.sub hid
    have hh := (hid.sub ((hw.div_const 2).mul tendsto_scaled_cot_half_width)).div
      (hw.pow 2) (by positivity : (2 * π) ^ 2 ≠ 0)
    rw [show (0 - (2 * π / 2) * (-2)) / (2 * π) ^ 2 = 1 / (2 * π) by field_simp; ring] at hh
    apply hh.congr'
    filter_upwards [hev] with θ hθ
    rw [frameBound_eq_closed (by linarith [hθ.2, pi_pos]) (by linarith [hθ.1])]
    simp only [Pi.div_apply]
    ring
  have hc : Tendsto (fun θ ↦ θ *
      (frameBound (2 * π - θ) - frameBound ((2 * π - θ) / 2) / 2))
      (𝓝[>] 0) (𝓝 (1 / (2 * π))) := by
    have hh := hn.sub ((hid.mul tendsto_frameBound_half_width).div_const 2)
    simp only [zero_mul, zero_div, sub_zero] at hh
    simpa only [mul_sub, mul_div_assoc] using hh
  refine ⟨?_, ?_, ?_⟩
  · have hh := (hc.const_mul 2).mul hs
    rw [show 2 * (1 / (2 * π)) * (2 * π) = 2 by field_simp] at hh
    simpa only [walkJRSFirst, sq, mul_assoc, mul_comm, mul_left_comm] using hh
  · have hh := ((hid.div_const 24).add hn).mul hs
    rw [show (0 / 24 + 1 / (2 * π)) * (2 * π) = 1 by field_simp; ring] at hh
    convert hh using 1
    exact funext fun θ ↦ by dsimp [walkUniformSecond]; ring
  · obtain ⟨_, _, h₁, h₂, h₃⟩ := walk_uniform_square_leading_terms
    -- The first summand is of order `θ⁻²`, so it contributes `0` at order `θ⁻³`.
    have h₁' := hid.mul h₁
    rw [zero_mul] at h₁'
    have hh := (h₁'.add h₂).add h₃
    rw [show 0 + π / 2 + 4 = 4 + π / 2 by ring] at hh
    apply hh.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    rw [walk_c2_eq_paper hw0 hw]
    ring

/-- The three asymptotic equivalents for a corrector on every rounded-clock cell. -/
theorem walk_uniform_coefficient_equivalents :
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walkJRSFirst (2 * π - θ))
      (fun θ ↦ 2 / θ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walkUniformSecond (2 * π - θ))
      (fun θ ↦ 1 / θ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun θ ↦ walkUniformSquare (2 * π - θ))
      (fun θ ↦ (4 + π / 2) / θ ^ 3) := by
  have convert_limit (f : ℝ → ℝ) (p : ℕ) (c : ℝ) (hc : c ≠ 0)
      (h : Tendsto (fun θ ↦ f θ * θ ^ p) (𝓝[>] 0) (𝓝 c)) :
      Asymptotics.IsEquivalent (𝓝[>] 0) f (fun θ ↦ c / θ ^ p) := by
    apply Asymptotics.isEquivalent_of_tendsto_one
    have hh := h.div_const c
    rw [div_self hc] at hh
    simpa only [Pi.div_def, div_div_eq_mul_div] using hh
  obtain ⟨h1, h2, h3⟩ := walk_uniform_coefficient_limits
  exact ⟨convert_limit _ 2 2 (by norm_num) h1,
    convert_limit _ 2 1 one_ne_zero h2,
    convert_limit _ 3 _ (by positivity) h3⟩


end UnitaryProducts.PaperProof
