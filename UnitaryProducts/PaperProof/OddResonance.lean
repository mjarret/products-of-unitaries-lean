/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ExamplesPi

/-! # Dense odd resonances and the sharp endpoint coefficient

The density and continuity argument in the paragraph after Example 5.2.
-/
@[expose] public section
noncomputable section
open Real Set Filter
open scoped Topology
namespace UnitaryProducts.PaperProof

/-- Every positive open interval contains a width whose total phase at some
odd integer runtime is an odd multiple of pi. Thus the width divided by pi
is a ratio of odd integers, exactly as in the paper. The construction chooses
an odd denominator, rounds the lower endpoint upwards, then adds a half-period. -/
theorem exists_odd_odd_resonant_width {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (ω : ℝ) (T m : ℕ), a < ω ∧ ω < b ∧ 0 < T ∧ Odd T ∧
      (T : ℝ) * ω = (2 * m + 1) * π := by
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (3 * π / (b - a))
  let T := 2 * n + 1
  have hnT : n ≤ T := by dsimp only [T]; omega
  have hTlarge : 3 * π / (b - a) < T :=
    hnlarge.trans_le (Nat.cast_le.mpr hnT)
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hTreal : 0 < (T : ℝ) := (by positivity : (0 : ℝ) < 3 * π / (b - a)).trans hTlarge
  have hT : 0 < T := Nat.cast_pos.mp hTreal
  have hlarge : 3 * π < (T : ℝ) * (b - a) := (div_lt_iff₀ hgap).mp hTlarge
  let m := ⌈a * T / (2 * π)⌉₊
  have hmlo : a * T ≤ (m : ℝ) * (2 * π) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp (Nat.le_ceil _)
  have hmhi : (m : ℝ) * (2 * π) < a * T + 2 * π := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ a * T / (2 * π))
    have h' := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < 2 * π)
    have he : (a * (T : ℝ) / (2 * π) + 1) * (2 * π) = a * T + 2 * π := by
      field_simp
    simpa only [he] using h'
  let ω := (2 * (m : ℝ) + 1) * π / T
  have hlo : a < ω := by
    apply (lt_div_iff₀ hTreal).mpr
    linarith [pi_pos]
  have hhi : ω < b := by
    apply (div_lt_iff₀ hTreal).mpr
    have halgebra : (T : ℝ) * (b - a) = b * T - a * T := by ring
    rw [halgebra] at hlarge
    linarith
  refine ⟨ω, T, m, hlo, hhi, hT, ⟨n, by dsimp only [T]⟩, ?_⟩
  dsimp only [ω]
  field_simp [hTreal.ne']

/-- The odd-over-odd density statement supplies the unrestricted odd-resonance
form used by the continuity argument. -/
theorem exists_odd_resonant_width {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (ω : ℝ) (T m : ℕ), a < ω ∧ ω < b ∧ 0 < T ∧
      (T : ℝ) * ω = (2 * m + 1) * π := by
  obtain ⟨ω, T, m, hlo, hhi, hT, _, hres⟩ := exists_odd_odd_resonant_width ha hab
  exact ⟨ω, T, m, hlo, hhi, hT, hres⟩

/-- Every odd multiple of a resonant denominator is resonant, and these
integer runtimes tend to infinity. This is the first limiting sequence in the
all-width optimality paragraph after Example 5.2. -/
theorem odd_resonant_runtimes {ω : ℝ} {q m : ℕ} (hq : 0 < q)
    (hres : (q : ℝ) * ω = (2 * m + 1) * π) :
    (∀ k : ℕ, 0 < q * (2 * k + 1) ∧
      ((q * (2 * k + 1) : ℕ) : ℝ) * ω =
        (2 * ((2 * m * k + m + k : ℕ) : ℝ) + 1) * π) ∧
    Tendsto (fun k : ℕ ↦ q * (2 * k + 1)) atTop atTop := by
  constructor
  · intro k
    refine ⟨Nat.mul_pos hq (by omega), ?_⟩
    push_cast
    calc
      (q : ℝ) * (2 * k + 1) * ω = (2 * k + 1) * ((q : ℝ) * ω) := by ring
      _ = (2 * k + 1) * ((2 * m + 1) * π) := by rw [hres]
      _ = _ := by ring
  · apply tendsto_atTop_mono (f := fun k : ℕ ↦ k) ?_ tendsto_id
    intro k
    have hqone : 1 ≤ q := hq
    have hmul := Nat.mul_le_mul_right (2 * k + 1) hqone
    change k ≤ q * (2 * k + 1)
    simp only [one_mul] at hmul
    exact (show k ≤ 2 * k + 1 by omega).trans hmul

/-- A continuous coefficient bounded at all odd-resonant widths below `w`
is bounded at `w` itself. This makes the paper's density argument explicit. -/
theorem coefficient_le_of_odd_resonances {f : ℝ → ℝ} {w c : ℝ}
    (hw : 0 < w) (hf : ContinuousAt f w)
    (hbound : ∀ (ω : ℝ) (T m : ℕ), 0 < ω → ω < w → 0 < T →
      (T : ℝ) * ω = (2 * m + 1) * π → f ω ≤ c) : f w ≤ c := by
  by_contra hnot
  have hcw : c < f w := lt_of_not_ge hnot
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hf (f w - c) (sub_pos.mpr hcw)
  let a := max (w / 2) (w - δ / 2)
  have ha : 0 < a := lt_of_lt_of_le (by positivity : (0 : ℝ) < w / 2) (le_max_left _ _)
  have haw : a < w := max_lt_iff.mpr ⟨by linarith, by linarith⟩
  obtain ⟨ω, T, m, haω, hωw, hT, hodd⟩ := exists_odd_resonant_width ha haw
  have hω : 0 < ω := ha.trans haω
  have hdist : dist ω w < δ := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hωw)]
    have hlow : w - δ / 2 < ω := (le_max_right _ _).trans_lt haω
    linarith
  have hsmall := hclose hdist
  rw [Real.dist_eq] at hsmall
  have hlo := (abs_lt.mp hsmall).1
  have hb := hbound ω T m hω hωw hT hodd
  linarith

/-- The closed endpoint coefficient is continuous at every admissible positive
width, and hence its values at odd resonances determine its optimal value. -/
theorem endpoint_coefficient_le_of_odd_resonances {w c : ℝ}
    (hw : 0 < w) (hw2 : w < 2 * π)
    (hbound : ∀ (ω : ℝ) (T m : ℕ), 0 < ω → ω < w → 0 < T →
      (T : ℝ) * ω = (2 * m + 1) * π →
      1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2 ≤ c) :
    1 / (2 * w * Real.sin (w / 2)) - 1 / w ^ 2 ≤ c := by
  have hsin : 0 < Real.sin (w / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hden : ContinuousAt (fun x : ℝ ↦ 2 * x * Real.sin (x / 2)) w := by fun_prop
  have hf : ContinuousAt (fun x : ℝ ↦ 1 / (2 * x * Real.sin (x / 2)) - 1 / x ^ 2) w :=
    (continuousAt_const.div hden (by positivity)).sub
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hw.ne'))
  exact coefficient_le_of_odd_resonances
    (f := fun x : ℝ ↦ 1 / (2 * x * Real.sin (x / 2)) - 1 / x ^ 2) (w := w) (c := c) hw hf hbound

/-- A quadratic remainder cannot reduce a linear endpoint coefficient.
This is applied to the spin error after multiplication by the runtime. -/
theorem linear_coefficient_le_of_quadratic_error {E : ℝ → ℝ} {ω c K a : ℝ}
    (hω : 0 < ω)
    (hlim : Tendsto (fun θ : ℝ ↦ E θ / (ω * |θ|)) (𝓝[≠] 0) (𝓝 a))
    (hbound : ∀ᶠ θ in 𝓝[≠] (0 : ℝ), E θ ≤ c * ω * |θ| + K * θ ^ 2) : a ≤ c := by
  have hzero : Tendsto (fun θ : ℝ ↦ |θ|) (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun θ : ℝ ↦ |θ|) (𝓝[≠] 0) (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [abs_zero] using h
  have hright : Tendsto (fun θ : ℝ ↦ c + K / ω * |θ|) (𝓝[≠] 0) (𝓝 c) := by
    simpa only [mul_zero, add_zero] using (hzero.const_mul (K / ω)).const_add c
  apply le_of_tendsto_of_tendsto hlim hright
  filter_upwards [hbound, self_mem_nhdsWithin] with θ hb hθ
  have hne : θ ≠ 0 := hθ
  have habs : 0 < |θ| := abs_pos.mpr hne
  have he : (c * ω * |θ| + K * θ ^ 2) / (ω * |θ|) = c + K / ω * |θ| := by
    have hs : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
    rw [hs]
    field_simp [hω.ne', habs.ne']
  exact (div_le_div_of_nonneg_right hb (mul_pos hω habs).le).trans_eq he


/-- The paper's order of limits: first take unbounded odd-resonant runtimes
in a uniform quadratic comparison with the axis distance, then let the
precession angle tend to zero, and finally use density and continuity in the
width. `E` is the runtime-scaled evolution error and `A` the runtime-scaled
axis distance. The two remainder constants are independent of runtime. -/
theorem endpoint_coefficient_optimal_time_first
    {E A : ℝ → ℕ → ℝ → ℝ} {w c : ℝ}
    (hw : 0 < w) (hw2 : w < 2 * π)
    (haxis : ∀ ω : ℝ, 0 < ω → ω < w → ∀ θ : ℝ,
      Tendsto (fun T : ℕ ↦ A ω T θ) atTop
        (𝓝 (|θ| * (1 / (2 * Real.sin (ω / 2)) - 1 / ω))))
    (herror : ∀ ω : ℝ, 0 < ω → ω < w →
      ∃ C : ℝ, ∀ᶠ θ in 𝓝[≠] (0 : ℝ), ∀ T m : ℕ, 0 < T →
        (T : ℝ) * ω = (2 * m + 1) * π →
        |E ω T θ - A ω T θ| ≤ C * θ ^ 2)
    (hcomparison : ∀ ω : ℝ, 0 < ω → ω < w →
      ∃ K : ℝ, ∀ᶠ θ in 𝓝[≠] (0 : ℝ), ∀ T m : ℕ, 0 < T →
        (T : ℝ) * ω = (2 * m + 1) * π →
        E ω T θ ≤ c * ω * |θ| + K * θ ^ 2) :
    1 / (2 * w * Real.sin (w / 2)) - 1 / w ^ 2 ≤ c := by
  apply endpoint_coefficient_le_of_odd_resonances hw hw2
  intro ω q m hω hωw hq hres
  obtain ⟨C, hC⟩ := herror ω hω hωw
  obtain ⟨K, hK⟩ := hcomparison ω hω hωw
  have hruntimes := odd_resonant_runtimes hq hres
  let a := 1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2
  have hsin : Real.sin (ω / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < ω / 2)
      (by linarith)).ne'
  have hfactor (θ : ℝ) :
      |θ| * (1 / (2 * Real.sin (ω / 2)) - 1 / ω) = a * (ω * |θ|) := by
    dsimp only [a]
    field_simp
  have hfirst : ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
      a * (ω * |θ|) ≤ c * ω * |θ| + (K + C) * θ ^ 2 := by
    filter_upwards [hC, hK] with θ hCθ hKθ
    have hlim := (haxis ω hω hωw θ).comp hruntimes.2
    rw [hfactor θ] at hlim
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro k
    have hT := (hruntimes.1 k).1
    have hodd := (hruntimes.1 k).2
    have he := (abs_le.mp (hCθ _ _ hT hodd)).1
    have hc := hKθ _ _ hT hodd
    change A ω (q * (2 * k + 1)) θ ≤ _
    rw [add_mul]
    linarith only [he, hc]
  have hnormalized : Tendsto (fun θ : ℝ ↦ a * (ω * |θ|) / (ω * |θ|))
      (𝓝[≠] 0) (𝓝 a) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hθne : θ ≠ 0 := hθ
    have hn : ω * |θ| ≠ 0 := mul_ne_zero hω.ne' (abs_ne_zero.mpr hθne)
    simp only [mul_div_cancel_right₀ _ hn]
  exact linear_coefficient_le_of_quadratic_error hω hnormalized hfirst

end UnitaryProducts.PaperProof
