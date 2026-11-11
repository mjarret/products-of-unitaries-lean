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
integer runtime is an odd multiple of pi. The construction rounds the lower
endpoint upwards, then adds a half-period. -/
theorem exists_odd_resonant_width {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (ω : ℝ) (T m : ℕ), a < ω ∧ ω < b ∧ 0 < T ∧
      (T : ℝ) * ω = (2 * m + 1) * π := by
  obtain ⟨T, hTlarge⟩ := exists_nat_gt (3 * π / (b - a))
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
  refine ⟨ω, T, m, hlo, hhi, hT, ?_⟩
  dsimp only [ω]
  field_simp [hTreal.ne']

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

/-- The endpoint coefficient cannot be decreased at any positive width: a
comparison with quadratic remainder and the odd-resonant spin limits forces
its linear coefficient to be at least the paper's closed value. -/
theorem endpoint_coefficient_optimal {E : ℝ → ℕ → ℝ → ℝ} {w c : ℝ}
    (hw : 0 < w) (hw2 : w < 2 * π)
    (hlimit : ∀ (ω : ℝ) (T m : ℕ), 0 < ω → ω < w → 0 < T →
      (T : ℝ) * ω = (2 * m + 1) * π →
      Tendsto (fun θ : ℝ ↦ E ω T θ / (ω * |θ|)) (𝓝[≠] 0)
        (𝓝 (1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2)))
    (hcomparison : ∀ (ω : ℝ) (T m : ℕ), 0 < ω → ω < w → 0 < T →
      (T : ℝ) * ω = (2 * m + 1) * π →
      ∃ K : ℝ, ∀ᶠ θ in 𝓝[≠] (0 : ℝ), E ω T θ ≤ c * ω * |θ| + K * θ ^ 2) :
    1 / (2 * w * Real.sin (w / 2)) - 1 / w ^ 2 ≤ c := by
  apply endpoint_coefficient_le_of_odd_resonances hw hw2
  intro ω T m hω hωw hT hodd
  obtain ⟨K, hK⟩ := hcomparison ω T m hω hωw hT hodd
  exact linear_coefficient_le_of_quadratic_error hω
    (hlimit ω T m hω hωw hT hodd) hK

end UnitaryProducts.PaperProof
