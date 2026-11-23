/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.RegulatedApproximation

/-! # Regulated functions are bounded, continuous outside a countable set, and integrable

Section 2, after Definition 2.1: "A regulated function is a uniform limit of piecewise-constant
functions [Dieudonné (7.6.1)], so it is bounded and continuous outside a countable set." It is
therefore integrable, which the proof of Theorem 2.2 uses for the integral of `U†RV` and the proof
of Theorem 3.6 for the integral in Duhamel's bound.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter MeasureTheory
open Complex (I)

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2, after Definition 2.1. Assuming Dieudonné (7.6.1), a regulated function is bounded:
it is within `1` of a piecewise-constant function, which takes finitely many values. -/
lemma IsRegulated.bounded (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ‖F x‖ ≤ C := by
  -- `F` is within `1` of a piecewise-constant `G`, and `‖G‖ ≤ C` as `G` takes finitely many values.
  obtain ⟨G, hG, herr⟩ := dieudonne_7_6_1 d F a b 1 hab hF zero_lt_one
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    hG.finite_image.isBounded
  refine ⟨1 + C, ?_⟩
  intro x hx
  calc
    ‖F x‖ ≤ ‖F x - G x‖ + ‖G x‖ := by
      simpa only [norm_sub_rev, add_comm] using norm_le_insert (G x) (F x)
    _ ≤ 1 + C := add_le_add (herr x hx).le (hC _ ⟨x, hx, rfl⟩)

/-- Section 2, after Definition 2.1. Assuming Dieudonné (7.6.1), a regulated function is
continuous outside a countable set: it is a uniform limit of piecewise-constant functions, each
continuous outside a finite set. -/
lemma IsRegulated.continuousWithinAt_off_countable (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    ∃ D : Set ℝ, D.Countable ∧
      ∀ x ∈ Icc a b, x ∉ D → ContinuousWithinAt F (Icc a b) x := by
  -- Piecewise-constant `Gₙ` within `1/(n+1)` of `F`, each continuous outside a finite set `Dₙ`.
  have happrox (n : ℕ) :=
    dieudonne_7_6_1 d F a b (1 / (n + 1)) hab hF (by positivity)
  choose G hG herr using happrox
  choose D hD hcont using fun n ↦ (hG n).continuousAt_off_finite
  -- The `Gₙ` converge to `F` uniformly for `x ∈ [a,b]`.
  have hunif : TendstoUniformlyOn G F atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)
    filter_upwards [he] with n hn
    intro x hx
    rw [dist_eq_norm]
    exact (herr n x hx).trans hn
  -- A uniform limit of functions continuous at `x` is continuous at `x`, so `F` is continuous
  -- outside the countable union of the `Dₙ`.
  refine ⟨⋃ n, D n, countable_iUnion (fun n ↦ (hD n).countable), ?_⟩
  intro x hx hxD
  have hc (n : ℕ) : ContinuousWithinAt (G n) (Icc a b) x := by
    apply (hcont n x hx ?_).continuousWithinAt
    intro hn
    exact hxD (mem_iUnion.mpr ⟨n, hn⟩)
  exact (hunif.tendstoUniformlyOnFilter.mono_right inf_le_right)
    |>.tendsto_of_eventually_tendsto (Eventually.of_forall hc) (hunif.tendsto_at hx)

/-- Assuming Dieudonné (7.6.1), a regulated function is integrable: it is bounded and continuous
outside a countable set, which has measure zero. -/
lemma IsRegulated.intervalIntegrable (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    IntervalIntegrable F volume a b := by
  obtain ⟨D, hD, hc⟩ := hF.continuousWithinAt_off_countable dieudonne_7_6_1 hab
  obtain ⟨C, hC⟩ := hF.bounded dieudonne_7_6_1 hab
  -- `F` is continuous outside the countable set `D`, which has measure zero, so `F` is measurable.
  have hcont : ContinuousOn F (Icc a b \ D) := by
    intro x hx
    exact (hc x hx.1 hx.2).mono diff_subset
  have hmeas := hcont.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff hD.measurableSet)
  have heq : volume.restrict (Icc a b \ D) = volume.restrict (Icc a b) := by
    apply Measure.restrict_congr_set
    apply diff_ae_eq_self.mpr
    exact measure_mono_null inter_subset_right (hD.measure_zero volume)
  rw [heq] at hmeas
  -- A measurable function bounded by `C` is integrable over `[a,b]`.
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top) hmeas C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- Second equality in the display of the proof of Theorem 2.2, on one piece `[a,b]`. Let
`A = (U†V)'` and `B = (U†YV)'` be regulated, and let `C = iU†RV` agree with `A - iB` for almost
every `t`, as the last line of (2.2) states. Then `C` is integrable, whatever the values of `R` at
the remaining `t`, and `∫ A = ∫ C + i ∫ B`. -/
lemma comparison_integral_residual (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {A B C : ℝ → 𝕄} {a b : ℝ}
    (hab : a ≤ b) (hA : IsRegulated A a b) (hB : IsRegulated B a b)
    (heq : C =ᵐ[volume.restrict (uIoc a b)] (fun t ↦ A t - I • B t)) :
    IntervalIntegrable C volume a b ∧
      (∫ t in a..b, A t) = (∫ t in a..b, C t) + I • (∫ t in a..b, B t) := by
  -- The regulated `A` and `B` are integrable, so `C` is, and `∫ C = ∫ A - i ∫ B`.
  have hiA := hA.intervalIntegrable dieudonne_7_6_1 hab
  have hiB := hB.intervalIntegrable dieudonne_7_6_1 hab
  have hi := hiA.sub (hiB.smul I)
  refine ⟨hi.congr_ae heq.symm, ?_⟩
  have he : (∫ t in a..b, C t) = ∫ t in a..b, A t - I • B t :=
    intervalIntegral.integral_congr_ae_restrict heq
  have hiIB : IntervalIntegrable (fun t ↦ I • B t) volume a b := hiB.smul I
  rw [he, intervalIntegral.integral_sub hiA hiIB, intervalIntegral.integral_smul]
  abel

end RoundedClocks
