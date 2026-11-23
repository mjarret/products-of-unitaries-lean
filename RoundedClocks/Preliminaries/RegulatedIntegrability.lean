/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.RegulatedApproximation

/-! # Boundedness and integrability of regulated families

Theorem 2.2 obtains boundedness and interval integrability from piecewise-constant approximation
of regulated matrix families.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter MeasureTheory
open Complex (I)

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2: approximation with error one and finite step image give boundedness. -/
lemma comparison_cited_bounded (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ‖F x‖ ≤ C := by
  obtain ⟨G, hG, herr⟩ := dieudonne_7_6_1 d F a b 1 hab hF zero_lt_one
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (comparison_step_finite_image hG).isBounded
  refine ⟨1 + C, ?_⟩
  intro x hx
  calc
    ‖F x‖ ≤ ‖F x - G x‖ + ‖G x‖ := by
      simpa only [norm_sub_rev, add_comm] using norm_le_insert (G x) (F x)
    _ ≤ 1 + C := add_le_add (herr x hx).le (hC _ ⟨x, hx, rfl⟩)

/-- Section 2: the uniform step limit is continuous within the interval off a countable set. -/
lemma comparison_cited_continuous_off_countable (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    ∃ D : Set ℝ, D.Countable ∧
      ∀ x ∈ Icc a b, x ∉ D → ContinuousWithinAt F (Icc a b) x := by
  have happrox (n : ℕ) :=
    dieudonne_7_6_1 d F a b (1 / (n + 1)) hab hF (by positivity)
  choose G hG herr using happrox
  choose D hD hcont using fun n ↦ comparison_step_continuous_off_finite (hG n)
  have hunif : TendstoUniformlyOn G F atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)
    filter_upwards [he] with n hn
    intro x hx
    rw [dist_eq_norm]
    exact (herr n x hx).trans hn
  refine ⟨⋃ n, D n, countable_iUnion (fun n ↦ (hD n).countable), ?_⟩
  intro x hx hxD
  have hc (n : ℕ) : ContinuousWithinAt (G n) (Icc a b) x := by
    apply (hcont n x hx ?_).continuousWithinAt
    intro hn
    exact hxD (mem_iUnion.mpr ⟨n, hn⟩)
  exact (hunif.tendstoUniformlyOnFilter.mono_right inf_le_right)
    |>.tendsto_of_eventually_tendsto (Eventually.of_forall hc) (hunif.tendsto_at hx)

/-- Section 2: boundedness and continuity off a null set give interval integrability. -/
lemma comparison_cited_intervalIntegrable (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {F : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hF : IsRegulated F a b) :
    IntervalIntegrable F volume a b := by
  obtain ⟨D, hD, hc⟩ := comparison_cited_continuous_off_countable dieudonne_7_6_1 hab hF
  obtain ⟨C, hC⟩ := comparison_cited_bounded dieudonne_7_6_1 hab hF
  have hcont : ContinuousOn F (Icc a b \ D) := by
    intro x hx
    exact (hc x hx.1 hx.2).mono diff_subset
  have hmeas := hcont.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff hD.measurableSet)
  have heq : volume.restrict (Icc a b \ D) = volume.restrict (Icc a b) := by
    apply Measure.restrict_congr_set
    apply diff_ae_eq_self.mpr
    exact measure_mono_null inter_subset_right (hD.measure_zero volume)
  rw [heq] at hmeas
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply IntegrableOn.of_bound (measure_Icc_lt_top) hmeas C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- The residual integral separates into the two regulated terms used in Theorem 2.2. -/
lemma comparison_cited_integrate_residual (dieudonne_7_6_1 : Dieudonne_7_6_1)
    {A B C : ℝ → 𝕄} {a b : ℝ}
    (hab : a ≤ b) (hA : IsRegulated A a b) (hB : IsRegulated B a b)
    (heq : C =ᵐ[volume.restrict (uIoc a b)] (fun t ↦ A t - I • B t)) :
    IntervalIntegrable C volume a b ∧
      (∫ t in a..b, A t) = (∫ t in a..b, C t) + I • (∫ t in a..b, B t) := by
  have hiA := comparison_cited_intervalIntegrable dieudonne_7_6_1 hab hA
  have hiB := comparison_cited_intervalIntegrable dieudonne_7_6_1 hab hB
  have hi := hiA.sub (hiB.smul I)
  refine ⟨hi.congr_ae heq.symm, ?_⟩
  have he : (∫ t in a..b, C t) = ∫ t in a..b, A t - I • B t :=
    intervalIntegral.integral_congr_ae_restrict heq
  have hiIB : IntervalIntegrable (fun t ↦ I • B t) volume a b := hiB.smul I
  rw [he, intervalIntegral.integral_sub hiA hiIB, intervalIntegral.integral_smul]
  abel

end RoundedClocks
