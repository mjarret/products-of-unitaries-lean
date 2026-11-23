/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueDerivative
public import RoundedClocks.Appendix.EndValueSeriesIdentities
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Endpoint differentiation of the multiplier

Lemma A.3 extends the partial-sum derivative from the open interval to both endpoints using the
countable-exception fundamental theorem and continuity.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

attribute [local instance] endValue_continuousSMul_real

/-- The countable-exception FTC and a continuous extension recover both endpoints. -/
theorem endValue_remove_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hd : DerivativeOffCountable f g a b) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  let G : ℝ → E := fun t ↦ g (projIcc a b hab t)
  have hG : Continuous G := hg.restrict.comp continuous_projIcc
  have he (t : ℝ) (ht : t ∈ Icc a b) : G t = g t := by
    simp only [G, projIcc_of_mem hab ht]
  obtain ⟨D, hD, hd⟩ := hd
  have hprim (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x in a..t, G x) = f t - f a := by
    apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le f G ht.1 hD
    · exact hf.mono (Icc_subset_Icc le_rfl ht.2)
    · intro x hx
      have hx' : x ∈ Icc a b := ⟨hx.1.1.le, hx.1.2.le.trans ht.2⟩
      rw [he x hx']
      exact (hd x hx' hx.2).hasDerivAt
        (Icc_mem_nhds hx.1.1 (hx.1.2.trans_le ht.2))
    · exact hG.intervalIntegrable _ _
  intro t ht
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (hG.intervalIntegrable a t) hG.stronglyMeasurable.stronglyMeasurableAtFilter
    hG.continuousAt).hasDerivWithinAt (s := Icc a b)
  have hp' := hp.add_const (f a)
  rw [he t ht] at hp'
  exact hp'.congr (fun x hx ↦ by rw [hprim x hx]; abel)
    (by rw [hprim t ht]; abel)

/-- The undifferentiated series is continuous by its uniform scalar majorant. -/
theorem endValue_continuousOn_series_cited [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ}
    (hs : Summable (fun n ↦ c n * w ^ n)) {Ω A : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hΩ : ContinuousOn Ω (Icc a b)) (hA : ContinuousOn A (Icc a b)) :
    ContinuousOn (fun t ↦ ∑' n, (c n : ℂ) • ((adL (Ω t) ^ n) (A t)))
      (Icc a b) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hL := endValue_adLCLM.continuous.comp_continuousOn hΩ
  have hpow (n : ℕ) : ContinuousOn (fun t ↦ adL (Ω t) ^ n) (Icc a b) := by
    induction n with
    | zero => simpa only [pow_zero] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (1 : 𝕄 →L[ℂ] 𝕄)) (Icc a b))
    | succ n ih => simpa only [pow_succ] using ih.clm_comp hL
  apply continuousOn_tsum (fun n ↦ ((hpow n).clm_apply hA).const_smul _)
    (hs.mul_right (max M 0))
  intro n t ht
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
  calc
    _ ≤ c n * (‖adL (Ω t) ^ n‖ * ‖A t‖) :=
      mul_le_mul_of_nonneg_left ((adL (Ω t) ^ n).le_opNorm _) (hc n)
    _ ≤ c n * (w ^ n * max M 0) := by
      apply mul_le_mul_of_nonneg_left _ (hc n)
      exact mul_le_mul ((norm_pow_le (adL (Ω t)) n).trans
        (pow_le_pow_left₀ (norm_nonneg (adL (Ω t))) (ha t ht) n))
        ((hM t ht).trans (le_max_left _ _)) (norm_nonneg _)
        (pow_nonneg ((norm_nonneg (adL (Ω t))).trans (ha t ht)) n)
    _ = _ := by ring

end RoundedClocks
