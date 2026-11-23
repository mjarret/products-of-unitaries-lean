/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueEndpointDerivative

/-! # Differentiation of the multiplier series

Lemma A.3 identifies the locally uniform limit of the differentiated partial sums at every point
of the closed interval.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

attribute [local instance] endValue_continuousSMul_real

/-- Dieudonné's partial-sum limit is unique and determines every interval point. -/
theorem endValue_partialSums_allPoints_cited
    (dieudonne_8_6_4 : Dieudonne_8_6_4)
    {f g : ℕ → ℝ → 𝕄} {u : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ n, ∀ t ∈ Icc a b, HasDerivWithinAt (f n) (g n t) (Icc a b) t)
    (hs : ∀ t ∈ Icc a b, Summable (fun n ↦ f n t))
    (hu : Summable u) (hb : ∀ n, ∀ t ∈ Icc a b, ‖g n t‖ ≤ u n)
    (hF : ContinuousOn (fun t ↦ ∑' n, f n t) (Icc a b))
    (hG : ContinuousOn (fun t ↦ ∑' n, g n t) (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ ∑' n, f n t)
      (∑' n, g n t) (Icc a b) t := by
  exact endValue_remove_countable hab hF hG
    (endValue_dieudonne_series dieudonne_8_6_4 hd ⟨le_rfl, hab⟩ hs hu hb)

/-- Termwise differentiation of the locally uniform series gives the commutator derivative. -/
theorem endValue_commutator_derivative_cited [NeZero d]
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ} (hw0 : 0 ≤ w) (hab : a ≤ b)
    (hs : Summable (fun n ↦ c n * w ^ n))
    (hs' : Summable (fun n ↦ c n * n * w ^ (n - 1)))
    {Ω A Ω' A' : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hdΩ : ∀ t ∈ Icc a b, HasDerivWithinAt Ω (Ω' t) (Icc a b) t)
    (hdA : ∀ t ∈ Icc a b, HasDerivWithinAt A (A' t) (Icc a b) t)
    (hΩ' : ContinuousOn Ω' (Icc a b)) (hA' : ContinuousOn A' (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt
      (fun t ↦ ∑' n, (c n : ℂ) • ((adL (Ω t) ^ n) (A t)))
      (∑' n, (c n : ℂ) • (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))) (Icc a b) t := by
  have hΩ : ContinuousOn Ω (Icc a b) := fun t ht ↦ (hdΩ t ht).continuousWithinAt
  have hA : ContinuousOn A (Icc a b) := fun t ht ↦ (hdA t ht).continuousWithinAt
  obtain ⟨u, hu, hb⟩ := endValue_curve_derivative_majorant hc hw0 hs hs' ha hA hΩ' hA'
  exact endValue_partialSums_allPoints_cited dieudonne_8_6_4 hab
    (fun n t ht ↦ endValue_hasDerivWithinAt_term Ω A (Ω' t) (A' t)
      (Icc a b) t (c n) n (hdΩ t ht) (hdA t ht))
    (fun t ht ↦ (endValue_summable_norm_series hc (ha t ht) hs).of_norm) hu hb
    (endValue_continuousOn_series_cited hc hs ha hΩ hA)
    (endValue_continuousOn_derivativeSeries hc hw0 hs hs' ha hΩ hA hΩ' hA')

/-- Scalar partial sums are scalar multiples of the one-by-one identity matrix. -/
theorem endValue_scalar_derivative_cited
    (dieudonne_8_6_4 : Dieudonne_8_6_4) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    deriv 𝒩 w = ∑' n : ℕ, multiplierCoeff n * n * w ^ (n - 1) := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 ≤ r := hw0.trans hwr.le
  have hI : -r ≤ r := neg_le_self hr0
  have hx (t : ℝ) (ht : t ∈ Icc (-r) r) : |t| ≤ r := abs_le.mpr ht
  let f : ℕ → ℝ → ℝ := fun n t ↦ multiplierCoeff n * t ^ n
  let g : ℕ → ℝ → ℝ := fun n t ↦ multiplierCoeff n * n * t ^ (n - 1)
  have hs := summable_multiplierCoeff_power (by rwa [abs_of_nonneg hr0])
  have hs' := summable_multiplierCoeff_deriv hr0 hr
  have hf (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ‖f n t‖ ≤ multiplierCoeff n * r ^ n := by
    simp only [f, norm_mul, Real.norm_eq_abs, abs_of_nonneg (multiplierCoeff_nonneg n),
      abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) (hx t ht) n)
      (multiplierCoeff_nonneg n)
  have hg (n : ℕ) (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ‖g n t‖ ≤ multiplierCoeff n * n * r ^ (n - 1) := by
    rw [show g n t = (multiplierCoeff n * n) * t ^ (n - 1) from rfl,
      norm_mul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (multiplierCoeff_nonneg n) (Nat.cast_nonneg n)), norm_pow,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg t) (hx t ht) _)
      (mul_nonneg (multiplierCoeff_nonneg n) (Nat.cast_nonneg n))
  let E : Matrix (Fin 1) (Fin 1) ℂ := 1
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (f n) (g n t) t := by
    simpa only [f, g, mul_assoc, Pi.pow_apply, id_eq, mul_one] using
      ((hasDerivAt_id t).pow n).const_mul (multiplierCoeff n)
  have hsum (t : ℝ) (ht : t ∈ Icc (-r) r) : Summable (fun n ↦ f n t) :=
    (Summable.of_norm_bounded hs (fun n ↦ hf n t ht))
  have hFM : ContinuousOn (fun t ↦ ∑' n, f n t • E) (Icc (-r) r) := by
    apply continuousOn_tsum (fun n ↦
      (continuous_const.mul (continuous_id.pow n)).continuousOn.smul continuousOn_const)
      (hs.mul_right ‖E‖)
    intro n t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hf n t ht) (norm_nonneg E)
  have hGM : ContinuousOn (fun t ↦ ∑' n, g n t • E) (Icc (-r) r) := by
    apply continuousOn_tsum (fun n ↦
      (continuous_const.mul (continuous_id.pow (n - 1))).continuousOn.smul
        continuousOn_const) (hs'.mul_right ‖E‖)
    intro n t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hg n t ht) (norm_nonneg E)
  have hM := endValue_partialSums_allPoints_cited dieudonne_8_6_4 hI
    (fun n t _ ↦ ((hd n t).smul_const E).hasDerivWithinAt)
    (fun t ht ↦ (hsum t ht).smul_const E) (hs'.mul_right ‖E‖)
    (fun n t ht ↦ by rw [norm_smul]; exact
      mul_le_mul_of_nonneg_right (hg n t ht) (norm_nonneg E)) hFM hGM
  have hwI : w ∈ Icc (-r) r := ⟨by linarith, hwr.le⟩
  have hMw := hM w hwI
  rw [(summable_multiplierCoeff_deriv hw0 hw).tsum_smul_const E] at hMw
  have hMw' : HasDerivWithinAt (fun t ↦ (∑' n, f n t) • E)
      ((∑' n, g n w) • E) (Icc (-r) r) w :=
    hMw.congr (fun t ht ↦ ((hsum t ht).tsum_smul_const E).symm)
      ((hsum w hwI).tsum_smul_const E).symm
  have hMw'' := hMw'.hasDerivAt (Icc_mem_nhds (by linarith) hwr)
  have hscalar :=
    (Complex.reCLM.comp
      ((matrixEntryCLM (d := 1) 0 0).restrictScalars ℝ)).hasFDerivAt.comp_hasDerivAt
      w hMw''
  have hreal : HasDerivAt (fun t ↦ ∑' n, f n t) (∑' n, g n w) w := by
    simpa [Function.comp_def, E, matrixEntryCLM_apply] using hscalar
  have heq : 𝒩 =ᶠ[𝓝 w] (fun t ↦ ∑' n, f n t) := by
    filter_upwards [Icc_mem_nhds (show -r < w by linarith) hwr] with t ht
    exact (endValue_coeffSeries_cited t ((hx t ht).trans_lt hr)).symm
  exact (hreal.congr_of_eventuallyEq heq).deriv

end RoundedClocks
