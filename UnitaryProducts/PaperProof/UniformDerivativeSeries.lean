/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.CommutatorTelescope
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Uniform convergence of the derivative series in Appendix A.3 -/
@[expose] public section
noncomputable section
open Complex Real Set Filter MeasureTheory Matrix
open scoped Topology BigOperators Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

/-- The Weierstrass test for the full derivative series in Lemma
A.3. The bound uses all `n` insertions and the two
uniform derivative bounds on the parameter interval. -/
theorem tendstoUniformlyOn_self_nested_derivative [NeZero d]
    {Ω D Dd : ℝ → 𝕄} {S : Set ℝ} {w C₁ C₂ : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : ∀ s ∈ S, (Ω s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ S), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hdΩ : ∀ s ∈ S, HasDerivWithinAt Ω (D s) S s)
    (hdD : ∀ s ∈ S, HasDerivWithinAt D (Dd s) S s)
    (hu : UniqueDiffOn ℝ S) (hD : ∀ s ∈ S, ‖D s‖ ≤ C₁)
    (hDd : ∀ s ∈ S, ‖Dd s‖ ≤ C₂) :
    TendstoUniformlyOn
      (fun N s ↦ ∑ n ∈ Finset.range N,
        ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
          derivWithin (fun t ↦ (adL (Ω t) ^ n) (D t)) S s)
      (fun s ↦ ∑' n : ℕ,
        ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
          derivWithin (fun t ↦ (adL (Ω t) ^ n) (D t)) S s) atTop S := by
  let u : ℕ → ℝ := fun n ↦
    |((bernoulli (n + 2) : ℚ) : ℝ)| * w ^ n /
      (Nat.factorial (n + 2) : ℝ) * C₂ +
    (|((bernoulli (n + 2) : ℚ) : ℝ)| * n * w ^ (n - 1) /
      (Nat.factorial (n + 2) : ℝ)) * (2 * C₁ ^ 2)
  have hs₁ := (summable_frameBound_majorant hw0 hw).mul_right C₂
  have hs₂ := (summable_frameLip_majorant hw0 hw).mul_right (2 * C₁ ^ 2)
  have hs : Summable u := hs₁.add hs₂
  apply tendstoUniformlyOn_tsum_nat hs
  intro n s hsS
  have hd := hasDerivWithinAt_nested_commutator (hdΩ s hsS) (hdD s hsS) n
  rw [hd.derivWithin (hu s hsS), norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hb := norm_nested_commutator_derivative_le (hΩ s hsS) hw0
    (hwidth s hsS) (D s) (Dd s) n
  have hb' : ‖cubicPowDerivative (adL (Ω s)) (adL (D s)) n (D s) +
      (adL (Ω s) ^ n) (Dd s)‖ ≤
      w ^ n * C₂ + 2 * (n : ℝ) * w ^ (n - 1) * C₁ ^ 2 := by
    apply hb.trans
    gcongr
    · exact hDd s hsS
    · exact hD s hsS
  calc
    _ ≤ (|((bernoulli (n+2) : ℚ) : ℝ)| / (Nat.factorial (n+2) : ℝ)) *
        (w ^ n * C₂ + 2 * (n : ℝ) * w ^ (n - 1) * C₁ ^ 2) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = u n := by dsimp only [u]; ring


/-- The two derivatives of the paper's `C²` curve are bounded on the closed
parameter interval, including the one-sided endpoint derivatives. -/
theorem self_curve_derivatives_bounded {Ω : ℝ → 𝕄}
    (hcΩ : ContDiffOn ℝ 2 Ω K) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ s ∈ K, ‖derivWithin Ω K s‖ ≤ C₁) ∧
      (∀ s ∈ K, ‖derivWithin (derivWithin Ω K) K s‖ ≤ C₂) := by
  have hcD : ContDiffOn ℝ 1 (derivWithin Ω K) K :=
    hcΩ.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcDd : ContDiffOn ℝ 0 (derivWithin (derivWithin Ω K) K) K :=
    hcD.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcD.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcDd.continuousOn
  exact ⟨C₁, C₂, (norm_nonneg _).trans (hC₁ 0 (by norm_num)),
    (norm_nonneg _).trans (hC₂ 0 (by norm_num)), hC₁, hC₂⟩

/-- The full derivative series converges uniformly on `[0,1]`
under exactly the path and width assumptions of Lemma A.3. -/
theorem tendstoUniformlyOn_self_curve_derivative [NeZero d] {Ω : ℝ → 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : ∀ s ∈ K, (Ω s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ K), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 2 Ω K) :
    TendstoUniformlyOn
      (fun N s ↦ ∑ n ∈ Finset.range N,
        ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
          derivWithin (fun t ↦ (adL (Ω t) ^ n) (derivWithin Ω K t)) K s)
      (fun s ↦ ∑' n : ℕ,
        ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
          derivWithin (fun t ↦ (adL (Ω t) ^ n) (derivWithin Ω K t)) K s) atTop K := by
  obtain ⟨C₁, C₂, _, _, hD, hDd⟩ := self_curve_derivatives_bounded hcΩ
  have hcD : ContDiffOn ℝ 1 (derivWithin Ω K) K :=
    hcΩ.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  exact tendstoUniformlyOn_self_nested_derivative hw0 hw hΩ hwidth
    (fun s hs ↦ (hcΩ.differentiableOn (by norm_num) s hs).hasDerivWithinAt)
    (fun s hs ↦ (hcD.differentiableOn (by norm_num) s hs).hasDerivWithinAt)
    uniqueDiffOn_Icc_zero_one hD hDd

/-- The full positive coefficient series for a differentiated self-input
multiplier, before separating its constant term. -/
theorem self_derivative_positive_series [NeZero d] (Ω D Dd : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    (∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
        (cubicPowDerivative (adL Ω) (adL D) n D + (adL Ω ^ n) Dd)) =
      unifiedFrameError Ω D D + frameOp Ω Dd := by
  have hsE := summable_frameError_positive Ω D D ha
  have hs := (summable_norm_frameSeries_terms (I • adL Ω) ha).of_norm
  have hp : Summable (fun n : ℕ ↦
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
        adL Ω ^ n) := hs.congr (UnitaryProducts.Prose.frame_term_I_smul (adL Ω))
  have hsP := (ContinuousLinearMap.apply ℂ 𝕄 Dd).summable hp
  simp only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply] at hsP
  simp_rw [smul_add]
  rw [hsE.tsum_add hsP, ← unifiedFrameError_positive_series Ω D D ha,
    ← UnitaryProducts.Prose.frameOp_eq_positive_series Ω Dd ha]

/-- The derivative is the full termwise differentiated positive series,
including its degree-zero input derivative. -/
theorem self_frame_derivative_eq_series [NeZero d]
    {Ω D : ℝ → 𝕄} {Dd : 𝕄} {S : Set ℝ} {s : ℝ}
    (hΩ : HasDerivWithinAt Ω (D s) S s) (hD : HasDerivWithinAt D Dd S s)
    (hu : UniqueDiffWithinAt ℝ S s) (ha : ‖I • adL (Ω s)‖ < 2 * π) :
    derivWithin (fun t ↦ frameOp (Ω t) (D t)) S s = ∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
        derivWithin (fun t ↦ (adL (Ω t) ^ n) (D t)) S s := by
  simp_rw [(hasDerivWithinAt_nested_commutator hΩ hD _).derivWithin hu]
  rw [self_derivative_positive_series _ _ _ ha,
    (hasDerivWithinAt_frameOp hΩ hD ha).derivWithin hu]

/-- Uniform convergence of the derivative series proves the `C¹` assertion
in Lemma A.3. The full series includes the constant term. -/
theorem contDiffOn_self_frame_uniform [NeZero d] {Ω : ℝ → 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : ∀ s ∈ K, (Ω s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ K), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 2 Ω K) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (derivWithin Ω K s)) K := by
  let D := derivWithin Ω K
  let Dd := derivWithin D K
  have hcD : ContDiffOn ℝ 1 D K :=
    hcΩ.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcDd : ContinuousOn Dd K :=
    (hcD.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num : (0 : WithTop ℕ∞) + 1 ≤
      1)).continuousOn
  have hdΩ (s : ℝ) (hs : s ∈ K) : HasDerivWithinAt Ω (D s) K s :=
    (hcΩ.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hdD (s : ℝ) (hs : s ∈ K) : HasDerivWithinAt D (Dd s) K s :=
    (hcD.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have ha (s : ℝ) (hs : s ∈ K) : ‖I • adL (Ω s)‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL (Ω s)‖ ≤ w by
      simpa only [pow_one] using UnitStepsProse.ad_power_norm_le (hΩ s hs) (hwidth s hs)
        1).trans_lt hw
  have hca : ContinuousOn (fun s ↦ adL (Ω s)) K :=
    (adLCLM d).continuous.comp_continuousOn hcΩ.continuousOn
  have hcb : ContinuousOn (fun s ↦ adL (D s)) K :=
    (adLCLM d).continuous.comp_continuousOn hcD.continuousOn
  have hcterm (n : ℕ) : ContinuousOn
      (fun s ↦ derivWithin (fun t ↦ (adL (Ω t) ^ n) (D t)) K s) K := by
    have hcPow : ContinuousOn (fun s ↦ cubicPowDerivative (adL (Ω s)) (adL (D s)) n) K := by
      unfold cubicPowDerivative
      exact continuousOn_finset_sum _ (fun j _ ↦ ((hca.pow _).mul hcb).mul (hca.pow _))
    apply ((hcPow.clm_apply hcD.continuousOn).add ((hca.pow n).clm_apply hcDd)).congr
    intro s hs
    exact (hasDerivWithinAt_nested_commutator (hdΩ s hs) (hdD s hs) n).derivWithin
      (uniqueDiffOn_Icc_zero_one s hs)
  have hu := tendstoUniformlyOn_self_curve_derivative hw0 hw hΩ hwidth hcΩ
  have hcSum : ContinuousOn (fun s ↦ ∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
        derivWithin (fun t ↦ (adL (Ω t) ^ n) (D t)) K s) K := by
    apply hu.continuousOn
    exact (Filter.Eventually.of_forall (fun N ↦
      continuousOn_finset_sum (Finset.range N) (fun n _ ↦ (hcterm n).const_smul _))).frequently
  have hcDeriv : ContinuousOn
      (derivWithin (fun s ↦ frameOp (Ω s) (D s)) K) K := by
    apply hcSum.congr
    intro s hs
    exact self_frame_derivative_eq_series (hdΩ s hs) (hdD s hs)
      (uniqueDiffOn_Icc_zero_one s hs) (ha s hs)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_derivWithin uniqueDiffOn_Icc_zero_one]
  refine ⟨?_, by simp, contDiffOn_zero.mpr hcDeriv⟩
  intro s hs
  exact (hasDerivWithinAt_frameOp (hdΩ s hs) (hdD s hs) (ha s hs)).differentiableWithinAt

end UnitaryProducts.PaperProof
