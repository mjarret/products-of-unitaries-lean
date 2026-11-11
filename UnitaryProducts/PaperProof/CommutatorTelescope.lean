/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.GeneralSeries
public import UnitaryProducts.Corrector.PartialFractions

/-! # The full insertion series and its Jacobi telescope in Lemma A.3 -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator Topology BigOperators
open Complex Real Set Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper.UnitStepsProse
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Cotangent partial fractions satisfy the assumptions on `g` in Appendix A. -/
theorem frame_nonnegativeSeries : NonnegativeSeries frameCoeff where
  nonneg := frameCoeff_nonneg
  converges := fun r hr0 hr ↦ summable_frameCoeff_power (by rwa [abs_of_nonneg hr0])

/-- The variation in the generator, with the input held fixed. -/
def unifiedFrameError (Ω Ωd D : 𝕄) : 𝕄 :=
  ∑' n, (frameCoeff n : ℂ) • cubicPowDerivative (adL Ω) (adL Ωd) n D

/-- The positive-coefficient form of the insertion map. -/
theorem unifiedFrameError_positive_series (Ω Ωd D : 𝕄) :
    unifiedFrameError Ω Ωd D = ∑' n,
      (frameCoeff n : ℂ) • cubicPowDerivative (adL Ω) (adL Ωd) n D := rfl

/-- Absolute convergence of the full insertion series with positive coefficients. -/
theorem summable_frameError_positive [NeZero d] (Ω A D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦ (frameCoeff n : ℂ) •
      cubicPowDerivative (adL Ω) (adL A) n D) := by
  have ha' : ‖adL Ω‖ < 2 * π := by simpa only [norm_smul, Complex.norm_I, one_mul] using ha
  have hs := (frame_nonnegativeSeries.summable_norm_derivative
    (a := adL Ω) (b := adL A) le_rfl ha').of_norm
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply] using
    (ContinuousLinearMap.apply ℂ 𝕄 D).summable hs

/-- Equation `eq:series-derivative` specialized to the cotangent multiplier. -/
theorem hasDerivWithinAt_frameOp [NeZero d] {Ω D : ℝ → 𝕄} {Ωd Dd : 𝕄}
    {S : Set ℝ} {s : ℝ}
    (hΩ : HasDerivWithinAt Ω Ωd S s) (hD : HasDerivWithinAt D Dd S s)
    (ha : ‖I • adL (Ω s)‖ < 2 * π) :
    HasDerivWithinAt (fun t ↦ frameOp (Ω t) (D t))
      (unifiedFrameError (Ω s) Ωd (D s) + frameOp (Ω s) Dd) S s := by
  have ha' : ‖adL (Ω s)‖ < 2 * π := by
    simpa only [norm_smul, Complex.norm_I, one_mul] using ha
  have hd := general_series_derivative frame_nonnegativeSeries hΩ hD ha'
  simp_rw [← cubicPowDerivative_outer_sum] at hd
  simpa only [commutatorSeries, algebraSeries, frameOp, positiveFrameSeries,
    unifiedFrameError, add_comm] using hd

/-- Continuous differentiability is the general series result with `g=N`. -/
theorem contDiffOn_frameOp [NeZero d] {Ω D : ℝ → 𝕄} {S : Set ℝ} {w : ℝ}
    (hw : w < 2 * π) (hΩ : ∀ s ∈ S, (Ω s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ S), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 1 Ω S) (hcD : ContDiffOn ℝ 1 D S) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (D s)) S := by
  exact general_series_contDiffOn frame_nonnegativeSeries hw hΩ hwidth hcΩ hcD

/-- `F(A)` in the exact positive-degree indexing used in Lemma A.3. -/
theorem unifiedFrameError_full_series [NeZero d] (Ω A D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    unifiedFrameError Ω A D = ∑' n : ℕ,
      ((frameCoeff (n + 1) : ℝ) : ℂ) •
        (∑ k ∈ Finset.range (n + 1),
          (adL Ω ^ k) (adL A ((adL Ω ^ (n - k)) D))) := by
  rw [unifiedFrameError_positive_series Ω A D,
    (summable_frameError_positive Ω A D ha).tsum_eq_zero_add]
  simp only [cubicPowDerivative, Finset.range_zero, Finset.sum_empty,
    ContinuousLinearMap.zero_apply, smul_zero, zero_add]
  apply tsum_congr
  intro n
  congr 1
  simpa only [Nat.add_sub_cancel] using cubicPowDerivative_outer_sum Ω A D (n + 1)

/-- The full insertion map is additive in its direction argument. -/
theorem unifiedFrameError_add_direction [NeZero d] (Ω A B D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    unifiedFrameError Ω (A + B) D = unifiedFrameError Ω A D + unifiedFrameError Ω B D := by
  have had : adL (A + B) = adL A + adL B := by
    apply ContinuousLinearMap.ext
    intro X
    simp only [ContinuousLinearMap.add_apply, adL_apply, add_mul, mul_add]
    abel
  have hpow (n : ℕ) : cubicPowDerivative (adL Ω) (adL (A + B)) n D =
      cubicPowDerivative (adL Ω) (adL A) n D +
        cubicPowDerivative (adL Ω) (adL B) n D := by
    simp only [cubicPowDerivative, had, mul_add, add_mul, Finset.sum_add_distrib,
      ContinuousLinearMap.add_apply]
  rw [unifiedFrameError_positive_series Ω (A + B) D,
    unifiedFrameError_positive_series Ω A D, unifiedFrameError_positive_series Ω B D]
  simp_rw [hpow, smul_add]
  exact (summable_frameError_positive Ω A D ha).tsum_add
    (summable_frameError_positive Ω B D ha)

/-- The insertion map is homogeneous in its direction argument. Together with
additivity this backs the paper's assertion that `F` is complex-linear. -/
theorem unifiedFrameError_smul_direction (Ω A D : 𝕄) (z : ℂ) :
    unifiedFrameError Ω (z • A) D = z • unifiedFrameError Ω A D := by
  have had : adL (z • A) = z • adL A := by
    change adLCLM d (z • A) = z • adLCLM d A
    exact map_smul (adLCLM d) z A
  have hp (n : ℕ) : cubicPowDerivative (adL Ω) (adL (z • A)) n D =
      z • cubicPowDerivative (adL Ω) (adL A) n D := by
    rw [cubicPowDerivative_outer_sum, cubicPowDerivative_outer_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [had, ContinuousLinearMap.smul_apply, map_smul]
  unfold unifiedFrameError
  calc
    _ = ∑' n, z • ((frameCoeff n : ℂ) •
        cubicPowDerivative (adL Ω) (adL A) n D) := by
      apply tsum_congr
      intro n
      rw [hp, smul_comm]
    _ = _ := tsum_const_smul'' z

/-- The paper's linear map `F` packages the insertion series and its linearity
before the decomposition of `Ω'` is applied. -/
def unifiedFrameErrorLinearMap [NeZero d] (Ω D : 𝕄) (ha : ‖I • adL Ω‖ < 2 * π) :
    𝕄 →ₗ[ℂ] 𝕄 where
  toFun A := unifiedFrameError Ω A D
  map_add' A B := unifiedFrameError_add_direction Ω A B D ha
  map_smul' z A := unifiedFrameError_smul_direction Ω A D z

/-- The estimate for `F(A)` in Lemma A.3 sums all `n` insertion bounds. -/
theorem norm_unifiedFrameError_le [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (A D : 𝕄) :
    ‖unifiedFrameError Ω A D‖ ≤ 2 * frameLip w * ‖A‖ * ‖D‖ := by
  have ha : ‖I • adL Ω‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL Ω‖ ≤ w by
      simpa only [pow_one] using ad_power_norm_le hΩ hwidth 1).trans_lt hw
  let c : ℕ → ℝ := fun n ↦ frameCoeff n
  let f : ℕ → 𝕄 := fun n ↦ (c n : ℂ) • cubicPowDerivative (adL Ω) (adL A) n D
  let g : ℕ → ℝ := fun n ↦
    (frameCoeff n * n * w ^ (n - 1)) * (2 * ‖A‖ * ‖D‖)
  have hg : Summable g := (frame_nonnegativeSeries.summable_derivative hw0 hw).mul_right _
  have hbound (n : ℕ) : ‖f n‖ ≤ g n := by
    dsimp only [f]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [c]; exact frameCoeff_nonneg _)]
    calc
      _ ≤ c n * (2 * n * w ^ (n - 1) * ‖A‖ * ‖D‖) :=
        mul_le_mul_of_nonneg_left (norm_cubicPowDerivative_ad_le hΩ hw0 hwidth A D n)
          (by dsimp [c]; exact frameCoeff_nonneg _)
      _ = g n := by dsimp [c, g]; ring
  have hfn : Summable (fun n ↦ ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound hg
  have he : unifiedFrameError Ω A D = ∑' n, f n := by
    rw [unifiedFrameError_full_series Ω A D ha]
    have hs : Summable f := summable_frameError_positive Ω A D ha
    rw [hs.tsum_eq_zero_add]
    have hz : f 0 = 0 := by simp [f, cubicPowDerivative]
    rw [hz, zero_add]
    apply tsum_congr
    intro n
    dsimp only [f, c]
    congr 1
    simpa only [Nat.add_sub_cancel] using
      (cubicPowDerivative_outer_sum Ω A D (n + 1)).symm
  rw [he]
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' n, g n := hfn.tsum_le_tsum hbound hg
    _ = 2 * frameLip w * ‖A‖ * ‖D‖ := by
      rw [show (∑' n, g n) = frameLip w * (2 * ‖A‖ * ‖D‖) from tsum_mul_right]
      ring

/-- The literal infinite Jacobi telescope in Lemma A.3. -/
theorem unifiedFrameError_commutator_series [NeZero d] (Ω B D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    unifiedFrameError Ω (adL Ω B) D = ∑' n : ℕ,
      ((frameCoeff (n + 1) : ℝ) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL B D) - adL B ((adL Ω ^ (n + 1)) D)) := by
  rw [unifiedFrameError_positive_series Ω (adL Ω B) D,
    (summable_frameError_positive Ω (adL Ω B) D ha).tsum_eq_zero_add]
  have hz : cubicPowDerivative (adL Ω) (adL (adL Ω B)) 0 D = 0 := by
    simp [cubicPowDerivative]
  rw [hz, smul_zero, zero_add]
  apply tsum_congr
  intro n
  rw [cubicPowDerivative_commutator_telescope]

/-- The positive-degree scalar series is `N(w)-N(0)`. -/
theorem frameBound_positive_tail {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∑' n : ℕ, frameCoeff (n + 1) * w ^ (n + 1)) = frameBound w - frameBound 0 := by
  have hsplit := (frame_nonnegativeSeries.converges w hw0 hw).tsum_eq_zero_add
  have hzero : frameBound 0 = frameCoeff 0 := by
    unfold frameBound
    rw [tsum_eq_single 0 (fun n hn ↦ by simp [zero_pow hn])]
    simp
  change frameBound w = _ at hsplit
  simpa only [pow_zero, mul_one, hzero, eq_sub_iff_add_eq, add_comm] using hsplit.symm

/-- Absolute convergence of the positive series for `N(ad Ω)` applied to a matrix. -/
theorem summable_frameOp_positive [NeZero d] (Ω D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      ((frameCoeff n : ℝ) : ℂ) • (adL Ω ^ n) D) := by
  have ha' : ‖adL Ω‖ < 2 * π := by simpa only [norm_smul, Complex.norm_I, one_mul] using ha
  have hs := (frame_nonnegativeSeries.summable_norm
    (A := 𝕄 →L[ℂ] 𝕄) (a := adL Ω) le_rfl ha').of_norm
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply] using
    (ContinuousLinearMap.apply ℂ 𝕄 D).summable hs

/-- Removing the constant coefficient gives the series for `N(ad Ω)-N(0)`. -/
theorem frameOp_sub_zero_series [NeZero d] (Ω D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    frameOp Ω D - (frameBound 0 : ℂ) • D = ∑' n : ℕ,
      ((frameCoeff (n + 1) : ℝ) : ℂ) • (adL Ω ^ (n + 1)) D := by
  have ha' : ‖adL Ω‖ < 2 * π := by simpa only [norm_smul, Complex.norm_I, one_mul] using ha
  change commutatorSeries frameCoeff Ω D - (frameBound 0 : ℂ) • D = _
  rw [commutatorSeries_eq_tsum frame_nonnegativeSeries Ω D ha',
    (summable_frameOp_positive Ω D ha).tsum_eq_zero_add]
  have hzero : frameBound 0 = frameCoeff 0 := by
    unfold frameBound
    rw [tsum_eq_single 0 (fun n hn ↦ by simp [zero_pow hn])]
    simp
  simp only [hzero, pow_zero, ContinuousLinearMap.one_apply, add_sub_cancel_left]

/-- Lemma A.3's closed form of `F([Ω,Λ])`. Jacobi turns the finite insertion
sum into a telescope, and summing its boundary terms gives the identity used
in the norm bound (F-split). -/
theorem unifiedFrameError_commutator_closed [NeZero d] (Ω B D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    unifiedFrameError Ω (adL Ω B) D =
      (frameOp Ω (adL B D) - (frameBound 0 : ℂ) • adL B D) -
        adL B (frameOp Ω D - (frameBound 0 : ℂ) • D) := by
  have hs (E : 𝕄) : Summable (fun n : ℕ ↦
      ((frameCoeff (n + 1) : ℝ) : ℂ) • (adL Ω ^ (n + 1)) E) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff 1).mpr (summable_frameOp_positive Ω E ha)
  rw [unifiedFrameError_commutator_series Ω B D ha,
    frameOp_sub_zero_series Ω (adL B D) ha, frameOp_sub_zero_series Ω D ha,
    (adL B).map_tsum (hs D), ← (hs (adL B D)).tsum_sub ((adL B).summable (hs D))]
  apply tsum_congr
  intro n
  simp only [smul_sub, map_smul]

/-- The positive series bounds `N(ad Ω)-N(0)` by `N(w)-N(0)`. -/
theorem norm_frameOp_sub_zero_le [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    ‖frameOp Ω D - (frameBound 0 : ℂ) • D‖ ≤
      (frameBound w - frameBound 0) * ‖D‖ := by
  have ha : ‖adL Ω‖ < 2 * π := by
    exact (show ‖adL Ω‖ ≤ w by
      simpa only [pow_one] using ad_power_norm_le hΩ hwidth 1).trans_lt hw
  have hb := general_series_bound frame_nonnegativeSeries.withoutConstant hΩ hw0 hw hwidth D
  rw [commutatorSeries_withoutConstant frame_nonnegativeSeries Ω D ha,
    scalarSeries_withoutConstant frame_nonnegativeSeries hw0 hw] at hb
  have hzero : frameBound 0 = frameCoeff 0 := by
    unfold frameBound
    rw [tsum_eq_single 0 (fun n hn ↦ by simp [zero_pow hn])]
    simp
  rw [hzero]
  exact hb

/-- The closed Jacobi expression is bounded by the positive-series estimate
for `N-N(0)` and the elementary commutator bound. -/
theorem norm_unifiedFrameError_commutator_le [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (B D : 𝕄) :
    ‖unifiedFrameError Ω (adL Ω B) D‖ ≤
      4 * (frameBound w - frameBound 0) * ‖B‖ * ‖D‖ := by
  have ha : ‖I • adL Ω‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL Ω‖ ≤ w by
      simpa only [pow_one] using ad_power_norm_le hΩ hwidth 1).trans_lt hw
  have htail : 0 ≤ frameBound w - frameBound 0 := by
    rw [← frameBound_positive_tail hw0 hw]
    exact tsum_nonneg (fun n ↦ mul_nonneg (frameCoeff_nonneg _) (pow_nonneg hw0 _))
  have hc (E : 𝕄) : ‖adL B E‖ ≤ 2 * ‖B‖ * ‖E‖ := by
    simpa only [zero_smul, sub_zero] using norm_adL_apply_le B E 0
  rw [unifiedFrameError_commutator_closed Ω B D ha]
  calc
    _ ≤ ‖frameOp Ω (adL B D) - (frameBound 0 : ℂ) • adL B D‖ +
        ‖adL B (frameOp Ω D - (frameBound 0 : ℂ) • D)‖ := norm_sub_le _ _
    _ ≤ (frameBound w - frameBound 0) * ‖adL B D‖ +
        2 * ‖B‖ * ‖frameOp Ω D - (frameBound 0 : ℂ) • D‖ :=
      add_le_add (norm_frameOp_sub_zero_le hΩ hw0 hw hwidth _) (hc _)
    _ ≤ (frameBound w - frameBound 0) * (2 * ‖B‖ * ‖D‖) +
        2 * ‖B‖ * ((frameBound w - frameBound 0) * ‖D‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hc D) htail)
        (mul_le_mul_of_nonneg_left (norm_frameOp_sub_zero_le hΩ hw0 hw hwidth D)
          (by positivity))
    _ = _ := by ring

/-- The positive-degree coefficients make `N(w)-N(0)` nonnegative. -/
theorem frameBound_sub_zero_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ frameBound w - frameBound 0 := by
  rw [← frameBound_positive_tail hw0 hw]
  exact tsum_nonneg (fun n ↦ mul_nonneg (frameCoeff_nonneg _) (pow_nonneg hw0 _))

/-- The arbitrary split (F-split): linearity, the insertion estimate, and the
closed Jacobi expression apply to every decomposition `D = X + [Ω,B]`. -/
theorem norm_unifiedFrameError_split_le [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    (D X B : 𝕄) (hdecomp : D = X + adL Ω B) :
    ‖unifiedFrameError Ω D D‖ ≤ 2 * frameLip w * ‖X‖ * ‖D‖ +
      4 * (frameBound w - frameBound 0) * ‖B‖ * ‖D‖ := by
  have ha : ‖I • adL Ω‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL Ω‖ ≤ w by
      simpa only [pow_one] using ad_power_norm_le hΩ hwidth 1).trans_lt hw
  have he : unifiedFrameError Ω D D =
      unifiedFrameError Ω X D + unifiedFrameError Ω (adL Ω B) D := by
    conv_lhs => arg 2; rw [hdecomp]
    exact (unifiedFrameErrorLinearMap Ω D ha).map_add X (adL Ω B)
  rw [he]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_unifiedFrameError_le hΩ hw0 hw hwidth X D)
      (norm_unifiedFrameError_commutator_le hΩ hw0 hw hwidth B D))

end UnitaryProducts.PaperProof
