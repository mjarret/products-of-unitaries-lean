/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UnifiedJumpsSupport

/-! # The three-term jump proof

The middle term follows the self-curve end-value estimate. The outer terms
compare the sampled derivative to the mean derivative on the affine cell.
-/
@[expose] public section
noncomputable section
open Real Complex Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof

section MeanDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "J" => Icc (0 : ℝ) 1

set_option maxHeartbeats 800000 in
-- The Banach-valued FTC requires interval and within-derivative elaboration.
/-- The affine cell slope is the mean derivative, by the Banach-valued FTC. -/
theorem jump_increment_eq_integral {H Hd : ℝ → E}
    (hd : ∀ s ∈ J, HasDerivWithinAt H (Hd s) J s)
    (hc : ContinuousOn Hd J) {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a ≤ b) :
    H b - H a = ∫ s in a..b, Hd s := by
  have hsub : Icc a b ⊆ J := Icc_subset_Icc ha.1 hb.2
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((HasDerivWithinAt.continuousOn hd).mono hsub) _ ((hc.mono hsub).intervalIntegrable_of_Icc hab)
  intro s hs
  exact (hd s (hsub (Ioo_subset_Icc_self hs))).hasDerivAt
    (Icc_mem_nhds (ha.1.trans_lt hs.1) (hs.2.trans_le hb.2))

set_option maxHeartbeats 800000 in
-- The two integral estimates elaborate both scalar and Banach-space calculations.
/-- Both endpoint errors of an averaged Lipschitz function are bounded by
half the Lipschitz constant times the cell length. -/
theorem jump_average_endpoint_errors {f : ℝ → E} {a b h : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖f t - f s‖ ≤ h * |t - s|) :
    ‖f b - (1 / (b - a)) • (∫ s in a..b, f s)‖ ≤ h * (b - a) / 2 ∧
    ‖(1 / (b - a)) • (∫ s in a..b, f s) - f a‖ ≤ h * (b - a) / 2 := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hi : IntervalIntegrable f volume a b := hc.intervalIntegrable_of_Icc hab.le
  have hright : f b - (1 / (b - a)) • (∫ s in a..b, f s) =
      (1 / (b - a)) • (∫ s in a..b, f b - f s) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, smul_sub, smul_smul, one_div_mul_cancel hlen.ne', one_smul]
  have hleft : (1 / (b - a)) • (∫ s in a..b, f s) - f a =
      (1 / (b - a)) • (∫ s in a..b, f s - f a) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, smul_sub, smul_smul, one_div_mul_cancel hlen.ne', one_smul]
  have hrightint : (∫ s in a..b, h * (b - s)) = h * (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ s) b]
    simp [integral_id, mul_div_assoc]
  have hleftint : (∫ s in a..b, h * (s - a)) = h * (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ s) a]
    simp [integral_id, mul_div_assoc]
  have hrightbound : ‖∫ s in a..b, f b - f s‖ ≤ h * (b - a) ^ 2 / 2 := by
    rw [← hrightint]
    apply intervalIntegral.norm_integral_le_of_norm_le hab.le
    · exact Filter.Eventually.of_forall fun s hs ↦ by
        simpa only [abs_of_nonneg (sub_nonneg.mpr hs.2)] using
          hlip s ⟨hs.1.le, hs.2⟩ b ⟨hab.le, le_rfl⟩
    · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable a b
  have hleftbound : ‖∫ s in a..b, f s - f a‖ ≤ h * (b - a) ^ 2 / 2 := by
    rw [← hleftint]
    apply intervalIntegral.norm_integral_le_of_norm_le hab.le
    · exact Filter.Eventually.of_forall fun s hs ↦ by
        simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1.le)] using
          hlip a ⟨le_rfl, hab.le⟩ s ⟨hs.1.le, hs.2⟩
    · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable a b
  constructor
  · rw [hright, norm_smul_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hrightbound (by positivity)).trans_eq
      (by field_simp)
  · rw [hleft, norm_smul_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hleftbound (by positivity)).trans_eq
      (by field_simp)

set_option maxHeartbeats 800000 in
-- The integral norm bound combines scalar and Banach-space instances.
omit [CompleteSpace E] in
/-- The norm of a mean derivative is bounded by the same uniform bound. -/
theorem jump_average_norm_le {f : ℝ → E} {a b L : ℝ} (hab : a < b)
    (hbound : ∀ s ∈ Icc a b, ‖f s‖ ≤ L) :
    ‖(1 / (b - a)) • (∫ s in a..b, f s)‖ ≤ L := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  rw [norm_smul_of_nonneg (by positivity)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s hs ↦ hbound s (by rw [uIoc_of_le hab.le] at hs; exact ⟨hs.1.le, hs.2⟩))
  have h := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / (b - a))
  rw [abs_of_pos hlen] at h
  exact h.trans_eq (by field_simp)

end MeanDerivative

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "J" => Icc (0 : ℝ) 1

set_option maxHeartbeats 800000 in
-- The matrix-valued affine derivative elaborates complex and real scalar structures.
/-- Both one-sided affine derivatives equal the same constant cell slope. -/
theorem jumpSegment_derivWithin (A B : 𝕄) {s : ℝ} (hs : s ∈ J) :
    derivWithin (jumpSegment A B) J s = B - A :=
  (hasDerivAt_jumpSegment A B s).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one s hs)

set_option maxHeartbeats 800000 in
-- The iterated within derivative uses the matrix real-scalar structure.
/-- The affine interpolant has zero second derivative, including its
one-sided values at the ends of the normalized cell. -/
theorem jumpSegment_second_derivWithin (A B : 𝕄) {s : ℝ} (hs : s ∈ J) :
    derivWithin (derivWithin (jumpSegment A B) J) J s = 0 := by
  rw [derivWithin_congr (fun t ht ↦ jumpSegment_derivWithin A B ht)
    (jumpSegment_derivWithin A B hs)]
  simp

set_option maxHeartbeats 800000 in
-- The frame-operator curve combines matrix and operator-algebra instances.
/-- The self-curve end value on an affine segment has the same within
derivative as the expression with its constant slope substituted. -/
theorem jumpSegment_frame_self_derivWithin (A B : 𝕄) {s : ℝ} (hs : s ∈ J) :
    derivWithin (fun t ↦ frameOp (jumpSegment A B t)
      (derivWithin (jumpSegment A B) J t)) J s =
      derivWithin (fun t ↦ frameOp (jumpSegment A B t) (B - A)) J s := by
  exact derivWithin_congr
    (fun t ht ↦ congrArg (frameOp (jumpSegment A B t)) (jumpSegment_derivWithin A B ht))
    (congrArg (frameOp (jumpSegment A B s)) (jumpSegment_derivWithin A B hs))

set_option maxHeartbeats 800000 in
-- The mesh rescaling combines Banach integration with matrix scalar structures.
/-- On an actual mesh cell, the slope is `T` times the derivative integral;
the two endpoint errors are `h/(2T)` and its norm is at most `L`. -/
theorem jump_sample_slope {H Hd : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    (hd : ∀ s ∈ J, HasDerivWithinAt H (Hd s) J s)
    {h L : ℝ} (hlip : ∀ s ∈ J, ∀ t ∈ J, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hbd : ∀ s ∈ J, ‖Hd s‖ ≤ L) {j : ℕ} (hj : j < T) :
    let a := (j : ℝ) / T
    let b := ((j : ℝ) + 1) / T
    let D := (T : ℝ) • (H b - H a)
    D = (T : ℝ) • (∫ s in a..b, Hd s) ∧
      ‖Hd b - D‖ ≤ h / (2 * T) ∧ ‖D - Hd a‖ ≤ h / (2 * T) ∧ ‖D‖ ≤ L := by
  intro a b D
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have ha : a ∈ J := walkCubic_sample hj.le
  have hb : b ∈ J := by
    simpa only [b, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using walkCubic_sample hj
  have hab : a < b := (div_lt_div_iff_of_pos_right ht).mpr (by linarith)
  have hlen : b - a = 1 / T := by dsimp [a, b]; ring
  have hinv : 1 / (b - a) = (T : ℝ) := by rw [hlen]; simp
  have hc : ContinuousOn Hd J := continuousOn_of_norm_sub_le hlip
  have hsub : Icc a b ⊆ J := Icc_subset_Icc ha.1 hb.2
  have hmean := jump_increment_eq_integral hd hc ha hb hab.le
  have hD : D = (T : ℝ) • (∫ s in a..b, Hd s) := by
    change (T : ℝ) • (H b - H a) = _
    rw [hmean]
  have he := jump_average_endpoint_errors hab (hc.mono hsub)
    (fun s hs t ht ↦ hlip s (hsub hs) t (hsub ht))
  have hn := jump_average_norm_le hab (fun s hs ↦ hbd s (hsub hs))
  rw [hinv, ← hD] at he hn
  have hcst : h * (b - a) / 2 = h / (2 * T) := by rw [hlen]; ring
  rw [hcst] at he
  exact ⟨hD, he.1, he.2, hn⟩

set_option maxHeartbeats 800000 in
-- The matrix additive identity elaborates the operator-valued frame expressions.
/-- Add and subtract the two self-curve end values. This is the exact
three-term decomposition preceding the first norm inequality. -/
theorem affine_jump_three_terms (A B Da Db Ea Eb : 𝕄) :
    frameOp B Db - frameOp A Da =
      frameOp B (Db - Eb) + (frameOp B Eb - frameOp A Ea) + frameOp A (Ea - Da) := by
  rw [frameOp_sub, frameOp_sub]
  abel

set_option maxHeartbeats 800000 in
-- The matrix norm inequalities elaborate the operator-valued frame expressions.
/-- The first displayed inequality in the jump proof is the triangle
inequality applied to the three-term decomposition. -/
theorem affine_jump_three_norms (A B Da Db Ea Eb : 𝕄) :
    ‖frameOp B Db - frameOp A Da‖ ≤
      ‖frameOp B (Db - Eb)‖ + ‖frameOp B Eb - frameOp A Ea‖ + ‖frameOp A (Ea - Da)‖ := by
  rw [affine_jump_three_terms A B Da Db Ea Eb]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

set_option maxHeartbeats 800000 in
-- The spectral-width bounds elaborate the matrix and operator-algebra instances.
/-- The second displayed inequality bounds the two outer terms by the
positive-series multiplier norm. -/
theorem affine_jump_outer_bounds [NeZero d] {A B Da Db Ea Eb : 𝕄}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π)
    (hAw : ∀ p q, |hA.eigenvalues p - hA.eigenvalues q| ≤ w)
    (hBw : ∀ p q, |hB.eigenvalues p - hB.eigenvalues q| ≤ w) :
    ‖frameOp B Db - frameOp A Da‖ ≤
      frameBound w * (‖Db - Eb‖ + ‖Ea - Da‖) + ‖frameOp B Eb - frameOp A Ea‖ := by
  have hca := norm_sub_smul_one_le_of_eigenvalues hA hw0 (eigen_interval hA hAw)
  have hcb := norm_sub_smul_one_le_of_eigenvalues hB hw0 (eigen_interval hB hBw)
  have hright := norm_frameOp_le (D := Db - Eb) hw hcb
  have hleft := norm_frameOp_le (D := Ea - Da) hw hca
  exact (affine_jump_three_norms A B Da Db Ea Eb).trans
    ((add_le_add (add_le_add hright le_rfl) hleft).trans_eq (by ring))

set_option maxHeartbeats 800000 in
-- The derivative integral combines matrix and operator-algebra estimates.
/-- Integrate the local self-curve estimate along an affine segment.
The derivative estimate is the sole analytic input supplied by Lemma A.3. -/
theorem affine_self_variation [NeZero d] {A B : 𝕄}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {w η : ℝ} (hw : w < 2 * π)
    (hAw : ∀ p q, |hA.eigenvalues p - hA.eigenvalues q| ≤ w)
    (hBw : ∀ p q, |hB.eigenvalues p - hB.eigenvalues q| ≤ w)
    (hpoint : ∀ s ∈ J,
      ‖derivWithin (fun t ↦ frameOp (jumpSegment A B t) (B - A)) J s‖ ≤
        η * ‖B - A‖ ^ 2) :
    ‖frameOp B (B - A) - frameOp A (B - A)‖ ≤ η * ‖B - A‖ ^ 2 := by
  have hFc : ContDiffOn ℝ 1 (fun t ↦ frameOp (jumpSegment A B t) (B - A)) J :=
    contDiffOn_frameOp hw (fun s _ ↦ isHermitian_jumpSegment hA hB s)
      (fun s hs ↦ width_jumpSegment hA hB hAw hBw hs)
      ((contDiff_jumpSegment A B).of_le (by simp)).contDiffOn contDiffOn_const
  have hi := unified_increment_integral_via_ftc hFc hpoint intervalIntegrable_const
    (show (0 : ℝ) ∈ J by norm_num) (show (1 : ℝ) ∈ J by norm_num) zero_le_one
  simpa [jumpSegment] using hi

set_option maxHeartbeats 800000 in
-- The integral chain combines matrix norms with scalar integral estimates.
/-- The third and fourth lines of the jump estimate: integrate the middle
self-curve increment, then insert its pointwise derivative majorant. -/
theorem affine_jump_integral_chain [NeZero d] {Ω D : ℝ → 𝕄} {Da Db : 𝕄}
    (hΩ : ∀ s ∈ J, (Ω s).IsHermitian) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ s (hs : s ∈ J) p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hF : ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (D s)) J)
    {g : ℝ → ℝ}
    (hbound : ∀ s ∈ J, ‖derivWithin (fun t ↦ frameOp (Ω t) (D t)) J s‖ ≤ g s)
    (hi : IntervalIntegrable g volume 0 1) :
    ‖frameOp (Ω 1) Db - frameOp (Ω 0) Da‖ ≤
      frameBound w * (‖Db - D 1‖ + ‖D 0 - Da‖) +
        ∫ s in (0 : ℝ)..1, ‖derivWithin (fun t ↦ frameOp (Ω t) (D t)) J s‖ ∧
    ‖frameOp (Ω 1) Db - frameOp (Ω 0) Da‖ ≤
      frameBound w * (‖Db - D 1‖ + ‖D 0 - Da‖) + ∫ s in (0 : ℝ)..1, g s := by
  have h0 : (0 : ℝ) ∈ J := by norm_num
  have h1 : (1 : ℝ) ∈ J := by norm_num
  have hout := affine_jump_outer_bounds (Da := Da) (Db := Db) (Ea := D 0) (Eb := D 1)
    (hΩ 0 h0) (hΩ 1 h1) hw0 hw (hwidth 0 h0) (hwidth 1 h1)
  have hnorm := unified_increment_norm_integral_chain hF h0 h1 zero_le_one
  have hmajor := unified_increment_integral_via_ftc hF hbound hi h0 h1 zero_le_one
  exact ⟨hout.trans (add_le_add le_rfl (hnorm.1.le.trans hnorm.2)),
    hout.trans (add_le_add le_rfl hmajor)⟩

set_option maxHeartbeats 800000 in
-- The cell estimate combines spectral bounds, derivatives, and interval integrals.
/-- One affine cell in Theorem 4.4(i): the mean-slope endpoint errors and
the self-curve middle term give the coefficient `N(w)*h + eta*L²`. -/
theorem affine_hamiltonian_cell_bound [NeZero d] {H Hd : ℝ → 𝕄}
    (hH : ∀ s ∈ J, (H s).IsHermitian)
    (hd : ∀ s ∈ J, HasDerivWithinAt H (Hd s) J s)
    {L h w η : ℝ} (hbd : ∀ s ∈ J, ‖Hd s‖ ≤ L)
    (hlip : ∀ s ∈ J, ∀ t ∈ J, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw0 : 0 ≤ w) (hw : w < 2 * π) (hη : 0 ≤ η)
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) (hab : a < b)
    (hAw : ∀ p q, |(hH a ha).eigenvalues p - (hH a ha).eigenvalues q| ≤ w)
    (hBw : ∀ p q, |(hH b hb).eigenvalues p - (hH b hb).eigenvalues q| ≤ w)
    (hpoint : ∀ s ∈ J,
      ‖derivWithin (fun t ↦ frameOp (jumpSegment (H a) (H b) t) (H b - H a)) J s‖ ≤
        η * ‖H b - H a‖ ^ 2) :
    ‖frameOp (H b) (Hd b) - frameOp (H a) (Hd a)‖ ≤
      (frameBound w * h + η * L ^ 2) * (b - a) := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hsub : Icc a b ⊆ J := Icc_subset_Icc ha.1 hb.2
  have hc : ContinuousOn Hd J := continuousOn_of_norm_sub_le hlip
  have hmean := jump_increment_eq_integral hd hc ha hb hab.le
  let D : 𝕄 := (1 / (b - a)) • (H b - H a)
  have herrors : ‖Hd b - D‖ ≤ h * (b - a) / 2 ∧ ‖D - Hd a‖ ≤ h * (b - a) / 2 := by
    simpa only [D, hmean] using jump_average_endpoint_errors hab (hc.mono hsub)
      (fun s hs t ht ↦ hlip s (hsub hs) t (hsub ht))
  have hmiddle := affine_self_variation (hH a ha) (hH b hb) hw hAw hBw hpoint
  have hdiff : ‖H b - H a‖ ≤ L * (b - a) := by
    simpa only [abs_of_pos hlen] using norm_sub_le_of_derivWithin_le hd hbd a ha b hb
  have hL : 0 ≤ L := (norm_nonneg _).trans (hbd a ha)
  have hscaled : ‖frameOp (H b) D - frameOp (H a) D‖ ≤ η * L ^ 2 * (b - a) := by
    have heq : frameOp (H b) D - frameOp (H a) D =
        (1 / (b - a)) • (frameOp (H b) (H b - H a) - frameOp (H a) (H b - H a)) := by
      simp only [D, frameOp]
      rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower, smul_sub]
    rw [heq, norm_smul_of_nonneg (by positivity)]
    calc
      _ ≤ (1 / (b - a)) * (η * ‖H b - H a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmiddle (by positivity)
      _ ≤ (1 / (b - a)) * (η * (L * (b - a)) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdiff 2) hη)
          (by positivity)
      _ = _ := by field_simp
  have hout := affine_jump_outer_bounds (Da := Hd a) (Db := Hd b) (Ea := D) (Eb := D)
    (hH a ha) (hH b hb) hw0 hw hAw hBw
  calc
    _ ≤ frameBound w * (‖Hd b - D‖ + ‖D - Hd a‖) +
        ‖frameOp (H b) D - frameOp (H a) D‖ := hout
    _ ≤ frameBound w * (h * (b - a) / 2 + h * (b - a) / 2) +
        η * L ^ 2 * (b - a) := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add herrors.1 herrors.2) (frameBound_nonneg hw0)) hscaled
    _ = _ := by ring

set_option maxHeartbeats 800000 in
-- The mesh sum elaborates the full matrix-valued cell estimate.
/-- Summation of the affine-cell bounds over the sampling mesh. Multiplying
by `1/T` gives the paper's sum of actual correction jumps. -/
theorem affine_hamiltonian_sum_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : ∀ s ∈ J, (H s).IsHermitian)
    (hd : ∀ s ∈ J, HasDerivWithinAt H (Hd s) J s)
    {L h w η : ℝ} (hbd : ∀ s ∈ J, ‖Hd s‖ ≤ L)
    (hlip : ∀ s ∈ J, ∀ t ∈ J, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw0 : 0 ≤ w) (hw : w < 2 * π) (hη : 0 ≤ η)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hpoint : ∀ j < T, ∀ s ∈ J,
      ‖derivWithin (fun t ↦ frameOp
        (jumpSegment (H ((j : ℝ) / T)) (H (((j : ℝ) + 1) / T)) t)
        (H (((j : ℝ) + 1) / T) - H ((j : ℝ) / T))) J s‖ ≤
      η * ‖H (((j : ℝ) + 1) / T) - H ((j : ℝ) / T)‖ ^ 2) :
    (∑ j ∈ Finset.range T,
      ‖frameOp (H (((j : ℝ) + 1) / T)) (Hd (((j : ℝ) + 1) / T)) -
        frameOp (H ((j : ℝ) / T)) (Hd ((j : ℝ) / T))‖) ≤
      frameBound w * h + η * L ^ 2 := by
  have ht : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hcell (j : ℕ) (hj : j < T) :
      ‖frameOp (H (((j : ℝ) + 1) / T)) (Hd (((j : ℝ) + 1) / T)) -
        frameOp (H ((j : ℝ) / T)) (Hd ((j : ℝ) / T))‖ ≤
        (frameBound w * h + η * L ^ 2) / T := by
    have hb : ((j : ℝ) + 1) / T ∈ J := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using walkCubic_sample hj
    have hbw : ∀ p q, |(hH _ hb).eigenvalues p - (hH _ hb).eigenvalues q| ≤ w := by
      simpa only [Nat.cast_add, Nat.cast_one] using hwidth (j + 1) hj
    have hab : (j : ℝ) / T < ((j : ℝ) + 1) / T :=
      (div_lt_div_iff_of_pos_right ht).mpr (by linarith)
    have hlength : ((j : ℝ) + 1) / T - (j : ℝ) / T = 1 / T := by ring
    simpa only [hlength, mul_one_div] using
      affine_hamiltonian_cell_bound hH hd hbd hlip hw0 hw hη
        (walkCubic_sample hj.le) hb hab (hwidth j hj.le) hbw (hpoint j hj)
  calc
    _ ≤ ∑ j ∈ Finset.range T, (frameBound w * h + η * L ^ 2) / T :=
      Finset.sum_le_sum fun j hj ↦ hcell j (Finset.mem_range.mp hj)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

end UnitaryProducts.PaperProof
