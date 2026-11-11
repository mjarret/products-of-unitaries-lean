/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Corrector.PartialFractions

/-!
# The operator series $\mathcal N(\mathrm{ad}_h)$ and its bounds

## Declarations

- `frameBound`
- `frameBound_eq_closedForm`
- `frameBound_mono`
- `frameBound_nonneg`
- `frameLip`
- `frameLip_nonneg`
- `hasDerivAt_frameBound`
- `one_div_twelve_le_frameBound`
- `summable_frameBound_majorant`
- `summable_frameLip_majorant`
- `frameOp`
- `norm_frameOp_le`
- `norm_frameOp_sub_le`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real

noncomputable section

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The nonnegative Taylor series obtained from the cotangent partial fractions. -/
def frameBound (w : ℝ) : ℝ := ∑' n : ℕ, frameCoeff n * w ^ n

/-- The termwise derivative of the cotangent coefficient series. -/
def frameLip (w : ℝ) : ℝ := ∑' n : ℕ, frameCoeff n * n * w ^ (n - 1)

/-- The coefficient series converges throughout the disc of radius `2π`. -/
theorem summable_frameBound_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦ frameCoeff n * x ^ n) :=
  summable_frameCoeff_power ((abs_of_nonneg hx0).trans_lt hx)

/-- Derivative summability follows from the standard holomorphic series theorem,
using a slightly larger circle inside the convergence disc. -/
theorem summable_frameLip_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 2 * π) :
    Summable (fun n : ℕ ↦ frameCoeff n * n * r ^ (n - 1)) := by
  let R := (r + 2 * π) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : R < 2 * π := by dsimp [R]; linarith
  have hR0 : 0 ≤ R := hr0.trans hrR.le
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (fun z : ℂ ↦ (frameCoeff n : ℂ) * z ^ n)
      ((frameCoeff n : ℂ) * n * z ^ (n - 1)) z := by
    convert ((hasDerivAt_id z).pow n).const_mul (frameCoeff n : ℂ) using 1
    simp [mul_assoc]
  have hs := Complex.hasSum_deriv_of_summable_norm (summable_frameBound_majorant hR0 hR)
    (F := fun n z ↦ (frameCoeff n : ℂ) * z ^ n) (U := Metric.ball 0 R)
    (fun n z _ ↦ (hd n z).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n z hz ↦ ?_) (z := (r : ℂ)) ?_
  · have hs' := Complex.reCLM.summable hs.summable
    simpa only [(hd _ _).deriv, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, zero_mul, mul_zero,
      sub_zero, ← Complex.ofReal_pow] using hs'
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (frameCoeff_nonneg n), norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z)
      (mem_ball_zero_iff.mp hz).le n) (frameCoeff_nonneg n)
  · simpa only [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hrR

/-- Every term of the scalar majorant is nonnegative. -/
theorem frameBound_nonneg {w : ℝ} (hw0 : 0 ≤ w) : 0 ≤ frameBound w :=
  tsum_nonneg fun n ↦ mul_nonneg (frameCoeff_nonneg n) (pow_nonneg hw0 n)

/-- Every term of its derivative majorant is nonnegative. -/
theorem frameLip_nonneg {w : ℝ} (hw0 : 0 ≤ w) : 0 ≤ frameLip w :=
  tsum_nonneg fun n ↦ mul_nonneg (mul_nonneg (frameCoeff_nonneg n) (Nat.cast_nonneg n))
    (pow_nonneg hw0 (n - 1))

/-- The constant coefficient of the partial-fraction series is `1/12`. -/
theorem one_div_twelve_le_frameBound {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    1 / 12 ≤ frameBound w := by
  have h := (summable_frameBound_majorant hw0 hw).le_tsum 0
    (fun n _ ↦ mul_nonneg (frameCoeff_nonneg n) (pow_nonneg hw0 n))
  simpa only [frameCoeff_zero, pow_zero, mul_one, frameBound] using h

/-- The nonnegative coefficient series is increasing on `[0,2π)`. -/
theorem frameBound_mono {w v : ℝ} (hw0 : 0 ≤ w) (hwv : w ≤ v) (hv : v < 2 * π) :
    frameBound w ≤ frameBound v :=
  (summable_frameBound_majorant hw0 (hwv.trans_lt hv)).tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hwv n) (frameCoeff_nonneg n))
    (summable_frameBound_majorant (hw0.trans hwv) hv)

/-- Cotangent partial fractions identify the positive series with the paper's formula. -/
theorem frameBound_eq_closedForm {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameBound x = (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 :=
  frameCoeff_series_eq_cot hx0.ne' ((abs_of_pos hx0).trans_lt hx)

/-- Termwise differentiation of the partial-fraction coefficient series. -/
theorem hasDerivAt_frameBound {x : ℝ} (hx : |x| < 2 * π) :
    HasDerivAt frameBound (frameLip x) x := by
  let r : ℝ := (|x| + 2 * π) / 2
  have hxr : |x| < r := by dsimp [r]; linarith
  have hr2 : r < 2 * π := by dsimp [r]; linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hmem : ∀ y ∈ Set.Ioo (-r) r, |y| < r := fun y hy ↦ abs_lt.mpr ⟨hy.1, hy.2⟩
  have hframe := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ ↦ frameCoeff n * n * r ^ (n - 1))
    (g := fun (n : ℕ) (y : ℝ) ↦ frameCoeff n * y ^ n)
    (g' := fun (n : ℕ) (y : ℝ) ↦ frameCoeff n * n * y ^ (n - 1))
    (summable_frameLip_majorant hr0.le hr2) isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected
    (fun n y _ ↦ ?_) (fun n y hy ↦ ?_) (y₀ := 0) ⟨by linarith, hr0⟩ ?_ (abs_lt.mp hxr)
  · exact hframe
  · convert (hasDerivAt_pow n y).const_mul (frameCoeff n) using 1; ring
  · simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (frameCoeff_nonneg n),
      abs_pow, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg y) (hmem y hy).le (n - 1))
      (mul_nonneg (frameCoeff_nonneg n) (Nat.cast_nonneg n))
  · exact summable_frameBound_majorant le_rfl (by positivity)

/-- The cotangent coefficient series evaluated in a Banach algebra. -/
def positiveFrameSeries (a : A) : A := ∑' n : ℕ, (frameCoeff n : ℂ) • a ^ n

omit [CompleteSpace A] in
/-- Absolute convergence of the positive operator series. -/
theorem summable_norm_positiveFrameSeries (a : A) (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦ ‖(frameCoeff n : ℂ) • a ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ ?_) (summable_frameBound_majorant (norm_nonneg a) ha)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (frameCoeff_nonneg n)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le a n) (frameCoeff_nonneg n)

omit [CompleteSpace A] in
/-- The positive algebra series is bounded by its scalar majorant. -/
theorem norm_positiveFrameSeries_le {a : A} {w : ℝ} (ha : ‖a‖ ≤ w) (hw : w < 2 * π) :
    ‖positiveFrameSeries a‖ ≤ frameBound w := by
  have hs := summable_norm_positiveFrameSeries a (ha.trans_lt hw)
  apply (norm_tsum_le_tsum_norm hs).trans
  apply hs.tsum_le_tsum (fun n ↦ ?_)
    (summable_frameBound_majorant ((norm_nonneg a).trans ha) hw)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (frameCoeff_nonneg n)]
  exact mul_le_mul_of_nonneg_left ((norm_pow_le a n).trans
    (pow_le_pow_left₀ (norm_nonneg a) ha n)) (frameCoeff_nonneg n)

/-- The positive algebra series is Lipschitz on each smaller convergence ball. -/
theorem norm_positiveFrameSeries_sub_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r)
    (hr : r < 2 * π) :
    ‖positiveFrameSeries a - positiveFrameSeries b‖ ≤ frameLip r * ‖a - b‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg a).trans ha
  have hsa := (summable_norm_positiveFrameSeries a (ha.trans_lt hr)).of_norm
  have hsb := (summable_norm_positiveFrameSeries b (hb.trans_lt hr)).of_norm
  have hdiff : positiveFrameSeries a - positiveFrameSeries b =
      ∑' n : ℕ, (frameCoeff n : ℂ) • (a ^ n - b ^ n) := by
    rw [positiveFrameSeries, positiveFrameSeries, ← hsa.tsum_sub hsb]
    exact tsum_congr fun n ↦ (smul_sub _ _ _).symm
  have hmaj (n : ℕ) : ‖(frameCoeff n : ℂ) • (a ^ n - b ^ n)‖ ≤
      (frameCoeff n * n * r ^ (n - 1)) * ‖a - b‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (frameCoeff_nonneg n)]
    exact (mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le ha hb n)
      (frameCoeff_nonneg n)).trans_eq (by ring)
  rw [hdiff, frameLip, ← tsum_mul_right]
  exact tsum_of_norm_bounded ((summable_frameLip_majorant hr0 hr).mul_right _).hasSum hmaj

end UnitaryProducts.Corrector

namespace UnitaryProducts

open UnitaryProducts.Corrector Complex Set MeasureTheory

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The entrywise multiplier N, evaluated by its nonnegative commutator series. -/
noncomputable def frameOp (h D : 𝕄) : 𝕄 := positiveFrameSeries (adL h) D

/-- The multiplier is linear in its input. -/
theorem frameOp_sub (h D E : 𝕄) :
    frameOp h (D - E) = frameOp h D - frameOp h E :=
  map_sub (positiveFrameSeries (adL h)) D E

/-- The commutator series satisfies the scalar-majorant norm bound. -/
theorem norm_frameOp_le [NeZero d] {h D : 𝕄} {c w : ℝ} (hw : w < 2 * π)
    (hwidth : ‖h - (c : ℂ) • 1‖ ≤ w / 2) : ‖frameOp h D‖ ≤ frameBound w * ‖D‖ := by
  have hA : ‖adL h‖ ≤ w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [(norm_nonneg _).trans hwidth])
    intro E
    exact (norm_adL_apply_le h E (c : ℂ)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg E))
  exact ((positiveFrameSeries (adL h)).le_opNorm D).trans
    (mul_le_mul_of_nonneg_right (norm_positiveFrameSeries_le hA hw) (norm_nonneg D))

/-- The multiplier changes by the input difference plus the commutator-series variation. -/
theorem norm_frameOp_sub_le [NeZero d] {h h' D D' : 𝕄} {c c' w : ℝ}
    (hw : w < 2 * π) (hwidth : ‖h - (c : ℂ) • 1‖ ≤ w / 2)
    (hwidth' : ‖h' - (c' : ℂ) • 1‖ ≤ w / 2) :
    ‖frameOp h D - frameOp h' D'‖ ≤
      frameBound w * ‖D - D'‖ + 2 * frameLip w * ‖D'‖ * ‖h - h'‖ := by
  have haw : ‖adL h‖ ≤ w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [(norm_nonneg _).trans hwidth])
    intro E
    exact (norm_adL_apply_le h E (c : ℂ)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg E))
  have ha'w : ‖adL h'‖ ≤ w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [(norm_nonneg _).trans hwidth'])
    intro E
    exact (norm_adL_apply_le h' E (c' : ℂ)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg E))
  have key : frameOp h D - frameOp h' D' = positiveFrameSeries (adL h) (D - D') +
      (positiveFrameSeries (adL h) - positiveFrameSeries (adL h')) D' := by
    simp only [frameOp, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [key]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((positiveFrameSeries (adL h)).le_opNorm (D - D')).trans
      (mul_le_mul_of_nonneg_right (norm_positiveFrameSeries_le haw hw) (norm_nonneg _))
  · have hd : ‖adL h - adL h'‖ ≤ 2 * ‖h - h'‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro E
      have he : (adL h - adL h') E = adL (h - h') E := by
        simp only [ContinuousLinearMap.sub_apply, adL_apply, sub_mul, mul_sub]
        abel
      rw [he]
      simpa only [zero_smul, sub_zero] using norm_adL_apply_le (h - h') E 0
    have hL : ‖positiveFrameSeries (adL h) - positiveFrameSeries (adL h')‖ ≤
        frameLip w * (2 * ‖h - h'‖) :=
      (norm_positiveFrameSeries_sub_le (a := adL h) (b := adL h') haw ha'w hw).trans
        (mul_le_mul_of_nonneg_left hd
          (frameLip_nonneg (by linarith [(norm_nonneg _).trans hwidth])))
    rw [show 2 * frameLip w * ‖D'‖ * ‖h - h'‖ = frameLip w * (2 * ‖h - h'‖) * ‖D'‖ by ring]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

end UnitaryProducts
