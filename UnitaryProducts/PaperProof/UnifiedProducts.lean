/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.PaperProof.WalkCoefficients

/-! # The walk comparison from the unified jump estimate -/
@[expose] public section
noncomputable section
open Complex Real Set Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

/-- Theorem 4.6: apply the clock theorem and the direct logarithm jump
bound first, then substitute the logarithm's first and second derivative bounds. -/
theorem unified_products_walk [NeZero d] {T : ℕ} (hT : 0 < T)
    (a : ℝ → ℝ) {w : ℝ} (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a K) (hunit : (walk W 1).1)
    (harc : ∀ s ∈ K, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W K) (H : ℝ → 𝕄)
    (hH : ∀ s ∈ K, (H s).IsHermitian)
    (hlog : ∀ s ∈ K, evol (H s) 1 = W s)
    (hwindow : ∀ s (hs : s ∈ K), ∀ i, (hH s hs).eigenvalues i ∈ Icc (a s) (a s + w))
    (U : ℝ → 𝕄) (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Wd := derivWithin W K
    let Wdd := derivWithin Wd K
    let c₀ := frameBound w - frameBound (w / 2) / 2
    ‖evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      (1 / T : ℝ) * (c₀ * walkLogSlope w * (‖Wd 0‖ + ‖Wd 1‖) +
        (1 / 24 + frameBound w) * walkLogSlope w * unitSupNorm Wdd +
          walk_square w * unitSupNorm Wd ^ 2) := by
  classical
  have hw0 : 0 ≤ w := by
    have hi := hwindow 0 (by norm_num) 0
    linarith [hi.1, hi.2]
  obtain ⟨H₀, hH₀, he₀, hunique, hc₀, hb₀⟩ := lem_walk_log a w hw0 hw W ha hunit harc hc
  have heq : EqOn H H₀ K :=
    fun s hs ↦ hunique s hs (H s) (hH s hs) (hwindow s hs) (hlog s hs)
  have hcH : ContDiffOn ℝ 2 H K := hc₀.congr heq
  have hfirstEq : EqOn (derivWithin H K) (derivWithin H₀ K) K :=
    fun s hs ↦ derivWithin_congr heq (heq hs)
  have hsecondEq : EqOn (derivWithin (derivWithin H K) K)
      (derivWithin (derivWithin H₀ K) K) K :=
    fun s hs ↦ derivWithin_congr hfirstEq (hfirstEq hs)
  have hS := walkLogSlope_nonneg hw0 hw
  have hN := frameBound_nonneg hw0
  have hη : 0 ≤ (2 : ℝ) * frameLip w :=
    mul_nonneg (by norm_num) (frameLip_nonneg hw0)
  have htail : 0 ≤ frameBound w - frameBound 0 :=
    sub_nonneg.mpr (frameBound_mono (by norm_num) hw0 hw)
  have hc0 := (walk_c0_bounds hw0 hw).1
  have hc1 : 0 ≤ (frameBound w - frameBound (w / 2) / 2) / 4 + 1 / 64 := by linarith
  let Hd := derivWithin H K
  let Hdd := derivWithin Hd K
  let Wd := derivWithin W K
  let Wdd := derivWithin Wd K
  have hHd : ContDiffOn ℝ 1 Hd K := hcH.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hHdd : ContinuousOn Hdd K :=
    hHd.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWd : ContDiffOn ℝ 1 Wd K := hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWdd : ContinuousOn Wdd K :=
    hWd.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  let L := walkLogSlope w * unitSupNorm Wd
  let M := walkLogSlope w * unitSupNorm Wdd + unitSupNorm Wd ^ 2 / Real.cos (w / 4) ^ 2
  have hlogbd (s : ℝ) (hs : s ∈ K) :
      ‖Hd s‖ ≤ walkLogSlope w * ‖Wd s‖ ∧
      ‖Hdd s‖ ≤ walkLogSlope w * ‖Wdd s‖ + ‖Wd s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
    have hb := hb₀ s hs
    rw [← hfirstEq hs, ← hsecondEq hs] at hb
    simpa only [walkLogSlope_closed hw0 hw] using hb
  have hfirst (s : ℝ) (hs : s ∈ K) : ‖Hd s‖ ≤ L :=
    (hlogbd s hs).1.trans
      (mul_le_mul_of_nonneg_left (norm_le_unitSupNorm hWd.continuousOn hs) hS)
  have hsecond (s : ℝ) (hs : s ∈ K) : ‖Hdd s‖ ≤ M :=
    (hlogbd s hs).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (norm_le_unitSupNorm hWdd hs) hS)
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_unitSupNorm hWd.continuousOn hs) 2)
        (sq_nonneg _)))
  have hsup : unitSupNorm Hd ≤ L :=
    csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr hfirst)
  have hsupSecond : unitSupNorm Hdd ≤ M :=
    csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr hsecond)
  have hsup0 : 0 ≤ unitSupNorm Hd :=
    (norm_nonneg (Hd 0)).trans (norm_le_unitSupNorm hHd.continuousOn (by norm_num))
  have hWsup0 : 0 ≤ unitSupNorm Wd :=
    (norm_nonneg (Wd 0)).trans (norm_le_unitSupNorm hWd.continuousOn (by norm_num))
  have hend : ‖Hd 0‖ + ‖Hd 1‖ ≤ walkLogSlope w * (‖Wd 0‖ + ‖Wd 1‖) :=
    (add_le_add (hlogbd 0 (by norm_num)).1
      (hlogbd 1 (by norm_num)).1).trans_eq (by ring)
  have hderH : ∀ s ∈ K, HasDerivWithinAt H (Hd s) K s :=
    fun s hs ↦ (hcH.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hlip := norm_sub_le_of_derivWithin_le
    (fun s hs ↦ (hHd.differentiableOn (by norm_num) s hs).hasDerivWithinAt)
    (fun s hs ↦ norm_le_unitSupNorm hHdd hs)
  have hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w := by
    intro j hj p q
    have hp := hwindow _ (walkCubic_sample hj) p
    have hq := hwindow _ (walkCubic_sample hj) q
    simpa only [add_sub_cancel_left] using abs_sub_le_of_le_of_le hp.1 hp.2 hq.1 hq.2
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hclock := thm_clocks hT H Hd U V hH hderH hlip hw hwidth hU hV
  dsimp only at hclock
  rw [cellConstant_eq_frameBound hw0 hw, paperClockJump_sum_eq H Hd hH hw hwidth] at hclock
  have hgap : ∀ s (hs : s ∈ K) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w := by
    intro s hs p q
    have hp := hwindow s hs p
    have hq := hwindow s hs q
    simpa only [add_sub_cancel_left] using abs_sub_le_of_le_of_le hp.1 hp.2 hq.1 hq.2
  have hchain := unified_jump_sum_bound hT H Hd W hw0 hw hH hgap hderH hcH
    (hc.of_le (by norm_num)) hlog
  have hjump := hchain.1.trans hchain.2
  have hcombined : ‖V T - U T‖ ≤ (1 / T : ℝ) *
      ((frameBound w - frameBound (w / 2) / 2) * (‖Hd 0‖ + ‖Hd 1‖) +
        (1 / 24 + frameBound w) * unitSupNorm Hdd +
        (((frameBound w - frameBound (w / 2) / 2) / 4 + 1 / 64) +
          (frameBound w - frameBound 0)) * unitSupNorm Hd ^ 2 +
        (2 * frameLip w) * unitSupNorm Wd * unitSupNorm Hd) :=
    hclock.trans ((add_le_add (le_refl ((1 / T : ℝ) *
      ((frameBound w - frameBound (w / 2) / 2) * (‖Hd 0‖ + ‖Hd 1‖) +
        unitSupNorm Hdd / 24 +
        ((frameBound w - frameBound (w / 2) / 2) / 4 + 1 / 64) *
          unitSupNorm Hd ^ 2))) hjump).trans_eq (by dsimp only [Hdd, Wd, frameLip]; ring))
  have hbound := hcombined.trans (mul_le_mul_of_nonneg_left
    (add_le_add
      (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hend hc0)
          (mul_le_mul_of_nonneg_left hsupSecond (by positivity)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsup0 hsup 2) (add_nonneg hc1 htail)))
      (mul_le_mul_of_nonneg_left hsup (mul_nonneg hη hWsup0)))
    (by positivity : 0 ≤ (1 / T : ℝ)))
  have hprod : (walk W T).2 = (unitProduct H T).1 :=
    stepProduct_eq_pieceProduct (fun j hj ↦ hlog _ (walkCubic_sample hj.le)) T le_rfl
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simp only [heV, div_self ht.ne', one_smul, hhalf, ← hprod] at hbound
  apply hbound.trans_eq
  have hcollect := walk_collect w (‖Wd 0‖ + ‖Wd 1‖) (unitSupNorm Wd) (unitSupNorm Wdd)
  convert congrArg (fun z : ℝ ↦ (1 / T : ℝ) * z) hcollect using 1
  dsimp [L, M, uniform_c1, uniform_c0, walkUniformSecond]
  ring


end UnitaryProducts.PaperProof
