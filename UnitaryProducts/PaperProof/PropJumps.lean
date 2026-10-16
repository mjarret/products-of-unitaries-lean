/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.CanonicalCell
public import UnitaryProducts.PaperProof.AffineJumps
public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.PaperProof.WalkCutFormula
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.WalkScalarCut
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.Units
public import UnitaryProducts.Prose.WalkComparisonJRS
public import UnitaryProducts.Prose.SyncSteps

public import UnitaryProducts.PaperProof.ExTruncationBits
public import UnitaryProducts.PaperProof.ThmTransfer
public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.UniformConstants
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.PaperProof.ClosedCellCorrector

/-!
# Cell jumps for paths and unitary families

## Declarations

- `unitClockJump`
- `unitClockJump_norm_sum`
- `unified_jump_sum_bound`
-/

@[expose] public section
open Real Complex Set Filter MeasureTheory
open UnitaryProducts.Corrector UnitaryProducts.Paper UnitaryProducts.Prose
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

/-- Section 4's change of common end value at the j-th cell boundary. -/
def unitClockJump (H Hd : ℝ → 𝕄) (T j : ℕ) : 𝕄 :=
  (1 / T : ℝ) • (frameOp (H ((j : ℝ) / T)) (Hd ((j : ℝ) / T)) -
    frameOp (H (((j : ℝ) - 1) / T)) (Hd (((j : ℝ) - 1) / T)))

/-- Section 4's jump, expressed through the entrywise multiplier of Definition 4.1. -/
def paperClockJump (H Hd : ℝ → 𝕄) (T j : ℕ) : 𝕄 :=
  (1 / T : ℝ) • (paperFrameOp (H ((j : ℝ) / T)) (Hd ((j : ℝ) / T)) -
    paperFrameOp (H (((j : ℝ) - 1) / T)) (Hd (((j : ℝ) - 1) / T)))

/-- The finite jump sum agrees with its convergent-series calculation. -/
theorem paperClockJump_sum_eq {T : ℕ}
    (H Hd : ℝ → 𝕄) (hH : ∀ s ∈ K, (H s).IsHermitian)
    {w : ℝ} (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w) :
    (∑ j ∈ Finset.Icc 1 T, ‖paperClockJump H Hd T j‖) =
      ∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖ := by
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hj1, hjT⟩ := Finset.mem_Icc.mp hj
  have hjm : j - 1 ≤ T := (Nat.sub_le j 1).trans hjT
  have hsub : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj1, Nat.cast_one]
  unfold paperClockJump unitClockJump
  rw [paperFrameOp_eq_series (hH _ (walkCubic_sample hjT)) hw (hwidth j hjT)]
  rw [← hsub, paperFrameOp_eq_series (hH _ (walkCubic_sample hjm)) hw (hwidth (j - 1) hjm)]

/-- Reindex the sum of jump norms by the T adjacent sample pairs. -/
theorem unitClockJump_norm_sum (H Hd : ℝ → 𝕄) (T : ℕ) :
    (∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖) =
      (1 / T : ℝ) * ∑ j ∈ Finset.range T,
        ‖frameOp (H (((j : ℝ) + 1) / T)) (Hd (((j : ℝ) + 1) / T)) -
          frameOp (H ((j : ℝ) / T)) (Hd ((j : ℝ) / T))‖ := by
  rw [sum_Icc_one_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [unitClockJump, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    norm_smul_of_nonneg (by positivity : 0 ≤ (1 / T : ℝ))]

/-- Theorem 4.4(i): the three-term jump decomposition on each affine
cell, using its mean derivative at both ends and Lemma A.3 on the self-curve. -/
theorem hamiltonian_jump_sum_integral [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : ∀ s ∈ K, (H s).IsHermitian)
    (hd : ∀ s ∈ K, HasDerivWithinAt H (Hd s) K s)
    {h w : ℝ} (hlip : ∀ s ∈ K, ∀ t ∈ K, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w) :
    (∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖) ≤
      (1 / T : ℝ) * (frameBound w * h + (2 * frameLip w) * unitSupNorm Hd ^ 2) := by
  have hw0 : 0 ≤ w := by simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) 0
  have hbd : ∀ s ∈ K, ‖Hd s‖ ≤ unitSupNorm Hd :=
    fun _ hs ↦ norm_le_unitSupNorm (continuousOn_of_norm_sub_le hlip) hs
  rw [unitClockJump_norm_sum]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply affine_hamiltonian_sum_bound hT H Hd hH hd hbd hlip hw0 hw
    (mul_nonneg (by norm_num) (frameLip_nonneg hw0)) hwidth
  intro j hj s hs
  let A := H ((j : ℝ) / T)
  let B := H (((j : ℝ) + 1) / T)
  have ha := walkCubic_sample (N := T) hj.le
  have hb : ((j : ℝ) + 1) / T ∈ K := by
    simpa only [Nat.cast_succ] using walkCubic_sample hj
  have hA : A.IsHermitian := hH _ ha
  have hB : B.IsHermitian := hH _ hb
  have hAw : ∀ p q, |hA.eigenvalues p - hA.eigenvalues q| ≤ w := hwidth j hj.le
  have hBw : ∀ p q, |hB.eigenvalues p - hB.eigenvalues q| ≤ w := by
    simpa only [Nat.cast_add, Nat.cast_one] using hwidth (j + 1) hj
  have hcurve := canonical_cell_series_bounds hw0 hw
    (fun u _ ↦ isHermitian_jumpSegment hA hB u)
    (fun u hu ↦ width_jumpSegment hA hB hAw hBw hu)
    ((contDiff_jumpSegment A B).of_le (by simp)).contDiffOn
  have hpoint := (hcurve.2 s hs).1
  rw [jumpSegment_frame_self_derivWithin A B hs,
    jumpSegment_second_derivWithin A B hs,
    jumpSegment_derivWithin A B hs] at hpoint
  simpa only [norm_zero, mul_zero, zero_add] using hpoint

/-- Integrate Lemma A.3 on each mesh interval and then sum. The two
inequalities instantiate the common chain in Theorem 4.4(ii). -/
theorem unified_jump_sum_bound {T : ℕ} (hT : 0 < T)
    (H Hd W : ℝ → 𝕄) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hH : ∀ s ∈ K, (H s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ K), ∀ p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w)
    (hd : ∀ s ∈ K, HasDerivWithinAt H (Hd s) K s)
    (hcH : ContDiffOn ℝ 2 H K)
    (hcW : ContDiffOn ℝ 1 W K) (hlog : ∀ s ∈ K, evol (H s) 1 = W s) :
    let Hdd := derivWithin Hd K
    let Wd := derivWithin W K
    let g := fun s ↦ frameBound w * ‖Hdd s‖ + (2 * frameLip w) * ‖Wd s‖ * ‖Hd s‖ +
      (frameBound w - frameBound 0) * ‖Hd s‖ ^ 2
    (∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖) ≤
      (1 / T : ℝ) * ∫ s in (0 : ℝ)..1, g s ∧
    (1 / T : ℝ) * (∫ s in (0 : ℝ)..1, g s) ≤
      (1 / T : ℝ) * (frameBound w * unitSupNorm Hdd +
        (2 * frameLip w) * unitSupNorm Wd * unitSupNorm Hd +
        (frameBound w - frameBound 0) * unitSupNorm Hd ^ 2) := by
  intro Hdd Wd g
  have hder : EqOn Hd (derivWithin H K) K := fun s hs ↦
    ((hd s hs).derivWithin (uniqueDiffOn_Icc_zero_one s hs)).symm
  have hcHd : ContDiffOn ℝ 1 Hd K :=
    (hcH.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)).congr hder
  have hself := canonical_cell_series_bounds hw0 hw hH hwidth hcH
  have heqF : EqOn (fun s ↦ frameOp (H s) (Hd s))
      (fun s ↦ frameOp (H s) (derivWithin H K s)) K :=
    fun s hs ↦ congrArg (frameOp (H s)) (hder hs)
  have hcurve : ContDiffOn ℝ 1 (fun s ↦ frameOp (H s) (Hd s)) K :=
    hself.1.congr heqF
  have hX : ∀ s ∈ K, derivWithin (fun t ↦ evol (H t) 1) K s = Wd s :=
    fun s hs ↦ derivWithin_congr hlog (hlog s hs)
  have hbound : ∀ s ∈ K, ‖derivWithin (fun t ↦ frameOp (H t) (Hd t)) K s‖ ≤ g s := by
    intro s hs
    simpa only [← derivWithin_congr heqF (heqF hs),
      ← derivWithin_congr hder (hder hs), ← hder hs, hX s hs] using (hself.2 s hs).2
  have hHdd : ContinuousOn Hdd K :=
    hcHd.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWd : ContinuousOn Wd K :=
    hcW.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hgc : ContinuousOn g K :=
    (continuousOn_const.mul hHdd.norm).add
      ((continuousOn_const.mul hWd.norm).mul hcHd.continuousOn.norm) |>.add
        (continuousOn_const.mul (hcHd.continuousOn.norm.pow 2))
  have htail : 0 ≤ frameBound w - frameBound 0 :=
    sub_nonneg.mpr (frameBound_mono (by norm_num) hw0 hw)
  have hi : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable_of_Icc zero_le_one
  constructor
  · rw [unitClockJump_norm_sum]
    exact mul_le_mul_of_nonneg_left
      (unified_mesh_integral_of_derivWithin hcurve hbound hi hT) (by positivity)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hmajor : ∀ s ∈ K, g s ≤ frameBound w * unitSupNorm Hdd +
        (2 * frameLip w) * unitSupNorm Wd * unitSupNorm Hd +
        (frameBound w - frameBound 0) * unitSupNorm Hd ^ 2 := by
      intro s hs
      have hWnonneg : 0 ≤ unitSupNorm Wd :=
        (norm_nonneg (Wd s)).trans (norm_le_unitSupNorm hWd hs)
      have hlinear := mul_le_mul_of_nonneg_left (norm_le_unitSupNorm hHdd hs)
        (frameBound_nonneg hw0)
      have hη : 0 ≤ (2 : ℝ) * frameLip w :=
        mul_nonneg (by norm_num) (frameLip_nonneg hw0)
      have hcross := mul_le_mul (mul_le_mul_of_nonneg_left (norm_le_unitSupNorm hWd hs) hη)
        (norm_le_unitSupNorm hcHd.continuousOn hs) (norm_nonneg _)
        (mul_nonneg hη hWnonneg)
      have hsquare := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_unitSupNorm hcHd.continuousOn hs) 2) htail
      exact add_le_add (add_le_add hlinear hcross) hsquare
    simpa using intervalIntegral.integral_mono_on (μ := volume) zero_le_one hi
      intervalIntegrable_const hmajor

/-- The two operator-series bounds on the same sum of
corrector jumps. The common FTC computation is instantiated on affine sample
interpolants in (i), and on the C² Hamiltonian and its derivative in (ii).
The second derivative and exponential derivative use one-sided endpoint values. -/
theorem jump_series_bounds [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : ∀ s ∈ K, (H s).IsHermitian)
    (hd : ∀ s ∈ K, HasDerivWithinAt H (Hd s) K s)
    {h w : ℝ} (hlip : ∀ s ∈ K, ∀ t ∈ K, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w) :
    ((∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖) ≤
      (1 / T : ℝ) * (frameBound w * h + (2 * frameLip w) * unitSupNorm Hd ^ 2)) ∧
    (ContDiffOn ℝ 2 H K →
      (∀ s (hs : s ∈ K) p q,
        |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w) →
      let W := fun s ↦ evol (H s) 1
      (∑ j ∈ Finset.Icc 1 T, ‖unitClockJump H Hd T j‖) ≤
        (1 / T : ℝ) * (frameBound w * unitSupNorm (derivWithin Hd K) +
          (2 * frameLip w) * unitSupNorm (derivWithin W K) * unitSupNorm Hd +
          (frameBound w - frameBound 0) * unitSupNorm Hd ^ 2)) := by
  refine ⟨hamiltonian_jump_sum_integral hT H Hd hH hd hlip hw hwidth, ?_⟩
  intro hcH hall
  have hw0 : 0 ≤ w := by
    simpa only [sub_self, abs_zero] using hall 0 (by norm_num) 0 0
  have hcW : ContDiffOn ℝ 1 (fun s ↦ evol (H s) 1) K := by
    intro s hs
    exact ((contDiffAt_evol_one (H s)).restrict_scalars ℝ).comp_contDiffWithinAt s
      ((hcH.of_le (by norm_num)) s hs)
  have hchain := unified_jump_sum_bound hT H Hd (fun s ↦ evol (H s) 1) hw0 hw
    hH hall hd hcH hcW (fun _ _ ↦ rfl)
  exact hchain.1.trans hchain.2

/-- **Theorem 4.4** (`thm:jumps`): both jump estimates with Definition 4.1's
entrywise multiplier and the closed scalar function and its derivative. -/
theorem thm_jumps [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : ∀ s ∈ K, (H s).IsHermitian)
    (hd : ∀ s ∈ K, HasDerivWithinAt H (Hd s) K s)
    {h w : ℝ} (hlip : ∀ s ∈ K, ∀ t ∈ K, ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w) :
    ((∑ j ∈ Finset.Icc 1 T, ‖paperClockJump H Hd T j‖) ≤
      (1 / T : ℝ) * (frameMult w * h + (2 * deriv frameMult w) * unitSupNorm Hd ^ 2)) ∧
    (ContDiffOn ℝ 2 H K →
      (∀ s (hs : s ∈ K) p q,
        |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w) →
      let W := fun s ↦ evol (H s) 1
      (∑ j ∈ Finset.Icc 1 T, ‖paperClockJump H Hd T j‖) ≤
        (1 / T : ℝ) * (frameMult w * unitSupNorm (derivWithin Hd K) +
          (2 * deriv frameMult w) * unitSupNorm (derivWithin W K) * unitSupNorm Hd +
          (frameMult w - frameMult 0) * unitSupNorm Hd ^ 2)) := by
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) 0
  rw [paperClockJump_sum_eq H Hd hH hw hwidth,
    paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw,
    paperFrameMult_eq_series (le_refl 0) (by positivity)]
  exact jump_series_bounds hT H Hd hH hd hlip hw hwidth

end UnitaryProducts.PaperProof
