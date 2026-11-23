/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.ResolventBounds
public import RoundedClocks.Appendix.LogarithmQuadratures

/-! # Integral norm estimates

Lemma A.2 bounds the resolvent integral and its derivative by the scalar quadratures determined by
the spectral width.
-/

@[expose] public section
noncomputable section
open Real Complex Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace RoundedClocks.WalkLog
open WalkLogCalculus
attribute [local instance] matrixCStarAlgebra

/-- Chord invertibility makes the resolvent continuous on the unit interval. -/
theorem continuousOn_fixed_resolvent {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V - 1))) :
    ContinuousOn (walkLogResolvent V) (Icc (0 : ℝ) 1) := by
  intro u hu'
  change ContinuousWithinAt (fun t : ℝ ↦ Ring.inverse (1 + t • (V - 1))) _ u
  exact (differentiableAt_inverse (𝕜 := ℝ) (hu u hu')).continuousAt.comp_continuousWithinAt
    (f := fun t : ℝ ↦ 1 + t • (V - 1))
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt)

/-- Both matrix kernels are integrable by continuity and chord invertibility. -/
theorem fixed_kernels_integrable {d : ℕ} (V D E : Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V - 1))) :
    IntervalIntegrable (fun u ↦ walkLogResolvent V u * D * walkLogResolvent V u)
      volume 0 1 ∧
    IntervalIntegrable (fun u ↦ walkLogResolvent V u * E * walkLogResolvent V u -
      (2 * u) • (walkLogResolvent V u * D * walkLogResolvent V u * D *
        walkLogResolvent V u)) volume 0 1 := by
  have hR := continuousOn_fixed_resolvent V hu
  have hD := (hR.mul (continuousOn_const (c := D))).mul hR
  have hE := (hR.mul (continuousOn_const (c := E))).mul hR
  constructor
  · exact hD.intervalIntegrable_of_Icc (by norm_num)
  · exact (hE.sub ((continuous_const.mul continuous_id).continuousOn.smul
      ((hD.mul continuousOn_const).mul hR))).intervalIntegrable_of_Icc (by norm_num)

/-- Submultiplicativity gives the squared resolvent sandwich estimate. -/
theorem sandwich_norm_le {d : ℕ} (R D : Matrix (Fin d) (Fin d) ℂ) :
    ‖R * D * R‖ ≤ ‖R‖ ^ 2 * ‖D‖ := by
  calc
    ‖R * D * R‖ ≤ ‖R * D‖ * ‖R‖ := norm_mul_le _ _
    _ ≤ (‖R‖ * ‖D‖) * ‖R‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖R‖ ^ 2 * ‖D‖ := by ring

/-- Submultiplicativity gives the cubic resolvent sandwich estimate. -/
theorem double_sandwich_norm_le {d : ℕ} (R D : Matrix (Fin d) (Fin d) ℂ) :
    ‖R * D * R * D * R‖ ≤ ‖R‖ ^ 3 * ‖D‖ ^ 2 := by
  calc
    ‖R * D * R * D * R‖ ≤ ‖R * D * R * D‖ * ‖R‖ := norm_mul_le _ _
    _ ≤ (‖R * D * R‖ * ‖D‖) * ‖R‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖R‖ ^ 2 * ‖D‖) * ‖D‖) * ‖R‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sandwich_norm_le R D) (norm_nonneg _))
        (norm_nonneg _)
    _ = ‖R‖ ^ 3 * ‖D‖ ^ 2 := by ring

/-- Integrating the sharp bounds preserves the weighted cubic kernel and exact constants. -/
theorem walkLog_integral_norm_bounds {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {μ w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwin : HasRealSpectrumIn H (Icc (μ - w / 2) (μ + w / 2)))
    (D E : Matrix (Fin d) (Fin d) ℂ) :
    let V := Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H)
    ‖walkLogFirstIntegral V D‖ ≤ κ w * ‖D‖ ∧
    ‖walkLogSecondIntegral V D E‖ ≤
      κ w * ‖E‖ + ‖D‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  intro V
  let q := fun u ↦ chordRadius w u
  let f := fun u ↦ 1 / q u
  let g := fun u ↦ (2 * u) / Real.sqrt (q u) ^ 3
  have hq : Continuous q := by dsimp [q, chordRadius]; fun_prop
  have hf : Continuous f := continuous_const.div hq
    (fun u ↦ (chordRadius_pos hw0 hw u).ne')
  have hg : Continuous g := (continuous_const.mul continuous_id).div
    ((Real.continuous_sqrt.comp hq).pow 3)
    (fun u ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (chordRadius_pos hw0 hw u)).ne')
  have hR (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :=
    fixed_phase_resolvent_bound hH (μ := μ) hw0 hw hwin hu
  have hint := fixed_kernels_integrable V D E (fun u hu ↦ (hR u hu).1)
  have hfirst (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (A : Matrix (Fin d) (Fin d) ℂ) :
      ‖walkLogResolvent V u * A * walkLogResolvent V u‖ ≤ f u * ‖A‖ := by
    exact (sandwich_norm_le _ _).trans
      (mul_le_mul_of_nonneg_right (hR u hu).2.2 (norm_nonneg _))
  have hcube (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖walkLogResolvent V u * D * walkLogResolvent V u * D * walkLogResolvent V u‖ ≤
        (1 / Real.sqrt (q u) ^ 3) * ‖D‖ ^ 2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) (hR u hu).2.1 3
    rw [div_pow, one_pow] at hp
    exact (double_sandwich_norm_le _ _).trans
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _))
  let r := WalkLogQuadratures.radius w
  have hsub := WalkLogQuadratures.quadrature_substitution w
  change (∫ u in (0 : ℝ)..1, f u) =
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v) ∧
    (∫ u in (0 : ℝ)..1, g u) =
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, (1 + v) / Real.sqrt (r v) ^ 3) at hsub
  have hsquare : (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v) = κ w :=
    WalkLogQuadratures.square_quadrature hw0 hw
  have hodd : (∫ v in (-1 : ℝ)..1, (1 + v) / Real.sqrt (r v) ^ 3) =
      ∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3 :=
    WalkLogQuadratures.cube_weighted_integral hw0 hw
  have hcubeIntegral :
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) =
        1 / Real.cos (w / 4) ^ 2 :=
    WalkLogQuadratures.cube_quadrature hw0 hw
  constructor
  · calc
      ‖walkLogFirstIntegral V D‖ ≤ ∫ u in (0 : ℝ)..1, f u * ‖D‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · exact Filter.Eventually.of_forall fun u hu ↦ hfirst u ⟨hu.1.le, hu.2⟩ D
        · exact (hf.mul continuous_const).intervalIntegrable _ _
      _ = ‖D‖ / 2 * (∫ v in (-1 : ℝ)..1, 1 / r v) := by
        rw [intervalIntegral.integral_mul_const, hsub.1]
        ring
      _ = κ w * ‖D‖ := by
        calc
          _ = ((1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v)) * ‖D‖ := by ring
          _ = κ w * ‖D‖ := by rw [hsquare]
  · calc
      ‖walkLogSecondIntegral V D E‖ ≤
          ∫ u in (0 : ℝ)..1, (f u * ‖E‖ + g u * ‖D‖ ^ 2) := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · apply Filter.Eventually.of_forall
          intro u hu
          have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
          have h2u : 0 ≤ 2 * u := mul_nonneg (by norm_num) hu.1.le
          calc
            _ ≤ ‖walkLogResolvent V u * E * walkLogResolvent V u‖ +
                ‖(2 * u) • (walkLogResolvent V u * D * walkLogResolvent V u * D *
                  walkLogResolvent V u)‖ := norm_sub_le _ _
            _ ≤ f u * ‖E‖ + g u * ‖D‖ ^ 2 := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h2u]
              have hb := mul_le_mul_of_nonneg_left (hcube u hu') h2u
              dsimp [g]
              convert add_le_add (hfirst u hu' E) hb using 1
              all_goals ring
        · exact ((hf.mul continuous_const).add (hg.mul continuous_const)).intervalIntegrable _ _
      _ = ‖E‖ / 2 * (∫ v in (-1 : ℝ)..1, 1 / r v) +
          ‖D‖ ^ 2 / 2 *
            (∫ v in (-1 : ℝ)..1, (1 + v) / Real.sqrt (r v) ^ 3) := by
        have hsplit :
            (∫ u in (0 : ℝ)..1, (f u * ‖E‖ + g u * ‖D‖ ^ 2)) =
              (∫ u in (0 : ℝ)..1, f u * ‖E‖) +
              (∫ u in (0 : ℝ)..1, g u * ‖D‖ ^ 2) :=
          intervalIntegral.integral_add
            ((hf.mul continuous_const).intervalIntegrable 0 1)
            ((hg.mul continuous_const).intervalIntegrable 0 1)
        rw [hsplit, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_mul_const, hsub.1, hsub.2]
        ring
      _ = κ w * ‖E‖ +
          ‖D‖ ^ 2 / 2 * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) := by
        rw [hodd]
        calc
          _ = ((1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v)) * ‖E‖ +
              ‖D‖ ^ 2 / 2 * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) := by
            ring
          _ = _ := by rw [hsquare]
      _ = κ w * ‖E‖ + ‖D‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
        calc
          _ = κ w * ‖E‖ + ‖D‖ ^ 2 *
              ((1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3)) := by
            ring
          _ = _ := by rw [hcubeIntegral]; ring

end RoundedClocks.WalkLog
