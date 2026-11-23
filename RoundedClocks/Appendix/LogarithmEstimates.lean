/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.ResolventBounds
public import RoundedClocks.Appendix.LogarithmQuadratures

/-! # Lemma A.2: the norm display

By (A.3) at `s₀` and `‖S_u‖² ≤ 1/r(v)`, with `u = (1+v)/2`,
`‖H'‖ ≤ (‖W'‖/2)∫_{-1}^{1} dv/r(v) = κ ‖W'‖`, and
`‖H''‖ ≤ (‖W''‖/2)∫_{-1}^{1} dv/r(v) + (‖W'‖²/2)∫_{-1}^{1} (1+v) r(v)^{-3/2} dv`, which is
`κ ‖W''‖ + ‖W'‖²/cos²(w/4)`.
-/

@[expose] public section
noncomputable section
open Real Complex Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace RoundedClocks.WalkLog
attribute [local instance] matrixCStarAlgebra

/-- `u ↦ S_u` is continuous for `0 ≤ u ≤ 1` when every `1 + u(V - 1)` is invertible. -/
theorem continuousOn_fixed_resolvent {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (hu : ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V - 1))) :
    ContinuousOn (walkLogResolvent V) (Icc (0 : ℝ) 1) := by
  intro u hu'
  change ContinuousWithinAt (fun t : ℝ ↦ Ring.inverse (1 + t • (V - 1))) _ u
  exact (differentiableAt_inverse (𝕜 := ℝ) (hu u hu')).continuousAt.comp_continuousWithinAt
    (f := fun t : ℝ ↦ 1 + t • (V - 1))
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt)

/-- The integrands `S_u D S_u` and `S_u E S_u - 2u S_u D S_u D S_u` of (A.3) are integrable for
`0 ≤ u ≤ 1`. -/
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

/-- `‖R D R‖ ≤ ‖R‖² ‖D‖`. -/
theorem sandwich_norm_le {d : ℕ} (R D : Matrix (Fin d) (Fin d) ℂ) :
    ‖R * D * R‖ ≤ ‖R‖ ^ 2 * ‖D‖ :=
  norm_mul₃_le.trans_eq (by ring)

/-- `‖R D R D R‖ ≤ ‖R‖³ ‖D‖²`. -/
theorem double_sandwich_norm_le {d : ℕ} (R D : Matrix (Fin d) (Fin d) ℂ) :
    ‖R * D * R * D * R‖ ≤ ‖R‖ ^ 3 * ‖D‖ ^ 2 := by
  calc
    ‖R * D * R * D * R‖ ≤ ‖R * D * R‖ * ‖D‖ * ‖R‖ := norm_mul₃_le
    _ ≤ (‖R‖ * ‖D‖ * ‖R‖) * ‖D‖ * ‖R‖ := by gcongr; exact norm_mul₃_le
    _ = _ := by ring

/-- The norm display in the proof of Lemma A.2, for `V = e^{iμ} e^{-iH}` with the spectrum of `H`
within `w/2` of `μ`: `‖∫₀¹ S_u D S_u du‖ ≤ κ ‖D‖` and
`‖∫₀¹ (S_u E S_u - 2u S_u D S_u D S_u) du‖ ≤ κ ‖E‖ + ‖D‖²/cos²(w/4)`. The paper has `D = W'` and
`E = W''`. -/
theorem walkLog_integral_norm_bounds {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {μ w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwin : HasRealSpectrumIn H (Icc (μ - w / 2) (μ + w / 2)))
    (D E : Matrix (Fin d) (Fin d) ℂ) :
    let V := Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H)
    ‖walkLogFirstIntegral V D‖ ≤ κ w * ‖D‖ ∧
    ‖walkLogSecondIntegral V D E‖ ≤
      κ w * ‖E‖ + ‖D‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  intro V
  let q := fun u ↦ radius w (2 * u - 1)
  let f := fun u ↦ 1 / q u
  let g := fun u ↦ (2 * u) / Real.sqrt (q u) ^ 3
  have hq : Continuous q := by dsimp [q, radius]; fun_prop
  have hf : Continuous f := continuous_const.div hq
    (fun u ↦ (radius_pos hw0 hw (2 * u - 1)).ne')
  have hg : Continuous g := (continuous_const.mul continuous_id).div
    ((Real.continuous_sqrt.comp hq).pow 3)
    (fun u ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (radius_pos hw0 hw (2 * u - 1))).ne')
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
  -- The substitution `u = (1+v)/2`, with `f u = 1/r(2u-1)` and `g u = 2u r(2u-1)^{-3/2}`.
  let r := radius w
  have hsub := quadrature_substitution w
  change (∫ u in (0 : ℝ)..1, f u) =
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v) ∧
    (∫ u in (0 : ℝ)..1, g u) =
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, (1 + v) / Real.sqrt (r v) ^ 3) at hsub
  have hsquare : (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v) = κ w :=
    square_quadrature hw0 hw
  have hodd : (∫ v in (-1 : ℝ)..1, (1 + v) / Real.sqrt (r v) ^ 3) =
      ∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3 :=
    cube_weighted_integral hw0 hw
  have hcubeIntegral :
      (1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) =
        1 / Real.cos (w / 4) ^ 2 :=
    cube_quadrature hw0 hw
  constructor
  -- Lines 1 and 2 of the norm display.
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
  -- Lines 3, 4, and 5 of the norm display.
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
      -- The substitution `u = (1+v)/2`.
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
      -- Line 4: `(1/2)∫ dv/r(v) = κ`, and the odd part `v r(v)^{-3/2}` integrates to zero.
      _ = κ w * ‖E‖ +
          ‖D‖ ^ 2 / 2 * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) := by
        rw [hodd]
        calc
          _ = ((1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / r v)) * ‖E‖ +
              ‖D‖ ^ 2 / 2 * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3) := by
            ring
          _ = _ := by rw [hsquare]
      -- Line 5: `(1/2)∫ r(v)^{-3/2} dv = 1/cos²(w/4)`.
      _ = κ w * ‖E‖ + ‖D‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
        calc
          _ = κ w * ‖E‖ + ‖D‖ ^ 2 *
              ((1 / 2 : ℝ) * (∫ v in (-1 : ℝ)..1, 1 / Real.sqrt (r v) ^ 3)) := by
            ring
          _ = _ := by rw [hcubeIntegral]; ring

end RoundedClocks.WalkLog
