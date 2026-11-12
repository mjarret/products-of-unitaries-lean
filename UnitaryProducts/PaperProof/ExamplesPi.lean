/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.PaperProof.WalkCoefficients

/-! # The width-pi specialization used in Theorem B -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
open Set Real
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Theorem B uses the exact width-pi specialization of (4.6),
with the rounded evolution identified by (2.5). -/
theorem products_pi [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ π)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      (1 / T : ℝ) * ((1 / (2 * π) - 1 / π ^ 2) * (‖Hd 0‖ + ‖Hd 1‖) +
        (1 / 24 + 1 / π ^ 2) * L +
        (5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64) * unitSupNorm Hd ^ 2) := by
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hw : π < 2 * π := by linarith [pi_pos]
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hbound := unit_steps_endpoint_bounds hT H Hd U V hH hd hlip hw hwidth hU hV
  rw [cellConstant_eq_frameBound pi_pos.le hw, paperFrameMult_eq_series pi_pos.le hw,
    paperFrameMult_deriv_eq_series pi_pos.le hw, frameBound_center_pi,
    frameBound_frameLip_pi.1, frameBound_frameLip_pi.2] at hbound
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simp only [heV, div_self ht.ne', one_smul, hhalf] at hbound
  exact hbound.trans_eq (by ring)

/-- The display after (4.6): both endpoint norms are at most the derivative
supremum, giving the three separate coefficients used in Theorem B. -/
theorem products_pi_supremum [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ π)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      (1 / T : ℝ) * ((2 * (1 / (2 * π) - 1 / π ^ 2)) * unitSupNorm Hd +
        (1 / 24 + 1 / π ^ 2) * L +
        (5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64) * unitSupNorm Hd ^ 2) := by
  have hc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  have hzero := norm_le_unitSupNorm hc (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hone := norm_le_unitSupNorm hc (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hc₀ : 0 ≤ 1 / (2 * π) - 1 / π ^ 2 := by
    rw [← frameBound_center_pi]
    exact UnitStepsProse.center_bound_nonneg pi_pos.le (by linarith [pi_pos])
  have hends := mul_le_mul_of_nonneg_left (add_le_add hzero hone) hc₀
  have hcoarse := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hends (le_refl ((1 / 24 + 1 / π ^ 2) * L)))
      (le_refl ((5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64) * unitSupNorm Hd ^ 2)))
    (by positivity : (0 : ℝ) ≤ 1 / T)
  exact (products_pi hT H Hd U hH hd hlip hwidth hU).trans (hcoarse.trans_eq (by ring))

/-- The three decimal coefficients in Theorem B are upper bounds for the exact
width-pi endpoint, Lipschitz, and quadratic coefficients of (4.6). -/
theorem products_pi_decimal_coefficients :
    2 * (1 / (2 * π) - 1 / π ^ 2) < (116 / 1000 : ℝ) ∧
    1 / 24 + 1 / π ^ 2 < (143 / 1000 : ℝ) ∧
    5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 < (61 / 1000 : ℝ) := by
  have hlo : (10000 / 31416 : ℝ) ≤ 1 / π := by
    apply (le_div_iff₀ pi_pos).mpr
    linarith [Real.pi_lt_d4]
  have hhi : 1 / π ≤ (10000 / 31415 : ℝ) := by
    apply (div_le_iff₀ pi_pos).mpr
    linarith [Real.pi_gt_d4]
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 2
  have hsqhi := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / π) hhi 2
  have hcubelo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000 / 31416) hlo 3
  refine ⟨?_, ?_, ?_⟩
  · rw [show 2 * (1 / (2 * π) - 1 / π ^ 2) = 1 / π - 2 * (1 / π) ^ 2 by ring]
    linarith
  · rw [show 1 / π ^ 2 = (1 / π) ^ 2 by ring]
    linarith
  · rw [show 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 =
        5 / 8 * (1 / π) - 1 / 4 * (1 / π) ^ 2 - 4 * (1 / π) ^ 3 + 1 / 64 by ring]
    linarith

end UnitaryProducts.PaperProof
