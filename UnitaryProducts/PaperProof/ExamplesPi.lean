/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.PaperProof.WalkCoefficients

/-! # The width-pi specialization used in Theorem A -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
open Set Real
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Theorem A uses the exact width-pi specialization of (4.6),
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
      hamiltonianEnergy π L H / T := by
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hw : π < 2 * π := by linarith [pi_pos]
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hbound := thm_jumps hT H Hd U V hH hd hlip hw hwidth hU hV
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simp only [heV, div_self ht.ne', one_smul, hhalf] at hbound
  exact hbound

/-- The three decimal coefficients in Theorem A are upper bounds for the exact
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

/-- The width-pi display in Appendix B: `𝓔_π(H)` is bounded by the three decimal
coefficients of Theorem A. Bound the endpoint norms, then each coefficient. -/
theorem hamiltonianEnergy_pi_bound (H Hd : ℝ → 𝕄)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) :
    hamiltonianEnergy π L H ≤ (116 / 1000 : ℝ) * unitSupNorm Hd +
      (143 / 1000 : ℝ) * L + (61 / 1000 : ℝ) * unitSupNorm Hd ^ 2 := by
  have hL : 0 ≤ L := by
    have h := hlip 0 (by norm_num) 1 (by norm_num)
    simp only [sub_zero, abs_one, mul_one] at h
    exact (norm_nonneg _).trans h
  have hw : π < 2 * π := by linarith [pi_pos]
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt π L H Hd hd,
    cellConstant_eq_frameBound pi_pos.le hw, paperFrameMult_eq_series pi_pos.le hw,
    paperFrameMult_deriv_eq_series pi_pos.le hw, frameBound_center_pi,
    frameBound_frameLip_pi.1, frameBound_frameLip_pi.2]
  have hc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  have hzero := norm_le_unitSupNorm hc (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hone := norm_le_unitSupNorm hc (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hD : 0 ≤ unitSupNorm Hd := (norm_nonneg _).trans hzero
  have hc₀ : 0 ≤ 1 / (2 * π) - 1 / π ^ 2 := by
    rw [← frameBound_center_pi]
    exact UnitStepsProse.center_bound_nonneg pi_pos.le hw
  obtain ⟨hc0, hcL, hcb⟩ := products_pi_decimal_coefficients
  have hends :
      (1 / (2 * π) - 1 / π ^ 2) * (‖Hd 0‖ + ‖Hd 1‖) ≤
        (116 / 1000 : ℝ) * unitSupNorm Hd := by
    calc
      _ ≤ (1 / (2 * π) - 1 / π ^ 2) * (unitSupNorm Hd + unitSupNorm Hd) :=
        mul_le_mul_of_nonneg_left (add_le_add hzero hone) hc₀
      _ = (2 * (1 / (2 * π) - 1 / π ^ 2)) * unitSupNorm Hd := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc0.le hD
  have hcoeff := add_le_add (add_le_add hends (mul_le_mul_of_nonneg_right hcL.le hL))
    (mul_le_mul_of_nonneg_right hcb.le (sq_nonneg (unitSupNorm Hd)))
  convert hcoeff using 1
  ring

/-- **Fact B.1** (`fact:pi`): the three exact width-pi values and the
Hamiltonian energy bound with the stated decimal coefficients. -/
theorem hamiltonianEnergy_pi_le (H Hd : ℝ → 𝕄)  -- Easier-to-read statement (v1.1.0): https://github.com/mjarret/products-of-unitaries-lean/blob/v1.1.0/UnitaryProducts/PaperProof/ExamplesPi.lean#L112
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) :
    cellConstant π = 1 / (2 * π) - 1 / π ^ 2 ∧
    frameMult π = 1 / π ^ 2 ∧
    deriv frameMult π = 1 / (4 * π) - 2 / π ^ 3 ∧
    hamiltonianEnergy π L H ≤ (116 / 1000 : ℝ) * unitSupNorm Hd +
      (143 / 1000 : ℝ) * L + (61 / 1000 : ℝ) * unitSupNorm Hd ^ 2 := by
  have hw : π < 2 * π := by linarith [pi_pos]
  refine ⟨?_, ?_, ?_, hamiltonianEnergy_pi_bound H Hd hd hlip⟩
  · rw [cellConstant_eq_frameBound pi_pos.le hw, frameBound_center_pi]
  · rw [paperFrameMult_eq_series pi_pos.le hw, frameBound_frameLip_pi.1]
  · rw [paperFrameMult_deriv_eq_series pi_pos.le hw]
    have hvalue := congrArg (fun x : ℝ ↦ x / 2) frameBound_frameLip_pi.2
    convert hvalue using 1 <;> ring

end UnitaryProducts.PaperProof
