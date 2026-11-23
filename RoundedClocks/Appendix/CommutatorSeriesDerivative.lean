/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.MatrixSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # The inner sum of equation (A.2)

For elements `a` and `b` of a ring, `powDeriv a b n` (in `Definitions.lean`) is
`∑_{j<n} a^{n-1-j} b a^j`, the derivative of `a ↦ aⁿ` in the direction `b`. With `a = [Ω,·]` and
`b = [Ω',·]` it is the sum over `k` in (A.2). This file proves that the sum telescopes when `b` is
a commutator `ab' - b'a`, that
`‖powDeriv a b n‖ ≤ n r^{n-1} ‖b‖` for `‖a‖ ≤ r`, and that `∑ n gₙ r^{n-1}` converges inside the
radius of convergence of `∑ gₙ xⁿ`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)

noncomputable section

namespace RoundedClocks

/-- `powDeriv` is additive in the direction. -/
theorem powDeriv_add {A : Type*} [Ring A] (a b c : A) (n : ℕ) :
    powDeriv a (b + c) n = powDeriv a b n + powDeriv a c n := by
  simp only [powDeriv, mul_add, add_mul, Finset.sum_add_distrib]

/-- On an inner derivation `[a,b]` the sum over `j` telescopes to `aⁿ b - b aⁿ`. -/
theorem powDeriv_commutator {A : Type*} [Ring A] (a b : A) (n : ℕ) :
    powDeriv a (a * b - b * a) n = a ^ n * b - b * a ^ n := by
  let f : ℕ → A := fun j ↦ a ^ (n - j) * b * a ^ j
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      a ^ (n - 1 - j) * (a * b - b * a) * a ^ j = f j - f (j + 1) := by
    have hjn := Finset.mem_range.mp hj
    dsimp only [f]
    rw [show n - j = (n - 1 - j) + 1 by omega, show n - (j + 1) = n - 1 - j by omega,
      pow_succ a (n - 1 - j), pow_succ' a j]
    noncomm_ring
  rw [powDeriv, Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  simp [f]

/-- `‖powDeriv a b n‖ ≤ n r^{n-1} ‖b‖` for `‖a‖ ≤ r`: each of the `n` terms is at most
`r^{n-1} ‖b‖`. -/
theorem norm_powDeriv_le {A : Type*} [NormedRing A] [NormOneClass A] {a b : A} {r : ℝ}
    (ha : ‖a‖ ≤ r) (n : ℕ) : ‖powDeriv a b n‖ ≤ n * r ^ (n - 1) * ‖b‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg a).trans ha
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤ r ^ (n - 1) * ‖b‖ := by
    have hjn := Finset.mem_range.mp hj
    calc
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤ ‖a ^ (n - 1 - j)‖ * ‖b‖ * ‖a ^ j‖ := norm_mul₃_le
      _ ≤ r ^ (n - 1 - j) * ‖b‖ * r ^ j := by
        gcongr <;> exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
      _ = r ^ (n - 1) * ‖b‖ := by
        rw [mul_right_comm, ← pow_add, show n - 1 - j + j = n - 1 by omega]
  refine (norm_sum_le_of_le _ hterm).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Inside the radius of convergence the derivative series converges: if every `gₙ ≥ 0` and
`∑ gₙ Rⁿ` converges, then `∑ n gₙ r^{n-1}` converges for `0 ≤ r < R`. -/
theorem summable_coeff_deriv {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {r R : ℝ} (hr0 : 0 ≤ r)
    (hrR : r < R) (hRs : Summable (fun n : ℕ ↦ g n * R ^ n)) :
    Summable (fun n : ℕ ↦ g n * n * r ^ (n - 1)) := by
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (fun z : ℂ ↦ (g n : ℂ) * z ^ n)
      ((g n : ℂ) * n * z ^ (n - 1)) z := by
    convert ((hasDerivAt_id z).pow n).const_mul (g n : ℂ) using 1
    simp [mul_assoc]
  have hs := Complex.hasSum_deriv_of_summable_norm hRs
    (F := fun n z ↦ (g n : ℂ) * z ^ n) (U := Metric.ball 0 R)
    (fun n z _ ↦ (hd n z).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n z hz ↦ ?_) (z := (r : ℂ)) ?_
  · have hs' := Complex.reCLM.summable hs.summable
    simpa only [(hd _ _).deriv, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, zero_mul, mul_zero,
      sub_zero, ← Complex.ofReal_pow] using hs'
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg n), norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z)
      (mem_ball_zero_iff.mp hz).le n) (hg n)
  · simpa only [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      using hrR

/-- The derivative coefficients `νₙ n r^{n-1}` are summable for `0 ≤ r < 2π`. -/
theorem summable_multiplierCoeff_deriv {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 2 * π) :
    Summable (fun n : ℕ ↦ multiplierCoeff n * n * r ^ (n - 1)) := by
  have hrR : r < (r + 2 * π) / 2 := by linarith
  exact summable_coeff_deriv multiplierCoeff_nonneg hr0 hrR
    (summable_multiplierCoeff_power (by rw [abs_of_nonneg (hr0.trans hrR.le)]; linarith))

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

omit [CompleteSpace A] in
/-- The termwise derivative series `∑ νₙ powDeriv a b n` converges absolutely. -/
theorem summable_norm_powDeriv {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (hr : r < 2 * π) :
    Summable (fun n : ℕ ↦ ‖(multiplierCoeff n : ℂ) • powDeriv a b n‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_multiplierCoeff_deriv ((norm_nonneg a).trans ha) hr).mul_right ‖b‖)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplierCoeff_nonneg n)]
  exact (mul_le_mul_of_nonneg_left (norm_powDeriv_le ha n)
    (multiplierCoeff_nonneg n)).trans_eq (by ring)

end BanachAlgebra

end RoundedClocks
