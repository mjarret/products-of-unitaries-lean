/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.SeparatedFrameKernel

/-!
# Scalar initial-value solutions for the periodic corrector

## Declarations

- `corrector_entry_endpoint`
- `corrector_entry_solutions`
- `corrector_entry_solutions_zero`
-/

@[expose] public section

open Complex Real Filter Set MeasureTheory
open scoped Topology

noncomputable section
namespace UnitaryProducts.Paper

/-- The real embedding `ℝ → ℂ` has derivative `1`. -/
theorem hasDerivAt_ofReal (τ : ℝ) : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 τ := by
  simpa using (hasDerivAt_id' τ).ofReal_comp

/-- The exponential factors in the endpoint calculation of the proof of Lemma A.1. -/
theorem corrector_entry_exp_cot {x : ℝ} (hs : Real.sin (x / 2) ≠ 0) :
    Complex.exp (-(I * (x : ℂ) / 2)) =
      (Real.sin (x / 2) : ℂ) * ((Real.cot (x / 2) : ℂ) - I) ∧
    Complex.exp (I * (x : ℂ) / 2) =
      (Real.sin (x / 2) : ℂ) * ((Real.cot (x / 2) : ℂ) + I) := by
  have hsC : Complex.sin (x / 2) ≠ 0 := by exact_mod_cast hs
  rw [show -(I * (x : ℂ) / 2) = -((x : ℂ) / 2) * I by ring,
    show I * (x : ℂ) / 2 = ((x : ℂ) / 2) * I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Real.cot_eq_cos_div_sin]
  push_cast
  constructor
  · field_simp [hsC]
    ring
  · field_simp [hsC]


/-- Supports the entrywise computation in the proof of Lemma A.1: for $x\ne0$ the
solutions of $Y_{pq}'+ixY_{pq}=\tau D_{pq}$ are
$Y_{pq}(\tau)=(1/x^2-i\tau/x)D_{pq}+ce^{-i\tau x}$; then
$Y_{pq}(\frac12)-Y_{pq}(-\frac12)=-i(D_{pq}/x+2c\sin(x/2))$; and if $\sin(x/2)\ne0$, the
choice $c=-D_{pq}/(2x\sin(x/2))$ gives both end values $\mathcal N(x)D_{pq}$.

Reading the statement against the paper:
* `a` is $D_{pq}$ and `Y c` is the solution with constant $c$.
* The first two clauses say that the `Y c` are solutions and that every solution is one of them.
* `frameMult x` is $\mathcal N(x)=(1-(x/2)\cot(x/2))/x^2$ (eq:N-def) for $x\ne0$.
* At $x\in2\pi\mathbb Z\setminus\{0\}$, where $\sin(x/2)=0$, the third clause shows that the end
  values of every solution differ by $-iD_{pq}/x$, so they agree only if $D_{pq}=0$.

The proof follows the paper's: differentiate the formula; for uniqueness,
$e^{i\tau x}(y-Y_0)$ has derivative $0$; for the end values,
$e^{\mp ix/2}=\cos(x/2)\mp i\sin(x/2)$. -/
theorem corrector_entry_solutions {x : ℝ} (hx : x ≠ 0) (a : ℂ) :
    let Y : ℂ → ℝ → ℂ := fun c τ ↦
      (1 / (x : ℂ) ^ 2 - I * (τ : ℂ) / x) * a + c * Complex.exp (-(I * (τ : ℂ) * x))
    (∀ (c : ℂ) (τ : ℝ), HasDerivAt (Y c) ((τ : ℂ) * a - I * x * Y c τ) τ) ∧
    (∀ y : ℝ → ℂ, (∀ τ : ℝ, HasDerivAt y ((τ : ℂ) * a - I * x * y τ) τ) → ∃ c, y = Y c) ∧
    (∀ c : ℂ, Y c (1 / 2) - Y c (-1 / 2) = -I * (a / x + 2 * c * Real.sin (x / 2))) ∧
    (Real.sin (x / 2) ≠ 0 →
      Y (-a / (2 * x * Real.sin (x / 2))) (1 / 2) =
          UnitaryProducts.Corrector.frameMult x * a ∧
        Y (-a / (2 * x * Real.sin (x / 2))) (-1 / 2) =
          UnitaryProducts.Corrector.frameMult x * a) := by
  intro Y
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  have hinv : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hxC
  have hY : ∀ (c : ℂ) (τ : ℝ), HasDerivAt (Y c) ((τ : ℂ) * a - I * x * Y c τ) τ := by
    intro c τ
    have ht := hasDerivAt_ofReal τ
    have h := ((((ht.const_mul I).div_const (x : ℂ)).const_sub (1 / (x : ℂ) ^ 2)).mul_const
      a).add ((((ht.const_mul I).mul_const (x : ℂ)).neg.cexp).const_mul c)
    simp only [Y]
    convert h using 1
    linear_combination ((τ : ℂ) * a * I ^ 2 - I * (x : ℂ)⁻¹ * a) * hinv + (τ : ℂ) * a * I_sq
  have huniq : ∀ y : ℝ → ℂ, (∀ τ : ℝ, HasDerivAt y ((τ : ℂ) * a - I * x * y τ) τ) →
      ∃ c, y = Y c := by
    intro y hy
    have hg : ∀ τ : ℝ, HasDerivAt
        (fun t : ℝ ↦ Complex.exp (I * (t : ℂ) * x) * (y t - Y 0 t)) 0 τ := by
      intro τ
      convert ((((hasDerivAt_ofReal τ).const_mul I).mul_const (x : ℂ)).cexp).mul
        ((hy τ).sub (hY 0 τ)) using 1
      rw [Pi.sub_apply]
      ring
    refine ⟨y 0 - Y 0 0, funext fun τ ↦ ?_⟩
    have he := congrArg (fun z ↦ Complex.exp (-(I * (τ : ℂ) * x)) * z)
      (is_const_of_deriv_eq_zero (fun t ↦ (hg t).differentiableAt) (fun t ↦ (hg t).deriv) τ 0)
    simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, Complex.exp_neg,
      inv_mul_cancel_left₀ (Complex.exp_ne_zero _)] at he
    simp only [Y, Complex.exp_neg] at he ⊢
    linear_combination he
  have e1 : Complex.exp (-(I * (1 / 2 : ℂ) * x)) =
      Complex.cos (x / 2) - Complex.sin (x / 2) * I := by
    rw [show -(I * (1 / 2 : ℂ) * x) = -((x : ℂ) / 2) * I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  have e2 : Complex.exp (-(I * (-1 / 2 : ℂ) * x)) =
      Complex.cos (x / 2) + Complex.sin (x / 2) * I := by
    rw [show -(I * (-1 / 2 : ℂ) * x) = (x : ℂ) / 2 * I by ring, Complex.exp_mul_I]
  refine ⟨hY, huniq, fun c ↦ ?_, fun hs ↦ ?_⟩
  · simp only [Y]
    push_cast
    rw [e1, e2]
    ring
  · have hsC : Complex.sin (x / 2) ≠ 0 := by exact_mod_cast hs
    rw [UnitaryProducts.Corrector.frameMult, if_neg hx, Real.cot_eq_cos_div_sin]
    simp only [Y]
    push_cast
    rw [e1, e2]
    constructor <;> field_simp <;> ring

/-- Supports the case $x=0$ of the entrywise computation of §4.1: every solution of
$Y_{pq}'=\tau D_{pq}$ is $Y_{pq}(\tau)=c+(\tau^2/2)D_{pq}$, so its end values agree.

Reading the statement against the paper:
* `a` is $D_{pq}$ and $c$ is `y 0`.

The proof follows the paper's: $y-(\tau^2/2)a$ has derivative $0$. -/
theorem corrector_entry_solutions_zero (a : ℂ) (y : ℝ → ℂ)
    (hy : ∀ τ : ℝ, HasDerivAt y ((τ : ℂ) * a) τ) :
    (∀ τ : ℝ, y τ = y 0 + (τ : ℂ) ^ 2 / 2 * a) ∧ y (1 / 2) = y (-1 / 2) := by
  have hg : ∀ τ : ℝ, HasDerivAt (fun t : ℝ ↦ y t - (t : ℂ) * t / 2 * a) 0 τ := by
    intro τ
    have ht := hasDerivAt_ofReal τ
    convert (hy τ).sub (((ht.mul ht).div_const 2).mul_const a) using 1
    ring
  have hs : ∀ τ : ℝ, y τ = y 0 + (τ : ℂ) ^ 2 / 2 * a := by
    intro τ
    have h := is_const_of_deriv_eq_zero (fun t ↦ (hg t).differentiableAt)
      (fun t ↦ (hg t).deriv) τ 0
    simp only [ofReal_zero, mul_zero, zero_div, zero_mul, sub_zero] at h
    linear_combination h
  refine ⟨hs, ?_⟩
  rw [hs, hs (-1 / 2), show (-1 / 2 : ℝ) = -(1 / 2) by ring, ofReal_neg, neg_sq]

/-- Integrating the scalar corrector equation across the cell. -/
theorem corrector_entry_integrated {x : ℝ} (a : ℂ) (y : ℝ → ℂ)
    (hy : ∀ t : ℝ, HasDerivAt y ((t : ℂ) * a - I * x * y t) t)
    (hp : y (1 / 2) = y (-1 / 2)) :
    (I * (x : ℂ)) * (∫ t in (-1 / 2 : ℝ)..(1 / 2), y t) = 0 ∧
      (∫ t in (-1 / 2 : ℝ)..(1 / 2), t) = 0 := by
  have hc : Continuous y := continuous_iff_continuousAt.mpr fun t ↦ (hy t).continuousAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (fun t _ ↦ hy t) ((show Continuous _ by fun_prop).intervalIntegrable _ _)
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [hp, sub_self, intervalIntegral.integral_sub, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul] at he
  rw [intervalIntegral.integral_ofReal] at he
  norm_num [integral_id] at he ⊢
  exact he

/-- the proof of Lemma A.1: integrating the scalar equation gives mean zero off the
zero frequency; the prescribed endpoint selects the mean-zero quadratic at zero. -/
theorem corrector_entry_mean_zero {x : ℝ} (a : ℂ) (y : ℝ → ℂ)
    (hy : ∀ t : ℝ, HasDerivAt y ((t : ℂ) * a - I * x * y t) t)
    (hp : y (1 / 2) = y (-1 / 2))
    (hi : y (-1 / 2) = (UnitaryProducts.Corrector.frameMult x : ℂ) * a) :
    ∫ t in (-1 / 2 : ℝ)..(1 / 2), y t = 0 := by
  by_cases hx : x = 0
  · have he := (corrector_entry_solutions_zero a y (by simpa [hx] using hy)).1
    have h0 := he (-1 / 2)
    rw [hi, hx] at h0
    rw [intervalIntegral.integral_congr (fun t _ ↦ he t)]
    simp_rw [← ofReal_pow]
    simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
      [intervalIntegral.integral_add, intervalIntegral.integral_const,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
        intervalIntegral.integral_ofReal]
    norm_num [UnitaryProducts.Corrector.frameMult, integral_pow, smul_eq_mul] at h0 ⊢
    linear_combination -h0
  · exact (mul_eq_zero.mp (corrector_entry_integrated a y hy hp).1).resolve_left
      (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx))

/-- A continuous scalar homogeneous solution on the closed cell, differentiable
in its interior, is zero under nonresonance, periodicity and zero mean at zero frequency. -/
theorem corrector_entry_homogeneous_eq_zero {x : ℝ}
    (hnr : ∀ n : ℤ, n ≠ 0 → x ≠ 2 * π * n)
    (y : ℝ → ℂ) (hc : ContinuousOn y (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hy : ∀ t ∈ Ioo (-1 / 2 : ℝ) (1 / 2), HasDerivAt y (-I * x * y t) t)
    (hp : y (1 / 2) = y (-1 / 2))
    (hm : x = 0 → ∫ t in (-1 / 2 : ℝ)..(1 / 2), y t = 0) :
    ∀ t ∈ Icc (-1 / 2 : ℝ) (1 / 2), y t = 0 := by
  let g := fun t : ℝ ↦ Complex.exp (I * (t : ℂ) * x) * y t
  have hgc : ContinuousOn g (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    ((continuous_const.mul continuous_ofReal).mul continuous_const).cexp.continuousOn.mul hc
  have hg (t) (ht : t ∈ Ioo (-1 / 2 : ℝ) (1 / 2)) : HasDerivAt g 0 t := by
    convert ((((hasDerivAt_ofReal t).const_mul I).mul_const (x : ℂ)).cexp).mul (hy t ht) using 1
    ring
  have hconst (t) (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : g t = g (-1 / 2) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hgc.mono (Icc_subset_Icc_right ht.2))
      (fun s hs ↦ hg s ⟨hs.1, hs.2.trans_le ht.2⟩)
      (intervalIntegrable_const (c := (0 : ℂ)))
    exact sub_eq_zero.mp (by simpa only [intervalIntegral.integral_zero] using h.symm)
  have hleft : y (-1 / 2) = 0 := by
    by_cases hx0 : x = 0
    · have hi := intervalIntegral.integral_congr (μ := volume) (a := -1 / 2) (b := 1 / 2)
        (fun t ht ↦ hconst t (by
          simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using ht))
      norm_num [g, hx0] at hi
      simpa only [neg_div] using hi.symm.trans (by simpa only [neg_div] using hm hx0)
    · have hs := (UnitaryProducts.Separation.zero_or_sin_half_ne_zero hnr).resolve_left hx0
      have h := hconst (1 / 2) (by norm_num)
      have ec := corrector_entry_exp_cot hs
      push_cast [g, hp] at h
      rw [show I * (1 / 2 : ℂ) * x = I * x / 2 by ring,
        show I * (-1 / 2 : ℂ) * x = -(I * x / 2) by ring, ec.1, ec.2] at h
      have he : (2 * (Real.sin (x / 2) : ℂ) * I) * y (-1 / 2) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp he).resolve_left
        (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr hs)) I_ne_zero)
  intro t ht
  have h := hconst t ht
  simp only [g, hleft, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)

end UnitaryProducts.Paper

namespace UnitaryProducts.Prose
/-- Section 4.1, the comparison with the commutator equation: for `x ≠ 0`, equal
end values are equivalent to `2 sin(x/2) c = -D/x`. The zero-frequency solution
has its own formula in `corrector_entry_solutions_zero`. -/
theorem corrector_equal_end_iff {x : ℝ} (hx : x ≠ 0) (D c : ℂ) :
    let Y := fun τ : ℝ ↦
      (1 / (x : ℂ) ^ 2 - I * (τ : ℂ) / x) * D + c * exp (-(I * (τ : ℂ) * x))
    Y (1 / 2) = Y (-1 / 2) ↔ 2 * (Real.sin (x / 2) : ℂ) * c = -D / x := by
  intro Y
  have he := (UnitaryProducts.Paper.corrector_entry_solutions hx D).2.2.1 c
  change Y (1 / 2) - Y (-1 / 2) = _ at he
  rw [← sub_eq_zero, he, mul_eq_zero]
  simp only [neg_ne_zero.mpr I_ne_zero, false_or]
  constructor <;> intro h <;> linear_combination h

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper
/-- The initial value selects the scalar solution with equal endpoints, including at zero. -/
theorem corrector_entry_endpoint {x : ℝ} (hx : x = 0 ∨ Real.sin (x / 2) ≠ 0) (a : ℂ) (y : ℝ → ℂ)
    (hy : ∀ t : ℝ, HasDerivAt y ((t : ℂ) * a - I * x * y t) t)
    (hi : y (-1 / 2) = (UnitaryProducts.Corrector.frameMult x : ℂ) * a) :
    y (1 / 2) = (UnitaryProducts.Corrector.frameMult x : ℂ) * a := by
  by_cases hx0 : x = 0
  · exact (corrector_entry_solutions_zero a y (by simpa [hx0] using hy)).2.trans hi
  · obtain ⟨_, hgeneral, _, hend⟩ := corrector_entry_solutions hx0 a
    obtain ⟨c, hc⟩ := hgeneral y hy
    obtain ⟨hr, hl⟩ := hend (hx.resolve_left hx0)
    have hc' : c = -a / (2 * x * Real.sin (x / 2)) := by
      rw [hc] at hi
      exact mul_right_cancel₀ (Complex.exp_ne_zero _) (add_left_cancel (hi.trans hl.symm))
    have hp : y (1 / 2) = y (-1 / 2) := by
      rw [hc, hc']
      apply (UnitaryProducts.Prose.corrector_equal_end_iff hx0 a _).2
      have hxC := ofReal_ne_zero.mpr hx0
      have hsC := ofReal_ne_zero.mpr (hx.resolve_left hx0)
      field_simp [hxC, hsC]
    exact hp.trans hi

end UnitaryProducts.Paper
