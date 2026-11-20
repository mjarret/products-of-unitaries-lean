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

- `corrector_entry_solutions`
-/

@[expose] public section

open Complex Real Filter Set MeasureTheory
open scoped Topology

noncomputable section
namespace UnitaryProducts.Paper

/-- The real embedding `ℝ → ℂ` has derivative `1`. -/
theorem hasDerivAt_ofReal (τ : ℝ) : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 τ := by
  simpa using (hasDerivAt_id' τ).ofReal_comp

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

end UnitaryProducts.Paper

namespace UnitaryProducts.Prose

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper

end UnitaryProducts.Paper
