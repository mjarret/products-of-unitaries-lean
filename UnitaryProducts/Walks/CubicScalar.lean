/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Two quadratures for Lemma A.2

## Declarations

- `walk_hessian_quadrature`
- `walk_hessian_quadrature_re`
- `walk_slope_quadrature`
- `walk_slope_quadrature_angle`
-/

@[expose] public section

open Real MeasureTheory
noncomputable section
namespace UnitaryProducts

/-- $\int_0^1 2u\,(A + B(2u-1)^2)^{-3/2}\,du = 1/A$ for $A > 0$, $B \ge 0$, $A + B = 1$. -/
theorem walk_hessian_quadrature {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hAB : A + B = 1) :
    (∫ t in (0:ℝ)..1, 2*t/(Real.sqrt (A+B*(2*t-1)^2))^3) = 1/A := by
  let q : ℝ → ℝ := fun t ↦ A+B*(2*t-1)^2
  have hq (t : ℝ) : 0<q t := add_pos_of_pos_of_nonneg hA (mul_nonneg hB (sq_nonneg _))
  have hs (t : ℝ) : 0<Real.sqrt (q t) := Real.sqrt_pos.mpr (hq t)
  have hd (t : ℝ) : HasDerivAt q (4*B*(2*t-1)) t := by
    convert (((((hasDerivAt_id t).const_mul 2).sub_const 1).pow 2).const_mul B).const_add A using
      1 ; simp only [id_eq] ; ring
  let F : ℝ → ℝ := fun t ↦ (2*t-1)/(2*A*Real.sqrt (q t))
  have hF (t : ℝ) : HasDerivAt F (1/(Real.sqrt (q t))^3) t := by
    have h := (((hasDerivAt_id t).const_mul 2).sub_const 1).div
      (((hd t).sqrt (hq t).ne').const_mul (2*A)) (by positivity : 2*A*Real.sqrt (q t)≠0)
    convert h using 1
    have he := Real.sq_sqrt (hq t).le
    simp only [id_eq, mul_one]
    field_simp [hA.ne', (hs t).ne']
    ring_nf
    rw [he]
    dsimp [q]
    ring
  have hcont : Continuous (fun t ↦ 1/(Real.sqrt (q t))^3) :=
    continuous_const.div ((Real.continuous_sqrt.comp (show Continuous q by
        dsimp [q]
        fun_prop)).pow 3)
      (fun t ↦ pow_ne_zero 3 (hs t).ne')
  have hbase : (∫ t in (0:ℝ)..1, 1/(Real.sqrt (q t))^3)=1/A := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t)
      (hcont.intervalIntegrable 0 1)]
    have hq0 : q 0=1 := by dsimp [q]; convert hAB using 1 ; ring
    have hq1 : q 1=1 := by dsimp [q]; convert hAB using 1 ; ring
    dsimp [F]
    rw [hq0,hq1,Real.sqrt_one]
    field_simp
    ring
  let f : ℝ → ℝ := fun t ↦ 2*t/(Real.sqrt (q t))^3
  have hfc : Continuous f := by
    exact (continuous_const.mul continuous_id).div
      ((Real.continuous_sqrt.comp (by dsimp [q]; fun_prop)).pow 3)
      (fun t ↦ pow_ne_zero 3 (hs t).ne')
  have hsym (t : ℝ) : q (1-t)=q t := by dsimp [q]; ring
  have hpair (t : ℝ) : f t+f (1-t)=2*(1/(Real.sqrt (q t))^3) := by
    dsimp [f]; rw [hsym]; ring
  have hi := intervalIntegral.integral_comp_sub_left f 1 (a:=0) (b:=1)
  norm_num only [sub_self,sub_zero] at hi
  have he := intervalIntegral.integral_add (μ:=volume) (hfc.intervalIntegrable 0 1)
    ((hfc.comp (show Continuous (fun t:ℝ ↦ 1-t) by fun_prop)).intervalIntegrable 0 1)
  change (∫ t in (0:ℝ)..1, f t+f (1-t)) =
    (∫ t in (0:ℝ)..1, f t)+(∫ t in (0:ℝ)..1, f (1-t)) at he
  simp_rw [hpair] at he
  rw [intervalIntegral.integral_const_mul,hi,hbase] at he
  change (∫ t in (0:ℝ)..1, f t)=1/A
  exact (mul_left_cancel₀ (by norm_num : (2:ℝ)≠0)
    (by simpa only [two_mul] using he.symm))

/-- Supports the second chord integral in the proof of Lemma A.2,
$\int_0^1 2u\,du/r_u^3 = 1/\cos^2(w/4)$: with $r_u = |1 + u(e^{iw/2} - 1)|$,
$r_u^2 = (1-u)^2 + u^2 + 2u(1-u)c$ for $c = \cos(w/2)$, and
$\int_0^1 2u\,((1-u)^2 + u^2 + 2u(1-u)c)^{-3/2}\,du = 2/(1 + c)$, which is $1/\cos^2(w/4)$. The
hypotheses $-1 < c \le 1$ hold for $0 \le w < 2\pi$. -/
theorem walk_hessian_quadrature_re {c : ℝ} (hc : -1 < c) (hc1 : c ≤ 1) :
    (∫ t in (0:ℝ)..1,
      2*t/(Real.sqrt ((1-t)^2+t^2+2*t*(1-t)*c))^3) = 2/(1+c) := by
  have h := walk_hessian_quadrature (A:=(1+c)/2) (B:=(1-c)/2)
    (by linarith) (by linarith) (by ring)
  have he (t : ℝ) : (1-t)^2+t^2+2*t*(1-t)*c = (1+c)/2+(1-c)/2*(2*t-1)^2 := by ring
  simp_rw [he]
  exact h.trans (by field_simp)

/-- $\int_0^1 (\cos^2 x + \sin^2 x\,(2u-1)^2)^{-1}\,du = x/(\sin x\cos x)$ for $0 < x < \pi/2$. -/
theorem walk_slope_quadrature_angle {x : ℝ} (hx : 0 < x) (hxπ : x < π / 2) :
    (∫ t in (0:ℝ)..1, 1/(Real.cos x^2+Real.sin x^2*(2*t-1)^2)) =
      x/(Real.sin x*Real.cos x) := by
  have hc : 0<Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hxπ⟩
  have hs : 0<Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  let q : ℝ → ℝ := fun t ↦ Real.cos x^2+Real.sin x^2*(2*t-1)^2
  have hq (t : ℝ) : 0<q t := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  let F : ℝ → ℝ := fun t ↦ Real.arctan ((2*t-1)*Real.tan x)/(2*Real.sin x*Real.cos x)
  have hF (t : ℝ) : HasDerivAt F (1/q t) t := by
    have h := ((Real.hasDerivAt_arctan ((2*t-1)*Real.tan x)).comp t
      ((((hasDerivAt_id t).const_mul 2).sub_const 1).mul_const (Real.tan x))).div_const
        (2*Real.sin x*Real.cos x)
    convert h using 1
    dsimp [q]
    rw [Real.tan_eq_sin_div_cos]
    simp only [mul_one]
    field_simp
  have hcont : Continuous (fun t ↦ 1/q t) := continuous_const.div
    (by dsimp [q]; fun_prop) (fun t ↦ (hq t).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t)
    (hcont.intervalIntegrable 0 1)]
  dsimp [F]
  norm_num only [mul_one,sub_self,sub_zero,mul_zero,zero_sub,neg_one_mul]
  rw [Real.arctan_neg]
  norm_num only [show (2:ℝ)-1=1 by norm_num,one_mul]
  simp_rw [Real.arctan_tan (by linarith [Real.pi_pos]) hxπ]
  field_simp; ring

/-- Supports the first chord integral in the proof of Lemma A.2,
$\int_0^1 du/r_u^2 = S$: with $r_u^2 = \cos^2(w/4) + (2u-1)^2\sin^2(w/4)$, the integral is
$S = (w/2)/\sin(w/2)$ for $0 < w < 2\pi$ (at $w = 0$, $r_u = 1$ and both sides are $1$). -/
theorem walk_slope_quadrature {w : ℝ} (hw : 0 < w) (hwπ : w < 2 * π) :
    (∫ t in (0:ℝ)..1, 1/(Real.cos (w/4)^2+Real.sin (w/4)^2*(2*t-1)^2)) =
      (w/2)/Real.sin (w/2) := by
  rw [walk_slope_quadrature_angle (by linarith) (by linarith), show w/2=2*(w/4) by ring,
    Real.sin_two_mul]
  field_simp

end UnitaryProducts
