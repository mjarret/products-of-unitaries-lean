/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.IntegralDressedCell
public import UnitaryProducts.Corrector.SeparatedFrameBounds

/-!
# The scalar Stein identity

## Declarations

- `centered_exp_integral`
- `frameMult_exp_sub`
- `frameMult_stein_scalar`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex MeasureTheory Set
noncomputable section
namespace UnitaryProducts.Separation

/-- The centered exponential moment, computed by an explicit primitive. -/
theorem centered_exp_integral {x : ℝ} (hx : x ≠ 0) :
    (∫ t in (0:ℝ)..1, (t-1/2 : ℝ) • Complex.exp ((x:ℂ)*I*t)) =
      (Complex.exp ((x:ℂ)*I)-1)/(x:ℂ)^2 +
        (Complex.exp ((x:ℂ)*I)+1)/(2*(x:ℂ)*I) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  let P : ℝ → ℂ := fun t ↦ Complex.exp ((x:ℂ)*I*t) *
    (((t:ℂ)-1/2)/((x:ℂ)*I) + 1/(x:ℂ)^2)
  have hd (t : ℝ) : HasDerivAt P ((t-1/2 : ℝ) • Complex.exp ((x:ℂ)*I*t)) t := by
    have he := (((hasDerivAt_id (t : ℂ)).comp_ofReal).const_mul ((x:ℂ)*I)).cexp
    have hl := (((hasDerivAt_id (t : ℂ)).comp_ofReal).sub_const (1/2)).div_const ((x:ℂ)*I)
    have hh := he.mul (hl.add_const (1/(x:ℂ)^2))
    convert hh using 1
    simp only [id_eq, mul_one, ← Complex.coe_smul, smul_eq_mul]
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]; ring
  have hc : Continuous (fun t : ℝ ↦ (t-1/2 : ℝ) • Complex.exp ((x:ℂ)*I*t)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (hc.intervalIntegrable 0 1)]
  simp only [P, ofReal_one, ofReal_zero, mul_one, mul_zero, Complex.exp_zero, one_mul]
  field_simp
  ring

/-- The cotangent factor supplies the centered exponential moment at every nonzero nonresonant x. -/
theorem frameMult_exp_sub {x : ℝ} (hx : x ≠ 0) (hs : Real.sin (x / 2) ≠ 0) :
    (UnitaryProducts.Corrector.frameMult x : ℂ) * (Complex.exp ((x:ℂ)*I)-1) =
      (Complex.exp ((x:ℂ)*I)-1)/(x:ℂ)^2 +
        (Complex.exp ((x:ℂ)*I)+1)/(2*(x:ℂ)*I) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hsC : (Real.sin (x/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have he : Complex.exp ((x:ℂ)*I) =
      ((Real.cos (x/2) : ℂ) + (Real.sin (x/2) : ℂ)*I)^2 := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have ht : (Real.sin (x/2) : ℂ)^2 + (Real.cos (x/2) : ℂ)^2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (x/2)
  have hc : (Complex.exp ((x:ℂ)*I)-1) * (Real.cos (x/2):ℂ) =
      I * (Complex.exp ((x:ℂ)*I)+1) * (Real.sin (x/2):ℂ) := by
    rw [he]
    linear_combination
      ((Real.cos (x/2):ℂ) + (Real.sin (x/2):ℂ)*I) * ht +
      (- (Real.cos (x/2):ℂ)*(Real.sin (x/2):ℂ)^2 -
        I*(Real.sin (x/2):ℂ)^3) * Complex.I_sq
  rw [UnitaryProducts.Corrector.frameMult, if_neg hx, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  linear_combination -(x:ℂ) * I * hc -
    (x:ℂ) * (Complex.exp ((x:ℂ)*I)+1) * (Real.sin (x/2):ℂ) * Complex.I_sq

/-- The scalar Stein identity; zero differences are included. -/
theorem frameMult_stein_scalar {x : ℝ} (hx : x = 0 ∨ Real.sin (x / 2) ≠ 0) :
    (UnitaryProducts.Corrector.frameMult x : ℂ) * (Complex.exp ((x:ℂ)*I)-1) =
      ∫ t in (0:ℝ)..1, (t-1/2 : ℝ) • Complex.exp ((x:ℂ)*I*t) := by
  by_cases hx0 : x = 0
  · subst x
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, sub_self, mul_zero]
    have hz : (∫ t in (0:ℝ)..1, t-1/2) = 0 := by
      simpa only [mul_one] using Dressed.integral_affine 0 1 (1/2) 1 |>.trans (by norm_num)
    simp only [← Complex.coe_smul, smul_eq_mul, mul_one,
      intervalIntegral.integral_ofReal, hz, Complex.ofReal_zero]
  · rw [centered_exp_integral hx0]
    exact frameMult_exp_sub hx0 (hx.resolve_left hx0)

end UnitaryProducts.Separation
