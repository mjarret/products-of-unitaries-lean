/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.DuhamelIntegral
public import UnitaryProducts.Corrector.ScalarEntrySolutions

/-!
# The cell boundary identity and the scalar resonance obstruction

Section 4.1 integrates the scalar corrector equation with its integrating
factor, evaluates the boundary difference and the nonzero-resonance
obstruction, and uses zero mean to select the zero-frequency solution.
-/

@[expose] public section

open Complex Real Set MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.Prose

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Section 4.1: multiplying the entry equation by its integrating factor. -/
theorem scalar_corrector_integrating_factor {x : ℝ} {a : ℂ} {y : ℝ → ℂ} {t : ℝ}
    (hy : HasDerivAt y ((t : ℂ) * a - I * x * y t) t) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (I * x * (s : ℂ)) * y s)
      ((t : ℂ) * Complex.exp (I * x * (t : ℂ)) * a) t := by
  convert (((Paper.hasDerivAt_ofReal t).const_mul (I * (x : ℂ))).cexp).mul hy using 1
  ring

/-- The scalar first moment on the centered cell, evaluated by its primitive. -/
theorem scalar_corrector_centered_moment {x : ℝ} (hx : x ≠ 0) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), (t : ℂ) * Complex.exp (I * x * (t : ℂ))) =
      Complex.exp (I * x / 2) * ((1 / 2 : ℂ) / (I * x) + 1 / (x : ℂ)^2) -
      Complex.exp (-(I * x / 2)) * ((-1 / 2 : ℂ) / (I * x) + 1 / (x : ℂ)^2) := by
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  let P : ℝ → ℂ := fun t ↦ Complex.exp (I * x * (t : ℂ)) *
    ((t : ℂ) / (I * x) + 1 / (x : ℂ)^2)
  have hd (t : ℝ) : HasDerivAt P ((t : ℂ) * Complex.exp (I * x * (t : ℂ))) t := by
    have he := (((Paper.hasDerivAt_ofReal t).const_mul (I * (x : ℂ))).cexp).mul
      (((Paper.hasDerivAt_ofReal t).div_const (I * (x : ℂ))).add_const (1 / (x : ℂ)^2))
    convert he using 1
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((show Continuous _ by fun_prop).intervalIntegrable _ _)]
  dsimp [P]
  push_cast
  congr 2 <;> ring

/-- The evaluated scalar cell moment in Section 4, written with sine and
cosine so that the nonzero resonance obstruction is visible. -/
theorem scalar_corrector_trig_moment {x : ℝ} (hx : x ≠ 0) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2), (t : ℂ) * Complex.exp (I * x * (t : ℂ))) =
      I * (2 * Complex.sin ((x : ℂ) / 2) / (x : ℂ) ^ 2 -
        Complex.cos ((x : ℂ) / 2) / x) := by
  rw [scalar_corrector_centered_moment hx]
  rw [show I * (x : ℂ) / 2 = ((x : ℂ) / 2) * I by ring,
    show -(((x : ℂ) / 2) * I) = (-((x : ℂ) / 2)) * I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The scalar entry of the equal-endpoint boundary identity in Section 4.
Only a continuously differentiable solution on the cell is needed. -/
theorem scalar_corrector_boundary {x : ℝ} (hx : x ≠ 0) {a : ℂ} {y : ℝ → ℂ}
    (hc : ContinuousOn y (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hy : ∀ t ∈ Ioo (-1 / 2 : ℝ) (1 / 2),
      HasDerivAt y ((t : ℂ) * a - I * x * y t) t)
    (hend : y (-1 / 2) = y (1 / 2)) :
    2 * I * Complex.sin ((x : ℂ) / 2) * y (1 / 2) =
      I * (2 * Complex.sin ((x : ℂ) / 2) / (x : ℂ) ^ 2 -
        Complex.cos ((x : ℂ) / 2) / x) * a := by
  have hgc : ContinuousOn (fun t : ℝ ↦ Complex.exp (I * x * (t : ℂ)) * y t)
      (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    (show Continuous (fun t : ℝ ↦ Complex.exp (I * x * (t : ℂ))) by
      fun_prop).continuousOn.mul hc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2) hgc
    (fun t ht ↦ scalar_corrector_integrating_factor (hy t ht))
    ((show Continuous _ by fun_prop).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, scalar_corrector_trig_moment hx, hend] at hi
  rw [hi]
  push_cast
  rw [show I * (x : ℂ) * (1 / 2) = ((x : ℂ) / 2) * I by ring,
    show I * (x : ℂ) * (-1 / 2) = (-((x : ℂ) / 2)) * I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- At a nonzero integer resonance the exponential moment is
`-i (-1)^m / x`, exactly the obstruction displayed in Section 4.1. -/
theorem scalar_corrector_resonant_moment {m : ℤ} (hm : m ≠ 0) :
    (∫ t in (-1 / 2 : ℝ)..(1 / 2),
      (t : ℂ) * Complex.exp (I * (2 * π * m : ℝ) * (t : ℂ))) =
      -I * (-1 : ℂ)^m / (2 * π * m : ℝ) := by
  have hx : (2 * π * m : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero)
    (Int.cast_ne_zero.mpr hm)
  have he : Complex.exp (I * (2 * π * m : ℝ) / 2) = (-1 : ℂ)^m := by
    rw [show I * (2 * π * m : ℝ) / 2 = ((m : ℂ) * π) * I by push_cast; ring,
      Complex.exp_mul_I]
    have hs : Complex.sin ((m : ℂ) * π) = 0 := by
      exact_mod_cast Real.sin_int_mul_pi m
    have hc : Complex.cos ((m : ℂ) * π) = (-1 : ℂ)^m := by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
        Real.cos_int_mul_pi, Complex.ofReal_zpow]
      norm_num
    rw [hs, hc, zero_mul, add_zero]
  have hen : Complex.exp (-(I * (2 * π * m : ℝ) / 2)) = (-1 : ℂ)^m := by
    rw [Complex.exp_neg, he, ← inv_zpow, inv_neg, inv_one]
  rw [scalar_corrector_centered_moment hx, he, hen]
  have hxC : ((2 * π * m : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- Equal end values at resonance force the integrated forcing to vanish.
The proof is the integrating-factor argument in Section 4.1. -/
theorem scalar_corrector_resonant_obstruction {m : ℤ} (hm : m ≠ 0)
    (a : ℂ) (y : ℝ → ℂ)
    (hc : ContinuousOn y (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hy : ∀ t ∈ Ioo (-1 / 2 : ℝ) (1 / 2), HasDerivAt y
      ((t : ℂ) * a - I * (2 * π * m : ℝ) * y t) t)
    (hp : y (1 / 2) = y (-1 / 2)) :
    a * (∫ t in (-1 / 2 : ℝ)..(1 / 2),
      (t : ℂ) * Complex.exp (I * (2 * π * m : ℝ) * (t : ℂ))) =
      -I * (-1 : ℂ)^m * a / (2 * π * m : ℝ) ∧
    -I * (-1 : ℂ)^m * a / (2 * π * m : ℝ) = 0 := by
  have hgc : ContinuousOn
      (fun t : ℝ ↦ Complex.exp (I * (2 * π * m : ℝ) * (t : ℂ)) * y t)
      (Icc (-1 / 2 : ℝ) (1 / 2)) :=
    (show Continuous (fun t : ℝ ↦ Complex.exp (I * (2 * π * m : ℝ) * (t : ℂ))) by
      fun_prop).continuousOn.mul hc
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2) hgc
    (fun t ht ↦ scalar_corrector_integrating_factor (hy t ht))
    ((show Continuous _ by fun_prop).intervalIntegrable _ _)
  have he : Complex.exp (I * (2 * π * m : ℝ) * (1 / 2 : ℝ)) =
      Complex.exp (I * (2 * π * m : ℝ) * (-1 / 2 : ℝ)) := by
    apply (exp_eq_exp_iff_exists_int).2
    refine ⟨m, ?_⟩
    push_cast
    ring
  rw [intervalIntegral.integral_mul_const, hp, he, sub_self,
    scalar_corrector_resonant_moment hm] at hi
  constructor
  · rw [scalar_corrector_resonant_moment hm]
    ring
  · convert hi using 1
    ring


end UnitaryProducts.Prose
