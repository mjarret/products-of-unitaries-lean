/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.Commutator

/-!
# The bound $\|\Phi^{-1}(i\,\mathrm{ad}_h)\| \le (w/2)/\sin(w/2)$

## Declarations

- `cot_half_sub_cot`
- `sinBound`
- `sinBound_nonneg`
-/

@[expose] public section

open scoped BigOperators
open Real

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `cot(y/2) - cot y = 1/sin y` for `0 < y < π`. -/
theorem cot_half_sub_cot {y : ℝ} (hy0 : 0 < y) (hy : y < π) :
    Real.cot (y / 2) - Real.cot y = 1 / Real.sin y := by
  have hs : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy0 hy).ne'
  have hs2 : Real.sin (y / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hsub := Real.sin_sub y (y / 2)
  rw [show y - y / 2 = y / 2 by ring] at hsub
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp
  linear_combination (-1 : ℝ) * hsub

end UnitaryProducts.Corrector

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open UnitaryProducts.Corrector Complex NormedSpace

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The sharper majorant of the inverse averaging operator, `(w/2)/sin(w/2)`: the constant $S$ of
Lemma A.2 for $0 < w < 2\pi$. At $w = 0$ it is $0/0 = 0$ in Lean, not the paper's $g(0)=1$;
`walkLogSlope` is the version continuous at $0$. -/
noncomputable def sinBound (w : ℝ) : ℝ := (w / 2) / Real.sin (w / 2)

theorem sinBound_nonneg {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) : 0 ≤ sinBound w :=
  div_nonneg (by linarith) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le

end UnitaryProducts
