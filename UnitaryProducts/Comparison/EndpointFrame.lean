/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import Mathlib.Data.Matrix.Basis
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# The center value of the periodic corrector

## Declarations

- `frameMult_sub_half`
- `two_frameMult_sub_half_pi`
- `norm_cellPrimitive_sub_center_le`
- `norm_frameExtension_le_center`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real Complex Set MeasureTheory
noncomputable section

namespace UnitaryProducts.Corrector
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The half-angle identity used to evaluate Theorem B's constant at width $\pi$:
$\mathcal N(x)-\mathcal N(x/2)/2=1/(2x\sin(x/2))-1/x^2$ for $0<x<2\pi$, from
$\cot\frac x4-\cot\frac x2=1/\sin\frac x2$. -/
theorem frameMult_sub_half {x : ℝ} (hx : 0 < x) (hx' : x < 2 * π) :
    frameMult x - frameMult (x/2)/2 = 1/(2*x*Real.sin (x/2)) - 1/x^2 := by
  have hx2 : x/2 ≠ 0 := div_ne_zero hx.ne' (by norm_num)
  have hs : Real.sin (x/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have ht := cot_half_sub_cot (y := x/2) (by linarith) (by linarith)
  rw [frameMult, if_neg hx.ne', frameMult, if_neg hx2]
  calc _ = (Real.cot ((x/2)/2)-Real.cot (x/2))/(2*x)-1/x^2 := by
          field_simp; ring
    _ = _ := by rw [ht]; field_simp

/-- At $x=\pi$: $2(\mathcal N(\pi)-\mathcal N(\pi/2)/2)=1/\pi-2/\pi^2$, that is, $2c_0$ at width
$\pi$. -/
theorem two_frameMult_sub_half_pi :
    2*(frameMult π-frameMult (π/2)/2) = 1/π-2/π^2 := by
  rw [frameMult_sub_half pi_pos (by linarith [pi_pos]), Real.sin_pi_div_two]
  ring

end UnitaryProducts.Corrector

namespace UnitaryProducts
open UnitaryProducts.Corrector Matrix
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end UnitaryProducts

namespace UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The integral term of the corrector moves by at most $(s-\frac12)^2\|D\|/2$ away from the
center, since its derivative has norm $|s-\frac12|\|D\|$ (proof of Lemma A.1). -/
theorem norm_cellPrimitive_sub_center_le (h D : 𝕄) (hh : h.IsHermitian) (s : ℝ) :
    ‖cellPrimitive h D s-cellPrimitive h D (1/2)‖ ≤ (s-1/2)^2/2*‖D‖ := by
  have hb := norm_cellPrimitive_sub_le h D hh (1/2) s
    (by simpa only [le_min_iff, max_le_iff, le_refl, true_and] using le_total (1/2 : ℝ) s)
  simpa only [sub_self, abs_zero, zero_add, ← sq, sq_abs] using hb

/-- The profile of the proof of Lemma A.1 in terms of the actual center value:
$\|Y(\tau)\|\le\|Y(0)\|+\frac{\tau^2}2\|D\|$, $\tau=s-\frac12$, for any starting value `Ybar`. -/
theorem norm_frameExtension_le_center (h D Ybar : 𝕄) (hh : h.IsHermitian) (s : ℝ) :
    ‖frameExtension h D Ybar s‖ ≤
      ‖frameExtension h D Ybar (1/2)‖+(s-1/2)^2/2*‖D‖ := by
  have hrot : evol h (s-1/2)*frameExtension h D Ybar (1/2)*evol h (-(s-1/2)) =
      evol h s*(Ybar+cellPrimitive h D (1/2))*evol h (-s) := by
    simp only [frameExtension, ← mul_assoc, ← evol_add, sub_add_cancel]
    rw [mul_assoc, ← evol_add, show -(1/2:ℝ)+ -(s-1/2) = -s by ring]
  have he : frameExtension h D Ybar s =
      evol h (s-1/2)*frameExtension h D Ybar (1/2)*evol h (-(s-1/2)) +
      evol h s*(cellPrimitive h D s-cellPrimitive h D (1/2))*evol h (-s) := by
    rw [hrot, frameExtension]
    simp only [mul_add, add_mul, mul_sub, sub_mul]
    abel
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [neg_neg] using norm_evol_conj_le hh (frameExtension h D Ybar (1/2)) (-(s-1/2))
  · simpa only [neg_neg] using
      (norm_evol_conj_le hh (cellPrimitive h D s-cellPrimitive h D (1/2)) (-s)).trans
        (norm_cellPrimitive_sub_center_le h D hh s)

end UnitaryProducts.Dressed
