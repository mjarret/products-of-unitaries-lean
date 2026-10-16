/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Comparison.EndpointFrame
public import UnitaryProducts.Comparison.IntegralDressedCell
public import UnitaryProducts.Comparison.UnitStepPathDAT
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Evolution.RoundedClock
public import UnitaryProducts.Walks.LogarithmSmoothness

/-!
# The residual on one piece of the rounded clock

## Declarations

- `integral_borrowed_half_majorant`
- `norm_borrowed_residual_profile`
- `norm_frameExtension_le_center_profile`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real
noncomputable section
namespace UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The residual majorant of an end half cell, integrated over its half step:
$\int_0^{1/2}(M(t-t^2/2)+(2-t)(q+t^2/2)L^2)\,dt=5M/48+(7q/8+13/384)L^2$. -/
theorem integral_borrowed_half_majorant (q L M : ℝ) :
    (∫ t in (0:ℝ)..(1/2), M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2) =
      5*M/48+(7*q/8+13/384)*L^2 := by
  let P : ℝ → ℝ := fun t ↦ M*(t^2/2-t^3/6)+L^2*(2*q*t-q*t^2/2+t^3/3-t^4/8)
  have hd (t : ℝ) : HasDerivAt P (M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2) t := by
    convert ((((hasDerivAt_pow 2 t).div_const 2).sub
      ((hasDerivAt_pow 3 t).div_const 6)).const_mul M).add
      (((((hasDerivAt_id t).const_mul (2*q)).sub
        (((hasDerivAt_pow 2 t).const_mul q).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub
        ((hasDerivAt_pow 4 t).div_const 8) |>.const_mul (L^2)) using 1 ; dsimp [P] ; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((by fun_prop : Continuous fun t:ℝ ↦ M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2).intervalIntegrable _ _)]
  dsimp [P]
  ring

/-- the proof of Lemma A.1 from a center bound: if $\|D\|\le L$ and $\|Y(0)\|\le qL$, then
$\|Y(s)\|\le(q+s^2/2)L$, with $s$ the offset from the center. -/
theorem norm_frameExtension_le_center_profile {h D Ybar : 𝕄} (hh : h.IsHermitian)
    {q L : ℝ} (hD : ‖D‖ ≤ L)
    (hcenter : ‖frameExtension h D Ybar (1 / 2)‖ ≤ q * L) (s : ℝ) :
    ‖frameExtension h D Ybar (s+1/2)‖ ≤ (q+s^2/2)*L := by
  have hb := norm_frameExtension_le_center h D Ybar hh (s+1/2)
  rw [add_sub_cancel_right] at hb
  exact (hb.trans (add_le_add hcenter
    (mul_le_mul_of_nonneg_left hD (by positivity)))).trans_eq (by ring)

/-- The residual majorant for a corrector borrowed from another sample: with a Taylor remainder
bound $r$ and
$\|K-h\|\le u$, $\|G-h\|\le v$, the borrowed-frame residual is at most $r+(u+v)(q+\tau^2/2)L$. -/
theorem norm_borrowed_residual_profile {K G h D Ybar : 𝕄} (hh : h.IsHermitian)
    {q L τ r u v : ℝ} (hD : ‖D‖ ≤ L)
    (hcenter : ‖frameExtension h D Ybar (1 / 2)‖ ≤ q * L)
    (hr : ‖K - G - τ • D‖ ≤ r) (hu : ‖K - h‖ ≤ u) (hv : ‖G - h‖ ≤ v) :
    ‖K-G-τ • D-I • ((K-h)*frameExtension h D Ybar (τ+1/2)-
      frameExtension h D Ybar (τ+1/2)*(G-h))‖ ≤ r+(u+v)*(q+τ^2/2)*L := by
  have hy := norm_frameExtension_le_center_profile hh hD hcenter τ
  calc _ ≤ ‖K-G-τ • D‖+‖I • ((K-h)*frameExtension h D Ybar (τ+1/2)-
        frameExtension h D Ybar (τ+1/2)*(G-h))‖ := norm_sub_le _ _
    _ = ‖K-G-τ • D‖+‖(K-h)*frameExtension h D Ybar (τ+1/2)-
        frameExtension h D Ybar (τ+1/2)*(G-h)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ r+(u*((q+τ^2/2)*L)+((q+τ^2/2)*L)*v) :=
      add_le_add hr ((norm_sub_le _ _).trans
        (add_le_add (norm_mul_le_of_le hu hy) (norm_mul_le_of_le hy hv)))
    _ = _ := by ring

end UnitaryProducts.Dressed
