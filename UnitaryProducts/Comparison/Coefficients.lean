/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.FrameDerivativeBounds
public import UnitaryProducts.Comparison.EndpointCoefficients
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Corrector.BernoulliBounds

/-!
# Width-`π` coefficients of the `C²` unit-step comparison

## Declarations

- `unitC1`
- `unitC1_ge`
- `unitC2`
- `unit_constants_bounds`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The coefficient of the step maxima of $\|H''\|$ at width $\pi$: the larger of the end-step
value $1/8$ and the interior value $1/24+\mathcal N(\pi)=1/24+1/\pi^2$. A closed real number. -/
def unitC1 : ℝ := max (1/8) (1/24+1/π^2)

/-- The coefficient of the step maxima of $\|H'\|^2$ at width $\pi$: the larger of the end-step
value $1/24+c_0$ and the interior value $c_0/4+1/64+2\mathcal N'(\pi)$, with
$c_0=1/(2\pi)-1/\pi^2$; `frameLip π` is $\mathcal N'(\pi)$. A closed real number. -/
def unitC2 : ℝ := max (1/24+(1/(2*π)-1/π^2)) ((1/(2*π)-1/π^2)/4+1/64+2*frameLip π)

/-- Numerical bounds on the width-$\pi$ constants: $c_0=1/(2\pi)-1/\pi^2=1/16-(1/\pi-1/4)^2<1/16$,
`unitC1` $<1/6$ (as $\pi^2>8$), and `unitC2` $<1/8$ (as $\pi^2<10$ gives
$2\mathcal N'(\pi)=(1-8/\pi^2)/(2\pi)<1/(10\pi)$). -/
theorem unit_constants_bounds :
    1/(2*π)-1/π^2 = 1/16-(1/π-1/4)^2 ∧ 1/(2*π)-1/π^2 < (1/16:ℝ) ∧
      unitC1 < 1/6 ∧ unitC2 < 1/8 := by
  have hp : 0 < π := pi_pos
  have h3 : 3 < π := pi_gt_three
  have h315 : π < 3.15 := pi_lt_d2
  have hsq : 1/(2*π)-1/π^2 = 1/16-(1/π-1/4)^2 := by field_simp; ring
  have hx4 : (1/4:ℝ) < 1/π := one_div_lt_one_div_of_lt hp (by linarith)
  have hc0 : 1/(2*π)-1/π^2 < (1/16:ℝ) := by
    rw [hsq]
    linarith [pow_pos (sub_pos.mpr hx4) 2]
  have h9 : (9:ℝ) < π^2 := by linarith [pow_lt_pow_left₀ h3 (by norm_num : (0:ℝ) ≤ 3) two_ne_zero]
  have h10 : π^2 < (10:ℝ) := by linarith [pow_lt_pow_left₀ h315 hp.le two_ne_zero]
  have hinv8 : 1/π^2 < (1/8:ℝ) := one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have hx3 : 1/π < (1/3:ℝ) := one_div_lt_one_div_of_lt (by norm_num) h3
  have hx0 : 0 < 1/π := one_div_pos.mpr hp
  have hx2 : (1/10:ℝ) < (1/π)^2 := by
    rw [div_pow, one_pow]
    exact one_div_lt_one_div_of_lt (pow_pos hp 2) h10
  have hlip : 2*frameLip π < (1/30:ℝ) := by
    have he : (1/(2*π)-4/π^3:ℝ) = (1/π)*(1/2-4*(1/π)^2) := by field_simp
    rw [frameBound_frameLip_pi.2, he]
    linarith [mul_lt_mul_of_pos_left (by linarith : 1/2-4*(1/π)^2 < (1/10:ℝ)) hx0]
  refine ⟨hsq, hc0, max_lt (by norm_num) (by linarith), max_lt (by linarith) (by linarith)⟩

/-- `unitC1` bounds both of its end-step and interior coefficients. -/
theorem unitC1_ge : (1/8:ℝ) ≤ unitC1 ∧ 1/24+1/π^2 ≤ unitC1 :=
  ⟨le_max_left _ _, le_max_right _ _⟩


end UnitaryProducts.Paper
