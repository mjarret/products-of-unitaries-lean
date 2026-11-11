/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.EndpointFrame
public import UnitaryProducts.Corrector.FrameBounds

/-!
# The constants at width `π`

## Declarations

- `frameBound_center_pi`
- `frameBound_frameLip_pi`
-/

@[expose] public section

open Real
noncomputable section
namespace UnitaryProducts.Corrector

/-- $\mathcal N(\pi)=1/\pi^2$ and $2\mathcal N'(\pi)=1/(2\pi)-4/\pi^3$, which enter the
coefficients of Theorem B.

Reading the statement against the paper:
* `frameBound` and `frameLip` are $\mathcal N$ and $\mathcal N'$ on $[0,2\pi)$
  (`paper_series_eq`); $\pi$ lies inside the disc of convergence, so neither `tsum` is a junk
  value.

The proof follows the paper's: evaluate the closed form
$\mathcal N(x)=(1-(x/2)\cot(x/2))/x^2$ at $\pi$, where $\cot(\pi/2)=0$; for the derivative,
differentiate the closed form near $\pi$ and identify the derivative with `frameLip`
(`hasDerivAt_frameMult`). -/
theorem frameBound_frameLip_pi :
    frameBound π=1/π^2 ∧ 2*frameLip π=1/(2*π)-4/π^3 := by
  have hp : |π| < 2*π := by rw [abs_of_pos pi_pos]; linarith [pi_pos]
  have hv : frameMult π=1/π^2 := by
    simp only [frameMult, if_neg pi_ne_zero, Real.cot_eq_cos_div_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_div, mul_zero, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [← abs_of_pos pi_pos, frameBound_abs_eq_frameMult hp, abs_of_pos pi_pos, hv]
  · let f : ℝ → ℝ := fun x ↦ (1-(x/2)*(Real.cos (x/2)/Real.sin (x/2)))/x^2
    have he : frameMult =ᶠ[nhds π] f := by
      filter_upwards [eventually_ne_nhds pi_ne_zero] with x hx
      simp only [frameMult, if_neg hx, Real.cot_eq_cos_div_sin, f]
    have hh := (hasDerivAt_id π).div_const 2
    have hd := ((hasDerivAt_const π (1:ℝ)).sub
      (hh.mul (hh.cos.div hh.sin (by simp only [id_eq, Real.sin_pi_div_two]; norm_num)))).div
        ((hasDerivAt_id π).pow 2) (pow_ne_zero _ pi_ne_zero)
    have hd' : HasDerivAt f (1/(4*π)-2/π^3) π := by
      convert hd using 1
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      field_simp; ring
    rw [(hasDerivAt_frameMult hp).unique (he.hasDerivAt_iff.mpr hd')]
    ring

/-- The value $c_0=(\pi-2)/(2\pi^2)$ of the constant $c_0$ of Theorem 4.2 at width $\pi$ and, with
`frameBound_frameLip_pi`, $\mathcal N(\pi/2)=(4-\pi)/\pi^2$; they enter the coefficients of
Theorem B.

Reading the statement against the paper:
* `frameBound` is $\mathcal N$ on $[0,2\pi)$, and $1/(2\pi)-1/\pi^2=(\pi-2)/(2\pi^2)$.

The proof follows the paper's: the half-angle identity $\cot(x/4)-\cot(x/2)=1/\sin(x/2)$ gives
$\mathcal N(x)-\mathcal N(x/2)/2=1/(2x\sin(x/2))-1/x^2$ (`two_frameMult_sub_half_pi`), evaluated at
$x=\pi$. -/
theorem frameBound_center_pi : frameBound π-frameBound (π/2)/2=1/(2*π)-1/π^2 := by
  have hp : |π| < 2*π := by rw [abs_of_pos pi_pos]; linarith [pi_pos]
  have hh : |π/2| < 2*π := by rw [abs_of_pos (by positivity)]; linarith [pi_pos]
  have he := two_frameMult_sub_half_pi
  rw [← frameBound_abs_eq_frameMult hp, ← frameBound_abs_eq_frameMult hh,
    abs_of_pos pi_pos, abs_of_pos (by positivity : 0 < π/2)] at he
  rw [show (1:ℝ)/(2*π)=(1/π)/2 by ring]
  ring_nf at he ⊢
  linarith

end UnitaryProducts.Corrector
