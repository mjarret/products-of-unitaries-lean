/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.LogarithmDerivativeBounds

/-!
# the spectral comparison and supporting bounds for the walk comparison

## Declarations

- `frameBound_eq_closed`
- `frameBound_sub_div_eq_integral`
- `frameLip_eq_closed`
- `walkConstant`
- `walkFrameSharp`
- `walkUnitCoefficientSharp`
- `walk_c0_bounds`
- `walk_constant_limit`
- `paper_mean_slope_eq`
- `tendsto_mul_frameBound_half`
- `tendsto_nhdsGT_of_continuousAt`
- `walk_asymptotics`
- `walk_reflect`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter UnitaryProducts.Corrector
noncomputable section

namespace UnitaryProducts.Paper
open UnitaryProducts

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

variable [NeZero d]

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts

/-- The coefficient $\eta = 2S(\kappa\mathcal N'(w) + 2S\int_0^1\mathcal N'(tw)\,dt)$ of the
spectral comparison,
with $S$ = `walkLogSlope w`, $\kappa$ = `walkLogSlope (w/2)`, $\mathcal N$ = `frameBound` and
$\mathcal N'$ = `frameLip`. The mean slope $\int_0^1\mathcal N'(tw)\,dt$ is written here as
$(\mathcal N(w) - 1/12)/w$ (`frameBound_sub_div_eq_integral`); both are `0` at $w = 0$
(`x / 0 = 0`). Every use assumes $0 \le w < 2\pi$, where the series converge. -/
def walkFrameSharp (w : ℝ) : ℝ :=
  2*walkLogSlope (w/2)*walkLogSlope w*frameLip w+
    4*(walkLogSlope w)^2*(frameBound w-1/12)/w

/-- The endpoint coefficient satisfies $0≤c_0≤\mathcal N(w)$; useful for common-coefficient
bounds. -/
theorem walk_c0_bounds {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ frameBound w-frameBound (w/2)/2 ∧ frameBound w-frameBound (w/2)/2 ≤ frameBound w := by
  have hh0 : 0 ≤ w/2 := div_nonneg hw0 two_pos.le
  have hmono := frameBound_mono hh0 (half_le_self hw0) hw
  have hnn := frameBound_nonneg hh0
  exact ⟨sub_nonneg.mpr ((half_le_self hnn).trans hmono), sub_le_self _ (div_nonneg hnn two_pos.le)⟩

/-- The mean slope of $\mathcal N$ on $[0, w]$ (the spectral comparison):
$\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ for $0 \le w < 2\pi$, both sides $0$ at
$w = 0$. The proof substitutes $x = tw$ and integrates $\mathcal N' = $ `frameLip`, the derivative
of $\mathcal N$ = `frameBound` (`hasDerivAt_frameBound`), from $\mathcal N(0) = 1/12$; $\mathcal N'$
is integrable as a nonnegative derivative. -/
theorem frameBound_sub_div_eq_integral {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (frameBound w - 1/12)/w = ∫ t in (0:ℝ)..1, frameLip (t*w) := by
  rcases eq_or_lt_of_le hw0 with h | h
  · -- At `w = 0` both sides are `0`: `x / 0 = 0`, and `𝒩'(0) = 0`.
    subst h
    simp only [div_zero, mul_zero, frameLip_zero, intervalIntegral.integral_zero]
  · have hw' : w ≠ 0 := h.ne'
    rw [intervalIntegral.integral_comp_mul_right frameLip hw', zero_mul, one_mul, smul_eq_mul]
    have hder : ∀ x ∈ uIcc (0:ℝ) w, HasDerivAt frameBound (frameLip x) x := by
      intro x hx
      rw [uIcc_of_le hw0] at hx
      exact hasDerivAt_frameBound (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    have hint : IntervalIntegrable frameLip volume 0 w := by
      refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := frameBound)
        (fun x hx ↦ (hder x hx).continuousAt.continuousWithinAt) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · rw [min_eq_left hw0, max_eq_right hw0] at hx
        exact hder x (by rw [uIcc_of_le hw0]; exact Ioo_subset_Icc_self hx)
      · rw [min_eq_left hw0, max_eq_right hw0] at hx
        exact frameLip_nonneg hx.1.le
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, frameBound_zero]
    field_simp

/-- The paper's series $\mathcal N(x) = \sum_{n\ge1}2/(4\pi^2n^2 - x^2)$ has mean slope
$\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ on $[0, w]$, $0 \le w < 2\pi$. -/
private theorem paper_mean_slope_eq {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    ∫ t in (0:ℝ)..1, deriv (fun y : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-y^2)) (t*w) =
      (frameBound w - 1/12)/w := by
  rw [frameBound_sub_div_eq_integral hw0 hw]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact (paper_series_eq (mul_nonneg ht.1 hw0)
    (lt_of_le_of_lt (mul_le_of_le_one_left hw0 ht.2) hw)).2

/-- The closed form (eq:N-def) of $\mathcal N$ on $(0, 2\pi)$:
$\mathcal N(x) = (1 - (x/2)\cot(x/2))/x^2$. -/
theorem frameBound_eq_closed {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameBound x = (1-(x/2)*Real.cot (x/2))/x^2 :=
  Corrector.frameBound_eq_closedForm hx0 hx

/-- The derivative of (eq:N-def) on $(0, 2\pi)$ (proof of the walk comparison):
$\mathcal N'(x) = -2/x^3 + \cot(x/2)/(2x^2) + 1/(4x\sin^2(x/2))$. The proof differentiates
$1/x^2 - \cos(x/2)/(2x\sin(x/2))$, which is `frameMult` near $x$, and compares with
`hasDerivAt_frameMult`. -/
theorem frameLip_eq_closed {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameLip x = -2/x^3+Real.cot (x/2)/(2*x^2)+1/(4*x*Real.sin (x/2)^2) := by
  have ha : |x| < 2 * π := by rwa [abs_of_pos hx0]
  have hsx : 0 < Real.sin (x/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- The closed form agrees with `frameMult` near `x`.
  have hev : (fun y ↦ 1/y^2 - Real.cos (y/2)/(2*y*Real.sin (y/2))) =ᶠ[𝓝 x] frameMult := by
    filter_upwards [lt_mem_nhds hx0] with y hy
    rw [frameMult, if_neg hy.ne', Real.cot_eq_cos_div_sin]
    field_simp
  have hs : HasDerivAt (fun y : ℝ ↦ Real.sin (y/2)) (Real.cos (x/2) * (1/2)) x :=
    ((hasDerivAt_id' x).div_const 2).sin
  have hc : HasDerivAt (fun y : ℝ ↦ Real.cos (y/2)) (-Real.sin (x/2) * (1/2)) x :=
    ((hasDerivAt_id' x).div_const 2).cos
  have hden : HasDerivAt (fun y : ℝ ↦ 2*y*Real.sin (y/2))
      (2*1*Real.sin (x/2) + 2*x*(Real.cos (x/2) * (1/2))) x :=
    ((hasDerivAt_id' x).const_mul 2).mul hs
  have hq : HasDerivAt (fun y : ℝ ↦ 1/y^2) (-(2*x)/(x^2)^2) x := by
    simpa [one_div] using (hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0.ne')
  have hne : 2*x*Real.sin (x/2) ≠ 0 := by positivity
  have hf := (hq.sub (hc.div hden hne)).congr_of_eventuallyEq hev.symm
  rw [(hasDerivAt_frameMult ha).unique hf, Real.cot_eq_cos_div_sin]
  field_simp
  linear_combination (4*x^2) * Real.sin_sq_add_cos_sq (x/2)

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
variable [NeZero d]

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A common coefficient for the supporting mesh comparison `walk_unit_comparison_sharp`:
$(1/8+c_2+\mathcal N(w))S^2+\eta$, with $c_2=\mathcal N(w)-\mathcal N(w/2)/2+1/24$.
the walk comparison keeps separate coefficients, proved by
`UnitaryProducts.Prose.walk_comparison_jrs`.
Every use assumes $0\le w<2\pi$. -/
def walkUnitCoefficientSharp (w : ℝ) : ℝ :=
  (1/8+(frameBound w-frameBound (w/2)/2+1/24)+frameBound w)*(walkLogSlope w)^2+walkFrameSharp w

/-- The common coefficient of `unit_step_walk_comparison_max`, in the omitted-arc length:
$(1/8+c_2+\mathcal N(w))S^2+\eta$ with $w=2\pi-\vartheta$.
It bounds the separate coefficients in `UnitaryProducts.Prose.walk_comparison_jrs`.
Every use assumes $0<\vartheta\le2\pi$. -/
def walkConstant (ϑ : ℝ) : ℝ :=
  (1/8+(frameBound (2*π-ϑ)-frameBound ((2*π-ϑ)/2)/2+1/24)+frameBound (2*π-ϑ))*
    (walkLogSlope (2*π-ϑ))^2+walkFrameSharp (2*π-ϑ)

/-- A function continuous at `0` tends to its value there from the right. -/
private theorem tendsto_nhdsGT_of_continuousAt {f : ℝ → ℝ} {L : ℝ} (hf : ContinuousAt f 0)
    (h0 : f 0 = L) : Tendsto f (𝓝[>] 0) (𝓝 L) :=
  h0 ▸ hf.tendsto.mono_left nhdsWithin_le_nhds

/-- `sin(φ/2) = (φ/2) sinc(φ/2)`, and at `w = 2π - φ` the reflections `sin(w/2) = sin(φ/2)`,
`cos(w/2) = -cos(φ/2)`, `sin(w/4) = cos(φ/4)`. -/
private theorem walk_reflect {φ : ℝ} (hφ : φ ≠ 0) :
    Real.sin (φ/2) = φ/2*Real.sinc (φ/2) ∧
    Real.sin ((2*π-φ)/2) = Real.sin (φ/2) ∧
    Real.cos ((2*π-φ)/2) = -Real.cos (φ/2) ∧
    Real.sin ((2*π-φ)/2/2) = Real.cos (φ/4) := by
  have e1 : (2*π-φ)/2 = π-φ/2 := by ring
  have e2 : (2*π-φ)/2/2 = π/2-φ/4 := by ring
  refine ⟨?_, by rw [e1, Real.sin_pi_sub], by rw [e1, Real.cos_pi_sub],
    by rw [e2, Real.sin_pi_div_two_sub]⟩
  rw [Real.sinc_of_ne_zero (div_ne_zero hφ two_ne_zero)]
  field_simp

/-- The asymptotics in the proof of the walk comparison, at $w = 2\pi - \vartheta$ as $\vartheta
\to 0^+$:
$\vartheta S \to 2\pi$, $\kappa \to \pi/2$, $\vartheta\mathcal N(w) \to 1/(2\pi)$, and
$\vartheta^2\mathcal N'(w) \to 1/(2\pi)$. Each quantity is, for $0 < \vartheta < \pi$, a function
continuous at $0$ written with $\operatorname{sinc}(\vartheta/2) = \sin(\vartheta/2)/(\vartheta/2)$,
by the closed forms of $S$, (eq:N-def), and its derivative (`frameLip_eq_closed`), with
$\sin(w/2) = \sin(\vartheta/2)$ and $\cot(w/2) = -\cot(\vartheta/2)$. -/
private theorem walk_asymptotics :
    Tendsto (fun φ ↦ φ*walkLogSlope (2*π-φ)) (𝓝[>] 0) (𝓝 (2*π)) ∧
    Tendsto (fun φ ↦ walkLogSlope ((2*π-φ)/2)) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun φ ↦ φ*frameBound (2*π-φ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun φ ↦ φ^2*frameLip (2*π-φ)) (𝓝[>] 0) (𝓝 (1/(2*π))) := by
  have hpi := pi_pos
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hsinc : ContinuousAt (fun φ : ℝ ↦ Real.sinc (φ/2)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 2)).continuousAt
  have hw : ContinuousAt (fun φ : ℝ ↦ 2*π-φ) 0 := continuousAt_const.sub continuousAt_id
  have hw0 : (2*π-0) ≠ 0 := by linarith
  have hc2 : ContinuousAt (fun φ : ℝ ↦ Real.cos (φ/2)) 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt
  have hc4 : ContinuousAt (fun φ : ℝ ↦ Real.cos (φ/4)) 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 4)).continuousAt
  have hs0 : Real.sinc ((0:ℝ)/2) ≠ 0 := by rw [zero_div, Real.sinc_zero]; norm_num
  -- At `0 < φ < π`: `sin(φ/2) > 0`, so `sinc(φ/2) ≠ 0`, and `w = 2π - φ ∈ (π, 2π)`.
  have hpos : ∀ φ ∈ Ioo 0 π, Real.sinc (φ/2) ≠ 0 ∧ 0 < 2*π-φ ∧ 2*π-φ < 2*π := by
    intro φ hφ
    obtain ⟨h1, -, -, -⟩ := walk_reflect hφ.1.ne'
    have hs : 0 < Real.sin (φ/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1])
      (by linarith [hφ.2])
    refine ⟨fun h ↦ ?_, by linarith [hφ.2], by linarith [hφ.1]⟩
    rw [h, mul_zero] at h1
    exact hs.ne' h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- φS(w) = (2π - φ)/sinc(φ/2).
    have hA : ContinuousAt (fun φ : ℝ ↦ (2*π-φ)/Real.sinc (φ/2)) 0 := hw.div hsinc hs0
    refine (tendsto_nhdsGT_of_continuousAt hA
      (by rw [zero_div, Real.sinc_zero]; ring)).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, -, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [walkLogSlope_eq_sinBound hwp hw2, sinBound, h2, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    field_simp
  · -- κ = (π/2 - φ/4)/cos(φ/4).
    have hA : ContinuousAt (fun φ : ℝ ↦ (2*π-φ)/4/Real.cos (φ/4)) 0 :=
      (hw.div_const 4).div hc4 (by rw [zero_div, Real.cos_zero]; norm_num)
    refine (tendsto_nhdsGT_of_continuousAt hA (by rw [zero_div, Real.cos_zero]; ring)).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨-, -, -, h4⟩ := walk_reflect hφ.1.ne'
    obtain ⟨-, hwp, hw2⟩ := hpos φ hφ
    rw [walkLogSlope_eq_sinBound (by linarith) (by linarith), sinBound, h4]
    ring
  · -- φ𝒩(w) = φ/w² + cos(φ/2)/(sinc(φ/2) w).
    have hA : ContinuousAt
        (fun φ : ℝ ↦ φ/(2*π-φ)^2+Real.cos (φ/2)/(Real.sinc (φ/2)*(2*π-φ))) 0 :=
      (continuousAt_id.div (hw.pow 2) (pow_ne_zero 2 hw0)).add
        (hc2.div (hsinc.mul hw) (mul_ne_zero hs0 hw0))
    have h0 : (0:ℝ)/(2*π-0)^2+Real.cos (0/2)/(Real.sinc (0/2)*(2*π-0)) = 1/(2*π) := by
      simp only [zero_div, Real.sinc_zero, Real.cos_zero, sub_zero, zero_add]; field_simp
    refine (tendsto_nhdsGT_of_continuousAt hA h0).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, h3, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [frameBound_eq_closed hwp hw2, Real.cot_eq_cos_div_sin, h2, h3, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    generalize Real.cos (φ/2) = γ
    field_simp
    ring
  · -- φ²𝒩'(w) = -2φ²/w³ - φcos(φ/2)/(w² sinc(φ/2)) + 1/(w sinc(φ/2)²).
    have hA : ContinuousAt (fun φ : ℝ ↦ -2*φ^2/(2*π-φ)^3-
        φ*Real.cos (φ/2)/((2*π-φ)^2*Real.sinc (φ/2))+1/((2*π-φ)*Real.sinc (φ/2)^2)) 0 :=
      (((continuousAt_const.mul (continuousAt_id.pow 2)).div (hw.pow 3) (pow_ne_zero 3 hw0)).sub
        ((continuousAt_id.mul hc2).div ((hw.pow 2).mul hsinc)
          (mul_ne_zero (pow_ne_zero 2 hw0) hs0))).add
        (continuousAt_const.div (hw.mul (hsinc.pow 2)) (mul_ne_zero hw0 (pow_ne_zero 2 hs0)))
    have h0 : -2*(0:ℝ)^2/(2*π-0)^3-0*Real.cos (0/2)/((2*π-0)^2*Real.sinc (0/2))+
        1/((2*π-0)*Real.sinc (0/2)^2) = 1/(2*π) := by
      simp only [zero_div, Real.sinc_zero, Real.cos_zero, sub_zero]; field_simp; ring
    refine (tendsto_nhdsGT_of_continuousAt hA h0).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, h3, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [frameLip_eq_closed hwp hw2, Real.cot_eq_cos_div_sin, h2, h3, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    generalize Real.cos (φ/2) = γ
    field_simp
    ring

/-- $\vartheta\,\mathcal N(w/2) \to 0$ as $\vartheta \to 0^+$, with $w = 2\pi - \vartheta$: by the
pole bound, $1/12 \le \mathcal N(w/2) \le \pi/(6(2\pi - w/2)) \le 1/6$ for $0 < \vartheta < \pi$. -/
private theorem tendsto_mul_frameBound_half :
    Tendsto (fun φ ↦ φ*frameBound ((2*π-φ)/2)) (𝓝[>] 0) (𝓝 0) := by
  have hpi := pi_pos
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hid : Tendsto (fun φ : ℝ ↦ φ) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have h6 := hid.div_const 6
  rw [zero_div] at h6
  refine squeeze_zero' ?_ ?_ h6
  · filter_upwards [hev] with φ hφ
    have h12 := one_div_twelve_le_frameBound (w := (2*π-φ)/2) (by linarith [hφ.2])
      (by linarith [hφ.1])
    exact mul_nonneg hφ.1.le (by linarith)
  · filter_upwards [hev] with φ hφ
    have hp := frameBound_le_pole (w := (2*π-φ)/2) (by linarith [hφ.2]) (by linarith [hφ.1])
    have hq : π/(6*(2*π-(2*π-φ)/2)) ≤ π/(6*π) :=
      div_le_div_of_nonneg_left hpi.le (by positivity) (by linarith [hφ.1])
    have he : π/(6*π) = 1/6 := by field_simp
    exact (mul_le_mul_of_nonneg_left ((hp.trans hq).trans_eq he) hφ.1.le).trans_eq (by ring)

/-- The closed forms and asymptotics the last paragraph of the proof of the walk comparison uses,
and the
order of the larger constant `walkConstant`: $(\frac18 + c_2 + \mathcal N(w))S^2 + \eta$ times
$\vartheta^3$ tends to $5\pi + 4$ as $\vartheta \to 0^+$. With $w = 2\pi - \vartheta$:
* (eq:N-def) and its derivative on $(0, 2\pi)$:
  $\mathcal N(x) = (1 - (x/2)\cot(x/2))/x^2$ and
  $\mathcal N'(x) = -2/x^3 + \cot(x/2)/(2x^2) + 1/(4x\sin^2(x/2))$;
* the mean slope $\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ for $0 < w < 2\pi$;
* $\vartheta S \to 2\pi$, $\kappa \to \pi/2$, $\vartheta\mathcal N(w) \to 1/(2\pi)$,
  $\vartheta^2\mathcal N'(w) \to 1/(2\pi)$,
  $\vartheta\int_0^1\mathcal N'(tw)\,dt \to 1/(4\pi^2)$, and
  $\vartheta c_2 \to 1/(2\pi)$ for $c_2 = \mathcal N(w) - \mathcal N(w/2)/2 + 1/24$ of Theorem 4.2,
  as $\mathcal N(w/2)$ stays bounded;
* `walkConstant ϑ`$\cdot\vartheta^3 \to 0 + 4\pi + \pi + 4$, from its four terms $S^2/8$,
  $(c_2 + \mathcal N(w))S^2$, $2\kappa S\mathcal N'(w)$, and $4S^2\int_0^1\mathcal N'(tw)\,dt$
  (`walk_constant_chord_limit` gives the limit for $c_3$ in the walk comparison).

Reading the statement against the paper: `N` is the partial-fraction series, equal to (eq:N-def) on
$[0, 2\pi)$ (`periodicCorrector_N_trig`), so `deriv N` is $\mathcal N'$ there; `S x` is
the paper's $g(x)=(x/2)/\sin(x/2)$, with $g(0)=1$, so `S (2*π-ϑ)` is $S$ and `S ((2*π-ϑ)/2)` is
$\kappa$;
`𝓝[>] 0` is the limit $\vartheta \to 0^+$; and `walkConstant ϑ` is the larger constant, whose
value in these terms is the second conjunct of `unit_step_walk_comparison_max`. -/
theorem walk_constant_limit :
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    (∀ x : ℝ, 0 < x → x < 2*π → N x = (1-(x/2)*Real.cot (x/2))/x^2 ∧
      deriv N x = -2/x^3+Real.cot (x/2)/(2*x^2)+1/(4*x*Real.sin (x/2)^2)) ∧
    (∀ w : ℝ, 0 < w → w < 2*π → ∫ t in (0:ℝ)..1, deriv N (t*w) = (N w-1/12)/w) ∧
    Tendsto (fun ϑ ↦ ϑ*S (2*π-ϑ)) (𝓝[>] 0) (𝓝 (2*π)) ∧
    Tendsto (fun ϑ ↦ S ((2*π-ϑ)/2)) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun ϑ ↦ ϑ*N (2*π-ϑ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ ϑ^2*deriv N (2*π-ϑ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ ϑ*∫ t in (0:ℝ)..1, deriv N (t*(2*π-ϑ))) (𝓝[>] 0) (𝓝 (1/(4*π^2))) ∧
    Tendsto (fun ϑ ↦ ϑ*(N (2*π-ϑ)-N ((2*π-ϑ)/2)/2+1/24)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ walkConstant ϑ*ϑ^3) (𝓝[>] 0) (𝓝 (5*π+4)) := by
  intro N S
  have hpi := pi_pos
  obtain ⟨hS, hκ, hN, hN'⟩ := walk_asymptotics
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hNx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : N x = frameBound x := (paper_series_eq hx0 hx).1
  have hDx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : deriv N x = frameLip x :=
    (paper_series_eq hx0 hx).2
  have hIx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) :
      ∫ t in (0:ℝ)..1, deriv N (t*x) = (frameBound x-1/12)/x := paper_mean_slope_eq hx0 hx
  have hSx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : S x = walkLogSlope x := walkLogSlope_closed hx0 hx
  have hid : Tendsto (fun φ : ℝ ↦ φ) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hwlim : Tendsto (fun φ : ℝ ↦ 2*π-φ) (𝓝[>] 0) (𝓝 (2*π)) := by
    simpa using tendsto_const_nhds.sub hid
  -- φ(𝒩(w) - 1/12)/w → (1/(2π))/(2π) = 1/(4π²).
  have hQ : Tendsto (fun φ ↦ φ*((frameBound (2*π-φ)-1/12)/(2*π-φ))) (𝓝[>] 0)
      (𝓝 (1/(4*π^2))) := by
    have h := (hN.sub (hid.div_const 12)).div hwlim (by positivity)
    have e : (1/(2*π)-0/12)/(2*π) = 1/(4*π^2) := by field_simp; ring
    rw [e] at h
    exact h.congr fun φ ↦ by simp only [Pi.div_apply]; ring
  -- φc₂ = φ𝒩(w) - φ𝒩(w/2)/2 + φ/24 → 1/(2π), as φ𝒩(w/2) → 0.
  have hC : Tendsto (fun φ ↦ φ*frameBound (2*π-φ)-φ*frameBound ((2*π-φ)/2)/2+φ/24) (𝓝[>] 0)
      (𝓝 (1/(2*π))) := by
    have h := (hN.sub (tendsto_mul_frameBound_half.div_const 2)).add (hid.div_const 24)
    rw [zero_div, zero_div, sub_zero, add_zero] at h
    exact h
  refine ⟨fun x hx0 hx ↦ ⟨(hNx x hx0.le hx).trans (frameBound_eq_closed hx0 hx),
      (hDx x hx0.le hx).trans (frameLip_eq_closed hx0 hx)⟩,
    fun w hw0 hw ↦ (hIx w hw0.le hw).trans (by rw [hNx w hw0.le hw]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hS.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hSx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hκ.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hSx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hN.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hNx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hN'.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hDx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hQ.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hIx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hC.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hNx _ (by linarith [hφ.2]) (by linarith [hφ.1]),
      hNx ((2*π-φ)/2) (by linarith [hφ.2]) (by linarith [hφ.1])]
    ring
  · -- c(φ)φ³ = (φS)²φ/8 + (φS)²(φc₂ + φ𝒩) + 2(φS)κ(φ²𝒩') + 4(φS)²(φ·mean slope).
    have h := ((((hS.pow 2).mul hid).const_mul (1/8)).add
      ((hS.pow 2).mul (hC.add hN))).add
      ((((hS.mul hκ).mul hN').const_mul 2).add (((hS.pow 2).mul hQ).const_mul 4))
    have e : 1/8*((2*π)^2*0)+(2*π)^2*(1/(2*π)+1/(2*π))+
        (2*(2*π*(π/2)*(1/(2*π)))+4*((2*π)^2*(1/(4*π^2)))) = 5*π+4 := by
      field_simp; ring
    rw [e] at h
    refine h.congr fun φ ↦ ?_
    unfold walkConstant walkFrameSharp
    ring

end UnitaryProducts.Paper
