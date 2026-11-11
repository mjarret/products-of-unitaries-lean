/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import UnitaryProducts.Comparison.EndpointFrame
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Hessian of the walk logarithm

## Declarations

- `Prose.chord_cut_contradiction`
- `Prose.chord_mem_slitPlane`
- `cfc_unit_chord`
- `chord_ne_zero_of_slitPlane`
- `continuousOn_walkLogResolvent`
- `contDiffOn_walkLogResolvent`
- `walkLogResolvent_mul_sub`
- `Prose.integral_log_chord`
- `hasDerivAt_integral_compact_rectangle`
- `hasDerivAt_walkLogDerivativeIntegral`
- `hasDerivAt_walkLogIntegral`
- `hasDerivWithinAt_ringInverse_path`
- `hasDerivWithinAt_walkLogIntegrand`
- `hasDerivWithinAt_walkLogResolvent`
- `hasDerivWithinAt_walkLogSandwich`
- `isStarNormal_evol_one`
- `norm_inv_unit_chord_le`
- `norm_sq_unit_chord`
- `norm_walkLogHessian_integral_le`
- `norm_walkLogHessian_integrand_le`
- `spectrum_evol_one_eq_exp_real`
- `spectrum_evol_one_subset_slitPlane`
- `walkLogDenom_halfAngle`
- `walkLogDenom_pos`
- `walkLogHessian_identity`
- `walkLogIntegral`
- `walkLogIntegral_eq_cfc`
- `walkLogIntegral_evol`
- `walkLogResolvent`
- `walkLogSlope`
- `walkLogSlope_eq_sinBound`
- `walkLogSlope_nonneg`
- `walkLogSlope_closed`
- `walkLogSlope_zero`
-/

@[expose] public section

open Real Set UnitaryProducts.Corrector Complex
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace UnitaryProducts

/-- The paper's $S = (w/2)/\sin(w/2)$, written as $1 + w^2(\mathcal N(w) - \mathcal N(w/2)/2)$ with
`frameBound` for $\mathcal N$, so that it is continuous at $0$ with value $1$ (the paper's
$g(0)=1$); `walkLogSlope_eq_sinBound` gives the closed form on $(0, 2\pi)$. Every use assumes
$0 \le w < 2\pi$; for $|w| \ge 2\pi$ the series of `frameBound w` diverges and `tsum` returns `0`.
-/
def walkLogSlope (w : ℝ) : ℝ :=
  1 + w ^ 2 * (frameBound w - frameBound (w / 2) / 2)

/-- $S = 1$ at $w = 0$. -/
theorem walkLogSlope_zero : walkLogSlope 0 = 1 := by
  simp [walkLogSlope]

/-- On $(0, 2\pi)$, `walkLogSlope w` is $(w/2)/\sin(w/2)$ (`sinBound`). -/
theorem walkLogSlope_eq_sinBound {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) :
    walkLogSlope w = sinBound w := by
  have ha : |w| < 2 * π := by rwa [abs_of_pos hw0]
  have hah : |w / 2| < 2 * π := by rw [abs_of_pos (half_pos hw0)]; linarith
  have hfw : frameBound w = frameMult w := by
    simpa only [abs_of_pos hw0] using frameBound_abs_eq_frameMult ha
  have hfwh : frameBound (w / 2) = frameMult (w / 2) := by
    simpa only [abs_of_pos (half_pos hw0)] using frameBound_abs_eq_frameMult hah
  rw [walkLogSlope, hfw, hfwh, frameMult_sub_half hw0 hw, sinBound]
  have hs := (Real.sin_pos_of_pos_of_lt_pi (half_pos hw0) (by linarith : w / 2 < π)).ne'
  field_simp; ring

/-- The closed sine quotient is the logarithm slope, including zero width. -/
theorem walkLogSlope_closed {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (if w = 0 then 1 else (w / 2) / Real.sin (w / 2)) = walkLogSlope w := by
  rcases eq_or_lt_of_le hw0 with h | h
  · subst w; simp [walkLogSlope_zero]
  · rw [if_neg h.ne', walkLogSlope_eq_sinBound h hw, sinBound]

/-- $S \ge 0$ on $[0, 2\pi)$. -/
theorem walkLogSlope_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ walkLogSlope w := by
  rcases eq_or_lt_of_le hw0 with he | hp
  · rw [← he, walkLogSlope_zero]; exact zero_le_one
  · rw [walkLogSlope_eq_sinBound hp hw]; exact sinBound_nonneg hp hw

section Resolvent

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The resolvent $Z_u = (1 + u(V - 1))^{-1}$ of the proof of Lemma A.2, along the segment from
$1$ to $V$. `Ring.inverse` returns `0` when $1 + u(V - 1)$ is not invertible; every use proves
invertibility first. -/
def walkLogResolvent (V : A) (t : ℝ) : A := Ring.inverse (1 + t • (V - 1))

omit [CompleteSpace A] in
/-- Lemma A.2: the division-free resolvent identity, valid also at `u = 0`. -/
theorem walkLogResolvent_mul_sub (V : A) (u : ℝ)
    (hu : IsUnit (1 + u • (V - 1))) :
    u • ((V - 1) * walkLogResolvent V u) = 1 - walkLogResolvent V u := by
  have hsum : walkLogResolvent V u + u • ((V - 1) * walkLogResolvent V u) = 1 := by
    rw [show walkLogResolvent V u + u • ((V - 1) * walkLogResolvent V u) =
        (1 + u • (V - 1)) * walkLogResolvent V u by
      rw [add_mul, one_mul, smul_mul_assoc]]
    exact Ring.mul_inverse_cancel _ hu
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hsum)

/-- Lemma A.2(ii): the resolvent is jointly `C²` in the path and chord parameters.
The inverse map is smooth on the units; the closed rectangle includes `u = 0`. -/
theorem contDiffOn_walkLogResolvent {V : ℝ → A} {S : Set ℝ}
    (hV : ContDiffOn ℝ 2 V S)
    (hu : ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ walkLogResolvent (V p.1) p.2)
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ V p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp contDiffOn_fst (fun p hp ↦ hp.1)
  have hh : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ 1 + p.2 • (V p.1 - 1))
      (S ×ˢ Icc (0 : ℝ) 1) :=
    contDiffOn_const.add (contDiffOn_snd.smul (hv.sub contDiffOn_const))
  intro p hp
  obtain ⟨v, hv⟩ := hu p.1 hp.1 p.2 hp.2
  have hi := contDiffAt_ringInverse (𝕜 := ℝ) (n := 2) v
  rw [hv] at hi
  exact hi.comp_contDiffWithinAt p (hh p hp)

/-- Lemma A.2(ii): the logarithm integrand is jointly `C²` in the path
and chord parameters, so compact integration preserves the path regularity. -/
theorem contDiffOn_walkLogIntegrand {V : ℝ → A} {S : Set ℝ}
    (hV : ContDiffOn ℝ 2 V S)
    (hu : ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ (V p.1 - 1) * walkLogResolvent (V p.1) p.2)
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hv : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ V p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp contDiffOn_fst (fun p hp ↦ hp.1)
  exact (hv.sub contDiffOn_const).mul (contDiffOn_walkLogResolvent hV hu)

/-- The inverse derivative in a form convenient for a real matrix path. -/
theorem hasDerivWithinAt_ringInverse_path {V : ℝ → A} {D : A} {s : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s) (hu : IsUnit (V s)) :
    HasDerivWithinAt (fun r ↦ Ring.inverse (V r))
      (-(Ring.inverse (V s) * D * Ring.inverse (V s))) S s := by
  obtain ⟨u, hu⟩ := hu
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  rw [hu] at hi
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← hu, Ring.inverse_unit] using hi.comp_hasDerivWithinAt s hV

/-- $\partial_s Z_u(V(s)) = -u\,Z_uV'Z_u$. -/
theorem hasDerivWithinAt_walkLogResolvent {V : ℝ → A} {D : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt (fun r ↦ walkLogResolvent (V r) t)
      (-t • (walkLogResolvent (V s) t * D * walkLogResolvent (V s) t)) S s := by
  simpa only [walkLogResolvent, mul_smul_comm, smul_mul_assoc, neg_smul] using
    hasDerivWithinAt_ringInverse_path (((hV.sub_const 1).const_smul t).const_add 1) hu

/-- The derivative of the logarithm integrand is $Z_uDZ_u$, as $u(V-1)Z_u = 1-Z_u$. -/
theorem hasDerivWithinAt_walkLogIntegrand {V : ℝ → A} {D : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt (fun r ↦ (V r - 1) * walkLogResolvent (V r) t)
      (walkLogResolvent (V s) t * D * walkLogResolvent (V s) t) S s := by
  let Z := walkLogResolvent (V s) t
  have hmul := walkLogResolvent_mul_sub (V s) t hu
  have hid : 1 - t • ((V s - 1) * Z) = Z := by
    change 1 - t • ((V s - 1) * walkLogResolvent (V s) t) = _
    rw [hmul, sub_sub_cancel]
  have hd := (hV.sub_const 1).mul (hasDerivWithinAt_walkLogResolvent hV hu)
  convert hd using 1
  change Z * D * Z = D * Z + (V s - 1) * (-t • (Z * D * Z))
  calc
    Z * D * Z = (1 - t • ((V s - 1) * Z)) * D * Z := by rw [hid]
    _ = _ := by
      simp only [add_mul, neg_mul, one_mul, smul_mul_assoc, mul_smul_comm, neg_smul,
        mul_neg,
        mul_assoc, sub_eq_add_neg]

/-- $(s, u) \mapsto Z_u(V(s))$ is jointly continuous where $1 + u(V(s) - 1)$ is invertible. -/
theorem continuousOn_walkLogResolvent {V : ℝ → A} {S : Set ℝ}
    (hV : ContinuousOn V S)
    (hu : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V s - 1))) :
    ContinuousOn (fun p : ℝ × ℝ ↦ walkLogResolvent (V p.1) p.2)
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hh : ContinuousOn (fun p : ℝ × ℝ ↦ 1 + p.2 • (V p.1 - 1))
      (S ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuous_snd.continuousOn.smul (hv.sub continuousOn_const))
  intro p hp
  have hi := (differentiableAt_inverse (𝕜 := ℝ) (hu p.1 hp.1 p.2 hp.2)).continuousAt
  exact hi.comp_continuousWithinAt
    (f := fun q : ℝ × ℝ ↦ 1 + q.2 • (V q.1 - 1)) (hh p hp)

/-- Differentiating the first resolvent sandwich gives the logarithm Hessian integrand. -/
theorem hasDerivWithinAt_walkLogSandwich {V D : ℝ → A} {Vd Dd : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V Vd S s)
    (hD : HasDerivWithinAt D Dd S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt
      (fun r ↦ walkLogResolvent (V r) t * D r * walkLogResolvent (V r) t)
      (walkLogResolvent (V s) t * Dd * walkLogResolvent (V s) t -
        t • (walkLogResolvent (V s) t * Vd * walkLogResolvent (V s) t *
          D s * walkLogResolvent (V s) t +
          walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t *
          Vd * walkLogResolvent (V s) t)) S s := by
  have hZ := hasDerivWithinAt_walkLogResolvent hV hu
  convert (hZ.mul hD).mul hZ using 1 ;
    simp only [Pi.mul_apply, add_mul, smul_mul_assoc, mul_smul_comm, neg_smul,
      neg_mul, mul_neg, smul_add, mul_assoc] ; abel

omit [CompleteSpace A] in
/-- The norm estimate for the Hessian integrand retains two resolvent powers on
the acceleration and three on the squared velocity. -/
theorem norm_walkLogHessian_integrand_le (Z D E : A) {t q : ℝ} (ht : 0 ≤ t) (hZ : ‖Z‖ ≤ q) :
    ‖Z * E * Z - (2 * t) • (Z * D * Z * D * Z)‖ ≤
      q ^ 2 * ‖E‖ + (2 * t) * q ^ 3 * ‖D‖ ^ 2 := by
  have hq : 0 ≤ q := (norm_nonneg _).trans hZ
  have h2 (E : A) : ‖Z * E * Z‖ ≤ q ^ 2 * ‖E‖ := by
    calc ‖Z * E * Z‖ ≤ q * ‖E‖ * q := norm_mul_le_of_le (norm_mul_le_of_le hZ le_rfl) hZ
      _ = _ := by ring
  have h3 : ‖Z * D * Z * D * Z‖ ≤ q ^ 3 * ‖D‖ ^ 2 := by
    calc ‖Z * D * Z * D * Z‖ ≤ ‖Z * D * Z‖ * ‖D‖ * ‖Z‖ := norm_mul₃_le
      _ ≤ q ^ 2 * ‖D‖ * ‖D‖ * q := by gcongr; exact h2 D
      _ = _ := by ring
  calc
    _ ≤ ‖Z * E * Z‖ + ‖(2 * t) • (Z * D * Z * D * Z)‖ := norm_sub_le _ _
    _ = ‖Z * E * Z‖ + (2 * t) * ‖Z * D * Z * D * Z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) ht)]
    _ ≤ q ^ 2 * ‖E‖ + (2 * t) * (q ^ 3 * ‖D‖ ^ 2) :=
      add_le_add (h2 E) (mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) ht))
    _ = _ := by ring

end Resolvent

section SpectralResolvent

-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements), so that `cfc` applies; see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra

/-- Squared distance from zero along a unit-circle chord. -/
theorem norm_sq_unit_chord (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) :
    ‖1 + t • (z - 1)‖ ^ 2 = 1 - 2 * t * (1 - t) * (1 - z.re) := by
  have hz' : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.smul_re, Complex.sub_re,
    Complex.add_im, Complex.one_im, Complex.smul_im, Complex.sub_im, sub_zero,
    zero_add, smul_eq_mul]
  linear_combination t ^ 2 * hz'

/-- The scalar denominator stays positive because the chord excludes the cut. -/
theorem walkLogDenom_pos {c t : ℝ} (hc0 : -1 < c) (hc1 : c ≤ 1) :
    0 < 1 - 2 * t * (1 - t) * (1 - c) := by
  linarith [mul_nonneg (div_nonneg (sub_nonneg.mpr hc1) two_pos.le) (sq_nonneg (2 * t - 1))]

/-- The scalar resolvent bound: for $|z| = 1$ and $\operatorname{Re} z \ge c > -1$,
$|1 + u(z - 1)|^{-1} \le (1 - 2u(1-u)(1-c))^{-1/2}$ on $[0, 1]$. -/
theorem norm_inv_unit_chord_le {z : ℂ} (hz : ‖z‖ = 1) {c t : ℝ}
    (hc0 : -1 < c) (hc1 : c ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hzre : c ≤ z.re) :
    ‖(1 + t • (z - 1))⁻¹‖ ≤
      (Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)))⁻¹ := by
  have hq := walkLogDenom_pos (t := t) hc0 hc1
  have hmul := mul_le_mul_of_nonneg_left hzre
    (mul_nonneg (mul_nonneg two_pos.le ht.1) (sub_nonneg.mpr ht.2))
  have hsq : 1 - 2 * t * (1 - t) * (1 - c) ≤ ‖1 + t • (z - 1)‖ ^ 2 := by
    rw [norm_sq_unit_chord z hz t]
    linear_combination hmul
  have hnorm : Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)) ≤
      ‖1 + t • (z - 1)‖ :=
    (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hsq⟩
  rw [norm_inv]
  exact (inv_le_inv₀ ((Real.sqrt_pos.mpr hq).trans_le hnorm)
    (Real.sqrt_pos.mpr hq)).mpr hnorm

/-- The functional calculus of $z \mapsto 1 + u(z - 1)$ at $V$ is $1 + u(V - 1)$. -/
theorem cfc_unit_chord {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    [IsStarNormal V] (t : ℝ) :
    cfc (fun z : ℂ ↦ 1 + t • (z - 1)) V = 1 + t • (V - 1) := by
  rw [cfc_const_add (p := IsStarNormal) 1 (fun z : ℂ ↦ t • (z - 1)) V (by fun_prop) inferInstance,
    cfc_smul t (fun z : ℂ ↦ z - 1) V (by fun_prop),
    cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
    cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V]
  simp only [map_one]

end SpectralResolvent

namespace Prose

/-- Section 4, proof of the logarithm lemma: the whole chord stays off the cut. -/
theorem chord_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    1 + u • (z - 1) ∈ Complex.slitPlane := by
  have hz' : 1 + (z - 1) ∈ Complex.slitPlane := by convert hz using 1; ring
  exact StarConvex.add_smul_mem Complex.starConvex_one_slitPlane hz' hu.1 hu.2

/-- Lemma A.2: Mathlib's principal-log integral along the segment from `1` to `z`. -/
theorem integral_log_chord {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (∫ u : ℝ in (0 : ℝ)..1, (z - 1) / (1 + (u : ℂ) * (z - 1))) = Complex.log z := by
  have hlog := Complex.log_eq_integral (z := z - 1) (by simpa using hz)
  simpa only [add_sub_cancel, div_eq_mul_inv, Complex.real_smul,
    intervalIntegral.integral_const_mul] using hlog.symm

/-- Section 4, the contradiction proof for the chord: zero imaginary part forces a
positive real part (unless `u = 0`, when the chord is `1`). -/
theorem chord_cut_contradiction {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (him : (1 + u • (z - 1)).im = 0) :
    (u = 0 ∨ (0 < u ∧ z.im = 0 ∧ 0 < z.re)) ∧
      0 < (1 + u • (z - 1)).re := by
  have hi : u * z.im = 0 := by simpa using him
  have hm := chord_mem_slitPlane hz hu
  have hre := (Complex.mem_slitPlane_iff.mp hm).resolve_right (not_not.mpr him)
  refine ⟨?_, hre⟩
  by_cases h0 : u = 0
  · exact Or.inl h0
  · have hzi : z.im = 0 := (mul_eq_zero.mp hi).resolve_left h0
    exact Or.inr ⟨lt_of_le_of_ne hu.1 (Ne.symm h0), hzi,
      (Complex.mem_slitPlane_iff.mp hz).resolve_right (not_not.mpr hzi)⟩

end Prose

section LogIntegral

open MeasureTheory Prose
-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements), so that `cfc` applies; see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The integral $\int_0^1 (V - 1)Z_u\,du$: the principal logarithm of $V$ when the spectrum of $V$
lies in the slit plane (`walkLogIntegral_eq_cfc`), and $-iH$ for $V = e^{-iH}$, $\|H\| < \pi$
(`walkLogIntegral_evol`). The interval integral is `0` for a non-integrable integrand; under the
slit-plane hypothesis the integrand is continuous. -/
def walkLogIntegral (V : 𝕄) : 𝕄 :=
  ∫ t : ℝ in (0 : ℝ)..1, (V - 1) * walkLogResolvent V t

/-- For $z$ in the slit plane and $u \in [0, 1]$, $1 + u(z - 1) \ne 0$ (the slit plane is
star-shaped about $1$). -/
theorem chord_ne_zero_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 + t • (z - 1) ≠ 0 := by
  exact Complex.slitPlane_ne_zero (Prose.chord_mem_slitPlane hz ht)

omit [NeZero d] in
/-- The scalar logarithm integral passes through the functional calculus. -/
theorem walkLogIntegral_eq_cfc (V : 𝕄) [IsStarNormal V]
    (hspec : spectrum ℂ V ⊆ Complex.slitPlane) :
    walkLogIntegral V = cfc Complex.log V := by
  let f : ℝ → ℂ → ℂ := fun t z ↦ (z - 1) * (1 + t • (z - 1))⁻¹
  have hf : ContinuousOn (Function.uncurry f) (Icc (0 : ℝ) 1 ×ˢ spectrum ℂ V) := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.inv₀ (by fun_prop)
    intro p hp he
    have hi : (1 + p.1 • (p.2 - 1)).im = 0 := by rw [he]; rfl
    have hpos := (chord_cut_contradiction (hspec hp.2) hp.1 hi).2
    simp only [he, Complex.zero_re, lt_self_iff_false] at hpos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (spectrum.isCompact V)).exists_bound_of_continuousOn hf
  have hcfc := cfc_setIntegral (μ := volume) measurableSet_Icc f (fun _ ↦ C) V hf
    (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht z hz ↦ hC (t, z) ⟨ht, hz⟩))
    (integrableOn_const (C := C) isCompact_Icc.measure_lt_top.ne (by finiteness)).hasFiniteIntegral
  have hscalar : ∀ z ∈ spectrum ℂ V, ∫ t in Icc (0 : ℝ) 1, f t z = Complex.log z := by
    intro z hz
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change (∫ t : ℝ in (0 : ℝ)..1, (z - 1) * (1 + t • (z - 1))⁻¹) = Complex.log z
    simpa only [div_eq_mul_inv, Complex.real_smul] using integral_log_chord (hspec hz)
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      cfc (f t) V = (V - 1) * walkLogResolvent V t := by
    intro t ht
    have hne : ∀ z ∈ spectrum ℂ V, 1 + t • (z - 1) ≠ 0 := fun z hz ↦
      chord_ne_zero_of_slitPlane (hspec hz) ht
    change cfc (fun z : ℂ ↦ (z - 1) * (1 + t • (z - 1))⁻¹) V = _
    have hinv : ContinuousOn (fun z : ℂ ↦ (1 + t • (z - 1))⁻¹) (spectrum ℂ V) :=
      (by fun_prop : ContinuousOn (fun z : ℂ ↦ 1 + t • (z - 1)) (spectrum ℂ V)).inv₀ hne
    rw [cfc_mul (fun z : ℂ ↦ z - 1) (fun z : ℂ ↦ (1 + t • (z - 1))⁻¹)
      V (by fun_prop) hinv,
      cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
      cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V,
      cfc_inv (p := IsStarNormal) (fun z : ℂ ↦ 1 + t • (z - 1)) V hne (by fun_prop) inferInstance,
      cfc_unit_chord]
    simp only [map_one, walkLogResolvent]
  rw [cfc_congr hscalar] at hcfc
  rw [walkLogIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, hcfc]
  exact integral_congr_ae
    (ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ (hpoint t ht).symm)

end LogIntegral

section CenteredBranch

-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements), so that `cfc` applies; see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Every eigenvalue of $e^{-iH}$ is $e^{-iu}$ with $|u| \le \|H\|$. -/
theorem spectrum_evol_one_eq_exp_real {H : 𝕄} (hH : H.IsHermitian)
    {z : ℂ} (hz : z ∈ spectrum ℂ (evol H 1)) :
    ∃ u : ℝ, |u| ≤ ‖H‖ ∧ z = Complex.exp (-I * (u : ℂ)) := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hH
  rw [evol_one_eq_cfc_exp H hH,
    cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) H hsa.isStarNormal
      (by fun_prop)] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have he : x = (x.re : ℂ) := IsSelfAdjoint.mem_spectrum_eq_re hsa hx
  refine ⟨x.re, ?_, congrArg (fun y : ℂ ↦ Complex.exp (-I * y)) he⟩
  have hb := spectrum.norm_le_norm_of_mem hx
  rwa [he, Complex.norm_real, Real.norm_eq_abs] at hb

/-- For $\|H\| < \pi$ the spectrum of $e^{-iH}$ lies in the slit plane. -/
theorem spectrum_evol_one_subset_slitPlane {H : 𝕄} (hH : H.IsHermitian)
    (hHn : ‖H‖ < π) : spectrum ℂ (evol H 1) ⊆ Complex.slitPlane := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := spectrum_evol_one_eq_exp_real hH hz
  have hangle : |(-u) - 0| < π := by simpa using hu.trans_lt hHn
  have he : -I * (u : ℂ) = ((-u : ℝ) : ℂ) * I := by push_cast; ring
  rw [he]
  simpa only [argDomain, neg_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Set.mem_setOf_eq] using exp_mul_I_mem_argDomain hangle

omit [NeZero d] in
/-- $e^{-iH}$ is normal for Hermitian $H$. -/
theorem isStarNormal_evol_one {H : 𝕄} (hH : H.IsHermitian) : IsStarNormal (evol H 1) :=
  ⟨by change star (evol H 1) * evol H 1 = evol H 1 * star (evol H 1)
      rw [star_evol_mul_self hH 1, mul_eq_one_comm.mpr (star_evol_mul_self hH 1)]⟩

/-- On a centered window smaller than a full turn, the integral is the prescribed branch. -/
theorem walkLogIntegral_evol {H : 𝕄} (hH : H.IsHermitian) (hHn : ‖H‖ < π) :
    walkLogIntegral (evol H 1) = (-I) • H := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hH
  letI : IsStarNormal H := hsa.isStarNormal
  letI := isStarNormal_evol_one hH
  rw [walkLogIntegral_eq_cfc _ (spectrum_evol_one_subset_slitPlane hH hHn),
    evol_one_eq_cfc_exp H hH]
  have hc : ContinuousOn Complex.log
      ((fun z : ℂ ↦ Complex.exp (-I * z)) '' spectrum ℂ H) := by
    apply (show ContinuousOn Complex.log Complex.slitPlane from
      fun z hz ↦ (continuousAt_clog hz).continuousWithinAt).mono
    rw [← cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) H
      hsa.isStarNormal (by fun_prop), ← evol_one_eq_cfc_exp H hH]
    exact spectrum_evol_one_subset_slitPlane hH hHn
  rw [← cfc_comp (R := ℂ) Complex.log (fun z : ℂ ↦ Complex.exp (-I * z)) H
    hsa.isStarNormal hc (by fun_prop)]
  have he : cfc (Complex.log ∘ fun z : ℂ ↦ Complex.exp (-I * z)) H =
      cfc (fun z : ℂ ↦ -I * z) H := by
    refine cfc_congr fun z hz ↦ ?_
    have hzreal : z = (z.re : ℂ) := IsSelfAdjoint.mem_spectrum_eq_re hsa hz
    have hb := (spectrum.norm_le_norm_of_mem hz).trans_lt hHn
    rw [hzreal, Complex.norm_real, Real.norm_eq_abs] at hb
    change Complex.log (Complex.exp (-I * z)) = -I * z
    apply Complex.log_exp
    · rw [hzreal]
      simpa using neg_lt_neg (abs_lt.mp hb).2
    · rw [hzreal]
      have hneg : -z.re < π := by linarith [(abs_lt.mp hb).1]
      simpa using hneg.le
  rw [he, cfc_const_mul_id (-I) H]

end CenteredBranch

section CompactDifferentiation

open MeasureTheory Filter
open scoped Topology

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Differentiation on a compact rectangle supplies its own uniform majorant. -/
theorem hasDerivAt_integral_compact_rectangle {F F' : ℝ → ℝ → A} {a b s : ℝ}
    (hs : s ∈ Ioo a b)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hF' : ContinuousOn (Function.uncurry F') (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hd : ∀ x ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasDerivAt (fun x ↦ ∫ t : ℝ in (0 : ℝ)..1, F x t)
      (∫ t : ℝ in (0 : ℝ)..1, F' s t) s := by
  have hx (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (F x) (Icc (0 : ℝ) 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx, ht⟩)
  have hx' (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (F' x) (Icc (0 : ℝ) 1) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hU : Set.uIoc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hK : Set.uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun _ ↦ C) (isOpen_Ioo.mem_nhds hs) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx0
    rw [hU]
    exact ((hx x ⟨hx0.1.le, hx0.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · exact (hK.symm ▸ hx s ⟨hs.1.le, hs.2.le⟩).intervalIntegrable
  · rw [hU]
    exact ((hx' s ⟨hs.1.le, hs.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · exact Filter.Eventually.of_forall fun t ht x hx0 ↦
      hC (x, t) ⟨⟨hx0.1.le, hx0.2.le⟩, Ioc_subset_Icc_self (hU ▸ ht)⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht x hx0 ↦
      hd x hx0 t (Ioc_subset_Icc_self (hU ▸ ht))

end CompactDifferentiation

section PathDerivatives

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- The first logarithm derivative obtained by differentiating its compact integral. -/
theorem hasDerivAt_walkLogIntegral {V D : ℝ → 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (D x) x)
    (hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V x - 1))) :
    HasDerivAt (fun x ↦ walkLogIntegral (V x))
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t) s := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  apply hasDerivAt_integral_compact_rectangle
    (F := fun x t ↦ (V x - 1) * walkLogResolvent (V x) t)
    (F' := fun x t ↦ walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
    hs ((hv.sub continuousOn_const).mul hZ)
    ((hZ.mul hd').mul hZ)
  intro x hx t ht
  exact (hasDerivWithinAt_walkLogIntegrand (S := Set.univ) (hd x hx).hasDerivWithinAt
    (hu x ⟨hx.1.le, hx.2.le⟩ t ht)).hasDerivAt (by simp)

omit [NeZero d] in
/-- The second logarithm derivative obtained from the differentiated resolvent sandwich. -/
theorem hasDerivAt_walkLogDerivativeIntegral {V D E : ℝ → 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (D x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt D (E x) x)
    (hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V x - 1))) :
    HasDerivAt
      (fun x ↦ ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * E s * walkLogResolvent (V s) t -
          (2 * t) • (walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t *
            D s * walkLogResolvent (V s) t)) s := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have he' : ContinuousOn (fun p : ℝ × ℝ ↦ E p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hE.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  apply hasDerivAt_integral_compact_rectangle
    (F := fun x t ↦ walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
    (F' := fun x t ↦ walkLogResolvent (V x) t * E x * walkLogResolvent (V x) t -
      (2 * t) • (walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t * D x *
        walkLogResolvent (V x) t))
    hs ((hZ.mul hd').mul hZ)
    (((hZ.mul he').mul hZ).sub
      ((continuousOn_const.mul continuous_snd.continuousOn).smul
        ((((hZ.mul hd').mul hZ).mul hd').mul hZ)))
  intro x hx t ht
  have hh := hasDerivWithinAt_walkLogSandwich (S := Set.univ) (hd x hx).hasDerivWithinAt
    (hdd x hx).hasDerivWithinAt (hu x ⟨hx.1.le, hx.2.le⟩ t ht)
  rw [← two_smul ℝ, smul_smul, mul_comm t 2] at hh
  exact hh.hasDerivAt (by simp)

end PathDerivatives

section HessianIdentity

open Filter
open scoped Topology
-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements), so that `cfc` applies; see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The Hessian identity follows from the exponential relation and the local branch window.
All derivative assumptions concern the actual paths. -/
theorem walkLogHessian_identity {H Hd V Vd Vdd : ℝ → 𝕄} {Hdd : 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b)
    (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
    (hwindow : ∀ x ∈ Icc a b, ‖H x‖ < π)
    (he : ∀ x ∈ Icc a b, evol (H x) 1 = V x)
    (hHd : ∀ x ∈ Ioo a b, HasDerivAt H (Hd x) x)
    (hHdd : HasDerivAt Hd Hdd s)
    (hV : ContinuousOn V (Icc a b))
    (hVd : ContinuousOn Vd (Icc a b))
    (hVdd : ContinuousOn Vdd (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (Vd x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt Vd (Vdd x) x) :
    (-I) • Hdd =
      ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * Vdd s * walkLogResolvent (V s) t -
          (2 * t) • (walkLogResolvent (V s) t * Vd s * walkLogResolvent (V s) t *
            Vd s * walkLogResolvent (V s) t) := by
  have hnormal (x : ℝ) (hx : x ∈ Icc a b) : IsStarNormal (V x) := by
    rw [← he x hx]; exact isStarNormal_evol_one (hH x hx)
  have hspec (x : ℝ) (hx : x ∈ Icc a b) : spectrum ℂ (V x) ⊆ Complex.slitPlane := by
    rw [← he x hx]
    exact spectrum_evol_one_subset_slitPlane (hH x hx) (hwindow x hx)
  have hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1,
      IsUnit (1 + t • (V x - 1)) := by
    intro x hx t ht
    letI := hnormal x hx
    rw [← cfc_unit_chord (V x) t]
    exact isUnit_cfc (p := IsStarNormal) (fun z : ℂ ↦ 1 + t • (z - 1)) (V x)
      (by fun_prop) (hnormal x hx) fun z hz ↦ chord_ne_zero_of_slitPlane (hspec x hx hz) ht
  have hI (x : ℝ) (hx : x ∈ Icc a b) : walkLogIntegral (V x) = (-I) • H x := by
    rw [← he x hx]
    exact walkLogIntegral_evol (hH x hx) (hwindow x hx)
  have hJ (x : ℝ) (hx : x ∈ Ioo a b) :
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V x) t * Vd x * walkLogResolvent (V x) t) = (-I) • Hd x := by
    have hder := hasDerivAt_walkLogIntegral hx hV hVd hd hu
    have heq : (fun y ↦ (-I) • H y) =ᶠ[𝓝 x] (fun y ↦ walkLogIntegral (V y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact (hI y ⟨hy.1.le, hy.2.le⟩).symm
    exact (hder.congr_of_eventuallyEq heq).unique ((hHd x hx).const_smul (-I))
  have hder := hasDerivAt_walkLogDerivativeIntegral hs hV hVd hVdd hd hdd hu
  have heq : (fun x ↦ (-I) • Hd x) =ᶠ[𝓝 s]
      (fun x ↦ ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V x) t * Vd x * walkLogResolvent (V x) t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
    exact (hJ x hx).symm
  exact ((hder.congr_of_eventuallyEq heq).unique (hHdd.const_smul (-I))).symm

end HessianIdentity

section IntegralEstimate

open MeasureTheory

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- Integrating the two resolvent powers separately preserves the sharper coefficients. -/
theorem norm_walkLogHessian_integral_le (V D E : 𝕄) {c : ℝ}
    (hc0 : -1 < c) (hc1 : c ≤ 1)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, ‖walkLogResolvent V t‖ ≤
      (Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)))⁻¹) :
    ‖∫ t : ℝ in (0 : ℝ)..1,
      walkLogResolvent V t * E * walkLogResolvent V t -
        (2 * t) • (walkLogResolvent V t * D * walkLogResolvent V t * D * walkLogResolvent V t)‖ ≤
      (∫ t : ℝ in (0 : ℝ)..1, ((Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)))⁻¹) ^ 2) * ‖E‖ +
      (∫ t : ℝ in (0 : ℝ)..1,
        (2 * t) * ((Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)))⁻¹) ^ 3) * ‖D‖ ^ 2 := by
  let r : ℝ → ℝ := fun t ↦ (Real.sqrt (1 - 2 * t * (1 - t) * (1 - c)))⁻¹
  have hr : Continuous r :=
    Continuous.inv₀ ((by fun_prop : Continuous (fun t : ℝ ↦ 1 - 2 * t * (1 - t) * (1 - c))).sqrt)
      fun t ↦ (Real.sqrt_pos.mpr (walkLogDenom_pos (t := t) hc0 hc1)).ne'
  have h1 : IntervalIntegrable (fun t ↦ r t ^ 2 * ‖E‖) volume 0 1 :=
    ((hr.pow 2).mul continuous_const).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t ↦ (2 * t) * r t ^ 3 * ‖D‖ ^ 2) volume 0 1 :=
    (((continuous_const.mul continuous_id).mul (hr.pow 3)).mul
      continuous_const).intervalIntegrable 0 1
  calc
    _ ≤ ∫ t : ℝ in (0 : ℝ)..1, r t ^ 2 * ‖E‖ + (2 * t) * r t ^ 3 * ‖D‖ ^ 2 := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1) _ (h1.add h2)
      exact Filter.Eventually.of_forall fun t ht ↦
        norm_walkLogHessian_integrand_le (walkLogResolvent V t) D E ht.1.le
          (hZ t ⟨ht.1.le, ht.2⟩)
    _ = _ := by
      rw [intervalIntegral.integral_add h1 h2,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

end IntegralEstimate

section FinalEstimate

/-- $1 - 2u(1-u)(1 - \cos(w/2)) = \cos^2(w/4) + \sin^2(w/4)(2u-1)^2$. The left side is the paper's
$r_u^2 = 1 - 4u(1-u)\sin^2(w/4)$, the bound on $\|Z_u\|^{-2}$ in the proof of Lemma A.2. -/
theorem walkLogDenom_halfAngle (w t : ℝ) :
    1 - 2 * t * (1 - t) * (1 - Real.cos (w / 2)) =
      Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * (2 * t - 1) ^ 2 := by
  rw [show w / 2 = 2 * (w / 4) by ring, Real.cos_two_mul]
  linear_combination (-(2 * t - 1) ^ 2) * Real.sin_sq_add_cos_sq (w / 4)

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end FinalEstimate

end UnitaryProducts
