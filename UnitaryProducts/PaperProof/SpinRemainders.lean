/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import UnitaryProducts.PaperProof.PrecessingSpin

/-! # Taylor remainders in the precessing-spin optimality argument -/
@[expose] public section
noncomputable section
open Real Set Filter Asymptotics
open scoped Topology Matrix.Norms.L2Operator
namespace UnitaryProducts.PaperProof.Spin

/-- Integrating a derivative estimate raises its power by one. This is the
one-variable specialization of Mathlib's integral remainder estimate. -/
theorem derivative_power_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (n : ℕ)
    (hdf : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x)
    (hd : deriv f =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ n)) :
    (fun x : ℝ ↦ f x - f 0) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ (n + 1)) := by
  have hderiv : fderiv ℝ f =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ ‖x - 0‖ ^ (n : ℝ)) := by
    rw [isBigO_iff] at hd ⊢
    obtain ⟨C, hC⟩ := hd
    refine ⟨C, ?_⟩
    filter_upwards [hC] with x hx
    simpa only [← norm_deriv_eq_norm_fderiv, sub_zero, Real.rpow_natCast,
      norm_pow, Real.norm_eq_abs, abs_pow, abs_abs] using hx
  have h := sub_isBigO_norm_rpow_add_one_of_fderiv (by positivity : (0 : ℝ) ≤ n) hdf hderiv
  rw [isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  simpa only [sub_zero, ← Nat.cast_add_one, Real.rpow_natCast,
    norm_pow, Real.norm_eq_abs, abs_pow, abs_abs] using hx

/-- A twice differentiable function with zero first derivative has a quadratic
remainder, obtained by applying the standard derivative and integral estimates. -/
theorem quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiffAt ℝ 2 f 0) (hd0 : deriv f 0 = 0) :
    (fun x : ℝ ↦ f x - f 0) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ 2) := by
  have hc : ContDiffAt ℝ 1 (deriv f) 0 := hf.derivWithin (by norm_num)
  have hd := hc.differentiableAt (by norm_num)
  have hb := hd.hasDerivAt.isBigO_sub
  simp only [hd0, sub_zero] at hb
  apply derivative_power_remainder 1 ?_ (by simpa only [pow_one] using hb)
  filter_upwards [hf.eventually (by norm_num)] with x hx
  exact hx.differentiableAt (by norm_num)

/-- Subtracting the linear Taylor term of a `C²` map leaves a quadratic
remainder. The codomain can be a matrix Banach space. -/
theorem linear_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} (hf : ContDiffAt ℝ 2 f 0) (hd : HasDerivAt f v 0) :
    (fun x : ℝ ↦ f x - f 0 - x • v) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ 2) := by
  let g := fun x : ℝ ↦ f x - f 0 - x • v
  have hg : ContDiffAt ℝ 2 g 0 := (hf.sub contDiffAt_const).sub (by fun_prop)
  have hgd : HasDerivAt g 0 0 := by
    convert (hd.sub_const (f 0)).sub ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1; simp
  have h := quadratic_remainder hg hgd.deriv
  simpa only [g, sub_self, zero_smul, sub_zero] using h

/-- Oddness removes the quadratic Taylor coefficient at zero. -/
theorem odd_second_derivative_zero {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) :
    deriv (deriv f) 0 = 0 := by
  have heven : ∀ x, deriv f (-x) = deriv f x := by
    intro x
    have he : (fun y ↦ f (-y)) = fun y ↦ -f y := funext hodd
    have hh := congrArg (fun g : ℝ → ℝ ↦ deriv g x) he
    dsimp only at hh
    rw [deriv_comp_neg] at hh
    have hn : deriv (fun y ↦ -f y) x = -deriv f x := by
      simp only [← fderiv_apply_one_eq_deriv, fderiv_fun_neg, ContinuousLinearMap.neg_apply]
    rw [hn] at hh
    exact neg_injective hh
  have he : (fun x ↦ deriv f (-x)) = deriv f := funext heven
  have hh := congrArg (fun g : ℝ → ℝ ↦ deriv g 0) he
  dsimp only at hh
  rw [deriv_comp_neg, neg_zero] at hh
  linarith

/-- A `C³` odd function has a cubic remainder after its linear term. -/
theorem odd_linear_taylor_remainder {f : ℝ → ℝ} {v : ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hd : HasDerivAt f v 0)
    (hodd : ∀ x, f (-x) = -f x) :
    (fun x : ℝ ↦ f x - v * x) =O[𝓝 (0 : ℝ)] (fun x : ℝ ↦ x ^ 3) := by
  have hzero : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linarith
  have hc : ContDiffAt ℝ 2 (deriv f) 0 := hf.derivWithin (by norm_num)
  have hderiv := quadratic_remainder hc (odd_second_derivative_zero hodd)
  rw [hd.deriv] at hderiv
  let g := fun x : ℝ ↦ f x - v * x
  have hg : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ g x := by
    filter_upwards [hf.eventually (by norm_num)] with x hx
    exact (hx.differentiableAt (by norm_num)).sub (by fun_prop)
  have he : deriv g =ᶠ[𝓝 (0 : ℝ)] fun x ↦ deriv f x - v := by
    filter_upwards [hf.eventually (by norm_num)] with x hx
    exact ((hx.differentiableAt (by norm_num)).hasDerivAt.sub
      ((hasDerivAt_id x).const_mul v)).deriv.trans (by simp)
  have hb := derivative_power_remainder 2 hg (hderiv.congr' he.symm Filter.EventuallyEq.rfl)
  simpa only [g, hzero, mul_zero, sub_zero] using hb

/-- The rotation phase selected near zero precession. -/
def spinPhase (ω : ℝ) (T : ℕ) (θ : ℝ) : ℝ :=
  Real.arccos (Real.cos (ω / 2) * Real.cos (θ / (2 * T)))

/-- The phase in the optimality paragraph is `ω/2 + O(θ²)` at fixed `T`. -/
theorem spin_phase_quadratic {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π) (T : ℕ) :
    (fun θ : ℝ ↦ spinPhase ω T θ - ω / 2) =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 2) := by
  have hx : ω / 2 ∈ Icc (0 : ℝ) π := ⟨by positivity, by linarith⟩
  have hcoslo : -1 < Real.cos (ω / 2) := by
    simpa only [Real.cos_pi] using
      Real.strictAntiOn_cos hx ⟨pi_pos.le, le_rfl⟩ (by linarith : ω / 2 < π)
  have hcoshi : Real.cos (ω / 2) < 1 := by
    simpa only [Real.cos_zero] using
      Real.strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ hx (by positivity : 0 < ω / 2)
  have harg : ContDiffAt ℝ 2
      (fun θ : ℝ ↦ Real.cos (ω / 2) * Real.cos (θ / (2 * T))) 0 := by fun_prop
  have hc : ContDiffAt ℝ 2 (spinPhase ω T) 0 := by
    have harc : ContDiffAt ℝ 2 Real.arccos (Real.cos (ω / 2) * Real.cos (0 / (2 * T))) := by
      simpa only [zero_div, Real.cos_zero, mul_one] using
        (Real.contDiffAt_arccos hcoslo.ne' hcoshi.ne :
          ContDiffAt ℝ 2 Real.arccos (Real.cos (ω / 2)))
    exact harc.comp 0 harg
  have hdarg : HasDerivAt (fun θ : ℝ ↦ Real.cos (ω / 2) * Real.cos (θ / (2 * T))) 0 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).div_const (2 * T)).cos).const_mul
      (Real.cos (ω / 2)) using 1; simp
  have hd : HasDerivAt (spinPhase ω T) 0 0 := by
    have harc : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - Real.cos (ω / 2) ^ 2)))
        (Real.cos (ω / 2) * Real.cos (0 / (2 * T))) := by
      simpa only [zero_div, Real.cos_zero, mul_one] using
        Real.hasDerivAt_arccos hcoslo.ne' hcoshi.ne
    have h := harc.comp 0 hdarg
    simpa [spinPhase] using h
  have hzero : spinPhase ω T 0 = ω / 2 := by
    simp only [spinPhase, zero_div, Real.cos_zero, mul_one]
    exact Real.arccos_cos (by positivity) (by linarith)
  simpa only [hzero] using quadratic_remainder hc hd.deriv

/-- Signed difference of the step and continuous rotation axes near zero. -/
def spinAxisAngle (ω : ℝ) (T : ℕ) (θ : ℝ) : ℝ :=
  Real.arctan (Real.sin (θ / (2 * T)) /
    (Real.sin (ω / 2) * Real.cos (θ / (2 * T)))) - Real.arctan (θ / (ω * T))

/-- The axis angle in the optimality paragraph has the displayed cubic remainder. -/
theorem spin_axis_angle_cubic {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    {T : ℕ} (hT : 0 < T) :
    (fun θ : ℝ ↦ spinAxisAngle ω T θ - θ / (2 * T) *
      (1 / Real.sin (ω / 2) - 2 / ω)) =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 3) := by
  have hs : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hc : ContDiffAt ℝ 3 (spinAxisAngle ω T) 0 := by
    unfold spinAxisAngle
    apply (Real.contDiff_arctan.contDiffAt.comp 0 ?_).sub
      (Real.contDiff_arctan.contDiffAt.comp 0 (by fun_prop))
    fun_prop (disch := simpa using hs.ne')
  have hodd : ∀ θ, spinAxisAngle ω T (-θ) = -spinAxisAngle ω T θ := by
    intro θ
    simp only [spinAxisAngle, neg_div, Real.sin_neg, Real.cos_neg, Real.arctan_neg]
    ring
  have hε := (hasDerivAt_id (0 : ℝ)).div_const (2 * (T : ℝ))
  have hratio := hε.sin.div (hε.cos.const_mul (Real.sin (ω / 2))) (by simpa using hs.ne')
  have hfirst := hratio.arctan
  have hsecond := ((hasDerivAt_id (0 : ℝ)).div_const (ω * T)).arctan
  have hd : HasDerivAt (spinAxisAngle ω T)
      ((1 / (2 * T)) * (1 / Real.sin (ω / 2) - 2 / ω)) 0 := by
    convert hfirst.sub hsecond using 1; simp
    field_simp
  have hb := odd_linear_taylor_remainder hc hd hodd
  convert hb using 1
  funext θ
  ring

/-- The symmetric step varies smoothly with the precession angle. -/
theorem step_contDiff (ω : ℝ) (T : ℕ) :
    ContDiff ℝ 2 (fun θ : ℝ ↦ step ω (θ / (2 * T))) := by
  simp_rw [step_closed]
  simp only [← Complex.ofRealCLM_apply]
  fun_prop

/-- The continuous frame factor varies smoothly near zero precession, as
seen in its elementary SU(2) formula. -/
theorem frozen_contDiffAt {a : ℝ} (ha : 0 < a) :
    ContDiffAt ℝ 2 (fun θ : ℝ ↦ UnitaryProducts.evol (a • X - θ • Z) (1 / 2)) 0 := by
  have he : (fun θ : ℝ ↦ UnitaryProducts.evol (a • X - θ • Z) (1 / 2)) =
      (fun θ : ℝ ↦ (Real.cos (Real.sqrt (a ^ 2 + (-θ) ^ 2) / 2) : ℂ) • 1 -
        (Complex.I * Real.sin (Real.sqrt (a ^ 2 + (-θ) ^ 2) / 2) /
          Real.sqrt (a ^ 2 + (-θ) ^ 2) : ℂ) • xz a (-θ)) := by
    funext θ
    have hp : 0 < a ^ 2 + (-θ) ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
    have hG : a • X - θ • Z = xz a (-θ) := by simp only [xz, neg_smul, sub_eq_add_neg]
    rw [hG, evol_xz_formula hp]
  rw [he]
  let r := fun θ : ℝ ↦ Real.sqrt (a ^ 2 + (-θ) ^ 2)
  have hp : a ^ 2 + (-(0 : ℝ)) ^ 2 ≠ 0 := by simpa using pow_ne_zero 2 ha.ne'
  have hr : ContDiffAt ℝ 2 r 0 :=
    (show ContDiffAt ℝ 2 (fun θ : ℝ ↦ a ^ 2 + (-θ) ^ 2) 0 by fun_prop).sqrt hp
  have hr0 : 0 < r 0 := Real.sqrt_pos.mpr (by positivity)
  have hcast {g : ℝ → ℝ} (hg : ContDiffAt ℝ 2 g 0) :
      ContDiffAt ℝ 2 (fun θ : ℝ ↦ (g θ : ℂ)) 0 := Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hg
  have hcos := hcast ((hr.div_const 2).cos)
  have hsin := hcast ((hr.div_const 2).sin)
  have hratio : ContDiffAt ℝ 2 (fun θ : ℝ ↦ (Complex.I * Real.sin (r θ / 2) / r θ : ℂ)) 0 := by
    simpa only [div_eq_mul_inv] using
      ((contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ ↦ Complex.I) 0).mul hsin).mul
        ((hcast hr).inv (Complex.ofReal_ne_zero.mpr hr0.ne'))
  have haxis : ContDiffAt ℝ 2 (fun θ : ℝ ↦ xz a (-θ)) 0 := by unfold xz; fun_prop
  exact (hcos.smul contDiffAt_const).sub (hratio.smul haxis)

/-- The actual frame error has the regularity needed for a quadratic Taylor
remainder. Powers are finite because the runtime is fixed here. -/
theorem frameError_contDiffAt {ω : ℝ} (hω : 0 < ω) {T : ℕ} (hT : 0 < T) :
    ContDiffAt ℝ 2 (fun θ : ℝ ↦ frameError ω θ T) 0 :=
  ((step_contDiff ω T).contDiffAt.pow T).sub
    (frozen_contDiffAt (mul_pos hω (Nat.cast_pos.mpr hT)))

/-- Taking the norm of a `C²` Taylor expansion preserves a quadratic remainder,
even though the norm itself need not be differentiable at zero. -/
theorem norm_linear_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} (hf : ContDiffAt ℝ 2 f 0) (hd : HasDerivAt f v 0)
    (hzero : f 0 = 0) :
    (fun θ : ℝ ↦ ‖f θ‖ - |θ| * ‖v‖) =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 2) := by
  have hb := linear_taylor_remainder hf hd
  simp only [hzero, sub_zero] at hb
  have he : (fun θ : ℝ ↦ ‖f θ‖ - |θ| * ‖v‖) =O[𝓝 (0 : ℝ)]
      (fun θ : ℝ ↦ f θ - θ • v) := by
    apply IsBigO.of_bound'
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs, norm_smul] using abs_norm_sub_norm_le (f θ) (θ • v)
  exact he.trans hb

/-- At an odd resonance, the comparison error has the exact leading term and
quadratic remainder asserted after Example 5.2, with runtime fixed. -/
theorem odd_resonance_error_quadratic {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    {T : ℕ} (hT : 0 < T) (m : ℕ) (hodd : (T : ℝ) * ω = (2 * m + 1) * π) :
    (fun θ : ℝ ↦ (T : ℝ) * ‖frameError ω θ T‖ -
      (1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2) * (ω * |θ|))
      =O[𝓝 (0 : ℝ)] (fun θ : ℝ ↦ θ ^ 2) := by
  have hs : Real.sin (ω / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < ω / 2) (by linarith)).ne'
  have hd := frameError_derivative hω hT hs
  have hb := (norm_linear_taylor_remainder (frameError_contDiffAt hω hT) hd
    (frameError_zero ω T)).const_mul_left (T : ℝ)
  have hc := tendsto_nhds_unique (frameError_normalized_limit hω hT hs)
    (precessing_spin_every_width hω hω2 hT m hodd)
  convert hb using 1
  funext θ
  rw [← hc]
  field_simp

/-- The normalized axis paired with `spinPhase` in the optimality paragraph. -/
def spinStepAxis (ω : ℝ) (T : ℕ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sin (spinPhase ω T θ))⁻¹ •
    xz (Real.sin (ω / 2) * Real.cos (θ / (2 * T))) (-Real.sin (θ / (2 * T)))

/-- Multiplying out the symmetric step gives the phase and unit axis stated
in the paper. The phase is the branch in `(0,π)` at every precession angle. -/
theorem spin_step_phase_axis {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    (T : ℕ) (θ : ℝ) :
    let χ := spinPhase ω T θ
    let N := spinStepAxis ω T θ
    0 < χ ∧ χ < π ∧ N.IsHermitian ∧ N * N = 1 ∧
      Real.cos χ = Real.cos (ω / 2) * Real.cos (θ / (2 * T)) ∧
      Real.sin χ • N = xz (Real.sin (ω / 2) * Real.cos (θ / (2 * T)))
        (-Real.sin (θ / (2 * T))) ∧
      step ω (θ / (2 * T)) = UnitaryProducts.evol N χ := by
  intro χ N
  let a := ω / 2
  let ε := θ / (2 * (T : ℝ))
  have ha : a ∈ Ioo (0 : ℝ) π := ⟨by dsimp [a]; positivity, by dsimp [a]; linarith⟩
  have hcoslo : -1 < Real.cos a := by
    simpa only [Real.cos_pi] using Real.strictAntiOn_cos
      ⟨ha.1.le, ha.2.le⟩ ⟨pi_pos.le, le_rfl⟩ ha.2
  have hcoshi : Real.cos a < 1 := by
    simpa only [Real.cos_zero] using Real.strictAntiOn_cos
      ⟨le_rfl, pi_pos.le⟩ ⟨ha.1.le, ha.2.le⟩ ha.1
  have habs : |Real.cos a * Real.cos ε| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ε) (abs_nonneg _)).trans_lt
      (by simpa only [mul_one] using abs_lt.mpr ⟨hcoslo, hcoshi⟩)
  have hprod := abs_lt.mp habs
  have hχ0 : 0 < χ := Real.arccos_pos.mpr hprod.2
  have hχπ : χ < π := Real.arccos_lt_pi.mpr hprod.1
  have hcos : Real.cos χ = Real.cos a * Real.cos ε :=
    Real.cos_arccos hprod.1.le hprod.2.le
  have hlen : (Real.sin a * Real.cos ε) ^ 2 + (-Real.sin ε) ^ 2 =
      1 - (Real.cos a * Real.cos ε) ^ 2 := by
    linear_combination Real.cos ε ^ 2 * Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq ε
  have hpos : 0 < (Real.sin a * Real.cos ε) ^ 2 + (-Real.sin ε) ^ 2 := by
    rw [hlen]
    exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr habs)
  have hr : Real.sqrt ((Real.sin a * Real.cos ε) ^ 2 + (-Real.sin ε) ^ 2) = Real.sin χ := by
    rw [hlen]
    exact (Real.sin_arccos _).symm
  obtain ⟨hN, hNN⟩ := xz_normalized hpos
  rw [hr] at hN hNN
  change N.IsHermitian at hN
  change N * N = 1 at hNN
  have hspos : 0 < Real.sin χ := Real.sin_pos_of_pos_of_lt_pi hχ0 hχπ
  have hscale : Real.sin χ • N = xz (Real.sin a * Real.cos ε) (-Real.sin ε) := by
    change Real.sin χ • ((Real.sin χ)⁻¹ • xz (Real.sin a * Real.cos ε) (-Real.sin ε)) = _
    rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  refine ⟨hχ0, hχπ, hN, hNN, hcos, hscale, ?_⟩
  rw [evol_involution hN hNN, hcos, step_closed]
  have hsmul : (Complex.I * (Real.sin χ : ℂ)) • N =
      Complex.I • xz (Real.sin a * Real.cos ε) (-Real.sin ε) := by
    rw [← hscale, ← IsScalarTower.algebraMap_smul ℂ (Real.sin χ) N, smul_smul]
    rfl
  rw [hsmul]
  have hmatrix : xz (Real.sin a * Real.cos ε) (-Real.sin ε) =
      (Real.sin a * Real.cos ε : ℂ) • X - (Real.sin ε : ℂ) • Z := by
    ext i j
    simp only [xz, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [hmatrix]
  simp only [a, ε, Complex.ofReal_mul]

/-- On the local branch where `cos ε` is positive, the normalized step axis
has the arctangent coordinates used by `spinAxisAngle`. -/
theorem spin_step_axis_arctan {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    (T : ℕ) (θ : ℝ) (hcos : 0 < Real.cos (θ / (2 * T))) :
    spinStepAxis ω T θ =
      xz (Real.cos (Real.arctan (Real.sin (θ / (2 * T)) /
        (Real.sin (ω / 2) * Real.cos (θ / (2 * T))))))
        (-Real.sin (Real.arctan (Real.sin (θ / (2 * T)) /
        (Real.sin (ω / 2) * Real.cos (θ / (2 * T)))))) := by
  let a := ω / 2
  let ε := θ / (2 * (T : ℝ))
  have hsin : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi (by dsimp [a]; positivity)
    (by dsimp [a]; linarith)
  obtain ⟨hc, hs⟩ := axis_arctan_coordinates (mul_pos hsin hcos) (Real.sin ε)
  change spinStepAxis ω T θ = xz (Real.cos (Real.arctan (Real.sin ε /
    (Real.sin a * Real.cos ε)))) (-Real.sin (Real.arctan (Real.sin ε / (Real.sin a * Real.cos ε))))
  rw [hc, hs]
  have hr : Real.sqrt ((Real.sin a * Real.cos ε) ^ 2 + Real.sin ε ^ 2) =
      Real.sin (spinPhase ω T θ) := by
    rw [spinPhase, Real.sin_arccos]
    congr 1
    linear_combination Real.cos ε ^ 2 * Real.sin_sq_add_cos_sq a + Real.sin_sq_add_cos_sq ε
  rw [hr]
  unfold spinStepAxis xz
  change (Real.sin (spinPhase ω T θ))⁻¹ •
      ((Real.sin a * Real.cos ε) • X + (-Real.sin ε) • Z) = _
  module

/-- Near zero precession, `spinAxisAngle` is precisely a signed angle between
the step axis and the continuous-frame axis: their anticommutator is its cosine.
The continuous axis is identified by `frozen_axis_angle`. -/
theorem spin_axis_angle_anticommutator {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    (T : ℕ) :
    ∀ᶠ θ in 𝓝 (0 : ℝ),
      let N := spinStepAxis ω T θ
      let M := xz (Real.cos (Real.arctan (θ / (ω * T))))
        (-Real.sin (Real.arctan (θ / (ω * T))))
      N * M + M * N = (2 * Real.cos (spinAxisAngle ω T θ) : ℂ) • 1 := by
  have hc : ContinuousAt (fun θ : ℝ ↦ Real.cos (θ / (2 * T))) 0 := by fun_prop
  have hpos := continuousAt_const.eventually_lt hc (by simp : (0 : ℝ) < Real.cos (0 / (2 * T)))
  filter_upwards [hpos] with θ hθ
  dsimp only
  rw [spin_step_axis_arctan hω hω2 T θ hθ]
  exact xz_angle_anticommutator _ _

end UnitaryProducts.PaperProof.Spin
