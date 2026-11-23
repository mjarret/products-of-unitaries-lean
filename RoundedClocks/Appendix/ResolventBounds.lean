/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.LocalLogarithm
public import RoundedClocks.Appendix.LogarithmQuadratures

/-! # Lemma A.2: the bound `‖S_u‖² ≤ 1/r(v)`

For `0 ≤ u ≤ 1`, let `v = 2u - 1` and `r(v) = cos²(w/4) + v² sin²(w/4)`. After the constant phase
of the proof, every eigenvalue `φ` of `H(s₀)` has `|φ| ≤ w/2`, the number
`1 + u(e^{-iφ} - 1) = e^{-iφ/2}(cos(φ/2) - iv sin(φ/2))` has squared modulus
`1 - (1-v²) sin²(φ/2) ≥ r(v)`, and so `‖S_u‖² ≤ 1/r(v)`. Here `radius w v` is `r(v)`.
-/

@[expose] public section

open Real Complex Set
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

attribute [local instance] matrixCStarAlgebra

/-- `1 + u(e^{-iφ} - 1) = e^{-iφ/2}(cos(φ/2) - iv sin(φ/2))` with `v = 2u - 1`. -/
theorem chord_factorization (φ u : ℝ) :
    1 + (u : ℂ) * (Complex.exp (-Complex.I * (φ : ℂ)) - 1) =
      Complex.exp (-Complex.I * ((φ / 2 : ℝ) : ℂ)) *
        ((Real.cos (φ / 2) : ℂ) - Complex.I * (2 * u - 1 : ℝ) * Real.sin (φ / 2)) := by
  have hexp (x : ℝ) : Complex.exp (-Complex.I * (x : ℂ)) =
      (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
    rw [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm Complex.I (Complex.sin _),
      Complex.cos_sub_sin_I, neg_mul, neg_mul, mul_comm]
  rw [hexp φ, hexp (φ / 2)]
  have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, show 2 * (φ / 2) = φ by ring]
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul, show 2 * (φ / 2) = φ by ring]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.one_im,
    mul_zero, zero_mul, add_zero, zero_add, one_mul, sub_zero, zero_sub]
  · rw [hc]
    linear_combination (2 * u - 1) * Real.cos_sq_add_sin_sq (φ / 2)
  · rw [hs]
    ring

/-- `|1 + u(e^{-iφ} - 1)|² = 1 - (1-v²) sin²(φ/2)` with `v = 2u - 1`. -/
theorem chord_norm_sq (φ u : ℝ) :
    ‖1 + u • (Complex.exp (-Complex.I * (φ : ℂ)) - 1)‖ ^ 2 =
      1 - (1 - (2 * u - 1) ^ 2) * Real.sin (φ / 2) ^ 2 := by
  rw [Complex.real_smul, chord_factorization, norm_mul]
  have he : -Complex.I * ((φ / 2 : ℝ) : ℂ) = ((-φ / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im,
    mul_zero, zero_mul, sub_zero, zero_sub, one_mul, zero_add]
  linear_combination Real.cos_sq_add_sin_sq (φ / 2)

/-- `|1 + u(e^{-iφ} - 1)|² ≥ r(v)` for `|φ| ≤ w/2`, `0 ≤ u ≤ 1`, and `v = 2u - 1`. -/
theorem chord_radius_lower {w φ u : ℝ} (hw : w < 2 * π)
    (hφ : |φ| ≤ w / 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    radius w (2 * u - 1) ≤ ‖1 + u • (Complex.exp (-I * (φ : ℂ)) - 1)‖ ^ 2 := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ)
    (by linarith : w / 2 ≤ π) hφ
  have hcφ := Real.cos_two_mul (|φ| / 2)
  have hcw := Real.cos_two_mul (w / 4)
  have hsφ := Real.sin_sq_add_cos_sq (|φ| / 2)
  have hsw := Real.sin_sq_add_cos_sq (w / 4)
  rw [show 2 * (|φ| / 2) = |φ| by ring] at hcφ
  rw [show 2 * (w / 4) = w / 2 by ring] at hcw
  have hs : Real.sin (|φ| / 2) ^ 2 ≤ Real.sin (w / 4) ^ 2 := by linarith
  have habs : Real.sin (|φ| / 2) ^ 2 = Real.sin (φ / 2) ^ 2 := by
    rcases le_total 0 φ with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn, neg_div, Real.sin_neg, neg_sq]
  rw [habs] at hs
  have hm : 0 ≤ 4 * u * (1 - u) :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) (sub_nonneg.mpr hu.2)
  have hb := mul_le_mul_of_nonneg_left hs hm
  rw [chord_norm_sq]
  dsimp [radius]
  linear_combination hb + Real.cos_sq_add_sin_sq (w / 4)

/-- `|(1 + u(e^{-iφ} - 1))⁻¹| ≤ r(v)^{-1/2}` for `|φ| ≤ w/2`, `0 ≤ u ≤ 1`, and `v = 2u - 1`. -/
theorem scalar_resolvent_le {w φ u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hφ : |φ| ≤ w / 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖(1 + u • (Complex.exp (-I * (φ : ℂ)) - 1))⁻¹‖ ≤
      1 / Real.sqrt (radius w (2 * u - 1)) := by
  have hp := Real.sqrt_pos.mpr (radius_pos hw0 hw (2 * u - 1))
  have hn : Real.sqrt (radius w (2 * u - 1)) ≤
      ‖1 + u • (Complex.exp (-I * (φ : ℂ)) - 1)‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg _, chord_radius_lower hw hφ hu⟩
  simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hp hn

/-- The functional calculus of `z ↦ 1 + u(z - 1)` at `V` is `1 + u(V - 1)`. -/
theorem cfc_chord {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) [IsStarNormal V] (u : ℝ) :
    cfc (fun z : ℂ ↦ 1 + u • (z - 1)) V = 1 + u • (V - 1) := by
  rw [cfc_const_add (p := IsStarNormal) 1 _ V (by fun_prop) inferInstance,
    cfc_smul u _ V (by fun_prop), cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
    cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V]
  simp only [map_one]

/-- For a normal `V` whose eigenvalues are `e^{-iφ}` with `|φ| ≤ w/2`: `1 + u(V - 1)` is invertible,
`‖S_u‖ ≤ r(v)^{-1/2}`, and `‖S_u‖² ≤ 1/r(v)`, with `v = 2u - 1`. -/
theorem phase_resolvent_bound {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    [IsStarNormal V] {w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hspec : ∀ z ∈ spectrum ℂ V,
      ∃ φ : ℝ, |φ| ≤ w / 2 ∧ z = Complex.exp (-I * (φ : ℂ)))
    (hu : u ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 + u • (V - 1)) ∧
      ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (radius w (2 * u - 1)) ∧
      ‖walkLogResolvent V u‖ ^ 2 ≤ 1 / radius w (2 * u - 1) := by
  have hn : ∀ z ∈ spectrum ℂ V, 1 + u • (z - 1) ≠ 0 := by
    intro z hz
    obtain ⟨φ, hφ, rfl⟩ := hspec z hz
    apply chord_ne_zero (phase_mem_slitPlane ?_) hu
    have hb := abs_le.mp hφ
    constructor <;> linarith [hb.1, hb.2]
  have hi : IsUnit (1 + u • (V - 1)) := by
    rw [← cfc_chord V u]
    exact isUnit_cfc _ V (by fun_prop) inferInstance hn
  have he : cfc (fun z : ℂ ↦ (1 + u • (z - 1))⁻¹) V = walkLogResolvent V u := by
    rw [cfc_inv (p := IsStarNormal) _ V hn (by fun_prop) inferInstance, cfc_chord]
    rfl
  have hb : ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (radius w (2 * u - 1)) := by
    rw [← he]
    apply norm_cfc_le (by positivity)
    intro z hz
    obtain ⟨φ, hφ, rfl⟩ := hspec z hz
    exact scalar_resolvent_le hw0 hw hφ hu
  refine ⟨hi, hb, ?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [div_pow, one_pow, Real.sq_sqrt (radius_pos hw0 hw (2 * u - 1)).le] using hs

/-- The bound `‖S_u‖² ≤ 1/r(v)` for `V = e^{iμ} e^{-iH}`, when the spectrum of the Hermitian `H`
lies within `w/2` of `μ`. -/
theorem fixed_phase_resolvent_bound {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {μ w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwin : HasRealSpectrumIn H (Icc (μ - w / 2) (μ + w / 2)))
    (hu : u ∈ Icc (0 : ℝ) 1) :
    let V := Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H)
    IsUnit (1 + u • (V - 1)) ∧
      ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (radius w (2 * u - 1)) ∧
      ‖walkLogResolvent V u‖ ^ 2 ≤ 1 / radius w (2 * u - 1) := by
  dsimp only
  rw [phase_exp_eq_cfc H hH μ]
  let f : ℂ → ℂ := fun z ↦ Complex.exp (I * (μ : ℂ)) * Complex.exp (-I * z)
  letI : IsStarNormal H := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  letI : IsStarNormal (cfc f H) := cfc_predicate f H
  apply phase_resolvent_bound (cfc f H) hw0 hw _ hu
  rw [cfc_map_spectrum f H (inferInstance : IsStarNormal H)
    ((Matrix.finite_spectrum H).continuousOn _)]
  rintro _ ⟨z, hz, rfl⟩
  have he := IsSelfAdjoint.mem_spectrum_eq_re
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hH) hz
  have hr : z.re ∈ spectrum ℝ H :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).spectrumRestricts.apply_mem hz
  have ht := hwin hr
  refine ⟨z.re - μ, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  dsimp [f]
  rw [he, ← Complex.exp_add]
  simp only [Complex.ofReal_re]
  congr 1
  push_cast
  ring

end RoundedClocks.WalkLog
