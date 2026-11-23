/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.LocalLogarithm

/-! # Sharp resolvent estimates

Lemma A.2 bounds the chord resolvent at every point, including both endpoints and zero spectral
width.
-/

@[expose] public section

open Real Complex Set
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

open WalkLogCalculus
attribute [local instance] matrixCStarAlgebra

/-- The scalar chord factorization written before the quadratures. -/
theorem chord_factorization (φ u : ℝ) :
    1 + (u : ℂ) * (Complex.exp (-Complex.I * (φ : ℂ)) - 1) =
      Complex.exp (-Complex.I * ((φ / 2 : ℝ) : ℂ)) *
        ((Real.cos (φ / 2) : ℂ) - Complex.I * (2 * u - 1 : ℝ) * Real.sin (φ / 2)) := by
  have hexp (x : ℝ) : Complex.exp (-Complex.I * (x : ℂ)) =
      (Real.cos x : ℂ) - Complex.I * (Real.sin x : ℂ) := by
    apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re]
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

/-- The squared modulus of the scalar chord in the centered variable. -/
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

/-- The paper's squared chord radius, with `v = 2u - 1`. -/
def chordRadius (w u : ℝ) : ℝ :=
  Real.cos (w / 4) ^ 2 + (2 * u - 1) ^ 2 * Real.sin (w / 4) ^ 2

/-- The radius is strictly positive even at zero width and at the chord endpoints. -/
theorem chordRadius_pos {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (u : ℝ) :
    0 < chordRadius w u := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The scalar squared modulus dominates the radius at the maximal phase width. -/
theorem chord_radius_lower {w φ u : ℝ} (hw : w < 2 * π)
    (hφ : |φ| ≤ w / 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    chordRadius w u ≤ ‖1 + u • (Complex.exp (-I * (φ : ℂ)) - 1)‖ ^ 2 := by
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
  dsimp [chordRadius]
  linear_combination hb + Real.cos_sq_add_sin_sq (w / 4)

/-- Taking the positive square root gives the scalar bound used for cubic products. -/
theorem scalar_resolvent_le {w φ u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hφ : |φ| ≤ w / 2) (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖(1 + u • (Complex.exp (-I * (φ : ℂ)) - 1))⁻¹‖ ≤
      1 / Real.sqrt (chordRadius w u) := by
  have hp := Real.sqrt_pos.mpr (chordRadius_pos hw0 hw u)
  have hn : Real.sqrt (chordRadius w u) ≤
      ‖1 + u • (Complex.exp (-I * (φ : ℂ)) - 1)‖ :=
    Real.sqrt_le_iff.mpr ⟨norm_nonneg _, chord_radius_lower hw hφ hu⟩
  simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hp hn

/-- Functional calculus sends the scalar chord to the matrix chord. -/
theorem cfc_chord {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) [IsStarNormal V] (u : ℝ) :
    cfc (fun z : ℂ ↦ 1 + u • (z - 1)) V = 1 + u • (V - 1) := by
  rw [cfc_const_add (p := IsStarNormal) 1 _ V (by fun_prop) inferInstance,
    cfc_smul u _ V (by fun_prop), cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
    cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V]
  simp only [map_one]

/-- The spectral calculus transfers the sharp scalar bound to any normal matrix. -/
theorem phase_resolvent_bound {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    [IsStarNormal V] {w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hspec : ∀ z ∈ spectrum ℂ V,
      ∃ φ : ℝ, |φ| ≤ w / 2 ∧ z = Complex.exp (-I * (φ : ℂ)))
    (hu : u ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 + u • (V - 1)) ∧
      ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (chordRadius w u) ∧
      ‖walkLogResolvent V u‖ ^ 2 ≤ 1 / chordRadius w u := by
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
  have hb : ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (chordRadius w u) := by
    rw [← he]
    apply norm_cfc_le (by positivity)
    intro z hz
    obtain ⟨φ, hφ, rfl⟩ := hspec z hz
    exact scalar_resolvent_le hw0 hw hφ hu
  refine ⟨hi, hb, ?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [div_pow, one_pow, Real.sq_sqrt (chordRadius_pos hw0 hw u).le] using hs

/-- The fixed phase in the local derivative formula has the sharp chord bound. -/
theorem fixed_phase_resolvent_bound {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) {μ w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwin : HasRealSpectrumIn H (Icc (μ - w / 2) (μ + w / 2)))
    (hu : u ∈ Icc (0 : ℝ) 1) :
    let V := Complex.exp (I * (μ : ℂ)) • NormedSpace.exp (-I • H)
    IsUnit (1 + u • (V - 1)) ∧
      ‖walkLogResolvent V u‖ ≤ 1 / Real.sqrt (chordRadius w u) ∧
      ‖walkLogResolvent V u‖ ^ 2 ≤ 1 / chordRadius w u := by
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
  have hr : z.re ∈ spectrum ℝ H := by
    apply (spectrum.algebraMap_mem_iff ℂ).mp
    change (z.re : ℂ) ∈ spectrum ℂ H
    rwa [← he]
  have ht := hwin hr
  refine ⟨z.re - μ, abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  dsimp [f]
  rw [he, ← Complex.exp_add]
  simp only [Complex.ofReal_re]
  congr 1
  push_cast
  ring

end RoundedClocks.WalkLog
