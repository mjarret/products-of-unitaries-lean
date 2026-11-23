/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.LogarithmChord
public import RoundedClocks.Appendix.LogarithmResolventCalculus

/-! # Principal logarithm integral

Lemma A.2 identifies the chord integral with the principal logarithm and transfers this identity
to matrices through the resolvent calculus.
-/

@[expose] public section

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology

noncomputable section
namespace RoundedClocks.WalkLog

open WalkLogCalculus

attribute [local instance] matrixCStarAlgebra

/-- Lemma A.2: Mathlib's principal-log integral along the segment from `1` to `z`. -/
theorem integral_log_chord {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (∫ u : ℝ in (0 : ℝ)..1, (z - 1) / (1 + (u : ℂ) * (z - 1))) = Complex.log z := by
  have hlog := Complex.log_eq_integral (z := z - 1) (by simpa using hz)
  simpa only [add_sub_cancel, div_eq_mul_inv, Complex.real_smul,
    intervalIntegral.integral_const_mul] using hlog.symm

/-- The functional calculus preserves the scalar logarithm integral. -/
theorem walkLogIntegral_eq_cfc {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) [IsStarNormal V]
    (hspec : spectrum ℂ V ⊆ Complex.slitPlane) :
    walkLogIntegral V = cfc Complex.log V := by
  let f : ℝ → ℂ → ℂ := fun t z ↦ (z - 1) * (1 + t • (z - 1))⁻¹
  have hf : ContinuousOn (Function.uncurry f) (Icc (0 : ℝ) 1 ×ˢ spectrum ℂ V) := by
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.inv₀ (by fun_prop)
    intro p hp
    exact chord_ne_zero (hspec hp.2) hp.1
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (spectrum.isCompact V)).exists_bound_of_continuousOn hf
  have hcfc := cfc_setIntegral (μ := volume) measurableSet_Icc f (fun _ ↦ C) V hf
    (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht z hz ↦ hC (t, z) ⟨ht, hz⟩))
    (integrableOn_const (C := C) isCompact_Icc.measure_lt_top.ne (by finiteness)).hasFiniteIntegral
  have hscalar : ∀ z ∈ spectrum ℂ V, ∫ t in Icc (0 : ℝ) 1, f t z = Complex.log z := by
    intro z hz
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change (∫ t : ℝ in (0 : ℝ)..1, (z - 1) * (1 + t • (z - 1))⁻¹) = Complex.log z
    simpa only [div_eq_mul_inv, Complex.real_smul] using integral_log_chord (hspec hz)
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      cfc (f t) V = (V - 1) * walkLogResolvent V t := by
    intro t ht
    have hne : ∀ z ∈ spectrum ℂ V, 1 + t • (z - 1) ≠ 0 := fun z hz ↦
      chord_ne_zero (hspec hz) ht
    change cfc (fun z : ℂ ↦ (z - 1) * (1 + t • (z - 1))⁻¹) V = _
    have hinv : ContinuousOn (fun z : ℂ ↦ (1 + t • (z - 1))⁻¹) (spectrum ℂ V) :=
      (by fun_prop : ContinuousOn (fun z : ℂ ↦ 1 + t • (z - 1)) (spectrum ℂ V)).inv₀ hne
    rw [cfc_mul (fun z : ℂ ↦ z - 1) (fun z : ℂ ↦ (1 + t • (z - 1))⁻¹)
      V (by fun_prop) hinv,
      cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
      cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V,
      cfc_inv (p := IsStarNormal) (fun z : ℂ ↦ 1 + t • (z - 1)) V hne
        (by fun_prop) inferInstance,
      cfc_const_add (p := IsStarNormal) 1 _ V (by fun_prop) inferInstance,
      cfc_smul t _ V (by fun_prop),
      cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ 1) V,
      cfc_id' ℂ V, cfc_const (p := IsStarNormal) 1 V]
    simp only [map_one, walkLogResolvent]
  rw [cfc_congr hscalar] at hcfc
  rw [walkLogIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, hcfc]
  exact integral_congr_ae
    (ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ (hpoint t ht).symm)

end RoundedClocks.WalkLog
