/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.PointwiseLogarithm

/-! # Chords inside the logarithmic domain

Lemma A.2 places every point of the chord from `1` to the unitary matrix inside the domain of the
principal logarithm.
-/

@[expose] public section

open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

attribute [local instance] matrixCStarAlgebra

/-- A phase strictly inside the principal turn avoids the logarithmic cut. -/
theorem phase_mem_slitPlane {φ : ℝ} (hφ : φ ∈ Ioo (-π) π) :
    Complex.exp (-I * (φ : ℂ)) ∈ Complex.slitPlane := by
  have him : (-I * (φ : ℂ)).im = -φ := by simp
  rw [Complex.exp_mem_slitPlane, him,
    (toIocMod_eq_self Real.two_pi_pos).2
      (show -φ ∈ Ioc (-π) (-π + 2 * π) from
        ⟨by linarith [hφ.2], by linarith [hφ.1]⟩)]
  linarith [hφ.1]

/-- Every chord from one to a point off the cut avoids zero, including its endpoints. -/
theorem chord_ne_zero {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 1 + u • (z - 1) ≠ 0 := by
  have hz' : 1 + (z - 1) ∈ Complex.slitPlane := by simpa using hz
  exact Complex.slitPlane_ne_zero
    (StarConvex.add_smul_mem Complex.starConvex_one_slitPlane hz' hu.1 hu.2)

/-- Functional calculus transfers the scalar chord gate without constructing a logarithm. -/
theorem isUnit_phase_chord {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : star W * W = 1) (c : ℂ)
    (hc : ∀ z ∈ spectrum ℂ W, c * z ∈ Complex.slitPlane)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    IsUnit (1 + u • (c • W - 1)) := by
  letI : IsStarNormal W :=
    ⟨by change star W * W = W * star W; rw [hW, mul_eq_one_comm.mp hW]⟩
  have he : cfc (fun z : ℂ ↦ 1 + u • (c * z - 1)) W =
      1 + u • (c • W - 1) := by
    rw [cfc_const_add (p := IsStarNormal) 1 _ W (by fun_prop) inferInstance,
      cfc_smul u _ W (by fun_prop), cfc_sub (fun z : ℂ ↦ c * z) (fun _ ↦ 1) W]
    rw [show (fun z : ℂ ↦ c * z) = (fun z : ℂ ↦ c • z) by rfl,
      cfc_smul c _ W (by fun_prop), cfc_id' ℂ W, cfc_const (p := IsStarNormal) 1 W]
    simp only [map_one]
  rw [← he]
  apply isUnit_cfc (p := IsStarNormal) (fun z : ℂ ↦ 1 + u • (c * z - 1)) W
    (by fun_prop) inferInstance
  exact fun z hz ↦ chord_ne_zero (hc z hz) hu

/-- Continuity with margin `(π-w/2)/2` gives the input-only local chord gate.
The center stays fixed at `a s₀+w/2`; relative neighborhoods include both endpoints,
and the statement permits `w=0`. -/
theorem eventually_isUnit_phase_chord {d : ℕ} {W : ℝ → Matrix (Fin d) (Fin d) ℂ}
    {a : ℝ → ℝ} {w s₀ : ℝ} (hw : w < 2 * π)
    (ha : ContinuousWithinAt a (Icc (0 : ℝ) 1) s₀)
    (hW : IsUnitaryFamily W 0 1) (harc : HasSpectrumInPhaseInterval W a w) :
    ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] s₀,
      |a s - a s₀| < (π - w / 2) / 2 ∧
      ∀ u ∈ Icc (0 : ℝ) 1,
        IsUnit (1 + u • (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s - 1)) := by
  have hm : 0 < (π - w / 2) / 2 := by linarith
  have hn := ha (Metric.ball_mem_nhds (a s₀) hm)
  filter_upwards [hn, self_mem_nhdsWithin] with s hs hsI
  have hs' : |a s - a s₀| < (π - w / 2) / 2 := by
    simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using hs
  refine ⟨hs', fun u hu ↦ isUnit_phase_chord (W s) (hW s hsI) _ ?_ hu⟩
  intro z hz
  obtain ⟨θ, hθ, rfl⟩ := harc s hsI z hz
  rw [← Complex.exp_add]
  have he : I * ((a s₀ + w / 2 : ℝ) : ℂ) + -I * (θ : ℂ) =
      -I * ((θ - (a s₀ + w / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  apply phase_mem_slitPlane
  have hb := abs_lt.mp hs'
  constructor <;> linarith [hθ.1, hθ.2]

end RoundedClocks.WalkLog
