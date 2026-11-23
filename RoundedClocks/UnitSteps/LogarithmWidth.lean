/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-! # Width of the logarithm spectrum

Corollary 4.7 places the extreme Hermitian eigenvalues on opposite sides of the band cut and bounds
their separation by the complementary unitary gap.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section

namespace RoundedClocks.WalkLeakageSpectrum

/-- The least and greatest spectral values lie on opposite sides of the band cut. -/
theorem extrema_straddle {d : ℕ} {H W : Matrix (Fin d) (Fin d) ℂ}
    {α β ℓ φ : ℝ} (hband : IsArcBand W α β)
    (himage : spectrum ℂ W =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ H)
    (hopen : HasRealSpectrumIn H (Ioo α (α + 2 * π)))
    (hℓ : IsLeast (spectrum ℝ H) ℓ) (hφ : IsGreatest (spectrum ℝ H) φ) :
    ℓ ∈ Ioo α β ∧ φ ∈ Ioo β (α + 2 * π) := by
  obtain ⟨z, hz, hzb⟩ := hband.2.2.2.1
  obtain ⟨x, hx, rfl⟩ := himage ▸ hz
  have hxb := (phase_mem_arc_iff hband.2.2.1 (hopen hx)).mp hzb
  obtain ⟨z, hz, hzb⟩ := hband.2.2.2.2.1
  obtain ⟨y, hy, rfl⟩ := himage ▸ hz
  have hby : β < y := by
    have hne : y ≠ β := by
      intro heq
      subst y
      exact hband.2.2.2.2.2.2 hz
    have hn : ¬ y < β := by
      intro hlt
      exact hzb ((phase_mem_arc_iff hband.2.2.1 (hopen hy)).mpr
        ⟨(hopen hy).1, hlt⟩)
    exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
  exact ⟨⟨(hopen hℓ.1).1, (hℓ.2 hx).trans_lt hxb.2⟩,
    ⟨hby.trans_le (hφ.2 hy), (hopen hφ.1).2⟩⟩

/-- The wraparound distance of the extreme pair bounds the eigenphase gap. -/
theorem extreme_gap_le {d : ℕ} {H W : Matrix (Fin d) (Fin d) ℂ}
    {α β ℓ φ : ℝ} (hband : IsArcBand W α β)
    (himage : spectrum ℂ W =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ H)
    (hopen : HasRealSpectrumIn H (Ioo α (α + 2 * π)))
    (hℓ : IsLeast (spectrum ℝ H) ℓ) (hφ : IsGreatest (spectrum ℝ H) φ) :
    eigenphaseGap W α β ≤ 2 * π - (φ - ℓ) := by
  obtain ⟨hleft, hright⟩ := extrema_straddle hband himage hopen hℓ hφ
  have hmem : ∀ x ∈ spectrum ℝ H,
      Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ W := by
    intro x hx
    rw [himage]
    exact ⟨x, hx, rfl⟩
  have hnonneg : ∀ x y : ℝ, 0 ≤ circleDistance x y := by
    intro x y
    exact le_ciInf fun k ↦ abs_nonneg _
  have hgap : eigenphaseGap W α β ≤ circleDistance ℓ φ := by
    apply csInf_le
    · exact ⟨0, by rintro r ⟨x, y, hx, hy, rfl⟩; exact hnonneg x y⟩
    · refine ⟨ℓ, φ, ⟨hmem ℓ hℓ.1, ⟨ℓ, hleft, rfl⟩⟩, ?_, rfl⟩
      refine ⟨hmem φ hφ.1, ?_⟩
      intro h
      have hf := (phase_mem_arc_iff hband.2.2.1 (hopen hφ.1)).mp h
      exact (not_lt_of_ge hright.1.le) hf.2
  have hwrap : circleDistance ℓ φ ≤ |ℓ - φ + 2 * π * (1 : ℤ)| :=
    ciInf_le ⟨0, by rintro r ⟨k, rfl⟩; exact abs_nonneg _⟩ (1 : ℤ)
  have hpos : 0 ≤ ℓ - φ + 2 * π * (1 : ℤ) := by
    have hl := (hopen hℓ.1).1
    have hr := (hopen hφ.1).2
    push_cast
    linarith
  rw [abs_of_nonneg hpos] at hwrap
  calc
    eigenphaseGap W α β ≤ circleDistance ℓ φ := hgap
    _ ≤ ℓ - φ + 2 * π * (1 : ℤ) := hwrap
    _ = 2 * π - (φ - ℓ) := by push_cast; ring

/-- The real spectrum fits in the interval based at its minimum with complementary-gap width. -/
theorem spectrum_enclosure {d : ℕ} {H W : Matrix (Fin d) (Fin d) ℂ}
    {α β ϑ : ℝ} (hband : IsArcBand W α β)
    (himage : spectrum ℂ W =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ H)
    (hopen : HasRealSpectrumIn H (Ioo α (α + 2 * π)))
    (hϑ : ϑ ≤ eigenphaseGap W α β) :
    IsLeast (spectrum ℝ H) (sInf (spectrum ℝ H)) ∧
      HasRealSpectrumIn H
        (Icc (sInf (spectrum ℝ H)) (sInf (spectrum ℝ H) + (2 * π - ϑ))) := by
  have hne : (spectrum ℝ H).Nonempty := by
    obtain ⟨z, hz, _⟩ := hband.2.2.2.1
    obtain ⟨x, hx, _⟩ := himage ▸ hz
    exact ⟨x, hx⟩
  have hc := spectrum.isCompact (𝕜 := ℝ) H
  have hl := hc.isLeast_sInf hne
  have hr := hc.isGreatest_sSup hne
  have hg := extreme_gap_le hband himage hopen hl hr
  refine ⟨hl, ?_⟩
  intro x hx
  exact ⟨hl.2 hx, by have hh := hr.2 hx; linarith⟩

end RoundedClocks.WalkLeakageSpectrum
