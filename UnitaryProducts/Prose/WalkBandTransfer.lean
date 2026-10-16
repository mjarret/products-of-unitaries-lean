/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Spectral.TrackedBandGap

/-!
# Distance to eigenphases and the closed spectral arc supplied by a band

## Declarations

- `band_pair_gap_display`
- `extreme_pair_width`
-/

@[expose] public section

open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.Prose


variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


omit [NeZero d] in
/-- The display in the proof of the spectral comparison: for phases `θ < β < φ` of one turn with
`e^{-iθ}`
in the band and `e^{-iφ}` outside it,
`Γ(W) ≤ min_k |θ - φ + 2πk| ≤ min {φ - θ, 2π - (φ - θ)}`; the first inequality is
Definition 2.5(ii) (`circularGap_le_gb` in the normal form `angularDistance_eq_min`), the
second is `k = 0` and `k = 1`. -/
theorem band_pair_gap_display {U : 𝕄} {α β θ φ : ℝ} (hθ : θ ∈ Ioo α β)
    (hφ : φ ∈ Ioo β (α + 2 * π))
    (hθs : Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U)
    (hφs : Complex.exp (-I * (φ : ℂ)) ∈ spectrum ℂ U) :
    Paper.circularGap U α β ≤ sInf (Set.range (fun k : ℤ ↦ |θ - φ + 2 * π * k|)) ∧
      sInf (Set.range (fun k : ℤ ↦ |θ - φ + 2 * π * k|)) ≤ min (φ - θ) (2 * π - (φ - θ)) := by
  have hle : θ ≤ φ := (hθ.2.trans hφ.1).le
  have hwrap : φ - θ ≤ 2 * π := by linarith [hθ.1, hφ.2]
  refine ⟨?_, circular_phase_inf_le_min hle hwrap⟩
  have hg := Paper.circularGap_le_gb hθ hφ hθs hφs
  have hdist := (Paper.angularDistance_isLeast θ φ).csInf_eq
  rw [Paper.angularDistance_eq_min hle hwrap] at hdist
  exact hg.trans_eq hdist.symm

/-- the spectral comparison: the least and greatest eigenvalues `l < β < r` are a cross-band pair,
and
the second term of the display gives `r - l ≤ 2π - Γ(W) ≤ 2π - ϑ`. -/
theorem extreme_pair_width {A U : 𝕄} (hA : A.IsHermitian) (he : evol A 1 = U)
    {α β ϑ : ℝ} (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π))
    (hβ : β < α + 2 * π)
    (hband : ∃ θ ∈ Ioo α β, Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U)
    (hcomp : ∃ θ ∈ Ioo β (α + 2 * π),
      Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U)
    (hϑ : ϑ ≤ Paper.circularGap U α β) :
    (-spectralBottom (-A)) - spectralBottom A ≤ 2 * π - Paper.circularGap U α β ∧
    2 * π - Paper.circularGap U α β ≤ 2 * π - ϑ := by
  have hl := isLeast_spectralBottom hA
  have hr := isGreatest_spectralTop hA
  have himg : ∀ x ∈ spectrum ℝ A,
      Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U := by
    intro x hx
    rw [← he, spectrum_evol_image hA]
    exact ⟨x, hx, rfl⟩
  have hstraddle := spectral_extrema_straddle_cut hA
    (by rw [← he, spectrum_evol_image hA]) hopen hβ hband hcomp
  have hdisplay := band_pair_gap_display
    ⟨(hopen _ hl.1).1, hstraddle.1⟩ ⟨hstraddle.2, (hopen _ hr.1).2⟩
    (himg _ hl.1) (himg _ hr.1)
  have hgap := (hdisplay.1.trans hdisplay.2).trans (min_le_right _ _)
  exact ⟨by linarith, by linarith⟩

end UnitaryProducts.Prose
