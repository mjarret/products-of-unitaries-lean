/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.SpectralWindow
public import UnitaryProducts.Paper.FineStepBounds

/-! # The circular gap in Definition 2.5 and its one-turn coordinates -/

@[expose] public section
open Complex Real Set
open UnitaryProducts UnitaryProducts.Paper
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Angular distance depends only on the two unit phases, not their representatives.
Mathlib identifies equal exponentials by an integer period; reduction modulo that
period leaves the representative defining `angularDistance` unchanged. -/
theorem angularDistance_eq_of_phase_eq {θ φ x y : ℝ}
    (hθ : Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ)))
    (hφ : Complex.exp (-I * (φ : ℂ)) = Complex.exp (-I * (y : ℂ))) :
    angularDistance θ φ = angularDistance x y := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hθ
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hφ
  have hn' : θ = x - (n : ℝ) * (2 * π) := by
    have hi := congrArg Complex.im hn
    simp at hi
    linarith
  have hm' : φ = y - (m : ℝ) * (2 * π) := by
    have hi := congrArg Complex.im hm
    simp at hi
    linarith
  have hdiff : θ - φ = (x - y) + (m - n) • (2 * π) := by
    rw [hn', hm']
    simp only [zsmul_eq_mul, Int.cast_sub]
    ring
  simp only [angularDistance, hdiff, toIcoMod_add_zsmul]

/-- Definition 2.5(ii) agrees exactly with the circular gap in one-turn coordinates.
Every complementary spectral phase has a representative between `β` and `α+2π`;
the two circular distances are then the minimum of the forward and wrapped lengths. -/
theorem spectralWindowGap_eq_circularGap {U : 𝕄} {α β : ℝ}
    (hU : star U * U = 1) (hαβ : α < β) (hβ2 : β < α + 2 * π)
    (hα : Complex.exp (-I * (α : ℂ)) ∉ spectrum ℂ U)
    (hβ : Complex.exp (-I * (β : ℂ)) ∉ spectrum ℂ U) :
    spectralWindowGap true U α β = circularGap U α β := by
  simp only [spectralWindowGap, circularGap, ↓reduceIte]
  congr 1
  ext r
  constructor
  · rintro ⟨θ, φ, hθ, hφ, rfl⟩
    obtain ⟨x, hx, hex⟩ := hθ.2
    change Complex.exp (-I * (x : ℂ)) = Complex.exp (-I * (θ : ℂ)) at hex
    obtain ⟨y, hy, hey⟩ := phase_of_unit (norm_of_mem_spectrum hU hφ.1) α
    have hxs : Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U := by
      rw [hex]
      exact hθ.1
    have hys : Complex.exp (-I * (y : ℂ)) ∈ spectrum ℂ U := by
      rw [← hey]
      exact hφ.1
    have hya : α < y := by
      apply lt_of_le_of_ne hy.1
      intro he
      exact hα (he ▸ hys)
    have hny : y ∉ Ioo α β := by
      intro hi
      exact hφ.2 ⟨y, hi, hey.symm⟩
    have hyb : β < y := by
      apply lt_of_le_of_ne (le_of_not_gt (fun h ↦ hny ⟨hya, h⟩))
      intro he
      exact hβ (he ▸ hys)
    refine ⟨x, y, hx, ⟨hyb, hy.2⟩, hxs, hys, ?_⟩
    calc
      angularDistance θ φ = angularDistance x y :=
        angularDistance_eq_of_phase_eq hex.symm hey
      _ = min (y - x) (2 * π - (y - x)) :=
        angularDistance_eq_min (by linarith [hx.2]) (by linarith [hx.1, hy.2])
  · rintro ⟨x, y, hx, hy, hxs, hys, rfl⟩
    refine ⟨x, y, ⟨hxs, ⟨x, hx, rfl⟩⟩, ⟨hys, ?_⟩, ?_⟩
    · rintro ⟨z, hz, he⟩
      have hzy := phase_inj ⟨hz.1, hz.2.trans hβ2⟩
        ⟨hαβ.trans hy.1, hy.2⟩ he
      linarith [hz.2, hy.1]
    · exact (angularDistance_eq_min (by linarith [hx.2, hy.1])
        (by linarith [hx.1, hy.2])).symm

/-- The gap of a walk band is the literal gap of Definition 2.5 at every parameter. -/
theorem walk_band_gap_eq (W : ℝ → 𝕄) (α β : ℝ → ℝ)
    (hband : circularBand W α β) (hu : (walk W 1).1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    spectralWindowGap true (W s) (α s) (β s) = circularGap (W s) (α s) (β s) := by
  have hb := hband.2.2 s hs
  exact spectralWindowGap_eq_circularGap (hu s hs) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1

/-- On arcs shorter than one turn, the moving-band predicate is precisely the
family-band predicate of Definition 2.5. Unitarity places all complementary
spectral points on that same turn, and excluded endpoints make both arcs open. -/
theorem walk_band_family_iff (W : ℝ → 𝕄) (α β : ℝ → ℝ)
    (hu : (walk W 1).1)
    (horder : ∀ s ∈ Icc (0 : ℝ) 1, α s < β s ∧ β s < α s + 2 * π) :
    circularBand W α β ↔ spectralWindowFamily true W α β := by
  constructor
  · intro hband
    refine ⟨hband.1, hband.2.1, ?_⟩
    intro s hs
    have hb := hband.2.2 s hs
    refine ⟨hu s hs, ?_, ?_, hb.2.2.1, hb.2.2.2.1⟩
    · obtain ⟨x, hx, hxs⟩ := hb.2.2.2.2.1
      exact ⟨_, hxs, x, hx, rfl⟩
    · obtain ⟨y, hy, hys⟩ := hb.2.2.2.2.2
      refine ⟨_, hys, ?_⟩
      rintro ⟨x, hx, he⟩
      have hxy := phase_inj ⟨hx.1, hx.2.trans hb.2.1⟩
        ⟨hb.1.trans hy.1, hy.2⟩ he
      linarith [hx.2, hy.1]
  · intro hfamily
    refine ⟨hfamily.1, hfamily.2.1, ?_⟩
    intro s hs
    have hb := hfamily.2.2 s hs
    have ho := horder s hs
    refine ⟨ho.1, ho.2, hb.2.2.2.1, hb.2.2.2.2, ?_, ?_⟩
    · obtain ⟨z, hzs, hzband⟩ := hb.2.1
      obtain ⟨x, hx, hex⟩ := hzband
      change Complex.exp (-I * (x : ℂ)) = z at hex
      refine ⟨x, hx, ?_⟩
      rw [hex]
      exact hzs
    · obtain ⟨z, hzs, hzout⟩ := hb.2.2.1
      obtain ⟨y, hy, hey⟩ := phase_of_unit (norm_of_mem_spectrum (hu s hs) hzs) (α s)
      have hys : Complex.exp (-I * (y : ℂ)) ∈ spectrum ℂ (W s) := by
        rw [← hey]
        exact hzs
      have hya : α s < y := by
        apply lt_of_le_of_ne hy.1
        intro he
        exact hb.2.2.2.1 (he ▸ hys)
      have hny : y ∉ Ioo (α s) (β s) := by
        intro hi
        exact hzout ⟨y, hi, hey.symm⟩
      have hyb : β s < y := by
        apply lt_of_le_of_ne (le_of_not_gt (fun h ↦ hny ⟨hya, h⟩))
        intro he
        exact hb.2.2.2.2 (he ▸ hys)
      exact ⟨y, ⟨hyb, hy.2⟩, hys⟩

end UnitaryProducts.PaperProof
