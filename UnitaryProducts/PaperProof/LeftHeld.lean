/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.BurgarthScaling
public import UnitaryProducts.PaperProof.ThmComparison


/-! # The introduction’s left-endpoint sampled generator -/

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
open Set Real MeasureTheory
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1: the actual left-endpoint held generator of the raw sampled
product differs from the continuous generator by at most `D/T`. -/
theorem left_held_generator_error {H Hd : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    {D : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖H (t / T) - H ((⌊t⌋ : ℝ) / T)‖ ≤ D / T := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (by norm_num))
  have hf0 : (0 : ℝ) ≤ (⌊t⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr ht.1
  have hfloor := Int.floor_le t
  have hfrac : t - (⌊t⌋ : ℝ) ≤ 1 := (Int.fract_lt_one t).le
  have hs : (⌊t⌋ : ℝ) / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hf0 hTr.le, (div_le_one hTr).mpr (hfloor.trans ht.2)⟩
  have htime : t / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩
  have hbound := norm_sub_le_of_derivWithin_le hd hD _ hs _ htime
  rw [← sub_div, abs_div, abs_of_nonneg (sub_nonneg.mpr hfloor), abs_of_pos hTr] at hbound
  calc
    _ ≤ D * ((t - (⌊t⌋ : ℝ)) / T) := hbound
    _ ≤ D * (1 / T) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hfrac hTr.le) hD0
    _ = D / T := by ring

/-- Section 1: integrating the raw left-held generator error over runtime `T`
gives a bound independent of `T`, exactly the Duhamel scaling in the prose. -/
theorem left_held_error_integral {H Hd : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    {D : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D) :
    ∫ t in (0 : ℝ)..T, ‖H (t / T) - H ((⌊t⌋ : ℝ) / T)‖ ≤ D := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  let G := fun t : ℝ ↦ H ((⌊t⌋ : ℝ) / T)
  have hGr : IsRegulated G 0 T := by
    have haux : IsRegulated G (↑(0 : ℕ)) (↑T) := by
      apply piecewise_regulated G (fun j : ℕ ↦ (j : ℝ))
        (fun j ↦ H ((j : ℝ) / T)) T
      intro j _ t ht
      have hf : ⌊t⌋ = (j : ℤ) := by
        apply Int.floor_eq_iff.mpr
        simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
          (show (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ) from ⟨ht.1.le, ht.2⟩)
      simp only [G, hf, Int.cast_natCast]
    simpa only [Nat.cast_zero] using haux
  have hc : ContinuousOn H (Icc (0 : ℝ) 1) := fun s hs ↦ (hd s hs).continuousWithinAt
  have hKc : ContinuousOn (fun t ↦ H (t / T)) (Icc (0 : ℝ) T) :=
    hc.comp (continuous_id.div_const (T : ℝ)).continuousOn
      (fun _ ht ↦ ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
  have hi := ((regulated_of_continuousOn hKc).intervalIntegrable_on hTr.le).sub
    (hGr.intervalIntegrable_on hTr.le)
  calc
    _ ≤ ∫ _t in (0 : ℝ)..T, D / T := intervalIntegral.integral_mono_on
      hTr.le hi.norm intervalIntegrable_const (fun _ ht ↦ left_held_generator_error hT hd hD ht)
    _ = D := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; field_simp

/-- The raw held product's Duhamel comparison is bounded by a runtime-independent
constant. The held evolution is identified with the sample product by the
existing piecewise-product identity. -/
theorem left_held_duhamel_bound {H Hd U V : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    {D : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D)
    (hKr : IsRegulated (fun t ↦ H (t / T)) 0 T)
    (hGr : IsRegulated (fun t ↦ H ((⌊t⌋ : ℝ) / T)) 0 T)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H ((⌊t⌋ : ℝ) / T)) V 0 T) :
    ‖V T - U T‖ ≤ ∫ t in (0 : ℝ)..T, ‖H (t / T) - H ((⌊t⌋ : ℝ) / T)‖ ∧
    (∫ t in (0 : ℝ)..T, ‖H (t / T) - H ((⌊t⌋ : ℝ) / T)‖) ≤ D := by
  exact ⟨duhamel_bound (Nat.cast_nonneg T) hKr hGr hU hV, left_held_error_integral hT hd hD⟩

end UnitaryProducts.PaperProof
