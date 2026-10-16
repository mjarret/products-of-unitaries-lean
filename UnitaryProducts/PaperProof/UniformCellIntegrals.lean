/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.RoundedClockQuarter

/-!
# Centered-cell integration of the periodic clock profile

## Declarations

- `clock_profile_subcell`
- `clock_profile_cell_split`
- `uniform_clock_integral_full`
- `uniform_clock_integral_subcell`
-/

@[expose] public section
noncomputable section
open Real Set MeasureTheory
open UnitaryProducts.Paper.UnitStepsProse
namespace UnitaryProducts.PaperProof

/-- Translate a continuous profile on any part of a rounded cell by `u = t-j`.
The rounding ties are null sets, so no evenness assumption is needed. -/
theorem clock_profile_subcell (j : ℤ) {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (ha : -(1 / 2 : ℝ) ≤ a) (hb : b ≤ 1 / 2) :
    IntervalIntegrable (fun t ↦ f (t - clock t)) volume (j + a) (j + b) ∧
    (∫ t in (j + a)..(j + b), f (t - clock t)) = ∫ u in a..b, f u := by
  have he : Set.EqOn (fun t ↦ f (t - (j : ℝ)))
      (fun t ↦ f (t - clock t)) (Ioo (j + a) (j + b)) := by
    intro t ht
    have hclock : clock t = j := clock_eq_of_abs_sub_lt
      (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp only [hclock]
  have hae := ae_eq_of_eqOn_Ioo (show (j : ℝ) + a ≤ j + b by linarith) he
  have hi : IntervalIntegrable (fun t ↦ f (t - (j : ℝ))) volume (j + a) (j + b) :=
    (hf.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  refine ⟨hi.congr_ae hae, ?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict hae.symm,
    intervalIntegral.integral_comp_sub_right]
  simp only [add_sub_cancel_left]

/-- Theorem 4.2 residual computation: split `[k,k+1]` at its rounding switch. Translating
its two halves gives the positive and negative halves of the same profile. -/
theorem clock_profile_unit_interval (k : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun t ↦ f (t - clock t)) volume k (k + 1) ∧
    (∫ t in (k : ℝ)..(k + 1), f (t - clock t)) =
      (∫ t in (k : ℝ)..(k + 1 / 2), f (t - k)) +
      (∫ t in ((k : ℝ) + 1 / 2)..(k + 1), f (t - k - 1)) ∧
    (∫ t in (k : ℝ)..(k + 1), f (t - clock t)) =
      ∫ u in (-(1 / 2) : ℝ)..(1 / 2), f u := by
  have hleft := clock_profile_subcell (k : ℤ) hf (a := 0) (b := 1 / 2)
    (by norm_num) (by norm_num) le_rfl
  have hright := clock_profile_subcell ((k : ℤ) + 1) hf (a := -(1 / 2)) (b := 0)
    (by norm_num) le_rfl (by norm_num)
  have he : (k : ℝ) + 1 + -(1 / 2) = k + 1 / 2 := by ring
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_one, add_zero, he] at hleft hright
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft.1 hright.1
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-(1 / 2)) 0) (hf.intervalIntegrable 0 (1 / 2))
  refine ⟨hleft.1.trans hright.1, ?_, ?_⟩
  · rw [← hsplit, hleft.2, hright.2, intervalIntegral.integral_comp_sub_right]
    have htranslate := intervalIntegral.integral_comp_sub_right f ((k : ℝ) + 1)
      (a := (k : ℝ) + 1 / 2) (b := (k : ℝ) + 1)
    simp only [sub_add_eq_sub_sub] at htranslate
    rw [htranslate]
    simp only [sub_self, add_sub_cancel_left]
    norm_num
  · rw [← hsplit, hleft.2, hright.2, add_comm, hsum]

/-- Theorem 4.2 residual computation's literal floor split: each of the `T` unit intervals
contributes one full profile integral. This also covers `T = 1`. -/
theorem clock_profile_cell_split (T : ℕ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IntervalIntegrable (fun t ↦ f (t - clock t)) volume 0 T ∧
    (∫ t in (0 : ℝ)..T, f (t - clock t)) =
      ∑ k ∈ Finset.range T,
        ((∫ t in (k : ℝ)..(k + 1 / 2), f (t - k)) +
         (∫ t in ((k : ℝ) + 1 / 2)..(k + 1), f (t - k - 1))) ∧
    (∫ t in (0 : ℝ)..T, f (t - clock t)) =
      (T : ℝ) * ∫ u in (-(1 / 2) : ℝ)..(1 / 2), f u := by
  have hi (k : ℕ) (_hk : k < T) :
      IntervalIntegrable (fun t ↦ f (t - clock t)) volume k ((k + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (clock_profile_unit_interval k hf).1
  have hint := IntervalIntegrable.trans_iterate (a := fun k : ℕ ↦ (k : ℝ)) hi
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hi
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hint hsum
  refine ⟨hint, ?_, ?_⟩
  · rw [← hsum]
    exact Finset.sum_congr rfl (fun k _ ↦ (clock_profile_unit_interval k hf).2.1)
  · rw [← hsum]
    simp only [(clock_profile_unit_interval _ hf).2.2,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- On any part of a centered cell, integrate an even clock profile by the
local variable `τ = Ns-j`. The equality includes both rounding ties. -/
theorem uniform_clock_integral_subcell {N : ℕ} (j : ℤ)
    {f : ℝ → ℝ} (he : ∀ t, f (-t) = f t) {a b : ℝ}
    (hab : a ≤ b) (ha : -(1 / 2 : ℝ) ≤ a) (hb : b ≤ 1 / 2) :
    (∫ s in (((j : ℝ) + a) / N)..(((j : ℝ) + b) / N), f (((N : ℝ) * s - clock (N * s)))) =
      (1 / N) * ∫ t in a..b, f t := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hslope : ((j : ℝ) + a) / N ≤ ((j : ℝ) + b) / N := by gcongr
  trans ∫ s in (((j : ℝ) + a) / N)..(((j : ℝ) + b) / N), f (-(j : ℝ) + N * s)
  · apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hslope] at hs
    have hlo := (div_le_iff₀' hn).mp hs.1
    have hhi := (le_div_iff₀' hn).mp hs.2
    have hdist : |(N : ℝ) * s - j| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hclock : |((N : ℝ) * s - clock (N * s))| = |(N : ℝ) * s - j| := by
      simpa only [abs_sub_comm] using clock_error_eq_on_closed_cell j hdist
    simp only [neg_add_eq_sub]
    rcases abs_eq_abs.mp hclock with h | h <;> rw [h]
    exact he _
  · simpa only [mul_div_cancel₀ _ hn.ne', neg_add_cancel_left, smul_eq_mul, one_div] using
      intervalIntegral.integral_comp_add_mul
        (a := ((j : ℝ) + a) / N) (b := ((j : ℝ) + b) / N) f hn.ne' (-(j : ℝ))

/-- the proof of Theorem 4.2: the full centered-cell integral and each half-cell integral.
The two halves agree for an even continuous profile, and the N-1 full cells
plus the two endpoint halves have the same weight as N full cells, also at N=1. -/
theorem uniform_clock_integral_full {N : ℕ} (hN : 1 ≤ N) (j : ℤ)
    {f : ℝ → ℝ} (hc : Continuous f) (he : ∀ t, f (-t) = f t) :
    (∫ s in (((j : ℝ) - 1 / 2) / N)..(((j : ℝ) + 1 / 2) / N), f (((N : ℝ) * s - clock (N * s)))) =
      (1 / N) * (∫ t in (-(1 / 2) : ℝ)..(1 / 2), f t) ∧
    (∫ s in (((j : ℝ) - 1 / 2) / N)..((j : ℝ) / N), f (((N : ℝ) * s - clock (N * s)))) =
      (1 / N) * (∫ t in (-(1 / 2) : ℝ)..0, f t) ∧
    (∫ s in ((j : ℝ) / N)..(((j : ℝ) + 1 / 2) / N), f (((N : ℝ) * s - clock (N * s)))) =
      (1 / N) * (∫ t in (0 : ℝ)..(1 / 2), f t) ∧
    (∫ t in (-(1 / 2) : ℝ)..0, f t) = (∫ t in (0 : ℝ)..(1 / 2), f t) ∧
    ((N - 1 : ℕ) : ℝ) * ((1 / N) * (∫ t in (-(1 / 2) : ℝ)..(1 / 2), f t)) +
      (1 / N) * (∫ t in (-(1 / 2) : ℝ)..0, f t) +
      (1 / N) * (∫ t in (0 : ℝ)..(1 / 2), f t) =
        (∫ t in (-(1 / 2) : ℝ)..(1 / 2), f t) := by
  have hcell (a b : ℝ) := uniform_clock_integral_subcell (N := N) j he (a := a) (b := b)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sub_eq_add_neg] using
      hcell (-(1 / 2)) (1 / 2) (by norm_num) le_rfl le_rfl
  · simpa only [sub_eq_add_neg, add_zero] using
      hcell (-(1 / 2)) 0 (by norm_num) le_rfl (by norm_num)
  · simpa only [add_zero] using hcell 0 (1 / 2) (by norm_num) (by norm_num) le_rfl
  · simpa only [he, neg_zero] using
      (intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := 1 / 2)).symm
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc.intervalIntegrable (-(1 / 2)) 0) (hc.intervalIntegrable 0 (1 / 2))
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_sub hN, Nat.cast_one, ← hsplit]
    field_simp
    ring

end UnitaryProducts.PaperProof
