/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries

/-! # Duhamel estimate for unit-step transfer

Example 4.5 compares the floor-clock evolution with the truncated product by integrating their
Hamiltonian difference on each unit cell.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

/-- Example 4.5: the floor clock is constant on each open unit cell. -/
lemma unit_transfer_floor_cell (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ)) : (⌊x⌋ : ℝ) = j := by
  have hf : ⌊x⌋ = (j : ℤ) := Int.floor_eq_iff.mpr (by
    simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
      And.intro hx.1.le hx.2)
  rw [hf, Int.cast_natCast]

/-- Example 4.5: one whole-interval Duhamel bound compares the two sampled walks. -/
theorem unit_transfer_stepProduct_error
    (dieudonne_7_6_1 : Dieudonne_7_6_1) (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    {T : ℕ} (hT : 1 ≤ T)
    {H Hk : ℝ → Matrix (Fin d) (Fin d) ℂ}
    (hH : IsTimeDepHamiltonian H) (hHk : IsTimeDepHamiltonian Hk) :
    ‖stepProduct Hk T - stepProduct H T‖ ≤
      ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖ := by
  let K := fun x : ℝ ↦ H ((⌊x⌋ : ℝ) / T)
  let G := fun x : ℝ ↦ Hk ((⌊x⌋ : ℝ) / T)
  let t := fun j : ℕ ↦ (j : ℝ)
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have ht : ∀ j < T, t j ≤ t (j + 1) := by
    intro j _
    dsimp only [t]
    exact_mod_cast Nat.le_succ j
  have hsample (j : ℕ) (hj : j < T) : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg j) hTpos.le
    · exact (div_le_one hTpos).mpr (by exact_mod_cast hj.le)
  have hKcell : ∀ j < T, ∀ x ∈ Ioo (t j) (t (j + 1)), K x = H (j / T) := by
    intro j _ x hx
    dsimp only [K]
    rw [unit_transfer_floor_cell j hx]
  have hGcell : ∀ j < T, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = Hk (j / T) := by
    intro j _ x hx
    dsimp only [G]
    rw [unit_transfer_floor_cell j hx]
  have hKreg : IsRegulated K 0 T := by
    simpa only [t, Nat.cast_zero] using
      piecewise_regulated K t (fun j ↦ H (j / T)) T hKcell
  have hGreg : IsRegulated G 0 T := by
    simpa only [t, Nat.cast_zero] using
      piecewise_regulated G t (fun j ↦ Hk (j / T)) T hGcell
  have hfloor (x : ℝ) (hx : x ∈ Icc (0 : ℝ) T) :
      (⌊x⌋ : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
    have hlo : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := by
      exact_mod_cast (Int.floor_nonneg.mpr hx.1)
    have hhi : (⌊x⌋ : ℝ) ≤ T := (Int.floor_le x).trans hx.2
    exact ⟨div_nonneg hlo hTpos.le, (div_le_one hTpos).mpr hhi⟩
  have hKh : IsHermitianFamily K 0 T := fun x hx ↦ hH _ (hfloor x hx)
  have hGh : IsHermitianFamily G 0 T := fun x hx ↦ hHk _ (hfloor x hx)
  obtain ⟨U, hU, hUT⟩ := piecewise_product ht (fun j hj ↦ hH _ (hsample j hj)) hKcell
  obtain ⟨V, hV, hVT⟩ := piecewise_product ht (fun j hj ↦ hHk _ (hsample j hj)) hGcell
  have hU0 : Generates K U 0 T := by simpa only [t, Nat.cast_zero] using hU
  have hV0 : Generates G V 0 T := by simpa only [t, Nat.cast_zero] using hV
  have hUend : U T = stepProduct H T := by
    simpa only [t, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
      Complex.ofReal_one, mul_one, stepProduct, sampleProduct] using hUT
  have hVend : V T = stepProduct Hk T := by
    simpa only [t, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
      Complex.ofReal_one, mul_one, stepProduct, sampleProduct] using hVT
  have hcell_ae (j : ℕ) (hj : j < T) :
      (fun x ↦ ‖K x - G x‖) =ᵐ[volume.restrict (uIoc (t j) (t (j + 1)))]
        (fun _ ↦ ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖) := by
    rw [uIoc_of_le (ht j hj), ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hKcell j hj x hx, hGcell j hj x hx]
  have hcell_int (j : ℕ) (hj : j < T) :
      IntervalIntegrable (fun x ↦ ‖K x - G x‖) volume (t j) (t (j + 1)) :=
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ ↦ ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖)
      volume (t j) (t (j + 1))).congr_ae (hcell_ae j hj).symm
  have hintegral : (∫ x in (0 : ℝ)..(T : ℝ), ‖K x - G x‖) =
      ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖ := by
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (n := T) (a := t) hcell_int
    simp only [t, Nat.cast_zero] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_congr_ae_restrict (hcell_ae j (Finset.mem_range.mp hj))]
    simp only [intervalIntegral.integral_const, t, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_left, one_smul]
  have hduhamel :=
    duhamel dieudonne_7_6_1 dieudonne_section_8_7 hTpos.le hKreg hKh hGreg hGh hU0 hV0
  rw [hUend, hVend, hintegral] at hduhamel
  exact hduhamel

end RoundedClocks
