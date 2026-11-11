/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnifiedQuadrature
public import UnitaryProducts.Prose.RoundedClockQuarter

/-! # Scaling of the integrated generator difference in the introduction -/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Real Set Matrix Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The held Hamiltonian on an integer time cell integrates to the
trapezoidal average of its endpoint samples. -/
theorem rounded_cell_integral (H : ℝ → 𝕄) {T j : ℕ} (hj : j < T) :
    (∫ t in (j : ℝ)..(j + 1 : ℝ), H ((⌊t + 1 / 2⌋ : ℝ) / T)) =
      (1 / 2 : ℝ) • (H ((j : ℝ) / T) + H ((j + 1 : ℝ) / T)) := by
  let G := fun t : ℝ ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)
  have hglobal : IntervalIntegrable G volume 0 T :=
    (rounded_hamiltonian_regulated H T).intervalIntegrable_on (Nat.cast_nonneg T)
  have hjT : (j : ℝ) + 1 ≤ T := by exact_mod_cast hj
  have hl : IntervalIntegrable G volume j (j + 1 / 2) := by
    apply hglobal.mono_set
    rw [uIcc_of_le (by linarith), uIcc_of_le (Nat.cast_nonneg T)]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (by linarith)
  have hr : IntervalIntegrable G volume (j + 1 / 2) (j + 1) := by
    apply hglobal.mono_set
    rw [uIcc_of_le (by linarith), uIcc_of_le (Nat.cast_nonneg T)]
    exact Icc_subset_Icc (by positivity) hjT
  have hleft : (∫ t in (j : ℝ)..(j + 1 / 2), G t) = (1 / 2 : ℝ) • H ((j : ℝ) / T) := by
    calc
      _ = ∫ _t in (j : ℝ)..(j + 1 / 2), H ((j : ℝ) / T) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne ((j : ℝ) + 1 / 2)] with t hne
        intro ht
        rw [uIoc_of_le (by linarith)] at ht
        have hfloor : ⌊t + 1 / 2⌋ = (j : ℤ) := by
          apply Int.floor_eq_iff.mpr
          simp only [Int.cast_natCast]
          constructor <;> linarith [ht.1, ht.2, (lt_of_le_of_ne ht.2 hne)]
        simp only [G, hfloor, Int.cast_natCast]
      _ = _ := by rw [intervalIntegral.integral_const]; congr 1; ring
  have hright : (∫ t in ((j : ℝ) + 1 / 2)..(j + 1), G t) =
      (1 / 2 : ℝ) • H ((j + 1 : ℝ) / T) := by
    calc
      _ = ∫ _t in ((j : ℝ) + 1 / 2)..(j + 1), H ((j + 1 : ℝ) / T) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith)] at ht
        have hfloor : ⌊t + 1 / 2⌋ = (j : ℤ) + 1 := by
          apply Int.floor_eq_iff.mpr
          simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]
          constructor <;> linarith [ht.1, ht.2]
        simp only [G, hfloor, Int.cast_add, Int.cast_natCast, Int.cast_one]
      _ = _ := by rw [intervalIntegral.integral_const]; congr 1; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, hleft, hright, smul_add]

/-- The integrated generator difference over a complete integer cell has
second-order size, by the already proved trapezoidal quadrature estimate. -/
theorem primitive_cell_bound {H Hd : ℝ → 𝕄} {T j : ℕ} (hT : 0 < T) (hj : j < T)
    {D L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) :
    ‖∫ t in (j : ℝ)..(j + 1 : ℝ), H (t / T) - H ((⌊t + 1 / 2⌋ : ℝ) / T)‖ ≤
      3 * L / (4 * (T : ℝ) ^ 2) := by
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hpath : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H t - H s‖ ≤ D * |t - s| :=
    fun s hs t ht ↦ norm_sub_le_of_derivWithin_le hd hD s hs t ht
  have hb := (quadrature_local_orders hT hj hd hpath hlip).2
  have hHc : ContinuousOn H (Icc (0 : ℝ) 1) := fun s hs ↦ (hd s hs).continuousWithinAt
  have hKc : ContinuousOn (fun t ↦ H (t / T)) (Icc (0 : ℝ) T) :=
    hHc.comp (continuous_id.div_const (T : ℝ)).continuousOn
      (fun _ ht ↦ ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
  have hKi : IntervalIntegrable (fun t ↦ H (t / T)) volume j (j + 1) := by
    apply (Prose.regulated_of_continuousOn hKc).intervalIntegrable_on hTr.le |>.mono_set
    rw [uIcc_of_le (by linarith), uIcc_of_le hTr.le]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (by exact_mod_cast hj)
  have hGi : IntervalIntegrable (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) volume j (j + 1) := by
    apply (rounded_hamiltonian_regulated H T).intervalIntegrable_on hTr.le |>.mono_set
    rw [uIcc_of_le (by linarith), uIcc_of_le hTr.le]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (by exact_mod_cast hj)
  rw [intervalIntegral.integral_sub hKi hGi, rounded_cell_integral H hj, norm_sub_rev]
  have hchange := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1)
    (fun x ↦ H (x / T)) (j : ℝ)
  simp only [add_zero] at hchange
  rw [hchange] at hb
  exact hb

/-- The primitive of the rounded generator error is uniformly `O(1/T)` on
all physical times, including incomplete cells. Complete cells use cancellation;
the last partial cell is bounded directly by the first derivative. -/
theorem burgarth_primitive_bound {H Hd : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    {D L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖∫ u in (0 : ℝ)..t, H (u / T) - H ((⌊u + 1 / 2⌋ : ℝ) / T)‖ ≤
      (3 * L / 4 + D / 2) / T := by
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (by norm_num))
  have hL0 : 0 ≤ L := by
    have h := hlip 0 (by norm_num) 1 (by norm_num)
    simpa only [sub_zero, abs_one, mul_one] using (norm_nonneg _).trans h
  let R := fun u : ℝ ↦ H (u / T) - H ((⌊u + 1 / 2⌋ : ℝ) / T)
  have hHc : ContinuousOn H (Icc (0 : ℝ) 1) := fun s hs ↦ (hd s hs).continuousWithinAt
  have hKc : ContinuousOn (fun t ↦ H (t / T)) (Icc (0 : ℝ) T) :=
    hHc.comp (continuous_id.div_const (T : ℝ)).continuousOn
      (fun _ ht ↦ ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
  have hRi : IntervalIntegrable R volume 0 T :=
    ((Prose.regulated_of_continuousOn hKc).intervalIntegrable_on hTr.le).sub
      ((rounded_hamiltonian_regulated H T).intervalIntegrable_on hTr.le)
  let n : ℕ := ⌊t⌋₊
  have hnlo : (n : ℝ) ≤ t := Nat.floor_le ht.1
  have hnhi : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
  have hnT : n ≤ T := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono ht.2
  have hni : IntervalIntegrable R volume 0 n := by
    apply hRi.mono_set
    rw [uIcc_of_le (Nat.cast_nonneg n), uIcc_of_le hTr.le]
    exact Icc_subset_Icc le_rfl (Nat.cast_le.mpr hnT)
  have hti : IntervalIntegrable R volume n t := by
    apply hRi.mono_set
    rw [uIcc_of_le hnlo, uIcc_of_le hTr.le]
    exact Icc_subset_Icc (Nat.cast_nonneg n) ht.2
  have hprefix : ‖∫ u in (0 : ℝ)..n, R u‖ ≤ 3 * L / (4 * T) := by
    rw [← quadrature_integral_partition n hni]
    calc
      _ ≤ ∑ j ∈ Finset.range n, ‖∫ u in (0 : ℝ)..1, R ((j : ℝ) + u)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 3 * L / (4 * (T : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hbound := primitive_cell_bound hT
          ((Finset.mem_range.mp hj).trans_le hnT) hd hD hlip
        have hchange := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := 1) R (j : ℝ)
        simp only [add_zero] at hchange
        rw [hchange]
        exact hbound
      _ = (n : ℝ) * (3 * L / (4 * (T : ℝ) ^ 2)) := by simp
      _ ≤ (T : ℝ) * (3 * L / (4 * (T : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnT) (by positivity)
      _ = 3 * L / (4 * T) := by field_simp
  have hpartial : ‖∫ u in (n : ℝ)..t, R u‖ ≤ D / (2 * T) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := R)
      (a := (n : ℝ)) (b := t) (C := D / (2 * T)) (by
        intro u hu
        rw [uIoc_of_le hnlo] at hu
        have huT : u ∈ Icc (0 : ℝ) T := ⟨(Nat.cast_nonneg n).trans hu.1.le, hu.2.trans ht.2⟩
        simpa only [R, norm_sub_rev] using
          ((rounded_hamiltonian_error_chain hd hD huT).1.trans
            (rounded_hamiltonian_error_chain hd hD huT).2))
    rw [abs_of_nonneg (sub_nonneg.mpr hnlo)] at hb
    exact hb.trans (mul_le_of_le_one_right (by positivity) (by linarith))
  change ‖∫ u in (0 : ℝ)..t, R u‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hni hti]
  exact (norm_add_le _ _).trans ((add_le_add hprefix hpartial).trans_eq (by ring))

/-- The introduction's primitive bound under exactly a Lipschitz derivative;
the derivative supremum is finite because the interval is compact. -/
theorem burgarth_primitive_uniform {H Hd : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    {L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖∫ u in (0 : ℝ)..t, H (u / T) - H ((⌊u + 1 / 2⌋ : ℝ) / T)‖ ≤
        (3 * L / 4 + unitSupNorm Hd / 2) / T := by
  have hdc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  exact fun _ ht ↦ burgarth_primitive_bound hT hd (fun _ hs ↦ norm_le_unitSupNorm hdc hs) hlip ht

/-- Any choice of a time in the physical interval has the same inverse-runtime
bound; its implied constant is independent of that choice of times. -/
theorem burgarth_primitive_bigO {H Hd : ℝ → 𝕄} {L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (τ : ℕ → ℝ) (hτ : ∀ T : ℕ, 0 < T → τ T ∈ Icc (0 : ℝ) T) :
    (fun T : ℕ ↦ ∫ u in (0 : ℝ)..τ T,
      H (u / T) - H ((⌊u + 1 / 2⌋ : ℝ) / T)) =O[atTop]
      (fun T : ℕ ↦ (1 : ℝ) / T) := by
  apply Asymptotics.IsBigO.of_bound (3 * L / 4 + unitSupNorm Hd / 2)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / T)]
  exact (burgarth_primitive_uniform ht hd hlip (τ T) (hτ T ht)).trans_eq (by ring)

/-- Both integrals of the generator norms have at most linear runtime growth.
The unrounded one is exactly `T` times its normalized integral. -/
theorem burgarth_generator_integrals {H : ℝ → 𝕄}
    (hc : ContinuousOn H (Icc (0 : ℝ) 1)) {T : ℕ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ‖H (t / T)‖) = (T : ℝ) * ∫ s in (0 : ℝ)..1, ‖H s‖ ∧
    (∫ t in (0 : ℝ)..T, ‖H (t / T)‖) ≤ (T : ℝ) * unitSupNorm H ∧
    (∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) ≤ (T : ℝ) * unitSupNorm H := by
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hKc : ContinuousOn (fun t ↦ H (t / T)) (Icc (0 : ℝ) T) :=
    hc.comp (continuous_id.div_const (T : ℝ)).continuousOn
      (fun _ ht ↦ ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
  have hKi := ((Prose.regulated_of_continuousOn hKc).intervalIntegrable_on hTr.le).norm
  have hGi := ((rounded_hamiltonian_regulated H T).intervalIntegrable_on hTr.le).norm
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_div, div_self hTr.ne', smul_eq_mul] using
      intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := (T : ℝ))
        (fun s ↦ ‖H s‖) hTr.ne'
  · calc
      _ ≤ ∫ _t in (0 : ℝ)..T, unitSupNorm H :=
        intervalIntegral.integral_mono_on hTr.le hKi intervalIntegrable_const
          (fun _ ht ↦ norm_le_unitSupNorm hc
            ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
      _ = _ := by simp
  · calc
      _ ≤ ∫ _t in (0 : ℝ)..T, unitSupNorm H :=
        intervalIntegral.integral_mono_on hTr.le hGi intervalIntegrable_const
          (fun _ ht ↦ norm_le_unitSupNorm hc (rounded_clock_sample_mem ht))
      _ = _ := by simp

/-- The rounded generator-norm integral differs from the continuous one by
at most a runtime-independent constant. Thus both have the same linear term. -/
theorem burgarth_rounded_integral_error {H Hd : ℝ → 𝕄} {D : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D) {T : ℕ} (hT : 0 < T) :
    |(∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) -
      (T : ℝ) * ∫ s in (0 : ℝ)..1, ‖H s‖| ≤ D / 2 := by
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hc : ContinuousOn H (Icc (0 : ℝ) 1) := fun _ hs ↦ (hd _ hs).continuousWithinAt
  have hKc : ContinuousOn (fun t ↦ H (t / T)) (Icc (0 : ℝ) T) :=
    hc.comp (continuous_id.div_const (T : ℝ)).continuousOn
      (fun _ ht ↦ ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩)
  have hKi := ((Prose.regulated_of_continuousOn hKc).intervalIntegrable_on hTr.le).norm
  have hGi := ((rounded_hamiltonian_regulated H T).intervalIntegrable_on hTr.le).norm
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t ↦ ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖ - ‖H (t / T)‖)
    (a := (0 : ℝ)) (b := (T : ℝ)) (C := D / (2 * T)) (by
      intro t ht
      rw [uIoc_of_le hTr.le] at ht
      rw [Real.norm_eq_abs]
      exact (abs_norm_sub_norm_le _ _).trans
        ((rounded_hamiltonian_error_chain hd hD (Ioc_subset_Icc_self ht)).1.trans
          (rounded_hamiltonian_error_chain hd hD (Ioc_subset_Icc_self ht)).2))
  rw [intervalIntegral.integral_sub hGi hKi, Real.norm_eq_abs,
    (burgarth_generator_integrals hc hT).1, sub_zero, abs_of_pos hTr] at hb
  exact hb.trans_eq (by field_simp)

/-- The normalized rounded generator-norm integral tends to the same path
integral as the continuous one. This is the precise linear-growth assertion
behind the introduction's `O(1)` comparison of bounds. -/
theorem burgarth_rounded_integral_linear_limit {H Hd : ℝ → 𝕄} {D : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ D) :
    Tendsto (fun T : ℕ ↦
      (∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) / T)
      atTop (𝓝 (∫ s in (0 : ℝ)..1, ‖H s‖)) := by
  let I := ∫ s in (0 : ℝ)..1, ‖H s‖
  let f := fun T : ℕ ↦ (∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) / T
  have hb : ∀ᶠ T : ℕ in atTop, |f T - I| ≤ (D / 2) / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have ht : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
    have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr ht
    have he : f T - I = ((∫ t in (0 : ℝ)..T,
        ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) - (T : ℝ) * I) / T := by
      dsimp only [f]
      rw [sub_div, mul_div_cancel_left₀ I hTr.ne']
    rw [he, abs_div, abs_of_pos hTr]
    exact div_le_div_of_nonneg_right (burgarth_rounded_integral_error hd hD ht) hTr.le
  have hdiff : Tendsto (fun T ↦ f T - I) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr
      (squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hb
        (tendsto_const_div_atTop_nhds_zero_nat (D / 2)))
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const I

/-- Multiplying the primitive bound by one plus the two generator-norm
integrals gives a runtime-independent bound, exactly the scaling described
in the introduction's discussion of Burgarth et al. -/
theorem burgarth_bound_scaling {H Hd : ℝ → 𝕄} {L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) {T : ℕ} (hT : 0 < T) :
    let C := 3 * L / 4 + unitSupNorm Hd / 2
    C / T * (1 + (∫ t in (0 : ℝ)..T, ‖H (t / T)‖) +
      (∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖)) ≤
      C * (1 + 2 * unitSupNorm H) := by
  intro C
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hc : ContinuousOn H (Icc (0 : ℝ) 1) := fun _ hs ↦ (hd _ hs).continuousWithinAt
  have hdc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  have hD0 : 0 ≤ unitSupNorm Hd := (norm_nonneg _).trans
    (norm_le_unitSupNorm hdc (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num))
  have hL0 : 0 ≤ L := by
    have h := hlip 0 (by norm_num) 1 (by norm_num)
    simpa only [sub_zero, abs_one, mul_one] using (norm_nonneg _).trans h
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hi := burgarth_generator_integrals hc hT
  calc
    _ ≤ C / T * (1 + (T : ℝ) * unitSupNorm H + (T : ℝ) * unitSupNorm H) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hi.2.1) hi.2.2)
        (div_nonneg hC0 hTr.le)
    _ = C * (1 / T + 2 * unitSupNorm H) := by field_simp; ring
    _ ≤ C * (1 + 2 * unitSupNorm H) := mul_le_mul_of_nonneg_left
      (by linarith [one_div_le_one_div_of_le zero_lt_one hT1]) hC0

/-- The numerical right side obtained from the cited primitive comparison is
`O(1)`, even though the primitive itself is uniformly `O(1/T)`. -/
theorem burgarth_bound_bigO {H Hd : ℝ → 𝕄} {L : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) :
    (fun T : ℕ ↦ (3 * L / 4 + unitSupNorm Hd / 2) / T *
      (1 + (∫ t in (0 : ℝ)..T, ‖H (t / T)‖) +
        (∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖))) =O[atTop]
          (fun _T : ℕ ↦ (1 : ℝ)) := by
  have hdc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  have hD0 : 0 ≤ unitSupNorm Hd := (norm_nonneg _).trans
    (norm_le_unitSupNorm hdc (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num))
  have hL0 : 0 ≤ L := by
    have h := hlip 0 (by norm_num) 1 (by norm_num)
    simpa only [sub_zero, abs_one, mul_one] using (norm_nonneg _).trans h
  apply Asymptotics.IsBigO.of_bound
    ((3 * L / 4 + unitSupNorm Hd / 2) * (1 + 2 * unitSupNorm H))
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hk0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖H (t / T)‖ :=
    intervalIntegral.integral_nonneg (Nat.cast_nonneg T) (fun _ _ ↦ norm_nonneg _)
  have hg0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖H ((⌊t + 1 / 2⌋ : ℝ) / T)‖ :=
    intervalIntegral.integral_nonneg (Nat.cast_nonneg T) (fun _ _ ↦ norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one, mul_one]
  exact burgarth_bound_scaling hd hlip ht

end UnitaryProducts.PaperProof
