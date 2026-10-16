/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.SharpnessExpansion
public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# Commuting products and trapezoidal quadrature

The commuting specialization in Section 4, immediately before Example 4.3.
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Real Set Matrix Filter MeasureTheory NormedSpace
open UnitaryProducts UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Commuting Hamiltonians combine inside one exponential. -/
theorem commuting_evol_mul {A B : 𝕄} (hAB : Commute A B) (a b : ℝ) :
    evol A a * evol B b = evol (a • A + b • B) 1 := by
  simp only [evol, one_smul, smul_add, smul_comm (-I)]
  exact (Matrix.exp_add_of_commute _ _
    ((((hAB.smul_left (-I)).smul_right (-I)).smul_left a).smul_right b)).symm

/-- A finite product of commuting samples is the exponential of their sum. -/
theorem commuting_pieceProduct (A : ℕ → 𝕄) (N : ℕ)
    (hc : ∀ j < N, ∀ k < N, Commute (A j) (A k)) :
    pieceProduct (fun _ ↦ 1) A N = evol (∑ j ∈ Finset.range N, A j) 1 := by
  induction N with
  | zero => simp [pieceProduct, evol]
  | succ N ih =>
    have hprev : ∀ j < N, ∀ k < N, Commute (A j) (A k) :=
      fun j hj k hk ↦ hc j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_of_lt hk)
    have hsum : Commute (A N) (∑ j ∈ Finset.range N, A j) :=
      Commute.sum_right _ _ _ fun j hj ↦ hc N (Nat.lt_succ_self N) j
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    rw [pieceProduct, ih hprev, commuting_evol_mul hsum, one_smul, one_smul,
      Finset.sum_range_succ, add_comm]

/-- The unit-step product for commuting values is the left-endpoint sum. -/
theorem commuting_unitProduct {H : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    (hc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Commute (H s) (H t)) :
    (unitProduct H T).1 = evol (∑ j ∈ Finset.range T, H (j / T)) 1 := by
  have hsample (j : ℕ) (hj : j ≤ T) : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one (Nat.cast_pos.mpr hT)).mpr ?_⟩
    exact_mod_cast hj
  exact commuting_pieceProduct _ T fun j hj k hk ↦
    hc _ (hsample j hj.le) _ (hsample k hk.le)

/-- Half-step phases replace the left-endpoint sum by the trapezoidal sum. -/
theorem commuting_trapezoidal_product {H : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    (hc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Commute (H s) (H t)) :
    evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) =
      evol ((1 / 2 : ℝ) • H 0 + (∑ j ∈ Finset.Ico 1 T, H (j / T)) +
        (1 / 2 : ℝ) • H 1) 1 := by
  have hsample (j : ℕ) (hj : j < T) : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, (div_le_one (Nat.cast_pos.mpr hT)).mpr ?_⟩
    exact_mod_cast hj.le
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hsum1 : Commute (H 1) (∑ j ∈ Finset.range T, H (j / T)) :=
    Commute.sum_right _ _ _ fun j hj ↦ hc 1 hone _ (hsample j (Finset.mem_range.mp hj))
  have hsum0 : Commute (∑ j ∈ Finset.range T, H (j / T)) (H 0) :=
    Commute.sum_left _ _ _ fun j hj ↦ hc _ (hsample j (Finset.mem_range.mp hj)) 0 hzero
  have hend : Commute (H 1) (H 0) := hc 1 hone 0 hzero
  rw [commuting_unitProduct hT hc, commuting_evol_mul hsum1, one_smul,
    commuting_evol_mul ((hend.smul_left (1 / 2 : ℝ)).add_left hsum0), one_smul,
    Finset.sum_Ico_eq_sub _ hT]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_div]
  congr 1
  module

/-- The integral of Hermitian matrices is Hermitian. -/
theorem isHermitian_intervalIntegral {K : ℝ → 𝕄} {a b : ℝ}
    (hi : IntervalIntegrable K volume a b)
    (hh : ∀ t ∈ uIcc a b, (K t).IsHermitian) :
    (∫ t in a..b, K t).IsHermitian := by
  change star (∫ t in a..b, K t) = ∫ t in a..b, K t
  have hstar := (starL ℝ : 𝕄 ≃L[ℝ] 𝕄).toContinuousLinearMap.intervalIntegral_comp_comm hi
  calc
    star (∫ t in a..b, K t) = ∫ t in a..b, star (K t) := hstar.symm
    _ = ∫ t in a..b, K t := intervalIntegral.integral_congr fun t ht ↦ (hh t ht).eq

/-- An integral commutes with every matrix commuting with all its integrand values. -/
theorem commute_intervalIntegral {K : ℝ → 𝕄} {a b : ℝ} {B : 𝕄}
    (hi : IntervalIntegrable K volume a b)
    (hc : ∀ t ∈ uIcc a b, Commute (K t) B) :
    Commute (∫ t in a..b, K t) B := by
  change (∫ t in a..b, K t) * B = B * ∫ t in a..b, K t
  rw [← mulR_apply, ← (mulR B).intervalIntegral_comp_comm hi,
    ← mulL_apply, ← (mulL B).intervalIntegral_comp_comm hi]
  exact intervalIntegral.integral_congr fun t ht ↦ (hc t ht).eq

/-- The averaging operator fixes matrices commuting with its Hamiltonian. -/
theorem phiSeries_commuting [NeZero d] {A B : 𝕄} (hc : Commute A B) :
    Corrector.phiSeries (I • adL A) B = B := by
  rw [phiSeries_adL_apply]
  have he (t : ℝ) : Commute (evol A (-t)) B :=
    ((hc.smul_left (-I)).smul_left (-t)).exp_left
  have hf (t : ℝ) : evol A (-t) * B * evol A t = B := by
    rw [(he t).eq, mul_assoc, ← evol_add]
    simp [evol_zero]
  simp only [hf, intervalIntegral.integral_const, sub_zero, one_smul]

/-- For pairwise commuting regulated Hermitian generators, evolution is the
exponential of the integrated generator. The primitive solves the evolution
ODE off the countable discontinuity set, and uniqueness identifies it. -/
theorem commuting_evolution_integral [NeZero d] {K U : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated K 0 T)
    (hh : ∀ t ∈ Icc (0 : ℝ) T, (K t).IsHermitian)
    (hc : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, Commute (K s) (K t))
    (hU : IsEvolution K U 0 T) :
    U T = NormedSpace.exp (-I • ∫ t in (0 : ℝ)..T, K t) := by
  let P := fun t ↦ ∫ s in (0 : ℝ)..t, K s
  have hi := hreg.intervalIntegrable hT
  have hisub {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IntervalIntegrable K volume 0 t :=
    hi.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2)
  have hP {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (P t).IsHermitian := by
    apply isHermitian_intervalIntegral (hisub ht)
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hh s ⟨hs.1, hs.2.trans ht.2⟩
  have hPK {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : Commute (P t) (K t) := by
    apply commute_intervalIntegral (hisub ht)
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact hc s ⟨hs.1, hs.2.trans ht.2⟩ t ht
  have hPc : ContinuousOn P (Icc (0 : ℝ) T) := by
    simpa only [P, uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hi
        (by simpa only [uIcc_of_le hT] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩))
  let V := fun t ↦ evol (P t) 1
  have hVc : ContinuousOn V (Icc (0 : ℝ) T) := by
    intro t ht
    exact ((hasFDerivAt_evol_one (hP ht)).continuousAt).comp_continuousWithinAt (hPc t ht)
  have hV0 : V 0 = 1 := by simp [V, P, evol]
  let S := {t ∈ Icc (0 : ℝ) T | ¬ ContinuousWithinAt K (Icc 0 T) t}
  have hS : S.Countable := hreg.countable_not_continuousWithinAt hT
  have hVd : ∀ t ∈ Ioo (0 : ℝ) T, t ∉ S →
      HasDerivWithinAt V (-I • (K t * V t)) (Icc 0 T) t := by
    intro t ht hn
    have ht' : t ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self ht
    have hKt : ContinuousWithinAt K (Icc 0 T) t :=
      not_not.mp fun hnot ↦ hn ⟨ht', hnot⟩
    letI : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht'⟩
    have hPd : HasDerivWithinAt P (K t) (Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right (hisub ht')
        ⟨Icc 0 T, self_mem_nhdsWithin, hreg.aestronglyMeasurable hT⟩ hKt
    have hd := ((hasFDerivAt_evol_one (hP ht')).restrictScalars ℝ).comp_hasDerivWithinAt t hPd
    have he : Commute (evol (P t) 1) (K t) :=
      (((hPK ht').smul_left (-I)).smul_left (1 : ℝ)).exp_left
    change HasDerivWithinAt V (evolDeriv (P t) (K t)) (Icc 0 T) t at hd
    rw [evolDeriv_apply, phiSeries_commuting (hPK ht'), he.eq] at hd
    exact hd
  obtain ⟨hUc, hU0, _, R, hR, hUd⟩ := hU
  have heq := evolution_eq_of_solves_off_countable R S hR hS hh hUc hVc hU0 hV0
    (fun t ht hn ↦ hUd t (Ioo_subset_Icc_self ht) hn) hVd ⟨hT, le_rfl⟩
  simpa only [V, P, evol, one_smul] using heq

/-- Section 4's commuting quadrature identity, in the paper's rescaled clock. -/
theorem commuting_rescaled_evolution [NeZero d] {H U : ℝ → 𝕄} {T : ℝ}
    (hT : 0 < T) (hreg : IsRegulated H 0 1)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, (H t).IsHermitian)
    (hc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Commute (H s) (H t))
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    U T = NormedSpace.exp (-I • ∫ t in (0 : ℝ)..T, H (t / T)) := by
  have hscale {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : t / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩
  exact commuting_evolution_integral hT.le (regulated_rescale hT hreg)
    (fun t ht ↦ hh _ (hscale ht)) (fun s hs t ht ↦ hc _ (hscale hs) _ (hscale ht)) hU

/-- A left-endpoint rule on a unit cell has error bounded by the variation
of the integrand from its left endpoint. -/
theorem left_quadrature_error_le {f : ℝ → 𝕄} {C : ℝ}
    (hi : IntervalIntegrable f volume 0 1)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - f 0‖ ≤ C) :
    ‖f 0 - ∫ t in (0 : ℝ)..1, f t‖ ≤ C := by
  have hint : ‖∫ t in (0 : ℝ)..1, f t - f 0‖ ≤ C := by
    simpa using norm_intervalIntegral_le zero_le_one hb
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const] at hint
  simpa [norm_sub_rev] using hint

/-- An affine rule integrates exactly; only the Taylor remainders remain in
the trapezoidal error. A uniform remainder bound suffices for its order. -/
theorem trapezoidal_quadrature_error_le {f : ℝ → 𝕄} {D : 𝕄} {C : ℝ}
    (hi : IntervalIntegrable f volume 0 1)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - f 0 - t • D‖ ≤ C) :
    ‖(1 / 2 : ℝ) • (f 0 + f 1) - ∫ t in (0 : ℝ)..1, f t‖ ≤ 3 / 2 * C := by
  let R := fun t ↦ f t - f 0 - t • D
  have hid : IntervalIntegrable (fun t : ℝ ↦ t • D) volume 0 1 :=
    (continuous_id.smul continuous_const).intervalIntegrable _ _
  have hR : (∫ t in (0 : ℝ)..1, R t) =
      (∫ t in (0 : ℝ)..1, f t) - f 0 - (1 / 2 : ℝ) • D := by
    rw [intervalIntegral.integral_sub (hi.sub intervalIntegrable_const) hid,
      intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_smul_const, integral_id]
    norm_num
  have hdecomp : (1 / 2 : ℝ) • (f 0 + f 1) - (∫ t in (0 : ℝ)..1, f t) =
      (1 / 2 : ℝ) • R 1 - ∫ t in (0 : ℝ)..1, R t := by
    rw [hR]
    dsimp [R]
    module
  have hint : ‖∫ t in (0 : ℝ)..1, R t‖ ≤ C := by
    simpa using norm_intervalIntegral_le zero_le_one hb
  have hend : ‖R 1‖ ≤ C := hb 1 ⟨zero_le_one, le_rfl⟩
  rw [hdecomp]
  calc
    ‖(1 / 2 : ℝ) • R 1 - ∫ t in (0 : ℝ)..1, R t‖ ≤
        ‖(1 / 2 : ℝ) • R 1‖ + ‖∫ t in (0 : ℝ)..1, R t‖ := norm_sub_le _ _
    _ ≤ 3 / 2 * C := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

/-- On each unit-time step, a Lipschitz Hamiltonian gives first-order left
quadrature error, and its Lipschitz derivative gives second-order trapezoidal
error. This supplies the local orders in the paragraph before Example 4.3. -/
theorem quadrature_local_orders {H Hd : ℝ → 𝕄} {T j : ℕ} (hT : 0 < T) (hj : j < T)
    {L h : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H t - H s‖ ≤ L * |t - s|)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|) :
    ‖H (j / T) - ∫ u in (0 : ℝ)..1, H ((j + u) / T)‖ ≤ L / T ∧
    ‖(1 / 2 : ℝ) • (H (j / T) + H ((j + 1 : ℝ) / T)) -
      ∫ u in (0 : ℝ)..1, H ((j + u) / T)‖ ≤ 3 * h / (4 * (T : ℝ) ^ 2) := by
  have htr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hL0 : 0 ≤ L := by
    have hb := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simpa using (norm_nonneg (H 1 - H 0)).trans hb
  have hh0 : 0 ≤ h := by
    have hb := hl 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simpa using (norm_nonneg (Hd 1 - Hd 0)).trans hb
  have hmap {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
      ((j : ℝ) + u) / T ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg j) hu.1) htr.le, (div_le_one htr).mpr ?_⟩
    have hj' : (j : ℝ) + 1 ≤ T := by exact_mod_cast hj
    linarith [hu.2]
  have hsample : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
    simpa using hmap (u := 0) ⟨le_rfl, zero_le_one⟩
  let f := fun u : ℝ ↦ H ((j + u) / T)
  have hHc : ContinuousOn H (Icc (0 : ℝ) 1) := fun s hs ↦ (hd s hs).continuousWithinAt
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    hHc.comp
      ((continuous_const.add continuous_id).div_const (T : ℝ)).continuousOn (fun _ hu ↦ hmap hu)
  have hfi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le zero_le_one]
  have hleft : ‖f 0 - ∫ u in (0 : ℝ)..1, f u‖ ≤ L / T := by
    apply left_quadrature_error_le hfi
    intro u hu
    have hb := hL _ hsample _ (hmap hu)
    have harg : ((j : ℝ) + u) / T - j / T = u / T := by ring
    dsimp [f]
    simp only [add_zero]
    calc
      ‖H ((j + u) / T) - H (j / T)‖ ≤ L * |((j : ℝ) + u) / T - j / T| := hb
      _ = L * (u / T) := by rw [harg, abs_of_nonneg (div_nonneg hu.1 htr.le)]
      _ ≤ L / T := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hL0 hu.2) htr.le
  have htrap : ‖(1 / 2 : ℝ) • (f 0 + f 1) - ∫ u in (0 : ℝ)..1, f u‖ ≤
      3 / 2 * (h / (2 * (T : ℝ) ^ 2)) := by
    apply trapezoidal_quadrature_error_le (D := (1 / (T : ℝ)) • Hd (j / T))
      hfi
    intro u hu
    have hb := UnitStepsProse.local_taylor_bound htr.le htr hd hl hsample (hmap hu)
    have hcoef : (T : ℝ) * h / (2 * (T : ℝ) ^ 3) = h / (2 * (T : ℝ) ^ 2) := by
      field_simp
    have hdcoef : (T : ℝ) / (T : ℝ) ^ 2 = 1 / (T : ℝ) := by field_simp
    rw [div_self htr.ne', one_smul, one_smul, hcoef, hdcoef] at hb
    have hsq : u ^ 2 ≤ 1 := pow_le_one₀ hu.1 hu.2
    simpa only [f, add_zero] using hb.trans (mul_le_of_le_one_right (by positivity) hsq)
  refine ⟨by simpa [f] using hleft, ?_⟩
  convert htrap using 1
  · simp [f]
  · ring

/-- The cell integrals in the quadrature interpretation partition the full
integral, including its rescaled Hamiltonian specialization. -/
theorem quadrature_integral_partition {K : ℝ → 𝕄} (T : ℕ)
    (hi : IntervalIntegrable K volume 0 T) :
    (∑ j ∈ Finset.range T, ∫ u in (0 : ℝ)..1, K ((j : ℝ) + u)) =
      ∫ t in (0 : ℝ)..T, K t := by
  have hcell (j : ℕ) (hj : j < T) : IntervalIntegrable K volume (j : ℝ) (j + 1 : ℕ) := by
    apply hi.mono_set
    rw [uIcc_of_le (by exact_mod_cast Nat.le_succ j), uIcc_of_le (Nat.cast_nonneg T)]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (by exact_mod_cast hj)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ ↦ (j : ℝ)) hcell
  simpa only [intervalIntegral.integral_comp_add_left, add_zero, Nat.cast_zero,
    Nat.cast_add, Nat.cast_one] using hsum

/-- Summing `T` local first-order errors gives an `O(1)` total, whereas
summing `T` local second-order errors gives an `O(1/T)` total. -/
theorem quadrature_accumulated_orders {T : ℕ} (hT : 0 < T)
    (E F : ℕ → 𝕄) {L C : ℝ}
    (hE : ∀ j < T, ‖E j‖ ≤ L / T)
    (hF : ∀ j < T, ‖F j‖ ≤ C / (T : ℝ) ^ 2) :
    ‖∑ j ∈ Finset.range T, E j‖ ≤ L ∧
    ‖∑ j ∈ Finset.range T, F j‖ ≤ C / T := by
  have htr : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  constructor
  · calc
      ‖∑ j ∈ Finset.range T, E j‖ ≤ ∑ j ∈ Finset.range T, ‖E j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range T, L / T :=
        Finset.sum_le_sum fun j hj ↦ hE j (Finset.mem_range.mp hj)
      _ = L := by simp; field_simp
  · calc
      ‖∑ j ∈ Finset.range T, F j‖ ≤ ∑ j ∈ Finset.range T, ‖F j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range T, C / (T : ℝ) ^ 2 :=
        Finset.sum_le_sum fun j hj ↦ hF j (Finset.mem_range.mp hj)
      _ = C / T := by simp; field_simp

end UnitaryProducts.Prose
