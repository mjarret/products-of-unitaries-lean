/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ResidualAlgebra
public import UnitaryProducts.Spectral.CircularBands
public import UnitaryProducts.Corrector.ScalarEntrySolutions
public import UnitaryProducts.Evolution.RoundedClockEvolution
public import UnitaryProducts.Comparison.EndpointConstants
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import UnitaryProducts.Approximation.JRSComparison
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Evolution.RoundedTransfer
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmBranch
public import Mathlib.Data.Matrix.Basis
public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative
public import UnitaryProducts.Spectral.ProjectorDistance
public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.LogarithmDerivativeBounds
public import UnitaryProducts.Comparison.SharpInT
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Corrector.FrameBounds
public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# Prose calculations for the periodic corrector

## Declarations

- `UnitaryProducts.PaperProof.all_grid_mem`
- `abs_clock_sub_le`
- `abs_integral_abs_zero`
- `ad_power_norm_le`
- `ae_eq_of_eqOn_Ioo`
- `center_bound_nonneg`
- `clock`
- `clock_bounds`
- `clock_eq_of_abs_sub_lt`
- `clock_error_integrable`
- `clock_error_periodic`
- `clock_switches_countable`
- `globalResidual`
- `hasDerivAt_centered_evolution`
- `hasDerivWithinAt_local_hamiltonian`
- `integral_clock_error_one`
- `integral_rounded_discrepancy`
- `integral_rounded_discrepancy_of_measurable`
- `integral_sample_error`
- `local_clock_weight_integrable`
- `local_taylor_bound`
- `local_taylor_chain`
- `local_taylor_integral`
- `meshInterval_eq`
- `mesh_reflection_clocks`
- `norm_pow_le_width`
- `normalized_rounded_evolutions`
- `path_sample_eq`
- `path_sub_eq_integral`
- `rounded_discrepancy_integrable`
- `rounded_discrepancy_measurable`
- `rounded_evolution_bound`
- `rounded_evolution_unit_steps`
- `rounded_path_sub_eq_integral`
- `rounded_residual_identity`
- `sample`
- `sample_eq_of_abs_sub_lt`
- `sample_mem`
- `sub_sample_eq_coordinate`
- `taylor_remainder_eq_integral`
- `trapezoid_square_error`
- `unit_steps_coefficient`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Set MeasureTheory Complex Real Filter

noncomputable section
namespace UnitaryProducts.PaperProof

/-- Every inclusive grid index lies in the parameter interval, also when N=0. -/
theorem all_grid_mem {N : ℕ} {r : ℤ} (hr : 0 ≤ r ∧ r ≤ (N : ℤ)) :
    (r : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (by exact_mod_cast hr.1) (Nat.cast_nonneg N),
    div_le_one_of_le₀ (by exact_mod_cast hr.2) (Nat.cast_nonneg N)⟩

end UnitaryProducts.PaperProof

namespace UnitaryProducts.Paper
namespace UnitStepsProse

/-- Section 4, opening paragraph: the rounded clock, with ties rounded upwards. -/
def clock (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- Section 4, opening paragraph: the rounded sample time. -/
def sample (N : ℕ) (s : ℝ) : ℝ := (clock (N * s) : ℝ) / N

/-- Section 4, the nearest-grid estimate before the periodic corrector construction. -/
theorem abs_clock_sub_le (x : ℝ) : |(clock x : ℝ) - x| ≤ 1 / 2 := by
  simpa only [clock, ← round_eq, abs_sub_comm] using abs_sub_round x

/-- Section 4, opening paragraph: every point strictly inside a rounded cell has its
center as its rounded clock. -/
theorem clock_eq_of_abs_sub_lt {x : ℝ} {j : ℤ} (h : |x - j| < 1 / 2) :
    clock x = j := by
  rw [clock, Int.floor_eq_iff]
  have hh := abs_lt.mp h
  constructor <;> linarith

/-- Section 4, opening paragraph: the rounded path is constant on each open sample cell. -/
theorem sample_eq_of_abs_sub_lt {N : ℕ} {s : ℝ} {j : ℤ}
    (hs : |s - (j : ℝ) / N| < 1 / (2 * N)) : sample N s = (j : ℝ) / N := by
  have hn : (0 : ℝ) < N := (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp
    (one_div_pos.mp ((abs_nonneg _).trans_lt hs))
  rw [sub_div' hn.ne', abs_div, abs_of_pos hn, div_mul_eq_div_div,
    div_lt_div_iff_of_pos_right hn, mul_comm s] at hs
  simp only [sample, clock_eq_of_abs_sub_lt hs]

/-- Section 4, opening paragraph: evaluation of any path at a point inside a rounded cell. -/
theorem path_sample_eq {E : Type*} (H : ℝ → E) {N : ℕ}
    {s : ℝ} {j : ℤ} (hs : |s - (j : ℝ) / N| < 1 / (2 * N)) :
    H (sample N s) = H ((j : ℝ) / N) := by rw [sample_eq_of_abs_sub_lt hs]

/-- Section 4, proof of the comparison theorem: distance from the rounded time is `τ/N`. -/
theorem sub_sample_eq_coordinate {N : ℕ} (hN : 0 < N) (s : ℝ) :
    s - sample N s = ((N : ℝ) * s - clock (N * s)) / N := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  dsimp [sample]; field_simp

/-- Section 4, following the opening display: the displayed coefficient is constant at N=T. -/
theorem unit_steps_coefficient {N : ℕ} (hN : 0 < N) (L : ℝ) :
    (N : ℝ) / (2 * N) * L = L / 2 ∧ (N : ℝ) * L / (4 * N) = L / 4 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor <;> field_simp

/-- Local Hamiltonian chain rule on its actual parameter domain, including endpoint half cells. -/
theorem hasDerivWithinAt_local_hamiltonian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : ℝ → E} {D : E} (T n j τ : ℝ)
    {S U : Set ℝ}
    (hd : HasDerivWithinAt H D U ((j + τ) / n))
    (hmap : Set.MapsTo (fun σ : ℝ ↦ (j + σ) / n) S U) :
    HasDerivWithinAt (fun σ : ℝ ↦ (T / n) • H ((j + σ) / n))
      ((T / n ^ 2) • D) S τ := by
  simpa only [smul_smul, div_mul_div_comm, mul_one, pow_two] using
    (hd.scomp τ (((hasDerivAt_id τ).const_add j).div_const n).hasDerivWithinAt
      hmap).const_smul (T / n)

/-- Section 4, the all-sample construction: the rounded integer lies between zero and `N`. -/
theorem clock_bounds {N : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ clock (N * s) ∧ clock (N * s) ≤ (N : ℤ) := by
  have hq := abs_le.mp (abs_clock_sub_le ((N : ℝ) * s))
  have h0 : (0 : ℝ) ≤ N * s := mul_nonneg (Nat.cast_nonneg N) hs.1
  have h1 : (N : ℝ) * s ≤ N :=
    (mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg N)).trans_eq (mul_one _)
  constructor
  · by_contra h
    have hi : clock (N * s) ≤ -1 := by omega
    have hr : ((clock (N * s) : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hi
    linarith [hq.1]
  · by_contra h
    have hi : (N : ℤ) + 1 ≤ clock (N * s) := by omega
    have hr : (N : ℝ) + 1 ≤ (clock (N * s) : ℝ) := by exact_mod_cast hi
    linarith [hq.2]

/-- Section 4, opening display: the rounded sample stays in the parameter interval. -/
theorem sample_mem {N : ℕ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    sample N s ∈ Icc (0 : ℝ) 1 := by
  exact PaperProof.all_grid_mem (clock_bounds (N := N) hs)

/-- Section 4, sharp version of the opening display: the rounding error is periodic. -/
theorem clock_error_periodic : Function.Periodic (fun x : ℝ ↦ |(clock x : ℝ) - x|) 1 := by
  intro x
  simp only [clock, ← round_eq, round_add_one, Int.cast_add, Int.cast_one,
    add_sub_add_right_eq_sub]

/-- Section 4, sharp version of the opening display: the scalar rounding error is integrable
on every bounded interval. -/
theorem clock_error_integrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ |(clock x : ℝ) - x|) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ ↦ (1 / 2 : ℝ)) volume a b).mono_fun'
  · have hm : Measurable (fun x : ℝ ↦ |(clock x : ℝ) - x|) := by
      unfold clock; fun_prop
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using abs_clock_sub_le x

/-- Section 4, sharp version of the opening display: the area under one period of the
nearest-integer distance is `1/4`. -/
theorem integral_clock_error_one : (∫ x in (0 : ℝ)..1, |(clock x : ℝ) - x|) = 1 / 4 := by
  have he : (∫ x in (0 : ℝ)..1, |(clock x : ℝ) - x|) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), |x| := by
    have hp := clock_error_periodic.intervalIntegral_add_eq 0 (-1 / 2)
    norm_num at hp
    rw [hp, show (-1 / 2 : ℝ) = -(1 / 2) by ring]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    by_cases ht : x < 1 / 2
    · have hq : clock x = 0 := by
        rw [clock, Int.floor_eq_iff]; norm_num; constructor <;> linarith [hx.1]
      simp [hq]
    · have hx' : x = 1 / 2 := by linarith [hx.2]
      norm_num [hx', clock]
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-1 / 2) 0)
    (continuous_abs.intervalIntegrable 0 (1 / 2))]
  have hl : (∫ x in (-1 / 2 : ℝ)..0, |x|) = ∫ x in (-1 / 2 : ℝ)..0, -x := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    exact abs_of_nonpos hx.2
  have hr : (∫ x in (0 : ℝ)..(1 / 2), |x|) = ∫ x in (0 : ℝ)..(1 / 2), x := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    exact abs_of_nonneg hx.1
  rw [hl, hr, intervalIntegral.integral_neg, integral_id, integral_id]
  norm_num

/-- Section 4: the exact full rounded-path clock integral, including both end half cells. -/
theorem integral_sample_error {N : ℕ} (hN : 0 < N) :
    (∫ s in (0 : ℝ)..1, |sample N s - s|) = 1 / (4 * N) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hp := clock_error_periodic.intervalIntegral_add_zsmul_eq (N : ℤ) 0
    clock_error_integrable
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at hp
  rw [integral_clock_error_one] at hp
  have hsample : (fun s : ℝ ↦ |sample N s - s|) =
      fun s ↦ |(clock (N * s) : ℝ) - N * s| / N := by
    funext s
    rw [sample, div_sub' hn.ne', abs_div, abs_of_pos hn]
  -- One factor 1/N is the sampling error; the second comes from changing variables.
  rw [hsample, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left (fun x : ℝ ↦ |(clock x : ℝ) - x|) hn.ne']
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [hp] -- N periods, each with clock-error integral 1/4.
  field_simp

/-- Section 4: the rounded-path discrepancy is at most `L/(4N)`. Only measurability of
this scalar discrepancy is needed beyond the stated Lipschitz bound; for a continuous path
it follows by composition with the measurable rounded clock. -/
theorem integral_rounded_discrepancy_of_measurable {E : Type*} [NormedAddCommGroup E]
    {H : ℝ → E} {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ L * |x - s|)
    (hm : AEStronglyMeasurable (fun s ↦ ‖H (sample N s) - H s‖)
      (volume.restrict (Icc (0 : ℝ) 1))) :
    (∫ s in (0 : ℝ)..1, ‖H (sample N s) - H s‖) ≤ L / (4 * N) := by
  have hi : IntervalIntegrable (fun s ↦ L * |sample N s - s|) volume 0 1 := by
    simp_rw [sample, div_sub' (Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ) ≠ 0),
      abs_div, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    simpa only [zero_div, div_self (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hN.ne')] using
      (((clock_error_integrable 0 N).comp_mul_left (c := (N : ℝ))).div_const (N : ℝ)).const_mul L
  have hbound : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H (sample N s) - H s‖ ≤ L * |sample N s - s| :=
    fun s hs ↦ hL _ (sample_mem (N := N) hs) _ hs
  have hf : IntervalIntegrable (fun s ↦ ‖H (sample N s) - H s‖) volume 0 1 := by
    apply hi.mono_fun'
    · exact hm.mono_set (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1))
    · refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs ↦ ?_
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      simpa only [norm_norm] using hbound s (Ioc_subset_Icc_self hs)
  calc (∫ s in (0 : ℝ)..1, ‖H (sample N s) - H s‖)
      ≤ ∫ s in (0 : ℝ)..1, L * |sample N s - s| :=
        intervalIntegral.integral_mono_on (by norm_num) hf hi hbound
    _ = L / (4 * N) := by
      rw [intervalIntegral.integral_const_mul, integral_sample_error hN]; ring

/-- Section 4, power-series argument: the power norm bound, valid in every normed algebra. -/
theorem norm_pow_le_width {A : Type*} [NormedRing A] [NormOneClass A]
    {a : A} {w : ℝ} (ha : ‖a‖ ≤ w) (n : ℕ) : ‖a ^ n‖ ≤ w ^ n :=
  (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) ha n)

/-- Section 4, sharpness example: the composite trapezoid rule for `s²` has error `1/(6N²)`;
multiplication by the evolution time `N` gives `1/(6N)`. -/
theorem trapezoid_square_error {N : ℕ} (hN : 0 < N) :
    ((∑ j ∈ Finset.range N, ((j : ℝ) / N) ^ 2) + 1 / 2) / N -
        (∫ s in (0 : ℝ)..1, s ^ 2) = 1 / (6 * (N : ℝ) ^ 2) ∧
    (N : ℝ) * (((∑ j ∈ Finset.range N, ((j : ℝ) / N) ^ 2) + 1 / 2) / N -
        (∫ s in (0 : ℝ)..1, s ^ 2)) = 1 / (6 * N) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [sum_sq_div_eq hN, integral_pow]
  norm_num
  constructor <;> field_simp <;> ring

/-- Section 4, opening display: continuity of the path on its parameter interval suffices
for measurability of its rounded discrepancy. -/
theorem rounded_discrepancy_measurable {E : Type*} [NormedAddCommGroup E]
    {H : ℝ → E} (hc : ContinuousOn H (Icc (0 : ℝ) 1)) {N : ℕ} :
    AEStronglyMeasurable (fun s ↦ ‖H (sample N s) - H s‖)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hq : StronglyMeasurable (fun s ↦ H (sample N s)) :=
    (StronglyMeasurable.of_discrete (f := fun j : ℤ ↦ H ((j : ℝ) / N))).comp_measurable
      (Int.measurable_floor.comp (by fun_prop : Measurable (fun s : ℝ ↦ N * s + 1 / 2)))
  exact (hq.aestronglyMeasurable.sub (hc.aestronglyMeasurable measurableSet_Icc)).norm

/-- Section 4: the sharp full rounded-path estimate under exactly the Lipschitz
hypothesis on `[0,1]`. -/
theorem integral_rounded_discrepancy {E : Type*} [NormedAddCommGroup E]
    {H : ℝ → E} {N : ℕ} (hN : 0 < N) {L : ℝ}
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ L * |x - s|) :
    (∫ s in (0 : ℝ)..1, ‖H (sample N s) - H s‖) ≤ L / (4 * N) := by
  have hc := continuousOn_of_norm_sub_le (fun s hs t ht ↦ hL t ht s hs)
  exact integral_rounded_discrepancy_of_measurable hN hL
    (rounded_discrepancy_measurable (N := N) hc)

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, opening display: the discrepancy is integrable under the stated Lipschitz
assumption; no global regularity of an extension outside `[0,1]` is needed. -/
theorem rounded_discrepancy_integrable {E : Type*} [NormedAddCommGroup E]
    {H : ℝ → E} {N : ℕ} {L : ℝ}
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ L * |x - s|) :
    IntervalIntegrable (fun s ↦ ‖H (sample N s) - H s‖) volume 0 1 := by
  have h₀ : 0 ≤ L := by simpa using (norm_nonneg _).trans (hL 1 (by norm_num) 0 (by norm_num))
  have hc := continuousOn_of_norm_sub_le (fun s hs t ht ↦ hL t ht s hs)
  refine (intervalIntegrable_const (c := L)).mono_fun'
    ((rounded_discrepancy_measurable (N := N) hc).mono_set ?_) ?_
  · simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1)
  refine ae_restrict_of_forall_mem measurableSet_uIoc fun s hs ↦ ?_
  have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using hs)
  have ht := sample_mem (N := N) hs'
  simpa only [norm_norm, mul_one] using (hL _ ht _ hs').trans
    (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [ht.1, hs'.2],
      by linarith [ht.2, hs'.1]⟩ : |sample N s - s| ≤ 1) h₀)

/-- Section 4, opening display: Duhamel for the two evolutions on normalized time,
followed by the sharp rounded-path integral estimate. -/
theorem rounded_evolution_bound {H U V : ℝ → 𝕄} {N : ℕ} (hN : 0 < N) {T L : ℝ}
    (hT : 0 ≤ T)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ L * |x - s|)
    (hU : IsEvolution (fun s ↦ T • H s) U 0 1)
    (hV : IsEvolution (fun s ↦ T • H (sample N s)) V 0 1) :
    ‖V 1 - U 1‖ ≤ T * (∫ s in (0 : ℝ)..1, ‖H (sample N s) - H s‖) ∧
      ‖V 1 - U 1‖ ≤ T * L / (4 * N) := by
  have he : (fun s ↦ ‖T • H s - T • H (sample N s)‖) =
      fun s ↦ T * ‖H (sample N s) - H s‖ := by
    funext s
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT, norm_sub_rev]
  have hi : IntervalIntegrable (fun s ↦ ‖T • H s - T • H (sample N s)‖) volume 0 1 := by
    rw [he]; exact (rounded_discrepancy_integrable (N := N) hL).const_mul T
  obtain ⟨hUc, hU₀, hUU, S, hS, hUd⟩ := hU
  obtain ⟨hVc, hV₀, hVV, R, hR, hVd⟩ := hV
  have hb := norm_sub_le_integral_sub_off_countable (S ∪ R) (hS.union hR)
    (by norm_num : (0 : ℝ) ≤ 1)
    hUc hVc
    (fun s hs hn ↦ hUd s hs (fun h ↦ hn (Or.inl h)))
    (fun s hs hn ↦ hVd s hs (fun h ↦ hn (Or.inr h))) hUU hVV
    (hU₀.trans hV₀.symm) hi
  rw [norm_sub_rev, he, intervalIntegral.integral_const_mul] at hb
  have hclock := integral_rounded_discrepancy hN hL
  have hscaled := mul_le_mul_of_nonneg_left hclock hT
  -- Combine Duhamel with the sharp L/(4N) clock integral and collect the factors.
  have hsharp : ‖V 1 - U 1‖ ≤ T * L / (4 * N) :=
    hb.trans (hscaled.trans_eq (by ring))
  exact ⟨hb, hsharp⟩

/-- Section 4: at unit steps `T=N`, the sharp Duhamel estimate is `L/4`. -/
theorem rounded_evolution_unit_steps {H U V : ℝ → 𝕄} {N : ℕ} {L : ℝ}
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ L * |x - s|)
    (hU : IsEvolution (fun s ↦ (N : ℝ) • H s) U 0 1)
    (hV : IsEvolution (fun s ↦ (N : ℝ) • H (sample N s)) V 0 1) :
    ‖V 1 - U 1‖ ≤ L / 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hb := (rounded_evolution_bound (N := 1) (by decide) (T := 0) le_rfl hL
      (by simpa using hU) (by simpa using hV)).2
    exact (show ‖V 1 - U 1‖ ≤ 0 by simpa using hb).trans
      (div_nonneg (unit_lipschitz_constant_nonneg (fun s hs t ht ↦ hL t ht s hs))
        (by norm_num))
  have hb := (rounded_evolution_bound hN (Nat.cast_nonneg N) hL hU hV).2
  rwa [(unit_steps_coefficient hN L).2] at hb

/-- Section 4.1, the remainder after imposing the corrector equation: its quadratic bound. -/
theorem local_taylor_bound {H Hd : ℝ → 𝕄} {T n h j τ : ℝ}
    (hT : 0 ≤ T) (hn : 0 < n)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hj : j / n ∈ Icc (0 : ℝ) 1) (ht : (j + τ) / n ∈ Icc (0 : ℝ) 1) :
    ‖(T / n) • H ((j + τ) / n) - (T / n) • H (j / n) -
      τ • ((T / n ^ 2) • Hd (j / n))‖ ≤ T * h / (2 * n ^ 3) * τ ^ 2 := by
  have hc : τ * (T / n ^ 2) = (T / n) * ((j + τ) / n - j / n) := by ring
  rw [smul_smul, hc, ← smul_smul, ← smul_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb := norm_taylor_sub_le_of_lipschitz_deriv_half_Icc H Hd hd hl _ hj _ ht
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ T / n)).trans_eq
  rw [← sub_div, add_sub_cancel_left]
  field_simp

/-- Section 4, the integral identity in the corrector motivation and rounded-path residual: the
fundamental theorem
on a subinterval, in either orientation, with derivatives taken within `[0,1]`. -/
theorem path_sub_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {H Hd : ℝ → E} {lo hi : ℝ}
    (hd : ∀ s ∈ Icc lo hi, HasDerivWithinAt H (Hd s) (Icc lo hi) s)
    (hc : ContinuousOn Hd (Icc lo hi)) {a b : ℝ}
    (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
    H b - H a = ∫ s in a..b, Hd s := by
  have hsub : uIcc a b ⊆ Icc lo hi := uIcc_subset_Icc ha hb
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (fun s hs ↦ ((hd s (hsub hs)).mono hsub).continuousWithinAt) (fun s hs ↦ ?_)
    ((hc.mono hsub).intervalIntegrable)
  exact ((hd s (hsub (Ioo_subset_Icc_self hs))).mono hsub).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.mpr ⟨Iio (max a b), isOpen_Iio, hs.2,
      fun y hy ↦ ⟨le_of_lt (lt_trans hs.1 hy.2), hy.1.le⟩⟩)

/-- Section 4, the residual calculation after unit-split: the rounded Hamiltonian difference
is the integral of the derivative, and the interval length is `τ/N`. -/
theorem rounded_path_sub_eq_integral {H Hd : ℝ → 𝕄} {N : ℕ} (hN : 0 < N) (T : ℝ)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    T • H s - T • H (sample N s) = T • (∫ u in sample N s..s, Hd u) ∧
      s - sample N s = ((N : ℝ) * s - clock (N * s)) / N := by
  refine ⟨?_, sub_sample_eq_coordinate hN s⟩
  rw [← smul_sub, path_sub_eq_integral hd hc (sample_mem (N := N) hs) hs]

/-- Section 4.1, the remainder after imposing the corrector equation: its exact integral formula. -/
theorem taylor_remainder_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {H Hd : ℝ → E} {lo hi : ℝ}
    (hd : ∀ s ∈ Icc lo hi, HasDerivWithinAt H (Hd s) (Icc lo hi) s)
    (hc : ContinuousOn Hd (Icc lo hi)) {a b : ℝ}
    (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
    H b - H a - (b - a) • Hd a = ∫ s in a..b, Hd s - Hd a := by
  rw [intervalIntegral.integral_sub ((hc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable)
    intervalIntegrable_const, intervalIntegral.integral_const,
    ← path_sub_eq_integral hd hc ha hb]

/-- Section 4, the global residual calculation: substituting the corrector ODE and the
fundamental theorem gives the integral remainder and the Hamiltonian-difference terms. -/
theorem rounded_residual_identity {H Hd : ℝ → 𝕄} {N : ℕ} (hN : 0 < N) (T : ℝ)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (Y : 𝕄) :
    T • H s - T • H (sample N s) -
        (((N : ℝ) * s - clock (N * s)) • ((T / N) • Hd (r / N)) - I • (T • (H (r / N) * Y - Y * H
          (r / N)))) -
        I • (T • (H s * Y - Y * H (sample N s))) =
      T • (∫ u in sample N s..s, Hd u - Hd (r / N)) -
        I • (T • ((H s - H (r / N)) * Y)) +
        I • (T • (Y * (H (sample N s) - H (r / N)))) := by
  have hp := rounded_path_sub_eq_integral hN T hd hc hs
  have hi : IntervalIntegrable Hd volume (sample N s) s :=
    (hc.mono (uIcc_subset_Icc (sample_mem (N := N) hs) hs)).intervalIntegrable
  have hrem : T • H s - T • H (sample N s) -
      ((N : ℝ) * s - clock (N * s)) • ((T / N) • Hd (r / N)) =
      T • (∫ u in sample N s..s, Hd u - Hd (r / N)) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const, smul_sub, ← hp.1, hp.2]
    simp only [smul_smul, div_eq_mul_inv]
    module
  have hode :
      (((N : ℝ) * s - clock (N * s)) • ((T / N) • Hd (r / N)) -
        I • (T • (H (r / N) * Y - Y * H (r / N)))) +
        I • ((T • H (r / N)) * Y - Y * (T • H (r / N))) =
      ((N : ℝ) * s - clock (N * s)) • ((T / N) • Hd (r / N)) := by
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub]
    abel
  have he := Prose.rounded_residual_of_remainder
    (T • H s) (T • H (sample N s)) (T • H (r / N))
    ((T / N) • Hd (r / N)) Y
    (((N : ℝ) * s - clock (N * s)) • ((T / N) • Hd (r / N)) -
      I • (T • (H (r / N) * Y - Y * H (r / N))))
    (T • (∫ u in sample N s..s, Hd u - Hd (r / N)))
    ((N : ℝ) * s - clock (N * s)) hrem hode
  simpa only [smul_mul_assoc, mul_smul_comm, ← smul_sub] using he

/-- the proof of Theorem 4.2, mesh geometry: reflection of the left half of a mesh step gives the
two
adjacent rounded integers and opposite local clocks.
The repeated expression `N * s - clock (N * s)` is the paper's local clock τ. -/
theorem mesh_reflection_clocks {N j : ℕ} {s : ℝ}
    (hs₀ : (j : ℝ) / N ≤ s) (hs₁ : s < ((j : ℝ) + 1 / 2) / N) :
    let sb := (2 * (j : ℝ) + 1) / N - s
    clock (N * s) = (j : ℤ) ∧ clock (N * sb) = (j : ℤ) + 1 ∧
      ((N : ℝ) * s - clock (N * s)) = N * s - j ∧
      ((N : ℝ) * sb - clock (N * sb)) = -(N * s - j) ∧
      |((N : ℝ) * sb - clock (N * sb))| = |((N : ℝ) * s - clock (N * s))| ∧
      |((N : ℝ) * s - clock (N * s))| = N * s - j := by
  intro sb
  have hn : (0 : ℝ) < N := lt_of_not_ge fun h ↦ by
    simpa [le_antisymm h (Nat.cast_nonneg N)] using hs₀.trans_lt hs₁
  have hlo := (div_le_iff₀' hn).mp hs₀
  have hhi := (lt_div_iff₀' hn).mp hs₁
  have hm : (N : ℝ) * sb = 2 * j + 1 - N * s := by dsimp [sb]; field_simp
  have hq : clock (N * s) = (j : ℤ) :=
    clock_eq_of_abs_sub_lt (by push_cast; exact abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hqb : clock (N * sb) = (j : ℤ) + 1 := clock_eq_of_abs_sub_lt <| by
    rw [hm]; push_cast; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have ht : ((N : ℝ) * s - clock (N * s)) = N * s - j := by simp [hq]
  have htb : ((N : ℝ) * sb - clock (N * sb)) = -(N * s - j) := by rw [hqb, hm]; push_cast; ring
  exact ⟨hq, hqb, ht, htb, by rw [htb, ht, abs_neg], by rw [ht, abs_of_nonneg (by linarith)]⟩

/-- Section 4, the exceptional switching points form a countable set. -/
theorem clock_switches_countable (N : ℕ) :
    {s : ℝ | (N : ℝ) * s + 1 / 2 = (clock (N * s) : ℝ)}.Countable := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num [clock]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine (Set.countable_range (fun j : ℤ ↦ ((j : ℝ) - 1 / 2) / N)).mono fun s hs ↦ ?_
  refine ⟨clock (N * s), ?_⟩
  dsimp only [mem_setOf_eq] at hs
  change ((clock (N * s) : ℝ) - 1 / 2) / N = s
  rw [← hs]; field_simp; ring

/-- Section 4: the residual of a differentiable correction piece against the rounded path. -/
def globalResidual (T : ℝ) (N : ℕ) (H Y : ℝ → 𝕄) (s : ℝ) : 𝕄 :=
  T • H s - T • H (sample N s) - deriv Y s -
    I • (T • (H s * Y s - Y s * H (sample N s)))

/-- the proof of Theorem 4.2, cell integration: changing finitely many endpoint values does not
change the
integral. This helper records equality almost everywhere from equality on the open interval. -/
theorem ae_eq_of_eqOn_Ioo {E : Type*} {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (he : EqOn f g (Ioo a b)) : f =ᵐ[volume.restrict (uIoc a b)] g := by
  rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact ae_restrict_of_forall_mem measurableSet_Ioo he

/-- the proof of Theorem 4.2, cell integration: any integrable weight remains integrable after
composing with
`|τ|` on one mesh step. -/
theorem local_clock_weight_integrable {N j : ℕ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 (1 / 2)) :
    IntervalIntegrable (fun s ↦ f |((N : ℝ) * s - clock (N * s))|) volume ((j : ℝ) / N) (((j : ℝ)
      + 1) / N) := by
  let a : ℝ := (j : ℝ) / N
  let m : ℝ := ((j : ℝ) + 1 / 2) / N
  let b : ℝ := ((j : ℝ) + 1) / N
  let c : ℝ := (2 * (j : ℝ) + 1) / N
  have ham : a ≤ m := by dsimp [a, m]; gcongr; norm_num
  have hmb : m ≤ b := by dsimp [m, b]; gcongr; norm_num
  have hca : c - a = b := by dsimp [c, a, b]; ring
  have hcm : c - m = m := by dsimp [c, m]; ring
  have hlin : IntervalIntegrable (fun s : ℝ ↦ f ((N : ℝ) * s - j)) volume a m := by
    have hh := (hf.comp_sub_right (j : ℝ)).comp_mul_left (c := (N : ℝ))
    simpa only [zero_add, add_comm (1 / 2 : ℝ) (j : ℝ)] using hh
  have hl : IntervalIntegrable (fun s ↦ f |((N : ℝ) * s - clock (N * s))|) volume a m := by
    apply hlin.congr_ae
    refine ae_eq_of_eqOn_Ioo ham fun s hs ↦ ?_
    exact (congrArg f (mesh_reflection_clocks hs.1.le hs.2).2.2.2.2.2).symm
  have hr : IntervalIntegrable (fun s ↦ f |((N : ℝ) * s - clock (N * s))|) volume m b := by
    have hh := (hl.comp_sub_left c).symm
    rw [hca, hcm] at hh
    apply hh.congr_ae
    refine ae_eq_of_eqOn_Ioo hmb fun s hs ↦ ?_
    have ht₀ : a ≤ c - s := by linarith [hs.2]
    have ht₁ : c - s < m := by linarith [hs.1]
    have he := (mesh_reflection_clocks ht₀ ht₁).2.2.2.2.1
    change |((N : ℝ) * (c - (c - s)) - clock (N * (c - (c - s))))| = |((N : ℝ) * (c - s) - clock
      (N * (c - s)))| at he
    rw [sub_sub_cancel] at he
    exact congrArg f he.symm
  exact hl.trans hr

/-- Section 4.1, the remainder after imposing the corrector equation equals the integral of the
rescaled derivative difference, including negative local times. -/
theorem local_taylor_integral {H Hd : ℝ → 𝕄} {T n j τ : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1))
    (hj : j / n ∈ Icc (0 : ℝ) 1) (ht : (j + τ) / n ∈ Icc (0 : ℝ) 1) :
    (T / n) • H ((j + τ) / n) - (T / n) • H (j / n) -
        τ • ((T / n ^ 2) • Hd (j / n)) =
      ∫ σ in (0 : ℝ)..τ, (T / n ^ 2) • Hd ((j + σ) / n) -
        (T / n ^ 2) • Hd (j / n) := by
  let f : ℝ → ℝ := fun σ ↦ (j + σ) / n
  let K : ℝ → 𝕄 := fun σ ↦ (T / n) • H (f σ)
  let Kd : ℝ → 𝕄 := fun σ ↦ (T / n ^ 2) • Hd (f σ)
  have hmap : MapsTo f (uIcc (0 : ℝ) τ) (Icc (0 : ℝ) 1) := by
    intro σ hσ
    apply (uIcc_subset_Icc hj ht)
    by_cases hn : 0 ≤ n
    · have hf : Monotone f := fun a b hab ↦
        div_le_div_of_nonneg_right (by simpa only [add_comm] using add_le_add_left hab j) hn
      simpa only [f, add_zero] using hf.image_uIcc_subset ⟨σ, hσ, rfl⟩
    · have hf : Antitone f := by
        intro a b hab
        simpa only [f, div_eq_mul_inv] using
          mul_le_mul_of_nonpos_right (by simpa only [add_comm] using add_le_add_left hab j)
            (inv_nonpos.mpr (le_of_lt (lt_of_not_ge hn)))
      simpa only [f, add_zero] using hf.image_uIcc_subset ⟨σ, hσ, rfl⟩
  have hK : ∀ σ ∈ uIcc (0 : ℝ) τ, HasDerivWithinAt K (Kd σ) (uIcc 0 τ) σ := by
    intro σ hσ
    exact hasDerivWithinAt_local_hamiltonian T n j σ (hd _ (hmap hσ)) hmap
  have hKd : ContinuousOn Kd (uIcc (0 : ℝ) τ) :=
    (hc.comp ((continuous_const.add continuous_id).div_const n).continuousOn hmap).const_smul _
  have hr := taylor_remainder_eq_integral hK hKd
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) τ)
    (right_mem_uIcc : τ ∈ uIcc (0 : ℝ) τ)
  simpa only [K, Kd, f, add_zero, sub_zero] using hr

/-- Section 4.1, the quadratic remainder estimate: the scalar integral of `|σ|` from zero to τ
has absolute value `τ²/2`. -/
theorem abs_integral_abs_zero (τ : ℝ) : |(∫ σ in (0 : ℝ)..τ, |σ|)| = τ ^ 2 / 2 := by
  have he := abs_integral_distance_of_outside (a := 0) (b := τ) (c := 0)
    ((le_total 0 τ).imp (le_min le_rfl) (max_le le_rfl))
  simpa only [sub_zero, abs_zero, zero_add, ← sq, sq_abs] using he

/-- Section 4, power-series paragraph: the commutator operator has norm bounded by spectral
width, so every power satisfies the exact majorant used there. -/
theorem ad_power_norm_le [NeZero d] {Ω : 𝕄} (hΩ : Ω.IsHermitian) {w : ℝ}
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (n : ℕ) :
    ‖(adL Ω) ^ n‖ ≤ w ^ n := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw₀ : 0 ≤ w := by simpa only [sub_self, abs_zero] using hw 0 0
  have hc := norm_sub_smul_one_le_of_eigenvalues hΩ hw₀ (eigen_interval hΩ hw)
  have hb : ‖adL Ω‖ ≤
      2 * ‖Ω - ((sInf (Set.range hΩ.eigenvalues) + w / 2 : ℝ) : ℂ) • 1‖ := by
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun E ↦ norm_adL_apply_le Ω E _
  exact norm_pow_le_width (a := adL Ω) (w := w) (by linarith) n

/-- Section 4, the global construction: the original and rounded paths on normalized time
have generators `TH` and `TĤ`, respectively. -/
theorem normalized_rounded_evolutions {T : ℝ} (hT : 0 < T) {N : ℕ}
    {H U V : ℝ → 𝕄} (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample N (t / T))) V 0 T) :
    IsEvolution (fun s ↦ T • H s) (fun s ↦ U (T * s)) 0 1 ∧
      IsEvolution (fun s ↦ T • H (sample N s)) (fun s ↦ V (T * s)) 0 1 := by
  constructor
  · simpa only [div_self hT.ne', div_one] using rescaled_evolution hU hT
  · simpa only [div_self hT.ne', div_one] using
      rescaled_evolution (H := fun s ↦ H (sample N s)) (T := T) hV hT

/-- Section 4.1, the quadratic remainder in prose: its derivative-difference integral
is bounded by `(Th/N³)|∫₀ᵗ|σ|dσ| = (Th/(2N³))t²`. -/
theorem local_taylor_chain {H Hd : ℝ → 𝕄} {T n h j τ : ℝ}
    (hT : 0 ≤ T) (hn : 0 < n)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hj : j / n ∈ Icc (0 : ℝ) 1) (ht : (j + τ) / n ∈ Icc (0 : ℝ) 1) :
    let E := (T / n) • H ((j + τ) / n) - (T / n) • H (j / n) -
      τ • ((T / n ^ 2) • Hd (j / n))
    ‖E‖ = ‖∫ σ in (0 : ℝ)..τ, (T / n ^ 2) • Hd ((j + σ) / n) -
        (T / n ^ 2) • Hd (j / n)‖ ∧
      ‖E‖ ≤ (T * h / n ^ 3) * |(∫ σ in (0 : ℝ)..τ, |σ|)| ∧
      (T * h / n ^ 3) * |(∫ σ in (0 : ℝ)..τ, |σ|)| = T * h / (2 * n ^ 3) * τ ^ 2 := by
  intro E
  have hc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hl
  refine ⟨congrArg norm (local_taylor_integral hd hc hj ht), ?_, ?_⟩
  · rw [abs_integral_abs_zero]; exact (local_taylor_bound hT hn hd hl hj ht).trans_eq (by ring)
  · rw [abs_integral_abs_zero]; ring

/-- Section 4, the stepwise residual argument: for `j<N` the mesh interval is exactly
the closed step `[j/N,(j+1)/N]`. -/
theorem meshInterval_eq {N j : ℕ} (hj : j < N) :
    meshInterval N j = Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N) := by
  have hh : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  simp only [meshInterval, max_eq_right (Nat.cast_nonneg j), min_eq_right hh]

open UnitaryProducts.Corrector

/-- Section 4, Theorem 4.2: the center coefficient `c₀=N(w)-N(w/2)/2` is nonnegative. -/
theorem center_bound_nonneg {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ frameBound w - frameBound (w / 2) / 2 := by
  have hmono : frameBound (w / 2) ≤ frameBound w :=
    frameBound_mono (by linarith) (by linarith) hw
  have hnonneg : 0 ≤ frameBound w := frameBound_nonneg hw₀
  -- Subtracting half the smaller bound leaves a nonnegative center coefficient.
  linarith

end UnitStepsProse
end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.UnitStepsProse.globalResidual
