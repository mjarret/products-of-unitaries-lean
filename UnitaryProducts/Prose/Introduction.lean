/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Algebra.Order.Round
public import UnitaryProducts.Comparison.OneSize
public import UnitaryProducts.Spectral.CircularBands
public import UnitaryProducts.Corrector.ScalarEntrySolutions
public import UnitaryProducts.Evolution.RegulatedComparison
public import UnitaryProducts.Paper.OneVariable
public import UnitaryProducts.Spectral.WidthAndGap

/-!
# Mathematical claims in the abstract and introduction

## Declarations

- `unit_sample_mem_le`
- `adjacent_corrector_jump_le`
- `band_gap_does_not_ensure_width`
- `bounded_path_rescale_width`
- `comparison_integrated_difference`
- `introduction_unit_step_error`
- `midpoint_bit_truncation_finite_precision`
- `midpoint_error_of_odd`
- `path_midpoint_error_of_odd`
- `periodic_corrector_zero_limit`
- `piecewise_constant_one_sided_limits`
- `rounded_clock_error_and_tie`
- `rounded_clock_nearest`
- `rounded_clock_sample_mem`
- `rounded_hamiltonian_regulated`
- `sampled_entry_map_finite_image`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Real Set Filter MeasureTheory Matrix
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed

noncomputable section
namespace UnitaryProducts.Paper

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1, the definition of the rounded clock: the rounding error is at most one half,
and the half-integer tie is rounded upward. -/
theorem rounded_clock_error_and_tie (t : ℝ) :
    |(⌊t + 1 / 2⌋ : ℝ) - t| ≤ 1 / 2 ∧
      ∀ n : ℤ, ⌊(n : ℝ) + 1 / 2 + 1 / 2⌋ = n + 1 := by
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · linarith [Int.lt_floor_add_one (t + 1 / 2)]
  · linarith [Int.floor_le (t + 1 / 2)]
  · intro n; rw [show (n : ℝ) + 1 / 2 + 1 / 2 = (n : ℝ) + 1 by ring]; simp

/-- Section 1, "the integer nearest t": the rounded clock minimizes distance to the integers;
the minimizer need not be unique at half-integers. -/
theorem rounded_clock_nearest (t : ℝ) (n : ℤ) :
    |(⌊t + 1 / 2⌋ : ℝ) - t| ≤ |(n : ℝ) - t| := by
  simpa only [round_eq, abs_sub_comm] using round_le t n

/-- Section 1, the rounded Hamiltonian: every rounded sample on the integer time interval
belongs to the parameter interval, including both endpoint half-cells. -/
theorem rounded_clock_sample_mem {N : ℕ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) N) : (⌊t + 1 / 2⌋ : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
  have hq0 : (0 : ℤ) ≤ ⌊t + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith [ht.1])
  have hqN : ⌊t + 1 / 2⌋ ≤ (N : ℤ) := Int.floor_le_iff.mpr (by push_cast; linarith [ht.2])
  exact ⟨div_nonneg (by exact_mod_cast hq0) (Nat.cast_nonneg N),
    div_le_one_of_le₀ (by exact_mod_cast hqN) (Nat.cast_nonneg N)⟩

/-- Section 1, regulated matrix families: finite piecewise-constant families have both one-sided
limits at the appropriate points. Node values remain unrestricted and can be sampled. -/
theorem piecewise_constant_one_sided_limits (H : ℝ → 𝕄) (a : ℕ → ℝ) (G : ℕ → 𝕄)
    (n : ℕ) (hc : ∀ j < n, ∀ x ∈ Ioo (a j) (a (j + 1)), H x = G j) :
    (∀ t ∈ Ico (a 0) (a n), ∃ L, Tendsto H (𝓝[>] t) (𝓝 L)) ∧
      (∀ t ∈ Ioc (a 0) (a n), ∃ L, Tendsto H (𝓝[<] t) (𝓝 L)) :=
  piecewise_regulated H a G n hc

/-- Every inclusive unit-step sample belongs to the parameter interval. -/
theorem unit_sample_mem_le {N j : ℕ} (hjN : j ≤ N) :
    (j : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg N),
    div_le_one_of_le₀ (Nat.cast_le.mpr hjN) (Nat.cast_nonneg N)⟩

/-- The abstract and Section 1, energy/time rescaling: a uniform operator-norm bound supplies
width at most pi at every sample, including the endpoint, after rescaling to sufficiently many
unit steps. The endpoint evolution is
unchanged. The sufficient step count is max(2, ceil(2TB/pi)), linear in duration and energy. -/
theorem bounded_path_rescale_width [NeZero d] {H U : ℝ → 𝕄} {T B : ℝ}
    (hT : 0 < T) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hB : ∀ s ∈ Icc (0 : ℝ) 1, ‖H s‖ ≤ B)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    ∃ N : ℕ, 2 ≤ N ∧ (N : ℝ) ≤ max 2 (2 * T * B / π + 1) ∧
      IsEvolution (fun t ↦ (T / N) • H (t / N))
        (fun t ↦ U ((T / N) * t)) 0 N ∧ U ((T / N) * N) = U T ∧
      ∀ j : ℕ, ∀ hj : j ≤ N, ∀ p q,
        (T / N) * |(hH _ (unit_sample_mem_le hj)).eigenvalues p -
          (hH _ (unit_sample_mem_le hj)).eigenvalues q| ≤ π := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  let N := max 2 ⌈2 * T * B / π⌉₊
  have hN : 2 ≤ N := le_max_left _ _
  have hceil := Nat.le_ceil (2 * T * B / π)
  have hcount : (N : ℝ) ≤ max 2 (2 * T * B / π + 1) := by
    dsimp [N]; rw [Nat.cast_max]; exact max_le_max le_rfl (Nat.ceil_lt_add_one (by positivity)).le
  have hTN : T * (2 * B) ≤ (N : ℝ) * π := by
    have hle : 2 * T * B / π ≤ (N : ℝ) := hceil.trans (Nat.cast_le.mpr (le_max_right _ _))
    linarith [(div_le_iff₀ pi_pos).mp hle]
  have hΔ : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) (p q : Fin d),
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ 2 * B := by
    intro s hs p q
    have hp := spectrum.norm_le_norm_of_mem ((hH s hs).eigenvalues_mem_spectrum_real p)
    have hq := spectrum.norm_le_norm_of_mem ((hH s hs).eigenvalues_mem_spectrum_real q)
    calc _ ≤ |(hH s hs).eigenvalues p| + |(hH s hs).eigenvalues q| := abs_sub _ _
      _ ≤ 2 * B := by simp only [Real.norm_eq_abs] at hp hq; linarith [hB s hs]
  obtain ⟨he, hend⟩ := rescaled_evolution_steps hT N (by omega) hU
  refine ⟨N, hN, hcount, he, hend, ?_⟩
  intro j hj p q
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  calc
    (T / N) * |(hH _ (unit_sample_mem_le hj)).eigenvalues p -
        (hH _ (unit_sample_mem_le hj)).eigenvalues q|
        ≤ (T / N) * (2 * B) :=
      mul_le_mul_of_nonneg_left (hΔ _ (unit_sample_mem_le hj) p q)
        (div_nonneg hT.le hNpos.le)
    _ = T * (2 * B) / N := div_mul_eq_mul_div _ _ _
    _ ≤ (N : ℝ) * π / N := div_le_div_of_nonneg_right hTN hNpos.le
    _ = π := by field_simp

/-- Section 1, the rounded-clock Hamiltonian is regulated regardless of the path's regularity. -/
theorem rounded_hamiltonian_regulated (H : ℝ → 𝕄) (N : ℕ) :
    IsRegulated (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / N)) 0 N := by
  let a : ℕ → ℝ := fun j ↦ if j = 0 then 0 else min N ((j : ℝ) - 1 / 2)
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a (N + 1) = N := by
    simp only [a, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
    exact min_eq_left (by linarith)
  rw [← ha0, ← haN]
  apply piecewise_regulated _ a (fun j ↦ H ((j : ℝ) / N)) (N + 1)
  intro j hj t ht
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (show j ≤ N by omega)
  have hlo : (j : ℝ) ≤ t + 1 / 2 := by
    by_cases hz : j = 0
    · subst j; simp only [ha0] at ht; push_cast; linarith [ht.1]
    · have he : a j = (j : ℝ) - 1 / 2 := by
        simp only [a, if_neg hz]; exact min_eq_right (by linarith)
      rw [he] at ht; linarith [ht.1]
  have hhi : t + 1 / 2 < (j : ℝ) + 1 := by
    have he : a (j + 1) ≤ (j : ℝ) + 1 / 2 := by
      simp only [a, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
      linarith [min_le_right (N : ℝ) ((j : ℝ) + 1 - 1 / 2)]
    linarith [ht.2]
  have hfloor : ⌊t + 1 / 2⌋ = (j : ℤ) := Int.floor_eq_iff.mpr
    ⟨by simpa only [Int.cast_natCast] using hlo,
      by simpa only [Int.cast_natCast] using hhi⟩
  simp only [hfloor, Int.cast_natCast, haN]

/-- Section 1, the bound for any odd entry function: local finiteness, monotonicity and even the
step-function condition are unnecessary for a fixed finite midpoint product. -/
theorem midpoint_error_of_odd {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hU : IsEvolution H U 0 T) (F : ℝ → ℝ) (hodd : ∀ x, F (-x) = -F x)
    (n : ℕ) (t : ℕ → ℝ) (ht : (variationCheckpoints H T n).2.1 t) :
    ‖midpointProduct ((levelFunctionData F).2 H) n t - U T‖ ≤
      (∑ j ∈ Finset.range n, ∫ x in t j..t (j + 1),
        ‖H x - H ((t j + t (j + 1)) / 2)‖) +
      T * ⨆ j : Fin n, ‖H ((t j + t (j + 1)) / 2) -
        (levelFunctionData F).1 (H ((t j + t (j + 1)) / 2))‖ := by
  have hmid : ∀ j < n, (t j + t (j + 1)) / 2 ∈ Icc 0 T := fun j hj ↦
    ⟨by linarith [ht.2.1 ▸ ht.1 (Nat.zero_le j), ht.1 (Nat.le_succ j)],
      by linarith [ht.2.2 ▸ ht.1 hj, ht.1 (Nat.le_succ j)]⟩
  let G := fun j ↦ scalarEntryMap F (H ((t j + t (j + 1)) / 2))
  have hb := piecewise_product_error_le_integral hT hreg hU n t ht G
    (fun j hj ↦ scalarEntryMap_isHermitian F hodd (hH _ (hmid j hj)))
  let β := ⨆ i : Fin n, ‖H ((t i + t (i + 1)) / 2) -
    (levelFunctionData F).1 (H ((t i + t (i + 1)) / 2))‖
  have hβ : ∀ j < n, ‖H ((t j + t (j + 1)) / 2) - G j‖ ≤ β := fun j hj ↦
    le_ciSup (f := fun i : Fin n ↦ ‖H ((t i + t (i + 1)) / 2) -
      (levelFunctionData F).1 (H ((t i + t (i + 1)) / 2))‖)
      (Set.finite_range _).bddAbove ⟨j, hj⟩
  have hi : ∀ j < n, ∀ c : 𝕄,
      IntervalIntegrable (fun x ↦ ‖H x - c‖) volume (t j) (t (j + 1)) := fun j hj c ↦
    (((hreg.intervalIntegrable_on hT.le).mono_set (by
      rw [uIcc_of_le (ht.1 (Nat.le_succ j)), uIcc_of_le hT.le]
      exact Icc_subset_Icc (ht.2.1 ▸ ht.1 (Nat.zero_le j))
        (ht.2.2 ▸ ht.1 hj))).sub intervalIntegrable_const).norm
  have hsum : ∑ j ∈ Finset.range n, ∫ _x in t j..t (j + 1), β = T * β := by
    simp only [intervalIntegral.integral_const, smul_eq_mul, ← Finset.sum_mul,
      Finset.sum_range_sub, ht.2.1, ht.2.2, sub_zero]
  refine hb.trans ?_
  change _ ≤ _ + T * β
  rw [← hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  rw [← intervalIntegral.integral_add (hi j hj' _) intervalIntegrable_const]
  exact intervalIntegral.integral_mono_on (ht.1 (Nat.le_succ j)) (hi j hj' _)
    ((hi j hj' _).add intervalIntegrable_const) fun x _ ↦
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add le_rfl (hβ j hj'))

/-- Section 1, the midpoint bound for any odd entry function, in the paper's path/time notation. -/
theorem path_midpoint_error_of_odd {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (F : ℝ → ℝ) (hodd : ∀ x, F (-x) = -F x)
    (n : ℕ) (s : ℕ → ℝ) (hs : (variationCheckpoints H 1 n).2.1 s) :
    ‖midpointProductOver ((levelFunctionData F).2 H) T n s - U T‖ ≤
      T * ((∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1),
        ‖H x - H ((s j + s (j + 1)) / 2)‖) +
      ⨆ j : Fin n, ‖H ((s j + s (j + 1)) / 2) -
        (levelFunctionData F).1 (H ((s j + s (j + 1)) / 2))‖) := by
  have hb := midpoint_error_of_odd hT (regulated_rescale hT hreg)
    (fun t ht ↦ hH (t / T) ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩)
    hU F hodd n (fun j ↦ T * s j) (checkpoints_rescale hT hs _)
  have hW : midpointProduct ((levelFunctionData F).2 (fun t ↦ H (t / T))) n
      (fun j ↦ T * s j) = midpointProductOver ((levelFunctionData F).2 H) T n s :=
    midpointProductOver_rescale ((levelFunctionData F).2 H) hT.ne' n s
  have hm : ∀ j, (T * s j + T * s (j + 1)) / 2 / T = (s j + s (j + 1)) / 2 :=
    fun j ↦ by field_simp
  rw [hW, osc_rescale H hT n s] at hb
  simp only [hm] at hb
  rwa [mul_add]


/-- Section 1, the O(T^-2) neighboring-corrector claim: this bounds each individual interior
junction, not just their sum. The actual end value is N(ad(H(j/T)))(H'(j/T)/T).
The bound is uniform in j and T; the endpoint half-cell junctions have zero jump. -/
theorem adjacent_corrector_jump_le [NeZero d] {H Hd : ℝ → 𝕄} {N : ℕ}
    (hN : 2 ≤ N) {w h : ℝ} (hw : w < 2 * π) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ h) (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|) (hdiff : ∀ j : ℕ, 0 < j → ∀ hj : j < N, ∀ p q,
      |(hH _ (unit_sample_mem hj)).eigenvalues p -
        (hH _ (unit_sample_mem hj)).eigenvalues q| ≤ w) (j : ℕ) (hj : 0 < j) (hjN : j + 1 < N) :
    ‖frameOp (H ((j + 1 : ℕ) / N)) ((1 / N : ℝ) • Hd ((j + 1 : ℕ) / N)) -
      frameOp (H ((j : ℝ) / N)) ((1 / N : ℝ) • Hd ((j : ℝ) / N))‖ ≤
      (frameBound w * h + 2 * frameLip w * h ^ 2) / (N : ℝ) ^ 2 := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff j hj (by omega) (0 : Fin d) (0 : Fin d)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hs := unit_sample_mem (show j < N by omega)
  have ht := unit_sample_mem hjN
  have hh : 0 ≤ h := (norm_nonneg _).trans (hbd _ hs)
  have hwidth (k : ℕ) (hk : 0 < k) (hkN : k < N) :
      ∃ z : ℝ, ‖H ((k : ℝ) / N) - (z : ℂ) • 1‖ ≤ w / 2 :=
    ⟨_, norm_sub_smul_one_le_of_eigenvalues (hH _ (unit_sample_mem hkN)) hw0
      (eigen_interval _ (hdiff k hk hkN))⟩
  obtain ⟨z, hz⟩ := hwidth j hj (by omega)
  obtain ⟨z', hz'⟩ := hwidth (j + 1) (by omega) hjN
  have hstep : |((j + 1 : ℕ) : ℝ) / N - (j : ℝ) / N| = 1 / N := by
    rw [← sub_div, abs_div, abs_of_pos hNR]; push_cast; simp
  have hδ := norm_sub_le_of_derivWithin_le hd hbd _ hs _ ht
  have hD := hlip _ hs _ ht
  rw [hstep] at hδ hD
  have hb := norm_frameOp_sub_le
    (D := (1 / N : ℝ) • Hd ((j + 1 : ℕ) / N))
    (D' := (1 / N : ℝ) • Hd ((j : ℝ) / N)) hw hz' hz
  rw [← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hNR)] at hb
  have hB := frameBound_nonneg hw0
  have hL := frameLip_nonneg hw0
  calc _ ≤ frameBound w * ((1 / N) * ‖Hd ((j + 1 : ℕ) / N) - Hd ((j : ℝ) / N)‖) +
        2 * frameLip w * ((1 / N) * ‖Hd ((j : ℝ) / N)‖) *
          ‖H ((j + 1 : ℕ) / N) - H ((j : ℝ) / N)‖ := hb
    _ ≤ frameBound w * ((1 / N) * (h * (1 / N))) +
        2 * frameLip w * ((1 / N) * h) * (h * (1 / N)) := by
      gcongr
      exact hbd _ hs
    _ = _ := by ring

/-- Section 1, the global O(T^-1) conclusion in the same unit-step convention as the individual
jump and residual bounds. At width pi an explicit bound is (2h+h^2)/T. -/
theorem introduction_unit_step_error [NeZero d] {H U : ℝ → 𝕄} {N : ℕ} (hN : 2 ≤ N)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1)) (h : ℝ)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h * |t - s|)
    (hdiff : ∀ j : ℕ, 0 < j → ∀ hj : j < N, ∀ p q,
      |(hH _ (unit_sample_mem hj)).eigenvalues p -
        (hH _ (unit_sample_mem hj)).eigenvalues q| ≤ π)
    (hU : IsEvolution (fun t ↦ H (t / N)) U 0 N) :
    ‖evol (H 1) (1 / 2) * (unitProduct H N).1 * evol (H 0) (-(1 / 2)) - U N‖ ≤
      (2 * h + h ^ 2) / N := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have he : (N : ℝ) / (2 * N) = 1 / 2 := by field_simp
  have hb := (unit_step_comparison_scaling_one_size H U N N hNR hN hH hc h hbd hlip
    (by simpa only [div_self hNR.ne', one_mul] using hdiff) hU).2 rfl
  simpa only [he, div_self hNR.ne', one_smul] using hb

/-- Section 1, the comparison lemma specialized to the integrated Hamiltonian difference.
This is the mathematical specialization described in the comparison with Burgarth et al.;
no assertion about the contents of an external document is encoded. Regulated generators,
including discontinuous ones, suffice. -/
theorem comparison_integrated_difference {K G U V : ℝ → 𝕄} {T : ℝ} (hT : 0 ≤ T)
    (hKr : IsRegulated K 0 T) (hGr : IsRegulated G 0 T)
    (hU : IsEvolution K U 0 T) (hV : IsEvolution G V 0 T) :
    let Y := fun t ↦ ∫ s in 0..t, K s - G s
    star (U T) * (1 - I • Y T) * V T - 1 =
      ∫ t in 0..T, star (U t) * (K t * Y t - Y t * G t) * V t := by
  intro Y
  have hRr := Prose.regulated_sub hKr hGr
  have hi := (hRr : Regulated _ 0 T).intervalIntegrable hT
  refine comparison_of_primitive hT K G U V Y _ (hRr.countable_not_continuousWithinAt hT)
    hKr hGr hU hV
    ((intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc).mono Icc_subset_uIcc)
    (by simp [Y]) (fun t ht hn ↦ ?_)
  exact intervalIntegral.integral_hasDerivAt_right
    (hi.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioo_subset_Icc_self ht))))
    ⟨Ioc 0 T, Ioc_mem_nhds ht.1 ht.2, hi.1.aestronglyMeasurable⟩
    ((not_not.mp (fun hc ↦ hn ⟨Ioo_subset_Icc_self ht, hc⟩)).continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- Section 1, finite entry data: finitely many samples,
with any entry map, supply finitely many held values. Bit precision for the midpoint path is
additionally certified by `midpoint_bit_truncation_finite_precision`. -/
theorem sampled_entry_map_finite_image (H : ℝ → 𝕄) (F : ℝ → ℝ) (n : ℕ)
    (s : Fin n → ℝ) (index : ℝ → Fin n) :
    Set.Finite (Set.range (fun t ↦ scalarEntryMap F (H (s (index t))))) :=
  (Set.finite_range (fun j : Fin n ↦ scalarEntryMap F (H (s j)))).subset
    (Set.range_comp_subset_range index (fun j ↦ scalarEntryMap F (H (s j))))

/-- Section 1, finite entry data: the truncated midpoint path
uses finitely many samples, and every real and imaginary entry is an integer divided by `2 ^ k`.
Here `index` selects a held interval; the conclusion holds for every selection, including any
choice at checkpoint boundaries. No regularity or Hermitian hypothesis is needed. -/
theorem midpoint_bit_truncation_finite_precision (H : ℝ → 𝕄) (k n : ℕ)
    (s : ℕ → ℝ) (index : ℝ → Fin n) :
    let G := fun t ↦ truncHerm k (H ((s (index t) + s ((index t : ℕ) + 1)) / 2))
    Set.Finite (Set.range G) ∧
      ∀ t p q, ∃ a b : ℤ, (G t p q).re = (a : ℝ) / 2 ^ k ∧
        (G t p q).im = (b : ℝ) / 2 ^ k := by
  intro G
  refine ⟨sampled_entry_map_finite_image H (truncBits k) n
    (fun j ↦ (s j + s ((j : ℕ) + 1)) / 2) index, fun t p q ↦ ?_⟩
  exact ⟨level k (H ((s (index t) + s ((index t : ℕ) + 1)) / 2) p q).re,
    level k (H ((s (index t) + s ((index t : ℕ) + 1)) / 2) p q).im, rfl, rfl⟩

/-- Section 1, the zero-frequency selection is the limit of the endpoint multiplier. The
corresponding
normalized solution is (tau^2/2 - 1/24)a and its common endpoint value is a/12. -/
theorem periodic_corrector_zero_limit (a : ℂ) :
    Tendsto (fun x : ℝ ↦ (UnitaryProducts.Corrector.frameMult x : ℂ) * a)
      (𝓝[≠] 0) (𝓝 (a / 12)) ∧
    (∀ τ : ℝ, HasDerivAt (fun t : ℝ ↦ ((t : ℂ) ^ 2 / 2 - 1 / 24) * a)
      ((τ : ℂ) * a) τ) ∧
    ((1 / 2 : ℂ) ^ 2 / 2 - 1 / 24) * a = a / 12 ∧
    ((-1 / 2 : ℂ) ^ 2 / 2 - 1 / 24) * a = a / 12 := by
  refine ⟨?_, fun τ ↦ ?_, by ring, by ring⟩
  · have hc := (Complex.continuous_ofReal.continuousAt.comp
      UnitaryProducts.Separation.analyticAt_frameMult_zero.continuousAt).mul_const a
    have he : ((UnitaryProducts.Corrector.frameMult 0 : ℝ) : ℂ) * a = a / 12 := by
      simp only [UnitaryProducts.Corrector.frameMult]; push_cast; ring
    simpa only [Function.comp_def, he] using hc.mono_left nhdsWithin_le_nhds
  · have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 τ := by simpa using (hasDerivAt_id' τ).ofReal_comp
    convert (((ht.pow 2).div_const 2).sub_const (1 / 24)).mul_const a using 1
    ring

/-- Section 1, a band gap does not ensure width: diag(0,7) has a positively separated band of
its exponential, but exceeds every width strictly below 2pi. The complementary rescaling claim
is `bounded_path_rescale_width`. -/
theorem band_gap_does_not_ensure_width :
    ∃ (hh : (diagonal ![(0 : ℂ), 7]).IsHermitian),
      (∀ w : ℝ, w < 2 * π → ∃ p q, w < |hh.eigenvalues p - hh.eigenvalues q|) ∧
      ∃ (S : Finset (Fin 2)) (hS : S.Nonempty) (hR : Sᶜ.Nonempty),
        0 < finiteEigenphaseGap hh.eigenvalues S hS hR :=
  width_band_gap_incomparable.2


end UnitaryProducts.Paper
