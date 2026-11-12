/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.PropTransfer

public import UnitaryProducts.Prose.FineSteps
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Comparison.OneSize
public import UnitaryProducts.PaperProof.ExTruncationBits
public import UnitaryProducts.Paper.FineStepBounds
public import UnitaryProducts.PaperProof.ThmComparison

/-!
# Section 3: cells of small oscillation

## Declarations

- `HasMidpointOscillation`
- `IsCheckpointPartition`
- `cellError_bddAbove`
- `checkpointPartition_pos`
- `checkpoint_midpoint_mem`
- `cor_jrs_oscillation`
- `exists_fine_bits_balanced`
- `exists_fine_bits_oscillation`
- `exists_oscillation_partition`
- `fine_bits_oscillation`
- `introthm_fine_oscillation`
- `maxCellError`
- `maxCellError_le`
- `midpoint_duhamel_integral`
- `norm_sub_le_maxCellError`
- `oscillation_exponential_tolerance`
- `oscillation_inverse_time_budget`
- `oscillation_inverse_time_count`
- `oscillation_inverse_time_count_rounding`
- `oscillation_inverse_time_product`
- `oscillation_inverse_time_tolerance`
- `oscillation_jrs_allocations`
- `rem_oscillation_count_lipschitz`
- `rem_oscillation_counts`
- `thm_fine_steps_sup`
- `uniform_cell_midpoint_distance`
-/

@[expose] public section
open scoped Matrix.Norms.L2Operator Topology ENNReal
open Set MeasureTheory Filter
open UnitaryProducts.Paper UnitaryProducts.Prose

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Checkpoints with prescribed endpoints, independently of any path's variation. -/
def IsCheckpointPartition (n : ℕ) (s : ℕ → ℝ) : Prop :=
  Monotone s ∧ s 0 = 0 ∧ s n = 1

/-- Definition 3.3: any finite ordered checkpoint list extends constantly after its last
point, preserving all checkpoints and satisfying the infinite-sequence encoding. -/
theorem checkpointPartition_constant_extension (n : ℕ) (s : ℕ → ℝ)
    (hs : ∀ i ≤ n, ∀ j ≤ n, i ≤ j → s i ≤ s j) (h0 : s 0 = 0) (hn : s n = 1) :
    IsCheckpointPartition n (fun j ↦ s (min j n)) ∧
      ∀ j ≤ n, s (min j n) = s j := by
  refine ⟨⟨?_, by simpa using h0, by simpa using hn⟩, ?_⟩
  · intro i j hij
    exact hs _ (min_le_right _ _) _ (min_le_right _ _) (min_le_min_right _ hij)
  · intro j hj
    rw [min_eq_left hj]

/-- Definition 3.3: midpoint error at most ε on every open cell. -/
def HasMidpointOscillation (H : ℝ → 𝕄) (n : ℕ) (s : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
    ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ ε

/-- A partition of the nondegenerate unit interval has at least one cell. -/
theorem checkpointPartition_pos {n : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpointPartition n s) : 0 < n :=
  -- If n = 0, the endpoint identities would give 1 = s n = s 0 = 0.
  Nat.pos_of_ne_zero fun hn ↦ by simpa [hn, hs.2.1] using hs.2.2

/-- Midpoints are in the parameter interval, including for empty cells. -/
theorem checkpoint_midpoint_mem {n : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpointPartition n s) {j : ℕ} (hj : j < n) :
    (s j + s (j + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
  have h0 := hs.2.1 ▸ hs.1 (Nat.zero_le j)
  have h1 := hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt hj)
  have h2 := hs.1 (Nat.le_succ j)
  constructor <;> linarith

/-- Largest open-cell error; inserting zero assigns zero to an empty cell. -/
def maxCellError (H : ℝ → 𝕄) (G : ℕ → 𝕄) (n : ℕ) (s : ℕ → ℝ) : ℝ :=
  ⨆ j : Fin n, sSup (insert 0 ((fun x ↦ ‖H x - G j‖) '' Ioo (s j) (s (j + 1))))

/-- Each cell's error set is bounded because a regulated path is bounded. -/
theorem cellError_bddAbove {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1)
    {n : ℕ} {s : ℕ → ℝ} (hs : IsCheckpointPartition n s) (G : ℕ → 𝕄)
    (j : Fin n) :
    BddAbove (insert 0 ((fun x ↦ ‖H x - G j‖) '' Ioo (s j) (s (j + 1)))) := by
  obtain ⟨B, hB0, hB⟩ := hreg.exists_norm_le zero_le_one
  refine ⟨B + ‖G j‖, ?_⟩
  rintro z (rfl | ⟨x, hx, rfl⟩)
  · positivity
  · have hx0 := hs.2.1 ▸ hs.1 (Nat.zero_le (j : ℕ))
    have hx1 := hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt j.isLt)
    have hnorm : ‖H x‖ ≤ B := hB x ⟨hx0.trans hx.1.le, hx.2.le.trans hx1⟩
    exact (norm_sub_le (H x) (G j)).trans (add_le_add hnorm le_rfl)

/-- The largest cell error bounds every point in every open cell. -/
theorem norm_sub_le_maxCellError {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1)
    {n : ℕ} {s : ℕ → ℝ} (hs : IsCheckpointPartition n s) (G : ℕ → 𝕄)
    {j : ℕ} (hj : j < n) {x : ℝ} (hx : x ∈ Ioo (s j) (s (j + 1))) :
    ‖H x - G j‖ ≤ maxCellError H G n s :=
  le_ciSup_of_le (Set.finite_range _).bddAbove ⟨j, hj⟩
    (le_csSup (cellError_bddAbove hreg hs G ⟨j, hj⟩) (Or.inr ⟨x, hx, rfl⟩))

/-- A nonnegative uniform pointwise error bounds the largest cell supremum. -/
theorem maxCellError_le {H : ℝ → 𝕄} {n : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpointPartition n s) (G : ℕ → 𝕄) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)), ‖H x - G j‖ ≤ ε) :
    maxCellError H G n s ≤ ε := by
  haveI : Nonempty (Fin n) := ⟨⟨0, checkpointPartition_pos hs⟩⟩
  refine ciSup_le fun j ↦ csSup_le ⟨0, Or.inl rfl⟩ ?_
  rintro z (rfl | ⟨x, hx, rfl⟩)
  · exact hε
  · exact hb j j.isLt x hx

/-- Duhamel for the held midpoint path on the full parameter interval. -/
theorem midpoint_duhamel_integral {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (F : ℝ → ℝ) (hodd : ∀ x, F (-x) = -F x) (n : ℕ) (s : ℕ → ℝ)
    (hs : IsCheckpointPartition n s) :
    ‖midpointProductOver ((levelFunctionData F).2 H) T n s - U T‖ ≤
      T * (∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1),
        ‖H x - (levelFunctionData F).1 (H ((s j + s (j + 1)) / 2))‖) := by
  classical
  let A := fun x ↦ scalarEntryMap F (H x)
  let G := fun j ↦ A ((s j + s (j + 1)) / 2)
  have hA : ∀ x ∈ Icc (0 : ℝ) 1, (A x).IsHermitian :=
    fun x hx ↦ (scalarEntryMap_and_error_isHermitian F hodd (hH x hx)).1
  -- Give K the value zero at checkpoints; their values do not affect the evolution.
  let cell := fun x j ↦ j < n ∧ x ∈ Ioo (s j) (s (j + 1))
  let K : ℝ → 𝕄 := fun x ↦ if h : ∃ j, cell x j then G h.choose else 0
  have hpieces : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)), K x = G j := by
    intro j hj x hx
    have hex : ∃ k, cell x k := ⟨j, hj, hx⟩
    have hc := hex.choose_spec
    have he : hex.choose = j := by
      rcases lt_trichotomy hex.choose j with hlt | he | hgt
      · have hh := hs.1 (Nat.succ_le_of_lt hlt)
        exact False.elim (by linarith [hc.2.2, hx.1])
      · exact he
      · have hh := hs.1 (Nat.succ_le_of_lt hgt)
        exact False.elim (by linarith [hc.2.1, hx.2])
    simp only [K, dif_pos hex, he]
  have hK : ∀ x ∈ Icc (0 : ℝ) 1, (K x).IsHermitian := by
    intro x _
    dsimp only [K]
    split_ifs with hx
    · exact hA _ (checkpoint_midpoint_mem hs hx.choose_spec.1)
    · exact Matrix.isHermitian_zero
  have hKr : IsRegulated K 0 1 := by
    simpa only [hs.2.1, hs.2.2] using piecewise_regulated K s G n hpieces
  obtain ⟨V, hV, hW⟩ :=
    midpointProductOver_eq_evolution_of_pieces hT hA hK n s hs hpieces
  -- Change time to s, then apply Duhamel once on the whole interval [0,1].
  have hUr := evolution_over_time hT hU
  have hVr := evolution_over_time hT hV
  -- Pair B with itself and project the first coordinate: scaling preserves both one-sided limits.
  have scale_reg (B : ℝ → 𝕄) (hB : IsRegulated B 0 1) :
      IsRegulated (fun x ↦ T • B x) 0 1 :=
    regulated_map₂ hB hB (fun p ↦ T • p.1) (continuous_fst.const_smul T)
  have hD := duhamel_bound zero_le_one
    (scale_reg H hreg) (scale_reg K hKr) hUr hVr
  have hi : IntervalIntegrable (fun x ↦ ‖H x - K x‖) volume 0 1 :=
    ((hreg.intervalIntegrable_on zero_le_one).sub
      (hKr.intervalIntegrable_on zero_le_one)).norm
  have hic (j : ℕ) (hj : j < n) :
      IntervalIntegrable (fun x ↦ ‖H x - K x‖) volume (s j) (s (j + 1)) := by
    apply hi.mono_set
    rw [uIcc_of_le (hs.1 (Nat.le_succ j)), uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (hs.2.1 ▸ hs.1 (Nat.zero_le j))
      (hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt hj))
  have hsum : (∫ x in (0 : ℝ)..1, ‖H x - K x‖) =
      ∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1), ‖H x - G j‖ := by
    have hadd := intervalIntegral.sum_integral_adjacent_intervals hic
    rw [hs.2.1, hs.2.2] at hadd
    rw [← hadd]
    refine Finset.sum_congr rfl fun j hj ↦ intervalIntegral.integral_congr_ae ?_
    have hn : ∀ᵐ x : ℝ ∂volume, x ≠ s (j + 1) := ae_iff.mpr (by simp)
    filter_upwards [hn] with x hx hmem
    rw [uIoc_of_le (hs.1 (Nat.le_succ j))] at hmem
    rw [hpieces j (Finset.mem_range.mp hj) x
      ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩]
  -- Duhamel (2.3) against the cellwise sample, after changing to normalized time.
  have hfirst : ‖midpointProductOver A T n s - U T‖ ≤
      T * (∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1), ‖H x - G j‖) := by
    simp only [mul_one, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hT,
      intervalIntegral.integral_const_mul] at hD
    rwa [hsum, ← hW] at hD
  exact hfirst

/-- Theorem 3.6 (`thm:fine-steps`): Duhamel,
in supremum form for arbitrary nondecreasing checkpoints. -/
theorem thm_fine_steps_sup {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (F : ℝ → ℝ) (hodd : ∀ x, F (-x) = -F x) (n : ℕ) (s : ℕ → ℝ)
    (hs : IsCheckpointPartition n s) :
    let M := fun j ↦ H ((s j + s (j + 1)) / 2)
    let G := fun j ↦ (levelFunctionData F).1 (M j)
    ‖midpointProductOver ((levelFunctionData F).2 H) T n s - U T‖ ≤
      T * maxCellError H G n s := by
  classical
  intro M G
  apply (midpoint_duhamel_integral hT hreg hH hU F hodd n s hs).trans
  apply mul_le_mul_of_nonneg_left _ hT.le
  calc
    _ ≤ ∑ j ∈ Finset.range n, ∫ _x in s j..s (j + 1), maxCellError H G n s :=
      Finset.sum_le_sum fun j hj ↦ intervalIntegral.integral_mono_on_of_le_Ioo
        (hs.1 (Nat.le_succ j))
        (localSteps_norm_integrable zero_lt_one hreg hs (Finset.mem_range.mp hj) _)
        intervalIntegrable_const
        (fun x hx ↦ norm_sub_le_maxCellError hreg hs G (Finset.mem_range.mp hj) hx)
    _ = maxCellError H G n s := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, ← Finset.sum_mul,
        Finset.sum_range_sub, hs.2.1, hs.2.2, sub_zero, one_mul]

/-- Lemma 3.4 (`lem:oscillation-partition`): regulated paths admit finitely many
strict cells with pairwise oscillation, and hence midpoint error, at most ε.
Hermiticity is unnecessary for this partition result. Pairwise cell oscillation
is bounded as well as the midpoint error. -/
theorem exists_oscillation_partition {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (s : ℕ → ℝ), IsCheckpointPartition n s ∧
      (∀ j < n, s j < s (j + 1)) ∧
      (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ ε) := by
  obtain ⟨n, τ, c, hτ, hsw, _, hb⟩ := exists_pieces_of_regulated
    zero_le_one hreg (half_pos hε)
  let s := switchTime τ
  have hs : IsCheckpointPartition n s :=
    ⟨switchTime_mono fun j ↦ (hτ j).le, switchTime_zero τ, hsw⟩
  have hpair : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε := by
    intro j hj x hx y hy
    -- Each point is within ε/2 of the cell value H(c j).
    calc
      ‖H x - H y‖ ≤ ‖H x - H (c j)‖ + ‖H (c j) - H y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖H x - H (c j)‖ + ‖H y - H (c j)‖ := by rw [norm_sub_rev (H (c j))]
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb j hj x hx) (hb j hj y hy)
      _ = ε := add_halves ε
  -- Positive cell durations make consecutive checkpoints strictly increasing.
  have hstrict : ∀ j < n, s j < s (j + 1) := by
    intro j _
    dsimp [s]
    rw [switchTime_succ]
    exact lt_add_of_pos_right _ (hτ j)
  -- The midpoint belongs to its open cell, so the pairwise bound applies.
  exact ⟨n, s, hs, hstrict, hpair, fun j hj x hx ↦
    hpair j hj x hx _ ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩⟩

/-- equation (3.1): bit error on any cells of midpoint error at most ε. -/
theorem fine_bits_oscillation {H U : ℝ → 𝕄} {T ε : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (n : ℕ) (s : ℕ → ℝ) (hs : IsCheckpointPartition n s) (hε : 0 ≤ ε)
    (hosc : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ ε)
    (k σ : ℕ)
    (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x))) :
    ‖midpointProductOver ((truncation k).2.2.2 H) T n s - U T‖ ≤
      T * (ε + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) := by
  have hbits := ex_truncation_bits (d := d) k
  have hduhamel := thm_fine_steps_sup hT hreg hH hU (truncation k).1 hbits.1 n s hs
  apply hduhamel.trans
  apply mul_le_mul_of_nonneg_left _ hT.le
  apply maxCellError_le hs _ (add_nonneg hε (by positivity))
  intro j hj x hx
  have hmid := checkpoint_midpoint_mem hs hj
  have htruncate := hbits.2 _ σ (hH _ hmid) (hsp _ hmid)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (H ((s j + s (j + 1)) / 2)) _).trans
    (add_le_add (hosc j hj x hx) htruncate)

/-- Theorem A (`introthm:fine-count`): regulated paths, checkpoints of
small midpoint oscillation, and the explicit product with its bit-error bound.
Any uniform sparsity upper bound is allowed; the paper uses the exact maximum.
Checkpoint existence and the factor identity are also supplied. -/
theorem introthm_fine_oscillation {H U : ℝ → 𝕄} {T ε : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) (hε : 0 < ε)
    (k σ : ℕ)
    (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x))) :
    (∃ (n : ℕ) (s : ℕ → ℝ), IsCheckpointPartition n s ∧
      HasMidpointOscillation H n s ε) ∧
    ∀ (n : ℕ) (s : ℕ → ℝ), IsCheckpointPartition n s →
      HasMidpointOscillation H n s ε →
      let W := midpointProductOver ((truncation k).2.2.2 H) T n s
      W = pieceProduct (scheduleDuration (fun j ↦ T * s j) n)
        (fun j ↦ (truncation k).2.2.2 H ((s j + s (j + 1)) / 2)) n ∧
      ‖W - U T‖ ≤ T * (ε + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) := by
  obtain ⟨n, s, hs, _, _, ho⟩ := exists_oscillation_partition hreg hε
  exact ⟨⟨n, s, hs, ho⟩, fun m t ht hosc ↦ ⟨midpointProductOver_eq _ T m t,
    fine_bits_oscillation hT hreg hH hU m t ht hε.le hosc k σ hsp⟩⟩

/-- Equation (3.1), existence form: every positive cell tolerance is available. -/
theorem exists_fine_bits_oscillation {H U : ℝ → 𝕄} {T ε : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) (hε : 0 < ε)
    (k σ : ℕ)
    (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x))) :
    ∃ (n : ℕ) (s : ℕ → ℝ), IsCheckpointPartition n s ∧
      (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ ε) ∧
      ‖midpointProductOver ((truncation k).2.2.2 H) T n s - U T‖ ≤
        T * (ε + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) := by
  obtain ⟨n, s, hs, _, _, ho⟩ := exists_oscillation_partition hreg hε
  exact ⟨n, s, hs, ho, fine_bits_oscillation hT hreg hH hU n s hs hε.le ho k σ hsp⟩

/-- Balancing the two errors gives the stated doubled bit bound when σ is positive. -/
theorem exists_fine_bits_balanced {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) (k σ : ℕ) (hσ : 0 < σ)
    (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x))) :
    ∃ (n : ℕ) (s : ℕ → ℝ), IsCheckpointPartition n s ∧
      ‖midpointProductOver ((truncation k).2.2.2 H) T n s - U T‖ ≤
        2 * Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ * T := by
  obtain ⟨n, s, hs, _, hb⟩ := exists_fine_bits_oscillation hT hreg hH hU
    (show 0 < Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ by positivity) k σ hsp
  exact ⟨n, s, hs, hb.trans_eq (by ring)⟩

/-- The three exact scalar budgets in the Example 3.8. -/
theorem oscillation_jrs_allocations {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    C / (2 * C / δ) = δ / 2 ∧
    (2 * C / δ) * (δ ^ 2 / (8 * C)) = δ / 4 ∧
    δ / 2 + δ / 4 + δ / 4 = δ :=
  ⟨by field_simp, by field_simp; ring, by ring⟩

/-- Example 3.8 (`cor:jrs`): the continuous bound plus two equal budgets,
without a variation hypothesis or an a priori number of cells.
Any uniform sparsity upper bound is allowed; the paper uses the exact maximum. -/
theorem cor_jrs_oscillation {H U : ℝ → 𝕄}
    (hreg : IsRegulated H 0 1) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ)
    (hU : IsEvolution (fun t ↦ H (t / (2 * C / δ))) U 0 (2 * C / δ))
    (hcont : ‖(1 - Q) * U (2 * C / δ) * P‖ ≤ C / (2 * C / δ))
    (n : ℕ) (s : ℕ → ℝ) (hs : IsCheckpointPartition n s)
    (hosc : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ δ ^ 2 / (8 * C))
    (k σ : ℕ)
    (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x)))
    (hk : Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ ^ 2 / (8 * C)) :
    let T := 2 * C / δ
    let W := midpointProductOver ((truncation k).2.2.2 H) T n s
    ‖(1 - Q) * W * P‖ ≤ C / T +
      T * (δ ^ 2 / (8 * C) + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) ∧
    C / T + T * (δ ^ 2 / (8 * C) + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) ≤
      δ / 2 + δ / 4 + δ / 4 ∧
    ‖(1 - Q) * W * P‖ ≤ δ := by
  intro T W
  have hT : 0 < T := div_pos (mul_pos two_pos hC) hδ
  have hb := fine_bits_oscillation hT hreg hH hU n s hs
    (by positivity : 0 ≤ δ ^ 2 / (8 * C)) hosc k σ hsp
  have htransfer := transfer_same_projectors hP hQ (U T) W
  have hl := (le_abs_self _).trans (htransfer.trans hb)
  have ha := oscillation_jrs_allocations hC hδ
  have hfirst : ‖(1 - Q) * W * P‖ ≤ C / T +
      T * (δ ^ 2 / (8 * C) + Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) := by
    dsimp only [W, T] at *
    linarith
  have hsecond : C / T + T * (δ ^ 2 / (8 * C) +
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) ≤ δ / 2 + δ / 4 + δ / 4 := by
    calc
      _ ≤ C / T + T * (δ ^ 2 / (8 * C) + δ ^ 2 / (8 * C)) := by gcongr
      _ = _ := by rw [mul_add, ha.1, ha.2.1]; ring
  exact ⟨hfirst, hsecond, (hfirst.trans hsecond).trans_eq ha.2.2⟩

/-- Uniform-cell geometry: distance to the midpoint is at most 1/(2N). -/
theorem uniform_cell_midpoint_distance (n j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((j : ℝ) / n) (((j + 1 : ℕ) : ℝ) / n)) :
    |x - ((j : ℝ) / n + ((j + 1 : ℕ) : ℝ) / n) / 2| ≤ 1 / (2 * n) := by
  have he : ((j + 1 : ℕ) : ℝ) / n - (j : ℝ) / n = 1 / n := by push_cast; ring
  rw [show 1 / (2 * (n : ℝ)) = (1 / n) / 2 by ring, abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2]

/-- Remark 3.7, Lipschitz case: every integer above the stated threshold works. -/
theorem rem_oscillation_count_lipschitz {H : ℝ → 𝕄}
   {L ε : ℝ}
    (hε : 0 < ε)
   (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖H x - H y‖ ≤ L * |x - y|)
   (n : ℕ)
   (hn : max 1 (L / (2 * ε)) ≤ (n : ℝ)) :
    let s := fun j : ℕ ↦ (j : ℝ) / n
    IsCheckpointPartition n s ∧
      (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
        ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ L / (2 * n)) ∧
      L / (2 * n) ≤ ε := by
  -- At x = 1 and y = 0, the Lipschitz hypothesis bounds a nonnegative norm by L.
  have hL : 0 ≤ L := by simpa using (norm_nonneg _).trans (hLip 1 (by norm_num) 0 (by norm_num))
  intro s
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hn)
  have hs : IsCheckpointPartition n s := by
    refine ⟨fun i j hij ↦ ?_, by simp [s], by simp [s, ne_of_gt hn0]⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hn0.le
  refine ⟨hs, ?_, ?_⟩
  · intro j hj x hx
    have hx0 := hs.2.1 ▸ hs.1 (Nat.zero_le j)
    have hx1 := hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt hj)
    calc
      _ ≤ L * |x - (s j + s (j + 1)) / 2| :=
        hLip x ⟨hx0.trans hx.1.le, hx.2.le.trans hx1⟩ _ (checkpoint_midpoint_mem hs hj)
      _ ≤ L * (1 / (2 * n)) :=
        mul_le_mul_of_nonneg_left (uniform_cell_midpoint_distance n j hx) hL
      _ = _ := by ring
  · have hcount : L / (2 * ε) ≤ (n : ℝ) := (le_max_right _ _).trans hn
    have hscaled : L ≤ (n : ℝ) * (2 * ε) :=
      (div_le_iff₀ (mul_pos two_pos hε)).mp hcount
    -- Clear the positive denominator 2n; the chosen threshold gives the error budget.
    apply (div_le_iff₀ (mul_pos two_pos hn0)).mpr
    linarith

/-- **Remark 3.7** (`rem:oscillation-counts`): the Lipschitz count,
including every-point midpoint geometry and the error bound.
The paper's `ℓ ≥ 0` follows from the Lipschitz hypothesis at 1 and 0. -/
theorem rem_oscillation_counts :
    ∀ (H : ℝ → 𝕄) (ℓ ε : ℝ), 0 < ε →
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖H x - H y‖ ≤ ℓ * |x - y|) →
      ∀ n : ℕ, max 1 (ℓ / (2 * ε)) ≤ (n : ℝ) →
      let s := fun j : ℕ ↦ (j : ℝ) / n
      IsCheckpointPartition n s ∧
        (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
          |x - (s j + s (j + 1)) / 2| ≤ 1 / (2 * n)) ∧
        (∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
          ‖H x - H ((s j + s (j + 1)) / 2)‖ ≤ ℓ / (2 * n)) ∧
        ℓ / (2 * n) ≤ ε ∧ HasMidpointOscillation H n s ε := by
  intro H ℓ ε hε hLip n hn s
  have h := rem_oscillation_count_lipschitz hε hLip n hn
  exact ⟨h.1, fun j _ x hx ↦ uniform_cell_midpoint_distance n j hx,
    h.2.1, h.2.2, fun j hj x hx ↦ (h.2.1 j hj x hx).trans h.2.2⟩

/-- After Theorem B: the cell contribution is at most c/T exactly at tolerance c/T². -/
theorem oscillation_inverse_time_tolerance {T ε c : ℝ} (hT : 0 < T) :
    T * ε ≤ c / T ↔ ε ≤ c / T ^ 2 := by
  -- T ε ≤ c/T iff (T ε)T ≤ c iff ε T² ≤ c iff ε ≤ c/T².
  rw [le_div_iff₀ hT, le_div_iff₀ (sq_pos_of_pos hT), mul_right_comm, ← sq, mul_comm]

/-- After Theorem B: the Lipschitz count at tolerance c/T² is LT²/(2c). -/
theorem oscillation_inverse_time_count {T c L : ℝ} (hT : 0 < T) (hc : 0 < c) :
    L / (2 * (c / T ^ 2)) = L * T ^ 2 / (2 * c) := by
  field_simp

/-- The count after Theorem B, including the additive one needed for a constant path.
For fixed positive L and c this is the claimed order LT². -/
theorem oscillation_inverse_time_count_rounding {T c L : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hL : 0 ≤ L) :
    let n := max 1 ⌈L * T ^ 2 / (2 * c)⌉₊
    max 1 (L / (2 * (c / T ^ 2))) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ 1 + L * T ^ 2 / (2 * c) := by
  intro n
  have ha : 0 ≤ L * T ^ 2 / (2 * c) := by positivity
  constructor
  · rw [oscillation_inverse_time_count hT hc]
    exact max_le (by exact_mod_cast (le_max_left _ _ : 1 ≤ n))
      ((Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _ : ⌈L * T ^ 2 / (2 * c)⌉₊ ≤ n)))
  · dsimp only [n]
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith [Nat.ceil_lt_add_one ha])

/-- Both error contributions of Theorem A can be budgeted to obtain 2c/T. -/
theorem oscillation_inverse_time_budget {T ε b c : ℝ} (hT : 0 < T)
    (hε : ε ≤ c / T ^ 2) (hb : b ≤ c / T ^ 2) :
    T * (ε + b) ≤ 2 * c / T := by
  rw [mul_add, show 2 * c / T = c / T + c / T by ring]
  exact add_le_add ((oscillation_inverse_time_tolerance hT).2 hε)
    ((oscillation_inverse_time_tolerance hT).2 hb)

/-- The comparison after Theorem B as an actual product bound: at most
1 + LT²/(2c) equal-cell factors and a bit budget c/T² give error at most 2c/T. -/
theorem oscillation_inverse_time_product {H U : ℝ → 𝕄}
   {T c L : ℝ}
   (hT : 0 < T)
   (hc : 0 < c)
    (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
   (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖H x - H y‖ ≤ L * |x - y|)
    (k σ : ℕ)
   (hsp : ∀ x ∈ Icc (0 : ℝ) 1, RowSparse σ (H x - (truncation k).2.2.1 (H x)))
    (hk : Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ c / T ^ 2) :
    let n := max 1 ⌈L * T ^ 2 / (2 * c)⌉₊
    let s := fun j : ℕ ↦ (j : ℝ) / n
    IsCheckpointPartition n s ∧ (n : ℝ) ≤ 1 + L * T ^ 2 / (2 * c) ∧
      ‖midpointProductOver ((truncation k).2.2.2 H) T n s - U T‖ ≤ 2 * c / T := by
  -- At x = 1 and y = 0, the Lipschitz hypothesis bounds a nonnegative norm by L.
  have hL : 0 ≤ L := by simpa using (norm_nonneg _).trans (hLip 1 (by norm_num) 0 (by norm_num))
  have hreg := regulated_of_continuousOn
    (continuousOn_of_norm_sub_le (fun s hs t ht ↦ hLip t ht s hs))
  intro n s
  have hn := oscillation_inverse_time_count_rounding hT hc hL
  have hε : 0 < c / T ^ 2 := div_pos hc (sq_pos_of_pos hT)
  have hs := rem_oscillation_count_lipschitz hε hLip n hn.1
  refine ⟨hs.1, hn.2, ?_⟩
  have hb := fine_bits_oscillation hT hreg hH hU n s hs.1 hε.le
    (fun j hj x hx ↦ (hs.2.1 j hj x hx).trans hs.2.2) k σ hsp
  exact hb.trans (oscillation_inverse_time_budget hT le_rfl hk)

/-- Discussion: the exponentially small target in the new tolerance formulation. -/
theorem oscillation_exponential_tolerance {T ε a b : ℝ} (hT : 0 < T) :
    T * ε ≤ Real.exp (-b * T ^ a) ↔ ε ≤ Real.exp (-b * T ^ a) / T := by
  rw [le_div_iff₀ hT, mul_comm]

end UnitaryProducts.PaperProof
