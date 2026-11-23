/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries

/-!
# Supporting lemmas for Section 3

These are the standard analytic and spectral facts used in the manuscript's proofs of the
fine-step results.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real InnerProductSpace
open Set Filter Finset Matrix MeasureTheory
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ## Entrywise truncation and the Schur test -/

/-- Applying an odd real function entrywise commutes with the adjoint. -/
theorem entrywise_adjoint (F : ℝ → ℝ) (hF : Function.Odd F) (A : 𝕄) :
    (entrywise F A).conjTranspose = entrywise F A.conjTranspose := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (hF (A j i).im).symm

/-- An odd entry map preserves Hermiticity, as does its error. -/
theorem entrywise_and_error_isHermitian (F : ℝ → ℝ) (hF : Function.Odd F)
    {A : 𝕄} (hA : A.IsHermitian) :
    (entrywise F A).IsHermitian ∧ (A - entrywise F A).IsHermitian := by
  have hFA : (entrywise F A).IsHermitian := by
    change (entrywise F A).conjTranspose = entrywise F A
    rw [entrywise_adjoint F hF A, hA.eq]
  exact ⟨hFA, hA.sub hFA⟩

/-- Bit truncation rounds a nonnegative real number toward zero. -/
theorem bitTruncation_nonneg_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ bitTruncation k x ∧ bitTruncation k x ≤ x := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rcases hx.eq_or_lt with rfl | hx
  · simp [bitTruncation]
  simp only [bitTruncation, Real.sign_of_pos hx, abs_of_pos hx, one_mul]
  have hf : 0 ≤ (⌊(2 : ℝ) ^ k * x⌋ : ℝ) := by
    exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hp.le hx.le)
  constructor
  · positivity
  · rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using Int.floor_le ((2 : ℝ) ^ k * x))

/-- Bit truncation lies between zero and its input, in either order. -/
theorem bitTruncation_mem_uIcc (k : ℕ) (x : ℝ) : bitTruncation k x ∈ uIcc 0 x := by
  rw [Set.mem_uIcc]
  rcases le_total 0 x with hx | hx
  · exact Or.inl (bitTruncation_nonneg_le k hx)
  · have hn := bitTruncation_nonneg_le k (neg_nonneg.mpr hx)
    have hodd : bitTruncation k (-x) = -bitTruncation k x := by
      simp only [bitTruncation, Real.sign_neg, abs_neg]
      ring
    rw [hodd] at hn
    exact Or.inr ⟨by linarith, by linarith⟩

/-- The discarded fractional part is strictly smaller than one binary unit. -/
theorem bitTruncation_error_lt (k : ℕ) (x : ℝ) :
    |x - bitTruncation k x| < ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hloss : |x - bitTruncation k x| = |x| - |bitTruncation k x| := by
    rcases Set.mem_uIcc.mp (bitTruncation_mem_uIcc k x) with h | h
    · have hx : 0 ≤ x := h.1.trans h.2
      simp only [abs_of_nonneg hx, abs_of_nonneg h.1,
        abs_of_nonneg (sub_nonneg.mpr h.2)]
    · have hx : x ≤ 0 := h.1.trans h.2
      simp only [abs_of_nonpos hx, abs_of_nonpos h.2,
        abs_of_nonpos (sub_nonpos.mpr h.1)]
      linarith
  have habs : |bitTruncation k x| = bitTruncation k |x| := by
    rcases Set.mem_uIcc.mp (bitTruncation_mem_uIcc k x) with h | h
    · rw [abs_of_nonneg (h.1.trans h.2), abs_of_nonneg h.1]
    · have hodd : bitTruncation k (-x) = -bitTruncation k x := by
        simp only [bitTruncation, Real.sign_neg, abs_neg]
        ring
      rw [abs_of_nonpos (h.1.trans h.2), abs_of_nonpos h.2, hodd]
  rw [hloss, habs]
  by_cases hx : x = 0
  · simp [hx, bitTruncation]
  have habspos : 0 < |x| := abs_pos.mpr hx
  rw [bitTruncation, Real.sign_of_pos habspos, abs_of_pos habspos]
  calc
    |x| - 1 * ((2 : ℝ) ^ k)⁻¹ * (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ) =
        ((2 : ℝ) ^ k * |x| - (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ)) /
          (2 : ℝ) ^ k := by field_simp
    _ < 1 / (2 : ℝ) ^ k :=
      (div_lt_div_iff_of_pos_right hp).2 (by
        simpa only [sub_lt_iff_lt_add, add_comm] using
          Int.lt_floor_add_one ((2 : ℝ) ^ k * |x|))
    _ = ((2 : ℝ) ^ k)⁻¹ := one_div _

/-- Each complex entry changes by at most `√2 2⁻ᵏ`. -/
theorem norm_sub_entrywise_bitTruncation_le (k : ℕ) (z : ℂ) :
    ‖z - ⟨bitTruncation k z.re, bitTruncation k z.im⟩‖ ≤
      √2 * ((2 : ℝ) ^ k)⁻¹ := by
  have hr := bitTruncation_error_lt k z.re
  have hi := bitTruncation_error_lt k z.im
  have hp : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
  have hr2 : (z.re - bitTruncation k z.re) ^ 2 ≤ (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hr.le 2)
  have hi2 : (z.im - bitTruncation k z.im) ^ 2 ≤ (((2 : ℝ) ^ k)⁻¹) ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hi.le 2)
  calc
    ‖z - ⟨bitTruncation k z.re, bitTruncation k z.im⟩‖ =
        √((z.re - bitTruncation k z.re) ^ 2 +
          (z.im - bitTruncation k z.im) ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    _ ≤ √(2 * (((2 : ℝ) ^ k)⁻¹) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = √2 * ((2 : ℝ) ^ k)⁻¹ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hp]

/-- Schur's test: bounds on absolute row and column sums bound the operator norm. -/
theorem norm_le_sqrt_of_row_col_sum_le {A : 𝕄} {r c : ℝ}
    (hr : ∀ i, ∑ j, ‖A i j‖ ≤ r) (hc : ∀ j, ∑ i, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ √(r * c) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Subsingleton.elim A 0]
  have hr0 : 0 ≤ r := (sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hr ⟨0, hd⟩)
  have hc0 : 0 ≤ c := (sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hc ⟨0, hd⟩)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  have hrow : ∀ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ^ 2 ≤
      r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
    intro i
    have h₁ : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ≤
        ∑ j, ‖A i j‖ * ‖x j‖ := by
      calc
        _ = ‖∑ j, A i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
        _ = _ := by simp
    calc
      _ ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := by gcongr
      _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
        sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun _ _ ↦ norm_nonneg _)
          (fun _ _ ↦ by positivity) fun _ _ ↦ by ring
      _ ≤ r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hr i) (sum_nonneg fun _ _ ↦ by positivity)
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero,
    EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (mul_nonneg hr0 hc0),
    EuclideanSpace.norm_sq_eq]
  calc
    ∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ^ 2 ≤
        ∑ i, r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := sum_le_sum fun i _ ↦ hrow i
    _ = r * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      rw [← mul_sum, sum_comm]
      simp only [sum_mul]
    _ ≤ r * ∑ j, c * ‖x j‖ ^ 2 := by gcongr with j; exact hc j
    _ = r * c * ∑ j, ‖x j‖ ^ 2 := by rw [← mul_sum]; ring

/-- A Hermitian matrix is bounded by any common bound on its absolute row sums. -/
theorem norm_le_row_sum_of_isHermitian {A : 𝕄} (hA : A.IsHermitian) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : ∀ i, ∑ j, ‖A i j‖ ≤ r) : ‖A‖ ≤ r := by
  have hc : ∀ j, ∑ i, ‖A i j‖ ≤ r := fun j ↦ by
    simpa only [← hA.apply j _, norm_star] using hr j
  calc
    ‖A‖ ≤ √(r * r) := norm_le_sqrt_of_row_col_sum_le hr hc
    _ = r := Real.sqrt_mul_self hr0

/-- A row with at most `s` nonzero entries, each at most `c`, has sum at most `s c`. -/
theorem sum_norm_row_le_of_card {A : 𝕄} {s : ℕ} {c : ℝ}
    (hs : ∀ i, (Finset.univ.filter fun j ↦ A i j ≠ 0).card ≤ s)
    (hc : ∀ i j, ‖A i j‖ ≤ c) (i : Fin d) : ∑ j, ‖A i j‖ ≤ s * c := by
  have hc0 : 0 ≤ c := (norm_nonneg (A i i)).trans (hc i i)
  rw [← sum_filter_add_sum_filter_not univ (fun j ↦ A i j ≠ 0)]
  have hzero : ∑ j ∈ {j | ¬ A i j ≠ 0}, ‖A i j‖ = 0 :=
    sum_eq_zero fun j hj ↦ by
      simp only [mem_filter, not_not] at hj
      simp [hj.2]
  rw [hzero, add_zero]
  calc
    _ ≤ ∑ _j ∈ {j | A i j ≠ 0}, c := sum_le_sum fun j _ ↦ hc i j
    _ = #{j | A i j ≠ 0} * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ s * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hs i) hc0

/-- The truncation error has at most `sparsity k H` nonzero entries in each row. -/
theorem truncation_error_card_le (k : ℕ) (H : ℝ → 𝕄) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (i : Fin d) :
    (Finset.univ.filter fun j ↦ (H x - entrywise (bitTruncation k) (H x)) i j ≠ 0).card ≤
      sparsity k H := by
  have hbdd : ∀ t : Icc (0 : ℝ) 1, BddAbove (Set.range fun p : Fin d ↦
      (Finset.univ.filter fun q ↦
        entrywise (bitTruncation k) (H t) p q ≠ H t p q).card) :=
    fun t ↦ ⟨d, by
      rintro _ ⟨p, rfl⟩
      exact (Finset.card_filter_le _ _).trans (by simp)⟩
  have hbdd' : BddAbove (Set.range fun t : Icc (0 : ℝ) 1 ↦ ⨆ p : Fin d,
      (Finset.univ.filter fun q ↦
        entrywise (bitTruncation k) (H t) p q ≠ H t p q).card) := by
    refine ⟨d, ?_⟩
    rintro _ ⟨t, rfl⟩
    rcases isEmpty_or_nonempty (Fin d) with h | h
    · simp
    · exact ciSup_le fun p ↦ (Finset.card_filter_le _ _).trans (by simp)
  calc
    (Finset.univ.filter fun j ↦
        (H x - entrywise (bitTruncation k) (H x)) i j ≠ 0).card =
        (Finset.univ.filter fun j ↦
          entrywise (bitTruncation k) (H x) i j ≠ H x i j).card := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Matrix.sub_apply,
        sub_ne_zero]
      exact not_congr eq_comm
    _ ≤ ⨆ p : Fin d, (Finset.univ.filter fun j ↦
        entrywise (bitTruncation k) (H x) p j ≠ H x p j).card :=
      le_ciSup (hbdd ⟨x, hx⟩) i
    _ ≤ sparsity k H := le_ciSup hbdd' ⟨x, hx⟩

/-! ## Regulated partitions -/

/-- Every checkpoint midpoint lies in `[0,1]`. -/
theorem checkpoint_midpoint_mem {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {j : ℕ} (hj : j < N) : (s j + s (j + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
  let t : ℕ → ℝ := fun i ↦ s (min i N)
  have hstep : ∀ i, t i ≤ t (i + 1) := fun i ↦ by
    rcases lt_or_ge i N with hi | hi
    · change s (min i N) ≤ s (min (i + 1) N)
      rw [min_eq_left hi.le, min_eq_left (Nat.succ_le_of_lt hi)]
      exact hs.1 i hi
    · change s (min i N) ≤ s (min (i + 1) N)
      rw [min_eq_right hi, min_eq_right (hi.trans i.le_succ)]
  have ht : Monotone t := monotone_nat_of_le_succ hstep
  have htj : t j = s j := by simp [t, min_eq_left hj.le]
  have htj1 : t (j + 1) = s (j + 1) := by simp [t, min_eq_left (Nat.succ_le_of_lt hj)]
  have ht0 : t 0 = 0 := by simp [t, hs.2.1]
  have htN : t N = 1 := by simp [t, hs.2.2]
  have h0 : 0 ≤ s j := by
    have h := ht (Nat.zero_le j)
    rwa [ht0, htj] at h
  have h1 : s (j + 1) ≤ 1 := by
    have h := ht (Nat.succ_le_of_lt hj)
    rwa [htj1, htN] at h
  have hcell := hs.1 j hj
  constructor <;> linarith

/-! ## Regulated step functions and their integrals -/

/-- Every point between the endpoints of a finite nondecreasing partition is a node or belongs
to the interior of one of its cells. -/
theorem checkpoint_or_mem_cell {N : ℕ} {s : ℕ → ℝ}
    (hmono : ∀ j < N, s j ≤ s (j + 1)) {x : ℝ} (hx : x ∈ Icc (s 0) (s N)) :
    (∃ j ≤ N, x = s j) ∨ ∃ j < N, x ∈ Ioo (s j) (s (j + 1)) := by
  induction N with
  | zero => exact Or.inl ⟨0, le_rfl, le_antisymm hx.2 hx.1⟩
  | succ N ih =>
      rcases le_or_gt x (s N) with hle | hgt
      · rcases ih (fun j hj ↦ hmono j (hj.trans N.lt_succ_self)) ⟨hx.1, hle⟩ with
          ⟨j, hj, rfl⟩ | ⟨j, hj, hxj⟩
        · exact Or.inl ⟨j, hj.trans N.le_succ, rfl⟩
        · exact Or.inr ⟨j, hj.trans N.lt_succ_self, hxj⟩
      · rcases hx.2.eq_or_lt with h | h
        · exact Or.inl ⟨N + 1, le_rfl, h⟩
        · exact Or.inr ⟨N, N.lt_succ_self, hgt, h⟩

/-- Checkpoints are nondecreasing between any two indices before the last checkpoint. -/
theorem checkpoints_mono {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : s i ≤ s j := by
  induction j with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact le_rfl
  | succ j ih =>
      rcases hij.eq_or_lt with rfl | hij
      · exact le_rfl
      · exact (ih (Nat.le_of_lt_succ hij) (j.le_succ.trans hj)).trans
          (hs.1 j (Nat.lt_of_succ_le hj))

/-- A function constant on the open cells of a finite partition is regulated; its values at the
nodes are unrestricted. -/
theorem piecewise_regulated_of_cells (K : ℝ → 𝕄) (s : ℕ → ℝ) (A : ℕ → 𝕄) (N : ℕ)
    (hK : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), K x = A j) :
    IsRegulated K (s 0) (s N) := by
  have first_change : ∀ (P : ℕ → Prop) (m : ℕ), P 0 → ¬ P m →
      ∃ j < m, P j ∧ ¬ P (j + 1) := by
    intro P m h0 hm
    induction m with
    | zero => exact absurd h0 hm
    | succ m ih =>
        by_cases h : P m
        · exact ⟨m, m.lt_succ_self, h, hm⟩
        · obtain ⟨j, hj, hp⟩ := ih h
          exact ⟨j, hj.trans m.lt_succ_self, hp⟩
  constructor
  · intro t ht
    obtain ⟨j, hj, hlo, hhi⟩ := first_change (fun j ↦ s j ≤ t) N ht.1
      (not_le.mpr ht.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (not_le.mp hhi)).filter_mono nhdsWithin_le_nhds] with x hx hxb
    exact (hK j hj x ⟨hlo.trans_lt hx, hxb⟩).symm
  · intro t ht
    obtain ⟨j, hj, hlo, hhi⟩ := first_change (fun j ↦ s j < t) N ht.1
      (not_lt.mpr ht.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hlo).filter_mono nhdsWithin_le_nhds] with x hx hxa
    exact (hK j hj x ⟨hxa, hx.trans_le (not_lt.mp hhi)⟩).symm

/-- Continuous operations preserve the one-sided limits of regulated families. -/
theorem regulated_map₂ {A B : ℝ → 𝕄} {a b : ℝ} (hA : IsRegulated A a b)
    (hB : IsRegulated B a b) (f : 𝕄 × 𝕄 → 𝕄) (hf : Continuous f) :
    IsRegulated (fun t ↦ f (A t, B t)) a b :=
  ⟨fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
      ((hA.1 t ht).choose_spec.prodMk_nhds (hB.1 t ht).choose_spec)⟩,
    fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
      ((hA.2 t ht).choose_spec.prodMk_nhds (hB.2 t ht).choose_spec)⟩⟩

/-- Multiplication by a fixed real scalar preserves regulatedness. -/
theorem regulated_const_smul {A : ℝ → 𝕄} {a b c : ℝ} (hA : IsRegulated A a b) :
    IsRegulated (fun t ↦ c • A t) a b :=
  regulated_map₂ hA hA (fun p ↦ c • p.1) (continuous_fst.const_smul c)

/-- Running a regulated unit-time family over a positive physical time preserves its one-sided
limits. -/
theorem regulated_div_time {A : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hA : IsRegulated A 0 1) : IsRegulated (fun t ↦ A (t / T)) 0 T := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hA.1 (t / T)
      ⟨div_nonneg ht.1 hT.le, (div_lt_one hT).2 ht.2⟩
    refine ⟨L, hL.comp ?_⟩
    exact (continuous_id.div_const T).continuousWithinAt.tendsto_nhdsWithin
      (fun _ hx ↦ (div_lt_div_iff_of_pos_right hT).2 hx)
  · intro t ht
    obtain ⟨L, hL⟩ := hA.2 (t / T)
      ⟨div_pos ht.1 hT, (div_le_one hT).2 ht.2⟩
    refine ⟨L, hL.comp ?_⟩
    exact (continuous_id.div_const T).continuousWithinAt.tendsto_nhdsWithin
      (fun _ hx ↦ (div_lt_div_iff_of_pos_right hT).2 hx)

/-- Changing physical time `t` to normalized time `s = t / T` multiplies the generator by `T`. -/
theorem generates_reparameterized {A V : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hV : Generates (fun t ↦ A (t / T)) V 0 T) :
    Generates (fun s ↦ T • A s) (fun s ↦ V (T * s)) 0 1 := by
  refine ⟨hV.1.comp (continuousOn_const.mul continuousOn_id) ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨mul_nonneg hT.le hs.1, (mul_le_iff_le_one_right hT).2 hs.2⟩
  · simpa using hV.2.1
  · intro s hs
    exact hV.2.2.1 (T * s)
      ⟨mul_nonneg hT.le hs.1, (mul_le_iff_le_one_right hT).2 hs.2⟩
  · obtain ⟨S, hS, hd⟩ := hV.2.2.2
    refine ⟨(fun s : ℝ ↦ T * s) ⁻¹' S,
      hS.preimage (fun x y hxy ↦ mul_left_cancel₀ hT.ne' hxy), fun s hs hsS ↦ ?_⟩
    have hmap : MapsTo (fun x : ℝ ↦ T * x) (Icc 0 1) (Icc 0 T) := fun x hx ↦
      ⟨mul_nonneg hT.le hx.1, (mul_le_iff_le_one_right hT).2 hx.2⟩
    have hd' := (hd (T * s) (hmap hs) hsS).scomp s
      (hasDerivAt_const_mul T).hasDerivWithinAt hmap
    rw [smul_comm T (-I)] at hd'
    simpa only [Function.comp_apply, mul_div_cancel_left₀ _ hT.ne', smul_mul, smul_smul,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, mul_assoc] using hd'

end RoundedClocks
