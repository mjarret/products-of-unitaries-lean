/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic

/-!
# Entrywise truncation: Section 3.1 and the proof of Example 3.2

After Definition 3.1: for an odd `F`, `(A^{(F)})† = (A†)^{(F)}`, so for a Hermitian `A` both
`A^{(F)}` and the error `A - A^{(F)}` are Hermitian.

The proof of Example 3.2, in the paper's order:

* bit truncation is odd (`bitTruncation_odd`);
* `|x - [x]_k| = |x| - |[x]_k| < 2^{-k}` (`bitTruncation_error_lt`);
* an entry `z` of the error has `|z| ≤ √2 2^{-k}` (`norm_sub_entrywise_bitTruncation_le`);
* the Schur test for a Hermitian matrix, `‖A‖ ≤ max_p ∑_q |A_pq|`
  (`norm_le_row_sum_of_isHermitian`);
* each row of the error has at most `σ_k` nonzero entries (`truncation_error_card_le`,
  `sum_norm_row_le_of_card`).
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

/-! ## Bit truncation of a real number -/

/-- Example 3.2(i): bit truncation is odd. In `[x]_k = sgn(x) 2^{-k} ⌊2^k |x|⌋`, only the factor
`sgn(x)` depends on the sign of `x`, and it is odd. -/
theorem bitTruncation_odd (k : ℕ) : Function.Odd (bitTruncation k) := by
  intro x
  simp only [bitTruncation, Real.sign_neg, abs_neg]
  ring

/-- For `x ≥ 0`, bit truncation rounds toward zero: `0 ≤ [x]_k ≤ x`. -/
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

/-- `[x]_k` lies between `0` and `x`. -/
theorem bitTruncation_mem_uIcc (k : ℕ) (x : ℝ) : bitTruncation k x ∈ uIcc 0 x := by
  rw [Set.mem_uIcc]
  rcases le_total 0 x with hx | hx
  · exact Or.inl (bitTruncation_nonneg_le k hx)
  · have hn := bitTruncation_nonneg_le k (neg_nonneg.mpr hx)
    rw [bitTruncation_odd k x] at hn
    exact Or.inr ⟨by linarith, by linarith⟩

/-- Proof of Example 3.2: `|x - [x]_k| = |x| - |[x]_k| < 2^{-k}`, as `[x]_k` lies between `0` and
`x` and `2^k |x| - ⌊2^k |x|⌋ < 1`. -/
theorem bitTruncation_error_lt (k : ℕ) (x : ℝ) :
    |x - bitTruncation k x| < ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  -- `|x - [x]_k| = |x| - |[x]_k|`, as `[x]_k` lies between `0` and `x`.
  have hloss : |x - bitTruncation k x| = |x| - |bitTruncation k x| := by
    rcases Set.mem_uIcc.mp (bitTruncation_mem_uIcc k x) with h | h
    · have hx : 0 ≤ x := h.1.trans h.2
      simp only [abs_of_nonneg hx, abs_of_nonneg h.1,
        abs_of_nonneg (sub_nonneg.mpr h.2)]
    · have hx : x ≤ 0 := h.1.trans h.2
      simp only [abs_of_nonpos hx, abs_of_nonpos h.2,
        abs_of_nonpos (sub_nonpos.mpr h.1)]
      linarith
  -- `|[x]_k| = [|x|]_k`, as bit truncation is odd.
  have habs : |bitTruncation k x| = bitTruncation k |x| := by
    rcases Set.mem_uIcc.mp (bitTruncation_mem_uIcc k x) with h | h
    · rw [abs_of_nonneg (h.1.trans h.2), abs_of_nonneg h.1]
    · rw [abs_of_nonpos (h.1.trans h.2), abs_of_nonpos h.2, bitTruncation_odd k x]
  rw [hloss, habs]
  by_cases hx : x = 0
  · simp [hx, bitTruncation]
  have habspos : 0 < |x| := abs_pos.mpr hx
  rw [bitTruncation, Real.sign_of_pos habspos, abs_of_pos habspos]
  -- `|x| - 2^{-k} ⌊2^k |x|⌋ = (2^k |x| - ⌊2^k |x|⌋)/2^k < 2^{-k}`.
  calc
    |x| - 1 * ((2 : ℝ) ^ k)⁻¹ * (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ) =
        ((2 : ℝ) ^ k * |x| - (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ)) /
          (2 : ℝ) ^ k := by field_simp
    _ < 1 / (2 : ℝ) ^ k :=
      (div_lt_div_iff_of_pos_right hp).2 (by
        simpa only [sub_lt_iff_lt_add, add_comm] using
          Int.lt_floor_add_one ((2 : ℝ) ^ k * |x|))
    _ = ((2 : ℝ) ^ k)⁻¹ := one_div _

/-- Proof of Example 3.2: an entry `z` of the truncation error has real and imaginary parts of
modulus below `2^{-k}`, so `|z| ≤ √(2 · 4^{-k}) = √2 2^{-k}`. -/
theorem norm_sub_entrywise_bitTruncation_le (k : ℕ) (z : ℂ) :
    ‖z - ⟨bitTruncation k z.re, bitTruncation k z.im⟩‖ ≤
      √2 * ((2 : ℝ) ^ k)⁻¹ := by
  exact (Complex.norm_le_sqrt_two_mul_max _).trans
    (mul_le_mul_of_nonneg_left (max_le (bitTruncation_error_lt k z.re).le
      (bitTruncation_error_lt k z.im).le) (Real.sqrt_nonneg _))

/-! ## The Schur test -/

/-- The Schur test for a Hermitian matrix, as the proof of Example 3.2 uses it:
`‖A‖ ≤ max_p ∑_q |A_pq|`. -/
theorem norm_le_row_sum_of_isHermitian {A : 𝕄} (hA : A.IsHermitian) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : ∀ i, ∑ j, ‖A i j‖ ≤ r) : ‖A‖ ≤ r := by
  -- The Hermitian Schur inequality follows by bounding the spectral radius by the row norm.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa [Subsingleton.elim A 0] using hr0
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI := matrixCStarAlgebra d
  have h2 : spectralRadius ℂ A = ‖A‖₊ :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).spectralRadius_eq_nnnorm
  have hinf : spectralRadius ℂ A ≤
      ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ENNReal) := by
    have h := @spectrum.spectralRadius_le_nnnorm ℂ 𝕄 _ Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra _ Matrix.linfty_opNormOneClass A
    rwa [Matrix.linfty_opNNNorm_def] at h
  rw [h2, ENNReal.coe_le_coe] at hinf
  have h3 : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) ≤ ⟨r, hr0⟩ :=
    Finset.sup_le fun i _ ↦ by
      rw [← NNReal.coe_le_coe]; push_cast; exact hr i
  exact_mod_cast hinf.trans h3

/-- A row with at most `s` nonzero entries, each of modulus at most `c`, has absolute sum at most
`s c`. -/
theorem sum_norm_row_le_of_card {A : 𝕄} {s : ℕ} {c : ℝ}
    (hs : ∀ i, (Finset.univ.filter fun j ↦ A i j ≠ 0).card ≤ s)
    (hc : ∀ i j, ‖A i j‖ ≤ c) (i : Fin d) : ∑ j, ‖A i j‖ ≤ s * c := by
  have hc0 : 0 ≤ c := (norm_nonneg (A i i)).trans (hc i i)
  calc ∑ j, ‖A i j‖ = ∑ j ∈ Finset.univ.filter (fun j ↦ A i j ≠ 0), ‖A i j‖ :=
        (Finset.sum_filter_of_ne fun j _ h ↦ norm_ne_zero_iff.mp h).symm
    _ ≤ (Finset.univ.filter fun j ↦ A i j ≠ 0).card • c :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ hc i j
    _ ≤ s * c := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs i) hc0

/-- By the definition of `σ_k`, each row of the error `H(x) - H^{(k)}(x)` has at most `σ_k`
nonzero entries, for `x ∈ [0,1]`. -/
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

end RoundedClocks
