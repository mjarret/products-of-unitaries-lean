/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Prose.FineSteps

/-!
# The paper proof of Example 3.2 (bits)

## Declarations

- `ex_truncation_bits`
- `odd_of_scalarEntryMap_preserves_hermitian`
- `scalarEntryMap_adjoint`
- `scalarEntryMap_and_error_isHermitian`
- `scalarEntryMap_preserves_hermitian_iff`
- `truncBits_entry_sqrt_chain`
- `truncBits_eq_sign_floor`
- `truncBits_error_chain`
- `truncBits_odd_from_sign`
- `truncBits_abs_loss`
- `truncBits_error_lt`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 3.1: odd entry maps commute with the adjoint for every matrix. -/
theorem scalarEntryMap_adjoint (F : ℝ → ℝ) (hodd : Function.Odd F) (A : 𝕄) :
    (scalarEntryMap F A).conjTranspose = scalarEntryMap F A.conjTranspose := by
  ext i j
  apply Complex.ext
  · rfl
  · exact (hodd (A j i).im).symm

/-- Section 3.1: the truncated sample and its error are Hermitian. -/
theorem scalarEntryMap_and_error_isHermitian (F : ℝ → ℝ) (hodd : Function.Odd F)
    {A : 𝕄} (hA : A.IsHermitian) :
    (scalarEntryMap F A).IsHermitian ∧ (A - scalarEntryMap F A).IsHermitian := by
  have hm : (scalarEntryMap F A).IsHermitian := by
    change (scalarEntryMap F A).conjTranspose = scalarEntryMap F A
    rw [scalarEntryMap_adjoint F hodd A, hA.eq]
  exact ⟨hm, hA.sub hm⟩

/-- Section 3.1: the off-diagonal pair `iy,-iy` forces oddness in dimension at least two. -/
theorem odd_of_scalarEntryMap_preserves_hermitian (hd : 2 ≤ d) (F : ℝ → ℝ)
    (hF : ∀ A : 𝕄, A.IsHermitian → (scalarEntryMap F A).IsHermitian) :
    Function.Odd F := by
  classical
  let p : Fin d := ⟨0, by omega⟩
  let q : Fin d := ⟨1, by omega⟩
  have hpq : p ≠ q := by simp [p, q]
  intro y
  let M : 𝕄 := fun i j ↦ if i = p ∧ j = q then ⟨0, y⟩ else 0
  let A := M + M.conjTranspose
  have hA : A.IsHermitian := by
    change (M + M.conjTranspose).conjTranspose = M + M.conjTranspose
    simp [Matrix.conjTranspose_add, add_comm]
  have he := congrArg Complex.im ((hF A hA).apply q p)
  simpa [scalarEntryMap, A, M, Matrix.add_apply, Matrix.conjTranspose_apply,
    hpq, hpq.symm] using he.symm

/-- Section 3.1: for `d ≥ 2`, oddness is exactly preservation of Hermitian matrices. -/
theorem scalarEntryMap_preserves_hermitian_iff (hd : 2 ≤ d) (F : ℝ → ℝ) :
    (∀ A : 𝕄, A.IsHermitian → (scalarEntryMap F A).IsHermitian) ↔ Function.Odd F :=
  ⟨odd_of_scalarEntryMap_preserves_hermitian hd F,
    fun hF _ hA ↦ (scalarEntryMap_and_error_isHermitian F hF hA).1⟩

/-- Example 3.2: the floor/ceiling implementation equals the paper's sign formula. -/
theorem truncBits_eq_sign_floor (k : ℕ) (x : ℝ) :
    truncBits k x = Real.sign x * ((2 : ℝ)^k)⁻¹ *
      (⌊(2 : ℝ)^k * |x|⌋ : ℝ) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [truncBits, level, if_neg (not_le.mpr hx), Real.sign_of_neg hx,
      abs_of_neg hx, mul_neg, Int.floor_neg, Int.cast_neg]
    ring
  · simp [truncBits, level]
  · simp only [truncBits, level, if_pos hx.le, Real.sign_of_pos hx, abs_of_pos hx]
    ring

/-- Example 3.2(i): only the sign factor changes under negation. -/
theorem truncBits_odd_from_sign (k : ℕ) : Function.Odd (truncBits k) := by
  intro x
  rw [truncBits_eq_sign_floor, truncBits_eq_sign_floor, Real.sign_neg, abs_neg]
  ring

/-- Proof of Example 3.2(ii): the literal square-root chain for one complex entry. -/
theorem truncBits_entry_sqrt_chain (k : ℕ) (z : ℂ) :
    let e := z - truncBitsC k z
    ‖e‖ = Real.sqrt (e.re ^ 2 + e.im ^ 2) ∧
    Real.sqrt (e.re ^ 2 + e.im ^ 2) < Real.sqrt (2 * ((4 : ℝ)^k)⁻¹) ∧
    Real.sqrt (2 * ((4 : ℝ)^k)⁻¹) = Real.sqrt 2 * ((2 : ℝ)^k)⁻¹ := by
  intro e
  have hr : |e.re| < ((2 : ℝ)^k)⁻¹ := abs_sub_truncBits_lt k z.re
  have hi : |e.im| < ((2 : ℝ)^k)⁻¹ := abs_sub_truncBits_lt k z.im
  have hp : 0 < ((2 : ℝ)^k)⁻¹ := by positivity
  have hs : ((4 : ℝ)^k)⁻¹ = (((2 : ℝ)^k)⁻¹)^2 := by
    have he : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    rw [he, inv_pow]
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    ring
  · apply Real.sqrt_lt_sqrt (by positivity)
    rw [hs]
    have hr2 : e.re ^ 2 < (((2 : ℝ)^k)⁻¹)^2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg e.re) hp.le).mpr hr
    have hi2 : e.im ^ 2 < (((2 : ℝ)^k)⁻¹)^2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg e.im) hp.le).mpr hi
    linarith
  · rw [hs, Real.sqrt_mul (by norm_num), Real.sqrt_sq hp.le]

/-- The interval assertion in Example 3.2 gives contraction and the absolute-value loss. -/
private theorem truncBits_abs_loss (k : ℕ) (x : ℝ) :
    |truncBits k x| ≤ |x| ∧ |x - truncBits k x| = |x| - |truncBits k x| := by
  rcases mem_uIcc.mp (Prose.truncBits_mem_uIcc k x) with h | h
  · have hx : 0 ≤ x := h.1.trans h.2
    simp only [abs_of_nonneg hx, abs_of_nonneg h.1,
      abs_of_nonneg (sub_nonneg.mpr h.2)]
    exact ⟨h.2, trivial⟩
  · have hx : x ≤ 0 := h.1.trans h.2
    simp only [abs_of_nonpos hx, abs_of_nonpos h.2,
      abs_of_nonpos (sub_nonpos.mpr h.1)]
    constructor <;> linarith

/-- The real error display in Example 3.2, from the discarded fractional part. -/
private theorem truncBits_error_lt (k : ℕ) (x : ℝ) :
    |x - truncBits k x| < ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have habs : |truncBits k x| = truncBits k |x| := by
    rcases mem_uIcc.mp (Prose.truncBits_mem_uIcc k x) with h | h
    · rw [abs_of_nonneg (h.1.trans h.2), abs_of_nonneg h.1]
    · rw [abs_of_nonpos (h.1.trans h.2), abs_of_nonpos h.2, truncBits_neg]
  rw [(truncBits_abs_loss k x).2, habs, truncBits, level, if_pos (abs_nonneg x)]
  calc
    |x| - (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ) / 2 ^ k =
        ((2 : ℝ) ^ k * |x| - (⌊(2 : ℝ) ^ k * |x|⌋ : ℝ)) / 2 ^ k := by
      field_simp
    _ < 1 / (2 : ℝ) ^ k :=
      (div_lt_div_iff_of_pos_right hp).2 (Prose.bit_fraction_lt_one k x)
    _ = ((2 : ℝ) ^ k)⁻¹ := one_div _

/-- Proof of Example 3.2(ii): the displayed scalar absolute-value loss and strict dyadic bound. -/
theorem truncBits_error_chain (k : ℕ) (x : ℝ) :
    |x - truncBits k x| = |x| - |truncBits k x| ∧
      |x| - |truncBits k x| < ((2 : ℝ)^k)⁻¹ := by
  have hloss := (truncBits_abs_loss k x).2
  exact ⟨hloss, hloss ▸ truncBits_error_lt k x⟩

/-- Internal bounds for Example 3.2: scalar loss, complex entry errors, and Schur.
The max-entry norm is a proof tool, not a separate part of the example. -/
private theorem truncation_proof_bounds (k : ℕ) :
    ((∀ x, (truncation (d := d) k).1 (-x) = -(truncation (d := d) k).1 x) ∧
      ∀ x, (truncation (d := d) k).1 x = x ↔ ∃ m : ℤ, x = m / 2 ^ k) ∧
    (∀ (H : ℝ → 𝕄) (t : ℝ), ∀ i j,
      |UnitaryProducts.truncBits k (H t i j).re-(H t i j).re| ≤ ((2:ℝ)^k)⁻¹ ∧
      |UnitaryProducts.truncBits k (H t i j).im-(H t i j).im| ≤ ((2:ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄), A.IsHermitian →
      ((truncation k).2.2.1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (truncation k).2.2.1 A i j = 0) ∧
      (sparsity 1 (A-(truncation k).2.2.1 A)).2 ≤
        Real.sqrt 2 * ((2 : ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄) (s : ℕ), A.IsHermitian →
      UnitaryProducts.RowSparse s (A-(truncation k).2.2.1 A) →
      ‖A-(truncation k).2.2.1 A‖ ≤ Real.sqrt 2*s*((2:ℝ)^k)⁻¹) := by
  -- (i): oddness.
  have hodd : ∀ x, truncBits k (-x) = -truncBits k x := truncBits_odd_from_sign k
  -- The displayed scalar loss bounds both components of each entry.
  have hcomponents : ∀ (H : ℝ → 𝕄) (t : ℝ), ∀ i j,
      |truncBits k (H t i j).re - (H t i j).re| ≤ ((2 : ℝ)^k)⁻¹ ∧
      |truncBits k (H t i j).im - (H t i j).im| ≤ ((2 : ℝ)^k)⁻¹ := by
    intro H t i j
    have hr := truncBits_error_chain k (H t i j).re
    have hi := truncBits_error_chain k (H t i j).im
    exact ⟨by simpa only [abs_sub_comm] using (hr.1.trans_lt hr.2).le,
      by simpa only [abs_sub_comm] using (hi.1.trans_lt hi.2).le⟩
  have hpoint : ∀ A : 𝕄, A.IsHermitian →
      ((truncation k).2.2.1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (truncation k).2.2.1 A i j = 0) ∧
      (sparsity 1 (A-(truncation k).2.2.1 A)).2 ≤
        Real.sqrt 2 * ((2 : ℝ)^k)⁻¹ := by
    intro A hA
    refine ⟨(scalarEntryMap_and_error_isHermitian (truncBits k) hodd hA).1, ?_, ?_⟩
    · intro i j hij
      change (⟨truncBits k (A i j).re, truncBits k (A i j).im⟩ : ℂ) = 0
      have hz : truncBits k 0 = 0 := Function.Odd.map_zero hodd
      simp only [hij, Complex.zero_re, Complex.zero_im, hz]
      rfl
    · exact maxEntryNorm_le (by positivity)
        (fun i j ↦ by
          have hc := truncBits_entry_sqrt_chain k (A i j)
          exact (hc.1.trans_lt (hc.2.1.trans_eq hc.2.2)).le)
  refine ⟨⟨hodd, truncBits_eq_self_iff k⟩, hcomponents, hpoint, ?_⟩
  -- (ii): apply Schur to the Hermitian error and insert the max-entry bound.
  intro A s hA hs
  exact (norm_le_sparsity_mul_maxEntryNorm (hA.sub (hpoint A hA).1) hs).trans
    ((mul_le_mul_of_nonneg_left (hpoint A hA).2.2 (Nat.cast_nonneg s)).trans_eq (by ring))

/-- **Example 3.2** (`ex:truncation-bits`): (i) bit truncation is odd;
(ii) the Hermitian truncation error has the stated operator-norm bound.
The norm estimate holds for every matrix and every certified row-sparsity bound.
The paper applies it to each Hermitian path value with the global maximum. -/
theorem ex_truncation_bits (k : ℕ) :  -- Easier-to-read statement (v1.1.0): https://github.com/mjarret/products-of-unitaries-lean/blob/v1.1.0/UnitaryProducts/PaperProof/ExTruncationBits.lean#L217
    Function.Odd (truncation (d := d) k).1 ∧
    (∀ (A : 𝕄) (s : ℕ), A.IsHermitian →
      UnitaryProducts.RowSparse s (A - (truncation k).2.2.1 A) →
      ‖A - (truncation k).2.2.1 A‖ ≤ Real.sqrt 2 * s * ((2 : ℝ)^k)⁻¹) := by
  have h := truncation_proof_bounds (d := d) k
  exact ⟨h.1.1, h.2.2.2⟩

end UnitaryProducts.PaperProof
