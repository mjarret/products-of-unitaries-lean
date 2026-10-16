/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.Adiabatic
public import UnitaryProducts.Evolution.Exponential

/-!
# Sparse matrices and the Schur test

## Declarations

- `RowSparse`
- `maxEntryNorm`
- `maxEntryNorm_le`
- `maxRowSum`
- `maxRowSum_le_sparsity_mul`
- `norm_entry_le_maxEntryNorm`
- `norm_le_maxRowSum`
- `norm_le_sparsity_mul_of_entry_le`
- `norm_le_sqrt_of_row_col_sum_le`
- `sum_norm_row_le`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator NNReal
open NormedSpace Set Finset Matrix

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Schur test**: row sums `≤ r` and column sums `≤ c` give `‖A‖ ≤ √(r c)`. The paper cites it
in §3.1 to bound a Hermitian matrix by its largest absolute row sum. -/
theorem norm_le_sqrt_of_row_col_sum_le {A : 𝕄} {r c : ℝ} (hr : ∀ i, ∑ j, ‖A i j‖ ≤ r)
    (hc : ∀ j, ∑ i, ‖A i j‖ ≤ c) : ‖A‖ ≤ √(r * c) := by
  -- The empty matrix (d = 0) is 0; otherwise r, c ≥ 0 since they bound sums of norms.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Subsingleton.elim A 0]
  have hr0 : 0 ≤ r := (sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hr ⟨0, hd⟩)
  have hc0 : 0 ≤ c := (sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hc ⟨0, hd⟩)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  -- Row estimate: |(Ax)_i|² ≤ (∑_j |A_ij|)(∑_j |A_ij| |x_j|²) ≤ r ∑_j |A_ij| |x_j|².
  have hrow : ∀ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ^ 2
      ≤ r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
    intro i
    have h1 : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ := by
      calc _ = ‖∑ j, A i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
        _ = _ := by simp
    calc _ ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := by gcongr
      _ ≤ (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
          sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun _ _ ↦ norm_nonneg _)
            (fun _ _ ↦ by positivity) fun _ _ ↦ by ring
      _ ≤ r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hr i) (sum_nonneg fun _ _ ↦ by positivity)
  -- Sum over rows and exchange the sums: ‖Ax‖² ≤ r ∑_j (∑_i |A_ij|) |x_j|² ≤ r c ‖x‖².
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero,
    EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (mul_nonneg hr0 hc0),
      EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x) i‖ ^ 2
      ≤ ∑ i, r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := sum_le_sum fun i _ ↦ hrow i
    _ = r * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
        rw [← mul_sum, sum_comm]; simp only [sum_mul]
    _ ≤ r * ∑ j, c * ‖x j‖ ^ 2 := by gcongr with j; exact hc j
    _ = r * c * ∑ j, ‖x j‖ ^ 2 := by rw [← mul_sum]; ring

/-- At most `s` nonzero entries in every row. Applied to a truncation error $H(t)-H^{(F)}(t)$, it
says that $F$ changes at most $s$ entries in each row of $H(t)$, the count $\sigma_F$ of §3.1;
for `s = 0` it says that the matrix is `0`. The positivity $s\ge1$ of an
$s$-sparse family is added separately, in `sparsity`. -/
def RowSparse (s : ℕ) (A : 𝕄) : Prop := ∀ i, #{j | A i j ≠ 0} ≤ s

/-- An $s$-sparse row with entries at most $c$ has absolute sum at most $sc$. -/
theorem sum_norm_row_le {A : 𝕄} {s : ℕ} {c : ℝ} (hs : RowSparse s A) (hc : ∀ i j, ‖A i j‖ ≤ c)
    (i : Fin d) : ∑ j, ‖A i j‖ ≤ s * c := by
  have hc0 : ∀ j, 0 ≤ c := fun j ↦ (norm_nonneg _).trans (hc i j)
  rw [← sum_filter_add_sum_filter_not univ (fun j ↦ A i j ≠ 0)]
  have hzero : ∑ j ∈ {j | ¬A i j ≠ 0}, ‖A i j‖ = 0 :=
    sum_eq_zero fun j hj ↦ by simp only [mem_filter, not_not] at hj; simp [hj.2]
  rw [hzero, add_zero]
  calc _ ≤ ∑ j ∈ {j | A i j ≠ 0}, c := sum_le_sum fun j _ ↦ hc i j
    _ = #{j | A i j ≠ 0} * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ s * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hs i) (hc0 i)

/-- Maximum absolute row sum $\max_p\sum_q|A_{pq}|$, as an `ℝ≥0`, with value zero for the empty
matrix ($d=0$). An adapter: this is Mathlib's $\ell^\infty$ operator norm
(`Matrix.linfty_opNNNorm_def`), named here because the $\ell^2$ operator norm is the matrix norm in
scope. -/
noncomputable def maxRowSum (A : 𝕄) : ℝ≥0 := univ.sup fun i ↦ ∑ j, ‖A i j‖₊

/-- Maximum entry norm $\|A\|_{\max}=\max_{p,q}|A_{pq}|$ (§3.1), as an `ℝ≥0`, with value zero for
the empty matrix ($d=0$). An adapter: this is Mathlib's entrywise sup norm (`Matrix.nnnorm_def`),
named here because the $\ell^2$ operator norm is the matrix norm in scope. -/
noncomputable def maxEntryNorm (A : 𝕄) : ℝ≥0 := univ.sup fun i ↦ univ.sup fun j ↦ ‖A i j‖₊

/-- A Hermitian matrix is bounded by its largest absolute row sum (§3.1): the Schur test with
column sums equal to row sums. -/
theorem norm_le_maxRowSum {A : 𝕄} (hA : A.IsHermitian) : ‖A‖ ≤ maxRowSum A := by
  have hrow : ∀ i, ∑ j, ‖A i j‖ ≤ (maxRowSum A : ℝ) := fun i ↦ by
    simpa only [NNReal.coe_sum, coe_nnnorm] using
      (NNReal.coe_le_coe.mpr (le_sup (f := fun i ↦ ∑ j, ‖A i j‖₊) (mem_univ i)))
  calc
    ‖A‖ ≤ √((maxRowSum A : ℝ) * maxRowSum A) :=
      norm_le_sqrt_of_row_col_sum_le hrow fun j ↦ by
        simpa only [← hA.apply j _, norm_star] using hrow j
    _ = maxRowSum A := Real.sqrt_mul_self (maxRowSum A).coe_nonneg

/-- The largest absolute row sum of an $s$-sparse matrix with entries at most $c$ is at most
$sc$. -/
theorem maxRowSum_le_sparsity_mul {A : 𝕄} {s : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hs : RowSparse s A) (hc : ∀ i j, ‖A i j‖ ≤ c) : (maxRowSum A : ℝ) ≤ s * c := by
  change (maxRowSum A : ℝ) ≤ (⟨s * c, mul_nonneg (Nat.cast_nonneg s) hc0⟩ : ℝ≥0)
  exact NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ ↦ NNReal.coe_le_coe.mp (by
    simpa only [NNReal.coe_sum, coe_nnnorm] using sum_norm_row_le hs hc i))

/-- Every entry is at most $\|A\|_{\max}$. -/
theorem norm_entry_le_maxEntryNorm (A : 𝕄) (i j : Fin d) :
    ‖A i j‖ ≤ (maxEntryNorm A : ℝ) := by
  exact_mod_cast (le_sup (f := fun j ↦ ‖A i j‖₊) (mem_univ j)).trans
    (le_sup (f := fun i ↦ univ.sup fun j ↦ ‖A i j‖₊) (mem_univ i))

/-- A uniform bound $c\ge0$ on the entries bounds $\|A\|_{\max}$. -/
theorem maxEntryNorm_le {A : 𝕄} {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i j, ‖A i j‖ ≤ c) :
    (maxEntryNorm A : ℝ) ≤ c :=
  NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ ↦ Finset.sup_le fun j _ ↦
    (by exact_mod_cast hc i j : ‖A i j‖₊ ≤ ⟨c, hc0⟩))

/-- **Sparse operator-norm bound**: an `s`-row-sparse Hermitian matrix with entries `≤ c` has
`‖A‖ ≤ s c` (§3.1, the bound $\|E\|\le s\|E\|_{\max}$ with $c=\|E\|_{\max}$). -/
theorem norm_le_sparsity_mul_of_entry_le {A : 𝕄} (hA : A.IsHermitian) {s : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hs : RowSparse s A) (hc : ∀ i j, ‖A i j‖ ≤ c) : ‖A‖ ≤ s * c := by
  calc
    ‖A‖ ≤ maxRowSum A := norm_le_maxRowSum hA
    _ ≤ s * (maxEntryNorm A : ℝ) :=
      maxRowSum_le_sparsity_mul (maxEntryNorm A).coe_nonneg hs (norm_entry_le_maxEntryNorm A)
    _ ≤ s * c := mul_le_mul_of_nonneg_left (maxEntryNorm_le hc0 hc) (Nat.cast_nonneg s)

end UnitaryProducts
