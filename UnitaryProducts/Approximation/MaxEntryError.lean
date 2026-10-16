/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.EntryError
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Evolution.Pieces

/-!
# Entry errors in the maximum norm

## Declarations

- `maxEntryNorm_le_of_entry_components`
- `norm_le_sparsity_mul_maxEntryNorm`
- `norm_sub_le_sparsity_mul_maxEntryNorm`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set WithLp
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The sparse Hermitian estimate in the entrywise maximum norm: $\|A\|\le s\|A\|_{\max}$ for a
Hermitian $s$-sparse $A$ (§3.1, the Schur test). -/
theorem norm_le_sparsity_mul_maxEntryNorm {A : 𝕄} (hA : A.IsHermitian)
    {s : ℕ} (hs : RowSparse s A) : ‖A‖ ≤ s * (maxEntryNorm A : ℝ) :=
  norm_le_sparsity_mul_of_entry_le hA (maxEntryNorm A).coe_nonneg hs
    (norm_entry_le_maxEntryNorm A)

/-- Zero preservation gives the support needed for the maximum-entry estimate:
$\|A-B\|\le s\|A-B\|_{\max}$ when $A$ is $s$-sparse and $B$ keeps its zero entries zero (§3.1,
$E=H(t)-H^{(F)}(t)$). -/
theorem norm_sub_le_sparsity_mul_maxEntryNorm {A B : 𝕄} {s : ℕ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : RowSparse s A)
    (hz : ∀ i j, A i j = 0 → B i j = 0) :
    ‖A - B‖ ≤ s * (maxEntryNorm (A - B) : ℝ) :=
  norm_le_sparsity_mul_maxEntryNorm (hA.sub hB) (rowSparse_entry_replacement hs hz).2

/-- Scalar component errors imply a maximum-entry error: if every entry has real and imaginary
parts of modulus at most $\delta$, then $\|A\|_{\max}\le\sqrt2\,\delta$ (proof of Example
3.2(ii)). -/
theorem maxEntryNorm_le_of_entry_components {A : 𝕄} {δ : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ i j, |(A i j).re| ≤ δ ∧ |(A i j).im| ≤ δ) :
    (maxEntryNorm A : ℝ) ≤ √2 * δ :=
  maxEntryNorm_le (mul_nonneg (Real.sqrt_nonneg 2) hδ) fun i j ↦
    (Complex.norm_le_sqrt_two_mul_max _).trans
      (mul_le_mul_of_nonneg_left (max_le (he i j).1 (he i j).2) (Real.sqrt_nonneg 2))

end UnitaryProducts
