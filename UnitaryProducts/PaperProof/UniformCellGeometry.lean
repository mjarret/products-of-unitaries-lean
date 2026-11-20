/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# UniformCellGeometry

## Declarations

- `sum_Icc_one_eq_sum_range`
- `uniform_local_hamiltonian_derivative`
-/
@[expose] public section
open Set Real
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof

/-- Reindex the N jumps by their right sample, j = 1,...,N. -/
theorem sum_Icc_one_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, f j = ∑ k ∈ Finset.range N, f (k + 1) := by
  simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm] using
    Finset.sum_Ico_eq_sum_range f 1 (N + 1)

end UnitaryProducts.PaperProof
