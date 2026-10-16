/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Approximation.VariationRegulated
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Evolution.Regulated
public import UnitaryProducts.Evolution.RegulatedExistence

/-!
# Sparsity of entry errors

## Declarations

- `rowSparse_entry_replacement`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A zero-preserving entry replacement preserves row sparsity, as does its error (§3.1: "Since an
odd $F$ has $F(0)=0$ and so keeps zero entries zero, the count is at most the number of nonzero
entries"). -/
theorem rowSparse_entry_replacement {A B : 𝕄} {s : ℕ}
    (hs : RowSparse s A) (hz : ∀ i j, A i j = 0 → B i j = 0) :
    RowSparse s B ∧ RowSparse s (A - B) := by
  classical
  have key : ∀ C : 𝕄, (∀ i j, A i j = 0 → C i j = 0) → RowSparse s C := fun C hC i ↦
    (Finset.card_le_card (Finset.monotone_filter_right _ fun j _ hj h ↦ hj (hC i j h))).trans (hs i)
  exact ⟨key B hz, key _ fun i j h ↦ by rw [Matrix.sub_apply, h, hz i j h, sub_self]⟩

end UnitaryProducts
