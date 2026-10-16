/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Evolution.Pieces

/-!
# Entrywise level maps

## Declarations

- `scalarEntryMap`
- `scalarEntryMap_isHermitian`
-/

@[expose] public section

namespace UnitaryProducts
open Set Finset Matrix

/-- Apply a real scalar map to both components of each matrix entry: the paper's
$A^{(f)}_{pq}=f(\operatorname{Re}A_{pq})+if(\operatorname{Im}A_{pq})$ (§3.1). Defined for every
`f`; the paper applies it to real functions (Definition 3.1). -/
noncomputable def scalarEntryMap (f : ℝ → ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ ⟨f (A i j).re, f (A i j).im⟩

/-- For odd `f`, the entry map preserves Hermitian matrices (§3.1: "each $H^{(F)}(s)$ … is
Hermitian"); only oddness is used. -/
theorem scalarEntryMap_isHermitian (f : ℝ → ℝ) (hodd : ∀ x, f (-x) = -f x)
    {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    (scalarEntryMap f A).IsHermitian := by
  ext i j
  change star (⟨f (A j i).re, f (A j i).im⟩ : ℂ) = ⟨f (A i j).re, f (A i j).im⟩
  rw [← hA.apply i j]
  exact Complex.ext rfl (hodd _).symm

end UnitaryProducts
