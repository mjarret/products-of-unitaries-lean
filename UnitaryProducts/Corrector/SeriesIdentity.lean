/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.Commutator
public import UnitaryProducts.Evolution.DysonSeries

/-!
# Continuity of the evolution and norms of conjugations

## Declarations

- `continuous_evol`
- `norm_evol_conj_le`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Complex Set UnitaryProducts.Corrector MeasureTheory Real

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The evolution operator is continuous in the time parameter. -/
theorem continuous_evol (G : 𝕄) : Continuous (evol G) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_evol G u).continuousAt

/-- Unitary conjugation does not increase the operator norm (Mathlib's `CStarRing` unitary
invariance, with `evol_mem_unitary`). -/
theorem norm_evol_conj_le {A : 𝕄} (hA : A.IsHermitian) (X : 𝕄) (t : ℝ) :
    ‖evol A (-t) * X * evol A t‖ ≤ ‖X‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hA t),
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hA (-t))]

end UnitaryProducts
