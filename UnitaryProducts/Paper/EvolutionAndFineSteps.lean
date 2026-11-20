/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.MidpointError
public import UnitaryProducts.Evolution.RoundedClockEvolution

/-!
# Existence of evolutions and the fine-step theorems

## Declarations

- `exists_unique_evolution`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator ENNReal
open Complex Set MeasureTheory
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Existence and uniqueness of evolutions** (§2.1, unnumbered). Every regulated Hermitian family
$H$ on $[0,T]$ generates exactly one $U$.

Reading the statement against the paper:
* "Exactly one" is existence together with `EqOn V U (Icc 0 T)` for every `V` that $H$
  generates: the evolution is unique on $[0,T]$, and its values outside $[0,T]$ are irrelevant.
* `hH` is the paper's standing assumption that families are Hermitian.

The proof projects existence and uniqueness out of `regulated_evolution_rounded`, that is, out of
`regulated_evolution`. The route differs from the paper's, which cites Dieudonné: existence is
built by hand as a uniform limit of evolutions of step approximations of $H$, with dominated
convergence for the integral equation; unitarity comes from $(U^\dagger U)'=0$ off a countable
set, as in the paper; and uniqueness comes from the Duhamel bound `duhamel`. -/
theorem exists_unique_evolution (H : ℝ → 𝕄) (T : ℝ) (hT : 0 < T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) (hreg : IsRegulated H 0 T) :
    ∃ U : ℝ → 𝕄, IsEvolution H U 0 T ∧
      ∀ V : ℝ → 𝕄, IsEvolution H V 0 T → EqOn V U (Icc 0 T) :=
  ((regulated_evolution_rounded (d := d)).1 H T hT hH hreg).imp fun _ h ↦ ⟨h.1, h.2.1⟩

end UnitaryProducts.Paper
