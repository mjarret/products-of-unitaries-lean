/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Regulated

/-!
# Equal-variation checkpoints and midpoint products

## Declarations

- `heldProduct`
- `scheduleDuration`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator Topology
open Complex Set MeasureTheory

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The durations $t_{j+1} - t_j$ of the checkpoints $t_0, \dots, t_n$, and $0$ for $j \ge n$. -/
noncomputable def scheduleDuration (t : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if j < n then t (j + 1) - t j else 0

/-- The midpoint product (Definition 3.5) of the family $\Theta \circ H$ on checkpoints
$t_0, \dots, t_n$: the product (2.5) of the family equal to $\Theta(H(t_{j+1/2}))$,
$t_{j+1/2} = (t_j + t_{j+1})/2$, on each piece; Definition 3.5 is the case $\Theta = \mathrm{id}$.
A piece with $t_{j+1} = t_j$ contributes the factor $1$, matching the paper's "coinciding
checkpoints give the factor $1$" (proof of Theorem 3.6). -/
noncomputable def heldProduct (Θ : 𝕄 → 𝕄) (H : ℝ → 𝕄) (n : ℕ) (t : ℕ → ℝ) : 𝕄 :=
  pieceProduct (scheduleDuration t n) (fun j ↦ Θ (H ((t j + t (j + 1)) / 2))) n

end UnitaryProducts
