/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.TruncationLevels
public import UnitaryProducts.Corrector.FrameBounds

/-!
# Partial fractions of $\mathcal N$ and non-resonance margins

## Declarations

- `frameMult_eq_tsum`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Real
noncomputable section

namespace UnitaryProducts.Corrector

/-- Partial fractions of the frame multiplier away from all integral resonances: for
$x \notin 2\pi\mathbb Z$, $(1 - (x/2)\cot(x/2))/x^2 = \sum_{n \ge 1} 2/(4\pi^2 n^2 - x^2)$,
the partial-fraction series of $\mathcal N$. It is Mathlib's `cot_series_rep` rescaled. -/
theorem frameMult_eq_tsum {x : ℝ} (hx : ∀ n : ℤ, x ≠ 2*π*n) :
    frameMult x = ∑' n : ℕ+, 2/(4*π^2*(n : ℝ)^2-x^2) := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  rw [frameMult, if_neg hx0]
  exact cot_form_eq_partialFractions hx

end UnitaryProducts.Corrector

namespace UnitaryProducts.Separation

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end UnitaryProducts.Separation

