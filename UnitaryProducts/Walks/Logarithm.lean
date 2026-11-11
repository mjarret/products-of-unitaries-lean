/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogarithmBranch

/-!
# Sampled products of walks

## Declarations

- `stepProduct`
- `stepProduct_eq_pieceProduct`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Real

namespace UnitaryProducts

open UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The partial sampled product $W((n-1)/N)\cdots W(0)$ of the unit steps $W(j/N)$, $j < n$;
`stepProduct W T T` is the paper's $W_T$ (§4.3), the second component of `walk W T`. At `n = 0` it
is the empty product `1`; with `N = 0` every factor is `W 0`, as Lean's `x / 0 = 0` (every use
takes `N > 0`). -/
noncomputable def stepProduct (W : ℝ → 𝕄) (N : ℕ) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => W (n / N) * stepProduct W N n

/-- If $e^{-iG(j/N)} = W(j/N)$ for $j < N$, the sampled product of the walk $W$ is the unit-step
product of $G$ (the piecewise-constant evolution product of its samples). The proof of
the walk comparison uses it with $G = \Lambda$. -/
theorem stepProduct_eq_pieceProduct {W G : ℝ → 𝕄} {N : ℕ}
    (h : ∀ j : ℕ, j < N → evol (G (j / N)) 1 = W (j / N)) :
    ∀ n ≤ N, stepProduct W N n = pieceProduct (fun _ ↦ 1) (fun j ↦ G (j / N)) n := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih => rw [stepProduct, ← h n (by omega), ih (by omega)]; rfl

end UnitaryProducts
