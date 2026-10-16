/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# Pointwise steps in the residual estimate

## Declarations

- `scaled_corrector_bound_LM`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Set MeasureTheory Complex Real Filter
open UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.Paper.UnitStepsProse

/-- Multiplying the corrector bound by NL gives the scaled bound in the proof of Lemma A.1. -/
theorem scaled_corrector_bound_LM {E : Type*} [SeminormedAddCommGroup E]
    {Y : E} {T L c₀ τ : ℝ} {N : ℕ} (hL : 0 ≤ L)
    (hy : ‖Y‖ ≤ (c₀ + τ ^ 2 / 2) * (T / (N : ℝ) ^ 2) * L) :
    N * L * ‖Y‖ ≤ N * L * (c₀ + τ ^ 2 / 2) * (T / (N : ℝ) ^ 2) * L ∧
      N * L * (c₀ + τ ^ 2 / 2) * (T / (N : ℝ) ^ 2) * L =
        (c₀ + τ ^ 2 / 2) * (T / N) * L ^ 2 := by
  constructor
  · exact (mul_le_mul_of_nonneg_left hy (mul_nonneg (Nat.cast_nonneg N) hL)).trans_eq
      (by ring)
  · convert congrArg (fun z ↦ (c₀ + τ ^ 2 / 2) * T * L ^ 2 * z)
      (div_self_mul_self' (N : ℝ)) using 1 <;> ring


end UnitaryProducts.Paper.UnitStepsProse
