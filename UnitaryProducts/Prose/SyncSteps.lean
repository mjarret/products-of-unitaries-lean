/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ResidualAlgebra
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.WalkComparisonJRS

/-!
# Local residuals and endpoint identities

## Declarations

- `free_arc_reflections`
-/

@[expose] public section

open Complex Real Set MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace UnitaryProducts.Prose

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The trigonometric reflections at width `2π - θ` in the proof of
the walk comparison. -/
theorem free_arc_reflections (θ : ℝ) :
    Real.sin ((2 * π - θ) / 2) = Real.sin (θ / 2) ∧
      Real.cos ((2 * π - θ) / 4) = Real.sin (θ / 4) ∧
      Real.cos ((2 * π - θ) / 2) = -Real.cos (θ / 2) := by
  have hhalf : (2 * π - θ) / 2 = π - θ / 2 := by ring
  have hquarter : (2 * π - θ) / 4 = π / 2 - θ / 4 := by ring
  rw [hhalf, hquarter, Real.sin_pi_sub, Real.cos_pi_div_two_sub, Real.cos_pi_sub]
  exact ⟨rfl, rfl, rfl⟩

end UnitaryProducts.Prose
