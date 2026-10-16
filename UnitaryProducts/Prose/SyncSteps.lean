/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ResidualAlgebra
public import UnitaryProducts.PaperProof.ThmUnitStepsMax
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.WalkComparisonJRS

/-!
# Local residuals and endpoint identities

## Declarations

- `corrector_residual_integral`
- `free_arc_reflections`
- `local_first_three_terms_eq_zero`
- `local_residual_five_terms`
-/

@[expose] public section

open Complex Real Set MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace UnitaryProducts.Prose

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Section 4.1: the five terms in the displayed residual, before choosing the correction. -/
theorem local_residual_five_terms {K Kd : ℝ → 𝕄} {τ : ℝ} (Y Yd : 𝕄)
    (hd : ∀ s ∈ uIcc (0 : ℝ) τ, HasDerivAt K (Kd s) s)
    (hi : IntervalIntegrable Kd volume 0 τ) :
    K τ - K 0 - Yd - I • (K τ * Y - Y * K 0) =
      τ • Kd 0 - Yd - I • (K 0 * Y - Y * K 0) +
        (∫ s in (0 : ℝ)..τ, Kd s - Kd 0) - I • ((K τ - K 0) * Y) := by
  rw [local_residual_at_sample,
    intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi,
    intervalIntegral.integral_const, sub_zero]
  abel


/-- Equation (4.1) makes the first three terms of the residual cancel. -/
theorem local_first_three_terms_eq_zero (K₀ D Y Yd : 𝕄) (τ : ℝ)
    (heq : Yd + I • (K₀ * Y - Y * K₀) = τ • D) :
    τ • D - Yd - I • (K₀ * Y - Y * K₀) = 0 := by
  rw [sub_sub, ← heq, sub_self]


/-- Substitution of the corrector equation leaves the integral of the change
in the derivative and the product of the Hamiltonian difference with the correction. -/
theorem corrector_residual_integral {K Kd : ℝ → 𝕄} {τ : ℝ} (Y Yd : 𝕄)
    (hd : ∀ s ∈ uIcc (0 : ℝ) τ, HasDerivAt K (Kd s) s)
    (hi : IntervalIntegrable Kd volume 0 τ)
    (heq : Yd + I • (K 0 * Y - Y * K 0) = τ • Kd 0) :
    K τ - K 0 - Yd - I • (K τ * Y - Y * K 0) =
      (∫ s in (0 : ℝ)..τ, Kd s - Kd 0) - I • ((K τ - K 0) * Y) := by
  rw [local_residual_five_terms Y Yd hd hi,
    local_first_three_terms_eq_zero (K 0) (Kd 0) Y Yd τ heq, zero_add]


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
