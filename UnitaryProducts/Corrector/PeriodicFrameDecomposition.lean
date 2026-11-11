/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import UnitaryProducts.Evolution.PiecewiseDressedComparison

/-!
# The periodic corrector on one cell

## Declarations

- `UnitaryProducts.Paper.corrector_cancels_taylor`
- `frameExtension_zero`
-/

@[expose] public section

namespace UnitaryProducts.Paper
open Complex
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1 and the abstract, within-step cancellation: substituting the corrector equation
removes the linear Taylor term from the comparison residual. The Taylor remainder and
the product of the Hamiltonian difference with the corrector remain. -/
theorem corrector_cancels_taylor (K G Y Yd D : 𝕄) (τ : ℝ)
    (heq : Yd + I • (G * Y - Y * G) = τ • D) :
    K - G - Yd - I • (K * Y - Y * G) =
      K - G - τ • D - I • ((K - G) * Y) := by
  rw [← heq]
  simp only [smul_sub, sub_mul, sub_sub]
  abel

end UnitaryProducts.Paper

namespace UnitaryProducts.Dressed
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The left endpoint is the prescribed frame value. -/
theorem frameExtension_zero (h D Ybar : 𝕄) : frameExtension h D Ybar 0 = Ybar := by
  simp only [frameExtension, cellPrimitive, intervalIntegral.integral_same, add_zero,
    neg_zero, evol_zero, one_mul, mul_one]

end
end UnitaryProducts.Dressed
