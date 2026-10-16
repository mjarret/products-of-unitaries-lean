/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.SimulationError
public import UnitaryProducts.Evolution.RoundedTransfer

/-!
# Half-step phases and endpoint leakage

## Declarations

- `half_step_leakage_comparison`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex
namespace UnitaryProducts
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Half-step phases preserve endpoint leakage.**  For Hermitian `H₀`, `H₁` and orthogonal
projectors `P`, `Q` commuting with them, the leakages of any `W` and `U` differ by at most the
distance from `W` to `e^{iH₁/2} U e^{-iH₀/2}`. -/
theorem half_step_leakage_comparison {H₀ H₁ P Q : 𝕄}
    (hH₀ : H₀.IsHermitian) (hH₁ : H₁.IsHermitian)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P H₀) (hQc : Commute Q H₁) (W U : 𝕄) :
    |‖(1 - Q) * W * P‖ - ‖(1 - Q) * U * P‖|
      ≤ ‖W - evol H₁ (-(1 / 2)) * U * evol H₀ (1 / 2)‖ := by
  have hQ' : Commute (1 - Q) (evol H₁ (-(1 / 2))) :=
    (Commute.one_left _).sub_left (commute_evol_right hQc _)
  have hP' : Commute P (evol H₀ (1 / 2)) := commute_evol_right hPc _
  have e : (1 - Q) * (evol H₁ (-(1 / 2)) * U * evol H₀ (1 / 2)) * P
      = evol H₁ (-(1 / 2)) * ((1 - Q) * U * P) * evol H₀ (1 / 2) := by
    simp only [mul_assoc]; rw [← hP'.eq, ← mul_assoc, hQ'.eq, mul_assoc]
  have hn : ‖(1 - Q) * U * P‖
      = ‖(1 - Q) * (evol H₁ (-(1 / 2)) * U * evol H₀ (1 / 2)) * P‖ := by
    rw [e, norm_evol_mul_mul_evol hH₁ hH₀]
  rw [hn]; exact projector_leakage_comparison hP hQ le_rfl

end UnitaryProducts
