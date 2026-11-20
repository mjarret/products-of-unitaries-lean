/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# The sharp rounded-clock Duhamel bound

## Declarations

- `clock_error_eq_on_closed_cell`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set MeasureTheory Real

noncomputable section
namespace UnitaryProducts.Paper

open UnitStepsProse

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace UnitStepsProse

/-- Section 4, cell integral calculation (sec4a-6): on a closed cell the distance to the
rounded clock equals the distance to the center, including both ties. -/
theorem clock_error_eq_on_closed_cell {x : ℝ} (j : ℤ)
    (hx : |x - j| ≤ 1 / 2) : |(clock x : ℝ) - x| = |x - j| := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  by_cases ht : x < (j : ℝ) + 1 / 2
  · have hq : clock x = j := by
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith
    rw [hq, abs_sub_comm]
  · have he : x = (j : ℝ) + 1 / 2 := by linarith
    subst x
    have hq : clock ((j : ℝ) + 1 / 2) = j + 1 := by
      unfold clock
      rw [show (j : ℝ) + 1 / 2 + 1 / 2 = (j : ℝ) + 1 by ring]
      simp
    rw [hq]
    push_cast
    ring_nf

end UnitStepsProse
end UnitaryProducts.Paper
