/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.Walks.WalkScalarCut

/-! # The crossing spectrum illustrated in Figure 1 -/
@[expose] public section
open Complex Real Set MeasureTheory
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.Prose
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Figure 1: two real eigenvalue branches can cross. The diagonal Hermitian
family has eigenvalues `s` and `-s`, meeting at zero and exchanging order. -/
theorem crossing_diagonal_spectrum (s : ℝ) :
    spectrum ℂ (Matrix.diagonal (![(s : ℂ), -(s : ℂ)] : Fin 2 → ℂ)) =
      {(s : ℂ), -(s : ℂ)} := by
  rw [spectrum_diagonal]
  ext z
  simp [or_comm]

end UnitaryProducts.Prose
