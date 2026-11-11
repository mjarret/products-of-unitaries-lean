/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.SeparatedFrameKernel

/-!
# A Schwartz-kernel operator acting by $\mathcal N$ on separated eigenoperators

## Declarations

- `isHermitian_real_smul`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator FourierTransform
open Complex MeasureTheory Set
noncomputable section
namespace UnitaryProducts.Separation

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A real multiple of a Hermitian matrix is Hermitian (applied to $2\pi h$). -/
theorem isHermitian_real_smul {h : 𝕄} (hh : h.IsHermitian) (r : ℝ) :
    (r • h).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint] at hh ⊢; exact (IsSelfAdjoint.all r).smul hh

end UnitaryProducts.Separation
