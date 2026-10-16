/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.SinTheta

/-!
# Window projectors are orthogonal projections

## Declarations

- `isStarProjection_windowProj`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator InnerProductSpace
open NormedSpace Complex Set Finset Matrix

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The window projector $P_{[m-c,m+c]}(A)$ is an orthogonal projection; in the junk case
(`A` not Hermitian) it is `0`, also a projection. -/
theorem isStarProjection_windowProj (m c : ℝ) (A : 𝕄) : IsStarProjection (windowProj m c A) := by
  unfold windowProj
  split_ifs with h
  exacts [isStarProjection_specProj h _, IsStarProjection.zero _]

end UnitaryProducts
