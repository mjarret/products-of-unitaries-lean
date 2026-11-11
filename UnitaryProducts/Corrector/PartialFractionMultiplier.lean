/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Corrector.PartialFractions
public import UnitaryProducts.Corrector.FrameMultiplier
/-! # Scalar identification of the partial-fraction Taylor series -/
@[expose] public section
open Real
noncomputable section
namespace UnitaryProducts.Corrector

/-- Appendix A: the positive Taylor series and the cotangent formula agree. -/
theorem frameMult_eq_frameCoeff_series {x : ℝ} (hx : |x| < 2 * π) :
    frameMult x = ∑' n : ℕ, frameCoeff n * x ^ n := by
  by_cases hx0 : x = 0
  · subst x
    rw [frameMult, if_pos rfl]
    simpa only [frameBound] using frameBound_zero.symm
  · rw [frameMult, if_neg hx0, frameCoeff_series_eq_cot hx0 hx]

end UnitaryProducts.Corrector
