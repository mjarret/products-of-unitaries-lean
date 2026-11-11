/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Corrector.FrameBounds
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# The unit-step comparison at width below `2π`: jump form and `C²` forms

## Declarations

- `paper_series_eq`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The paper's series $\mathcal N(x)=\sum_{n\ge1}2/(4\pi^2n^2-x^2)$ and its derivative are the
positive series bounds `frameBound`, `frameLip` on $[0,2\pi)$. -/
theorem paper_series_eq {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    (∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)) = frameBound x ∧
      deriv (fun y : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-y^2)) x = frameLip x := by
  have ha : |x| < 2*π := by rwa [abs_of_nonneg hx0]
  exact ⟨(frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt ha)).symm.trans
      (by simpa only [abs_of_nonneg hx0] using (frameBound_abs_eq_frameMult ha).symm),
    (deriv_frameMult_eq_partialFractions ha).symm.trans (hasDerivAt_frameMult ha).deriv⟩

end UnitaryProducts.Paper
