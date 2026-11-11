/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian

/-! # The complex end-value multiplier

The complex extension of the correction's end-value multiplier agrees with
the real multiplier on real arguments. Its power series is developed in
`Corrector.PartialFractions`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory Topology
open scoped Real
open UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.WalkCut

/-- The complex extension of the end-value multiplier, with its removable value at zero. -/
def complexFrameMult (x : ℂ) : ℂ :=
  if x = 0 then 1 / 12 else (1 - (x / 2) * Complex.cot (x / 2)) / x ^ 2

/-- Restriction to real arguments recovers the paper's end-value multiplier. -/
theorem complexFrameMult_ofReal (x : ℝ) : complexFrameMult x = (frameMult x : ℂ) := by
  by_cases hx : x = 0
  · simp [complexFrameMult, frameMult, hx]
  · simp [complexFrameMult, frameMult, hx, Complex.ofReal_cot]

end UnitaryProducts.WalkCut
