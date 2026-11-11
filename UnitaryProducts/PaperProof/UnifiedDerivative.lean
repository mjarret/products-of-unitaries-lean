/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.PaperProof.MatrixSeries

/-! # Real-parameter differentiation of complex operator curves

These scalar-restriction and evaluation rules are used by the general power-series
derivative in Appendix A, including one-sided derivatives at interval endpoints.
-/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
open Complex Real Set Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper.UnitStepsProse

namespace UnitaryProducts.Corrector
section BanachSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Compose a real-parameter derivative with a complex-linear map. -/
theorem hasDerivWithinAt_complex_clm_comp (L : E →L[ℂ] F)
    {v : ℝ → E} {vd : E} {S : Set ℝ} {s : ℝ}
    (hv : HasDerivWithinAt v vd S s) :
    HasDerivWithinAt (fun t ↦ L (v t)) (L vd) S s :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s hv

/-- Evaluation of a complex-linear operator curve along a real parameter. -/
theorem hasDerivWithinAt_complex_clm_apply {L : ℝ → E →L[ℂ] F} {Ld : E →L[ℂ] F}
    {v : ℝ → E} {vd : E} {S : Set ℝ} {s : ℝ}
    (hL : HasDerivWithinAt L Ld S s) (hv : HasDerivWithinAt v vd S s) :
    HasDerivWithinAt (fun t ↦ L t (v t)) (Ld (v s) + L s vd) S s := by
  have hrestrict := (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).hasFDerivAt
    |>.comp_hasDerivWithinAt s hL
  exact hrestrict.clm_apply hv
end BanachSpace
end UnitaryProducts.Corrector

