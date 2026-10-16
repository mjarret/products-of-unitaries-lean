/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.ChainSteps
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian

/-! # Invariance of the corrector under scalar shifts

Subtracting a scalar multiple of the identity changes neither the adjoint map
nor the correction's end-value multiplier.
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
open UnitaryProducts.Corrector UnitaryProducts.WalkCut

noncomputable section
namespace UnitaryProducts.PaperProof

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

/-- Subtracting a scalar multiple of the identity leaves the adjoint map unchanged. -/
theorem adL_sub_smul_one (H : 𝕄) (c : ℂ) : adL (H - c • 1) = adL H := by
  ext1 E
  simp only [adL_apply, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

/-- Centering the logarithm by a scalar leaves its corrector multiplier unchanged. -/
theorem frameOp_sub_smul_one (H : 𝕄) (c : ℂ) (D : 𝕄) : frameOp (H - c • 1) D = frameOp H D := by
  simp only [frameOp, adL_sub_smul_one]

section ContourDerivative

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

end ContourDerivative

end UnitaryProducts.PaperProof
