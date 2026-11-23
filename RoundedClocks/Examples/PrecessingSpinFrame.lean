/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinMatrix
public import RoundedClocks.Preliminaries

/-! The rotating-frame calculation opening the proof of Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction needed for Mathlib's exponential identities. -/
local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- The two constant generators in the first rotating-frame display obey the product rule. -/
theorem rotating_frame_derivative
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ exp (u • A) * exp (u • (B - A)))
      (exp (t • A) * B * exp (t • (B - A))) t := by
  have hA := hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  have hB := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B - A) t
  convert hA.mul hB using 1
  rw [← mul_assoc (exp (t • A)), mul_sub, sub_mul, ← add_sub_assoc, add_sub_cancel_left]

/-- The inverse rotating-frame factors cancel in the differential equation. -/
theorem rotating_frame_cancel (A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    exp (-(t • A)) * exp (t • A) = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl (t • A))),
    neg_add_cancel, NormedSpace.exp_zero]

/-- The conjugated sample factor in the sentence following the opening displays. -/
theorem rotating_frame_sample (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    exp (exp A * B * exp (-A)) = exp A * exp B * exp (-A) := by
  rw [Matrix.exp_neg]
  exact Matrix.exp_conj (exp A) B (NormedSpace.isUnit_exp A)

end RoundedClocks.PrecessingSpin
