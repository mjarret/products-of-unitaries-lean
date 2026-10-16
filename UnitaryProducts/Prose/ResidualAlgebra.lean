/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-!
# Residual algebra before differentiation

The residual expansion only needs a Taylor-remainder identity and the corrector ODE.
Keeping that algebra separate from full derivatives permits its use on endpoint half cells.
-/

@[expose] public section
noncomputable section
open Complex

namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Separate the frozen commutator from the changing Hamiltonian. -/
theorem local_commutator_split (K K₀ Y : 𝕄) :
    K * Y - Y * K₀ = (K₀ * Y - Y * K₀) + (K - K₀) * Y := by
  simp only [sub_mul]
  abel

/-- The residual subtracts the frozen corrector equation from the Hamiltonian difference. -/
theorem local_residual_at_sample (K K₀ Y Yd : 𝕄) :
    K - K₀ - Yd - I • (K * Y - Y * K₀) =
      (K - K₀) - (Yd + I • (K₀ * Y - Y * K₀)) - I • ((K - K₀) * Y) := by
  rw [local_commutator_split K K₀ Y, smul_add]
  abel

/-- The five-term residual expansion needs only the verified Taylor remainder equality. -/
theorem local_residual_five_terms_of_remainder (K K₀ D Y Yd J : 𝕄) (τ : ℝ)
    (hrem : K - K₀ - τ • D = J) :
    K - K₀ - Yd - I • (K * Y - Y * K₀) =
      τ • D - Yd - I • (K₀ * Y - Y * K₀) + J - I • ((K - K₀) * Y) := by
  rw [local_residual_at_sample, ← hrem]
  abel

/-- Substitute the corrector equation into the five-term expansion.
The final term records a discrepancy between the sampling and freezing points;
it vanishes when they agree, as in the proof of Lemma A.1. -/
theorem rounded_residual_of_remainder (K K₀ G D Y Yd J : 𝕄) (τ : ℝ)
    (hrem : K - K₀ - τ • D = J)
    (hode : Yd + I • (G * Y - Y * G) = τ • D) :
    K - K₀ - Yd - I • (K * Y - Y * K₀) =
      J - I • ((K - G) * Y) + I • (Y * (K₀ - G)) := by
  rw [local_residual_five_terms_of_remainder K K₀ D Y Yd J τ hrem]
  have hYd : Yd = τ • D - I • (G * Y - Y * G) := by
    rw [← hode]
    abel
  rw [hYd]
  simp only [smul_sub, sub_mul, mul_sub]
  abel

end UnitaryProducts.Prose
