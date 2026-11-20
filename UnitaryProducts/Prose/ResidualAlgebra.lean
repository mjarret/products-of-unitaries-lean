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

end UnitaryProducts.Prose
