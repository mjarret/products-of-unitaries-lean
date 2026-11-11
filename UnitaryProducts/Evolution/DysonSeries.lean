/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Simulation

/-!
# Integral form of the Schrödinger equation

## Declarations

- `norm_intervalIntegral_le`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory NormedSpace

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A constant bound on the integrand bounds the integral. -/
theorem norm_intervalIntegral_le {f : ℝ → 𝕄} {a t C : ℝ} (hat : a ≤ t)
    (h : ∀ s ∈ Icc a t, ‖f s‖ ≤ C) : ‖∫ s in a..t, f s‖ ≤ C * (t - a) := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦
    h s (Ioc_subset_Icc_self (by rwa [uIoc_of_le hat] at hs))
  rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - a)] at hn

end UnitaryProducts
