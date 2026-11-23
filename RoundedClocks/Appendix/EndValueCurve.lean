/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CommutatorSeriesDerivative

/-! # Matrix-curve derivative bounds

Lemma A.3 controls finite commutator sums along a matrix curve and prepares their telescoping
derivative identity.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Real scalar multiplication on complex operators agrees with complex coercion. -/
theorem endValue_real_smul_operator (r : ℝ) (T : 𝕄 →L[ℂ] 𝕄) :
    (r : ℂ) • T = r • T := by
  ext A i j
  simp

/-- Transport joint scalar continuity along the inclusion of real scalars. -/
theorem endValue_continuousSMul_real : ContinuousSMul ℝ (𝕄 →L[ℂ] 𝕄) := by
  constructor
  have h : Continuous (fun p : ℝ × (𝕄 →L[ℂ] 𝕄) ↦ (p.1 : ℂ) • p.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
  simpa only [endValue_real_smul_operator] using h

attribute [local instance] endValue_continuousSMul_real

/-- Jacobi's identity turns a matrix commutator into a commutator of operators. -/
theorem endValue_adL_commutator (Ω Λ : 𝕄) :
    adL (adL Ω Λ) = adL Ω * adL Λ - adL Λ * adL Ω := by
  apply ContinuousLinearMap.ext
  intro A
  change (Ω * Λ - Λ * Ω) * A - A * (Ω * Λ - Λ * Ω) =
    Ω * (Λ * A - A * Λ) - (Λ * A - A * Λ) * Ω -
      (Λ * (Ω * A - A * Ω) - (Ω * A - A * Ω) * Λ)
  noncomm_ring

/-- The finite inner sum in (F-split) telescopes after Jacobi's identity. -/
theorem endValue_insertion_commutator (Ω Λ : 𝕄) (n : ℕ) :
    powDeriv (adL Ω) (adL (adL Ω Λ)) n =
      adL Ω ^ n * adL Λ - adL Λ * adL Ω ^ n := by
  rw [endValue_adL_commutator, powDeriv_commutator]

end RoundedClocks
