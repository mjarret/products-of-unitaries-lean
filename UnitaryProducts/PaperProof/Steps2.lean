/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.FinalSteps

/-!
# Norm steps for the comparison of evolutions

## Declarations

- `duhamel_display_chain`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Equation (2.3), `eq:duhamel`: unitarity and the integral norm inequality after
the zero-correction specialization of Theorem 2.2. -/
theorem duhamel_display_chain {K G U V : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b)
    (hidentity : star (U b) * V b - 1 =
      ∫ t in a..b, I • (star (U t) * (K t - G t) * V t)) :
    ‖V b - U b‖ = ‖star (U b) * V b - 1‖ ∧
    ‖star (U b) * V b - 1‖ =
      ‖∫ t in a..b, I • (star (U t) * (K t - G t) * V t)‖ ∧
    ‖∫ t in a..b, I • (star (U t) * (K t - G t) * V t)‖ ≤
      ∫ t in a..b, ‖K t - G t‖ := by
  have mem (W : 𝕄) := (Matrix.mem_unitaryGroup_iff' (A := W)).mpr
  refine ⟨Prose.unitary_difference_norm ⟨U b, mem _ (hU.2.2.1 b ⟨hab, le_rfl⟩)⟩ (V b),
    congrArg norm hidentity, ?_⟩
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq
    (intervalIntegral.integral_congr fun t ht ↦ ?_)
  rw [uIcc_of_le hab] at ht
  rw [norm_smul, Complex.norm_I, one_mul,
    CStarRing.norm_mul_mem_unitary _ (mem _ (hV.2.2.1 t ht)),
    CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem
      (mem _ (hU.2.2.1 t ht)))]

end UnitaryProducts.PaperProof
