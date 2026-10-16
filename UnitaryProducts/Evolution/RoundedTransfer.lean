/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitStepPathDAT
public import UnitaryProducts.Evolution.RoundedClock

/-!
# Half-step phases, spectral projectors and norms

## Declarations

- `commute_evol_right`
- `commute_specProj`
- `norm_evol_mul_mul_evol`
- `PaperProof.uniform_phase_error_norm`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Real UnitaryProducts.Corrector MeasureTheory Complex

namespace UnitaryProducts
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

open Classical in
/-- A spectral projector of `A` commutes with `A`. -/
theorem commute_specProj {A : 𝕄} (hA : A.IsHermitian) (S : Set ℝ) :
    Commute (specProj hA S) A := by
  refine toEuclideanCLM_injective fun v ↦ ?_
  rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    toEuclideanCLM_specProj]
  refine ext_basis hA.eigenvectorBasis fun j ↦ ?_
  rw [inner_proj, isDiag_eigenvectorBasis hA j, isDiag_eigenvectorBasis hA j, inner_proj]
  by_cases h : hA.eigenvalues j ∈ S <;> simp [h]

/-- What commutes with `G` commutes with `e^{-iuG}`. -/
theorem commute_evol_right {P G : 𝕄} (h : Commute P G) (u : ℝ) : Commute P (evol G u) :=
  ((h.smul_right (-I)).smul_right u).exp_right

/-- Multiplying by unitaries `e^{-iuA}`, `e^{-ivB}` on the two sides preserves the norm. -/
theorem norm_evol_mul_mul_evol {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian) (X : 𝕄)
    (u v : ℝ) : ‖evol A u * X * evol B v‖ = ‖X‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (evol_mem_unitary hB v),
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary hA u)]

namespace PaperProof

/-- Undoing the two endpoint phases preserves the error norm. -/
theorem uniform_phase_error_norm (A₀ A₁ W X : 𝕄)
    (h₀ : A₀.IsHermitian) (h₁ : A₁.IsHermitian) (t : ℝ) :
    ‖W - evol A₁ (-t) * X * evol A₀ t‖ =
      ‖evol A₁ t * W * evol A₀ (-t) - X‖ := by
  have he : evol A₁ t * (W - evol A₁ (-t) * X * evol A₀ t) * evol A₀ (-t) =
      evol A₁ t * W * evol A₀ (-t) - X := by
    simp only [mul_sub, sub_mul, mul_assoc, ← evol_add, add_neg_cancel, evol_zero, mul_one]
    simp only [← mul_assoc, ← evol_add, add_neg_cancel, evol_zero, one_mul]
  rw [← he, norm_evol_mul_mul_evol h₁ h₀]

end PaperProof

end UnitaryProducts
