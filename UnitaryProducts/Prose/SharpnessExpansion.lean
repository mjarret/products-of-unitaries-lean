/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.ChainSteps

/-!
# Expanded sharpness computation in Section 4

The proof displays the expanded quadratic phase used in the shared
phase-error computation for the corrected and uncorrected products.

## Declarations

- `sharp_unit_step_expanded`
The two endpoint phases are handled in `PaperProof.sharp_phase_error`.
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
open Complex Real Set Matrix MeasureTheory
open UnitaryProducts UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.Prose

/-- The expanded phase in the proof of Example 4.4. -/
theorem sharp_unit_step_expanded {T : ℕ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T) :
    (unitProduct sharpFamily T).1 =
      evol (Matrix.diagonal ![(1 : ℂ), -1])
        ((T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) := by
  have ht : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have htrap := (UnitStepsProse.trapezoid_square_error hT).2
  rw [integral_pow] at htrap
  norm_num at htrap
  rw [(sharp_unit_step_exponentials hT hU).1]
  congr 1
  field_simp [ht] at htrap ⊢
  linarith


/-- The scalar integrated-Hamiltonian argument used in the sharpness proof.
The comparison evolution is explicitly the exponential of the time integral;
its endpoint is evaluated by `integral_quadratic_clock`. -/
theorem sharp_evolution_endpoint_via_integral {T : ℝ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T) :
    U T = evol (Matrix.diagonal ![(1 : ℂ), -1]) (T / 3) := by
  have hscalar (t : ℝ) : (∫ s in (0 : ℝ)..t, (s / T) ^ 2) = t ^ 3 / (3 * T ^ 2) := by
    simp_rw [div_pow]
    rw [intervalIntegral.integral_div, integral_pow]
    norm_num
    field_simp
  have hV (t : ℝ) :
      HasDerivAt
        (fun t ↦ evol (Matrix.diagonal ![(1 : ℂ), -1])
          (∫ s in (0 : ℝ)..t, (s / T) ^ 2))
        (-I • (sharpFamily (t / T) *
          evol (Matrix.diagonal ![(1 : ℂ), -1])
            (∫ s in (0 : ℝ)..t, (s / T) ^ 2))) t := by
    simpa only [hscalar] using localSteps_hasDerivAt_sharpEvolution hT.ne' t
  obtain ⟨hUc, hU0, -, S, hS, hUd⟩ := hU
  have heq := UnitaryProducts.evolution_eq_of_solves_off_countable (T := T) S ∅ hS
    countable_empty (fun t _ ↦ localSteps_isHermitian_sharpFamily (t / T)) hUc
    (fun t _ ↦ (hV t).continuousAt.continuousWithinAt) hU0
    (by simp [UnitaryProducts.evol_zero])
    (fun t ht htS ↦ hUd t (Ioo_subset_Icc_self ht) htS)
    (fun t _ _ ↦ (hV t).hasDerivWithinAt) ⟨hT.le, le_rfl⟩
  rw [heq, integral_quadratic_clock]

end UnitaryProducts.Prose
