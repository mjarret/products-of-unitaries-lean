/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Comparison.SharpInT

/-!
# Standalone steps of the paper's prose arguments

## Declarations

- `sharp_evolution_endpoint`
- `sharp_unit_step_exponentials`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Complex Set MeasureTheory Filter
open UnitaryProducts.Paper UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4.2, sharpness example: the evolution endpoint is `exp(-i(T/3)Z)`. -/
theorem sharp_evolution_endpoint {T : ℝ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T) :
    U T = evol (Matrix.diagonal ![(1 : ℂ), -1]) (T / 3) := by
  obtain ⟨hUc, hU0, -, S, hS, hUd⟩ := hU
  have hV := localSteps_hasDerivAt_sharpEvolution hT.ne'
  have heq := UnitaryProducts.evolution_eq_of_solves_off_countable (T := T) S ∅ hS
    countable_empty (fun t _ ↦ localSteps_isHermitian_sharpFamily (t / T)) hUc
    (fun t _ ↦ (hV t).continuousAt.continuousWithinAt) hU0
    (by simp [UnitaryProducts.evol_zero])
    (fun t ht htS ↦ hUd t (Ioo_subset_Icc_self ht) htS)
    (fun t _ _ ↦ (hV t).hasDerivWithinAt) ⟨hT.le, le_rfl⟩
  rw [heq]
  congr 1
  field_simp

/-- Section 4.2, sharpness display: at unit steps the product has both displayed phase
forms, and the half-step-processed endpoint has phase `T/3-1/2`. Here the positive integer
`N` is the paper's `T`. -/
theorem sharp_unit_step_exponentials {N : ℕ} (hN : 0 < N)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / N)) U 0 N) :
    (unitProduct sharpFamily N).1 = evol (Matrix.diagonal ![(1 : ℂ), -1])
      (∑ j ∈ Finset.range N, ((j : ℝ) / N)^2) ∧
    (unitProduct sharpFamily N).1 = evol (Matrix.diagonal ![(1 : ℂ), -1])
      (((N : ℝ) - 1) * (2 * N - 1) / (6 * N)) ∧
    evol (sharpFamily 1) (-(1 / 2)) * U N * evol (sharpFamily 0) (1 / 2) =
      evol (Matrix.diagonal ![(1 : ℂ), -1]) ((N : ℝ) / 3 - 1 / 2) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hprod : (unitProduct sharpFamily N).1 =
      evol (Matrix.diagonal ![(1 : ℂ), -1])
        (∑ j ∈ Finset.range N, ((j : ℝ) / N)^2) := by
    simpa only [div_self hn, one_smul, one_mul, unitProduct] using
      localSteps_pieceProduct_sharpFamily (N : ℝ) N N
  refine ⟨hprod, ?_, ?_⟩
  · rw [hprod, sum_sq_div_eq hN]
    congr 1
    field_simp
    ring
  · rw [sharp_evolution_endpoint (by exact_mod_cast hN) hU]
    have h1 : evol (sharpFamily 1) (-(1 / 2)) =
        evol (Matrix.diagonal ![(1 : ℂ), -1]) (-(1 / 2)) := by
      rw [sharpFamily, localSteps_evol_smul_sharp, one_pow, mul_one]
    have h0 : evol (sharpFamily 0) (1 / 2) = 1 := by
      rw [sharpFamily, localSteps_evol_smul_sharp, zero_pow two_ne_zero, mul_zero, evol_zero]
    rw [h1, h0, mul_one, ← evol_add]
    congr 1
    ring

end UnitaryProducts.Prose
