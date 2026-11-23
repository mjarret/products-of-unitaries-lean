/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Evolution in the sharpness example

Example 4.3 solves the two-level continuous evolution by a rotating-frame transformation and
evaluates the required integral.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks.UnitSharp

/-- The diagonal matrix in Example 4.3. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

/-- The quadratic Hamiltonian in Example 4.3. -/
def H (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (s ^ 2 : ℝ) • Z

/-- The exponential of the fixed skew-adjoint generator. -/
def E (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := exp (u • (-I • Z))

/-- The matrix `Z` is Hermitian. -/
theorem Z_isHermitian : IsHermitian Z := by
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; fin_cases i <;> simp)

/-- Every value of the quadratic Hamiltonian is Hermitian. -/
theorem H_isHermitian (s : ℝ) : IsHermitian (H s) := by
  change (s ^ 2 • Z).IsHermitian
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  exact (IsSelfAdjoint.all (s ^ 2)).smul Z_isHermitian.isSelfAdjoint

/-- The exponential of the skew-adjoint generator is unitary. -/
theorem E_isUnitary (u : ℝ) : IsUnitary (E u) := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact Unitary.star_mul_self_of_mem <| NormedSpace.exp_mem_unitary_of_mem_skewAdjoint <|
    skewAdjoint.smul_mem u (Z_isHermitian.isSelfAdjoint.smul_mem_skewAdjoint hI)

/-- The derivative of `E` is multiplication by its constant generator. -/
theorem hasDerivAt_E (u : ℝ) : HasDerivAt E ((-I • Z) * E u) u :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) _ _

/-- The cubic phase solves the Schrödinger equation for the quadratic Hamiltonian. -/
theorem hasDerivAt_evolution {T : ℝ} (hT : T ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ E (t ^ 3 / (3 * T ^ 2)))
      (-I • (H (t / T) * E (t ^ 3 / (3 * T ^ 2)))) t := by
  have hφ : HasDerivAt (fun t : ℝ ↦ t ^ 3 / (3 * T ^ 2)) ((t / T) ^ 2) t := by
    convert (hasDerivAt_pow 3 t).div_const (3 * T ^ 2) using 1
    field_simp
    ring
  convert (hasDerivAt_E (t ^ 3 / (3 * T ^ 2))).scomp t hφ using 1
  rw [H, smul_mul_assoc, smul_mul_assoc, smul_comm]

/-- Integrating the rescaled quadratic Hamiltonian gives `TZ/3`. -/
theorem integral_H (T : ℝ) (hT : 0 < T) :
    (∫ t in 0..T, H (t / T)) = (T / 3) • Z := by
  simp_rw [H, div_pow]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_div,
    integral_pow]
  congr 1
  simp only [Nat.reduceAdd, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    sub_zero]
  field_simp
  all_goals ring

/-- Dieudonné's existence and uniqueness identify the explicit endpoint evolution. -/
theorem evolution_end (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (T : ℕ) (hT : 1 ≤ T) : evolution H T T = E ((T : ℝ) / 3) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let G : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t ↦ H (t / T)
  let U : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t ↦ E (t ^ 3 / (3 * (T : ℝ) ^ 2))
  have hGc : Continuous G := by
    dsimp [G, H]
    fun_prop
  have hreg : IsRegulated G 0 T := by
    constructor <;> intro t _
    · exact ⟨G t, hGc.continuousAt.mono_left inf_le_left⟩
    · exact ⟨G t, hGc.continuousAt.mono_left inf_le_left⟩
  have hG : IsHermitianFamily G 0 T := fun t _ ↦ H_isHermitian _
  have hU : Generates G U 0 T := by
    refine ⟨?_, ?_, ?_, ∅, countable_empty, ?_⟩
    · exact fun t _ ↦
        (hasDerivAt_evolution hTr.ne' t).continuousAt.continuousWithinAt
    · simp [U, E]
    · exact fun t _ ↦ E_isUnitary _
    · exact fun t _ _ ↦ (hasDerivAt_evolution hTr.ne' t).hasDerivWithinAt
  have hcanon : Generates G (evolutionOf G T) 0 T :=
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3
      hTr.le hreg hG
  have heq := generates_unique dieudonne_10_5_4 hreg hcanon hU
  have hphase : (T : ℝ) ^ 3 / (3 * (T : ℝ) ^ 2) = (T : ℝ) / 3 := by
    field_simp
  have hexp : exp (-I • (∫ t in 0..(T : ℝ), H (t / T))) = E ((T : ℝ) / 3) := by
    rw [integral_H (T : ℝ) hTr, E, smul_comm]
  calc
    evolution H T T = exp (-I • (∫ t in 0..(T : ℝ), H (t / T))) := by
      change evolutionOf G T T = _
      rw [heq ⟨hTr.le, le_rfl⟩]
      dsimp [U]
      rw [hphase, hexp]
    _ = E ((T : ℝ) / 3) := hexp

end RoundedClocks.UnitSharp
