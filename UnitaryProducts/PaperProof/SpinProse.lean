/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.PrecessingSpin

/-! # Commutation criterion for the sampled precessing spin. -/

@[expose] public section
open scoped Matrix.Norms.L2Operator
open Complex Real Matrix
open UnitaryProducts UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof.Spin
attribute [local instance] matrixCStarAlgebra

/-- Consecutive equatorial axes have commutator proportional to the sine of
how far the axis advances, as used after Example 5.2. -/
theorem axis_commutator (a b : ℝ) :
    axis a * axis b - axis b * axis a = (2 * I * Real.sin (b - a) : ℂ) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axis, X, Y, Z, Real.sin_sub] <;> ring

/-- Two sampled half-turns commute exactly when the sine of their axis
separation vanishes. Multiplying both axes by `-i` does not change this condition. -/
theorem half_turn_commute_iff (a b : ℝ) :
    Commute ((-I) • axis a) ((-I) • axis b) ↔ Real.sin (b - a) = 0 := by
  change ((-I) • axis a) * ((-I) • axis b) = ((-I) • axis b) * ((-I) • axis a) ↔ _
  rw [← sub_eq_zero]
  have he : ((-I) • axis a) * ((-I) • axis b) -
      ((-I) • axis b) * ((-I) • axis a) = -(axis a * axis b - axis b * axis a) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul_neg, Complex.I_mul_I,
      neg_one_smul, neg_sub_neg]
    abel
  rw [he, neg_eq_zero, axis_commutator, smul_eq_zero]
  have hz : Z ≠ 0 := by
    intro hh
    have hh' := congrArg norm hh
    rw [norm_Z, norm_zero] at hh'
    norm_num at hh'
  simp [hz, mul_eq_zero, Complex.I_ne_zero, -Complex.ofReal_sin]

/-- At width π every sample is the half-turn about its equatorial field axis. -/
theorem half_turn_factor (θ s : ℝ) :
    evol (family π θ s) 1 = (-I) • axis (θ * s) := by
  rw [family, Prose.localSteps_evol_smul_sharp,
    evol_involution (axis_relations _).1 (axis_relations _).2]
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Consecutive sampled half-turns fail to commute unless the sine of the
angular increment vanishes, exactly as stated after Example 5.2. -/
theorem consecutive_half_turns_commute_iff (θ : ℝ) (T j : ℕ) :
    Commute (evol (family π θ (j / T)) 1)
      (evol (family π θ ((j + 1) / T)) 1) ↔ Real.sin (θ / T) = 0 := by
  rw [half_turn_factor, half_turn_factor, half_turn_commute_iff]
  rw [show θ * (((j : ℝ) + 1) / (T : ℝ)) - θ * ((j : ℝ) / (T : ℝ)) =
    θ / (T : ℝ) by ring]

end UnitaryProducts.PaperProof.Spin
