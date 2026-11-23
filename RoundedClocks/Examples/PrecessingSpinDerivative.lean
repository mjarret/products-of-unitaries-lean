/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinMatrix

/-! The Hamiltonian derivative norm in the fourth display of Example 5.2. -/

@[expose] public section

open NormedSpace (exp)
open Complex (I)
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction for the rotating frame exponential. -/
local instance derivativeNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- The rotating-frame generator is skew-adjoint, so its exponential is unitary. -/
theorem derivative_frame_unitary (θ s : ℝ) :
    exp (s • (-(θ / 2 * I) • Z)) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  change star (s • (-(θ / 2 * I) • Z)) = -(s • (-(θ / 2 * I) • Z))
  rw [star_smul, star_smul, show star Z = Z from matrix_relations.2.1]
  simp only [star_trivial, Complex.star_def, map_neg, map_mul, map_div₀,
    Complex.conj_ofReal, map_ofNat, Complex.conj_I, mul_neg, neg_neg, neg_smul,
    smul_neg]

/-- Differentiating the conjugated X gives the commutator in the rotating frame. -/
theorem conjugated_X_derivative (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ exp (t • A) * X * exp (t • (-A)))
      (exp (s • A) * (A * X - X * A) * exp (s • (-A))) s := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) A s).mul_const X).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s)
  convert h using 1
  noncomm_ring

/-- The Pauli anticommutator makes the rotating-frame derivative have norm |θ|. -/
theorem frame_commutator_norm (θ : ℝ) :
    ‖(-(θ / 2 * I) • Z) * X - X * (-(θ / 2 * I) • Z)‖ = |θ| := by
  have hXZ : X * Z = -(Z * X) := eq_neg_of_add_eq_zero_left matrix_relations.2.2.2.2
  have he : (-(θ / 2 * I) • Z) * X - X * (-(θ / 2 * I) • Z) =
      (-(θ * I)) • (Z * X) := by
    rw [smul_mul_assoc, mul_smul_comm, hXZ, smul_neg, sub_neg_eq_add, ← add_smul]
    congr 1
    ring
  have hX : ‖X‖ = 1 := by
    have h := congrArg norm matrix_relations.2.2.1
    rw [matrix_relations.1.isSelfAdjoint.norm_mul_self, norm_one] at h
    exact (sq_eq_sq₀ (norm_nonneg X) zero_le_one).mp (by simpa using h)
  have hZ : Z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Unitary.mem_iff]
    change star Z * Z = 1 ∧ Z * star Z = 1
    rw [show star Z = Z from matrix_relations.2.1]
    exact ⟨matrix_relations.2.2.2.1, matrix_relations.2.2.2.1⟩
  have hc : ‖-((θ : ℂ) * I)‖ = |θ| := by
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  calc
    _ = ‖-((θ : ℂ) * I)‖ * ‖Z * X‖ := by rw [he, norm_smul]
    _ = |θ| := by rw [hc, CStarRing.norm_mem_unitary_mul X hZ, hX, mul_one]

/-- Example 5.2's derivative norm, including the one-sided endpoint derivatives. -/
theorem hamiltonian_derivWithin_norm {ω : ℝ} (hω : 0 ≤ ω) (θ : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let H := fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * t / 2 * I) • Z) * X * exp ((θ * t / 2 * I) • Z))
    ‖derivWithin H (Set.Icc (0 : ℝ) 1) s‖ = ω * |θ| / 2 := by
  intro H
  let A := -(θ / 2 * I) • Z
  have hH : H = fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (t • A) * X * exp (t • (-A))) := by
    funext t
    have hl : -(θ * t / 2 * I) • Z = t • A := by
      rw [show t • A = ((t : ℂ) * -(θ / 2 * I)) • Z by
        ext i j
        simp only [A, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
        ring]
      congr 1
      ring
    have hr : (θ * t / 2 * I) • Z = t • (-A) := by
      rw [smul_neg, ← hl, ← neg_smul]
      congr 1
      ring
    change (ω / 2 : ℝ) • (exp _ * X * exp _) = _
    rw [hl, hr]
  rw [hH]
  have hd : HasDerivAt (fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (t • A) * X * exp (t • (-A))))
      ((ω / 2 : ℝ) • (exp (s • A) * (A * X - X * A) * exp (s • (-A)))) s :=
    (conjugated_X_derivative A s).const_smul (ω / 2 : ℝ)
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs), norm_smul]
  have hright : exp (s • (-A)) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [smul_neg, ← neg_smul]
    exact derivative_frame_unitary θ (-s)
  rw [CStarRing.norm_mul_mem_unitary _ hright,
    CStarRing.norm_mem_unitary_mul _ (derivative_frame_unitary θ s), frame_commutator_norm,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hω (by norm_num))]
  ring

end RoundedClocks.PrecessingSpin
