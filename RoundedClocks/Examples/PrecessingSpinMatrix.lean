/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-! The matrix calculations in Example 5.2, manuscript lines 36–60. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix
open NormedSpace (exp)
local postfix:max "†" => Matrix.conjTranspose

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- The operator norm supplies the C-star algebra used for the exponential formula. -/
local instance : CStarAlgebra (Matrix (Fin 2) (Fin 2) ℂ) where

/-- Example 5.2's matrix X. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Example 5.2's matrix Z. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Hermitian involutions and anticommutation used in the displayed products. -/
theorem matrix_relations :
    X.IsHermitian ∧ Z.IsHermitian ∧ X * X = 1 ∧ Z * Z = 1 ∧ X * Z + Z * X = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X, Z, Matrix.IsHermitian, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Example 5.2's involution exponential, by functional calculus on the spectrum ±1. -/
theorem exp_involution (N : Matrix (Fin 2) (Fin 2) ℂ)
    (hN : N.IsHermitian) (hNN : N * N = 1) (a : ℝ) :
    exp ((-Complex.I * (a : ℂ)) • N) =
      (Real.cos a : ℂ) • 1 - (Complex.I * Real.sin a) • N := by
  have hnormal : IsStarNormal N := hN.isSelfAdjoint.isStarNormal
  have hspectrum (z : ℂ) (hz : z ∈ spectrum ℂ N) : z = 1 ∨ z = -1 := by
    have hs := spectrum.pow_mem_pow N 2 hz
    rw [pow_two, hNN, spectrum.one_eq, Set.mem_singleton_iff] at hs
    exact sq_eq_one_iff.mp hs
  rw [← CFC.complex_exp_eq_normedSpace_exp,
    ← cfc_comp_const_mul (-Complex.I * a) Complex.exp N
      Complex.continuous_exp.continuousOn]
  calc
    _ = cfc (fun z : ℂ ↦ (Real.cos a : ℂ) - (Complex.I * Real.sin a) * z) N := by
      apply cfc_congr
      intro z hz
      rcases hspectrum z hz with rfl | rfl
      · dsimp only
        rw [mul_one, show -Complex.I * (a : ℂ) = (-a : ℂ) * Complex.I by ring,
          Complex.exp_mul_I]
        simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin]
        ring
      · dsimp only
        rw [show (-Complex.I * (a : ℂ)) * (-1) = (a : ℂ) * Complex.I by ring,
          Complex.exp_mul_I]
        simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
        ring
    _ = _ := by
      rw [cfc_sub (fun _ : ℂ ↦ (Real.cos a : ℂ))
        (fun z : ℂ ↦ (Complex.I * Real.sin a) * z) N continuousOn_const
        (continuous_const.mul continuous_id).continuousOn,
        cfc_const _ N hnormal, cfc_const_mul_id _ N hnormal,
        Algebra.algebraMap_eq_smul_one]

/-- The stated reason for S = -iN: the quarter turn is (1-iX)/√2. -/
theorem quarter_turn_X :
    exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • X) =
      (Real.sqrt 2)⁻¹ • (1 - Complex.I • X) := by
  rw [exp_involution X matrix_relations.1 matrix_relations.2.2.1,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have hp : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
    exact Real.sq_sqrt (by norm_num)
  rw [hs]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv]
  ring

/-- Multiplying the three factors of S after the quarter-turn rewrite gives -iN. -/
theorem half_turn_step (epsilon : ℝ) :
    let E := exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • X)
    E * exp ((Complex.I * (epsilon : ℂ)) • Z) * E =
      (-Complex.I) • (Real.cos epsilon • X - Real.sin epsilon • Z) := by
  dsimp only
  rw [quarter_turn_X,
    show Complex.I * (epsilon : ℂ) = -Complex.I * ((-epsilon : ℝ) : ℂ) by
      push_cast; ring,
    exp_involution Z matrix_relations.2.1 matrix_relations.2.2.2.1,
    Real.cos_neg, Real.sin_neg]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [X, Z, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;>
    field_simp <;> ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_three, hs] <;> ring

/-- A real combination of X and Z is Hermitian, as in the third norm line. -/
theorem xz_hermitian (a b : ℝ) : (a • X + b • Z).IsHermitian := by
  exact ((show IsSelfAdjoint a from rfl).smul matrix_relations.1.isSelfAdjoint).add
    ((show IsSelfAdjoint b from rfl).smul matrix_relations.2.1.isSelfAdjoint)

/-- Anticommutation gives A² = (a²+b²)1 in the third norm line. -/
theorem xz_square (a b : ℝ) :
    (a • X + b • Z) * (a • X + b • Z) = (a ^ 2 + b ^ 2) • 1 := by
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [matrix_relations.2.2.1, matrix_relations.2.2.2.1]
  rw [show b * a = a * b by ring, add_assoc, ← add_assoc ((a * b) • (X * Z)),
    ← smul_add, matrix_relations.2.2.2.2, smul_zero, zero_add, ← add_smul]
  simp only [pow_two]

/-- The C-star norm identifies A² with ‖A‖²1 in the third norm line. -/
theorem xz_square_norm (a b : ℝ) :
    (a • X + b • Z) * (a • X + b • Z) = ‖a • X + b • Z‖ ^ 2 • 1 := by
  have hnorm := congrArg norm (xz_square a b)
  rw [(xz_hermitian a b).isSelfAdjoint.norm_mul_self, norm_smul, norm_one,
    mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hnorm
  rw [hnorm, xz_square]

/-- The mixed terms cancel in (A+is)†(A+is), exactly as below the norm display. -/
theorem imaginary_square (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (s : ℝ) :
    (A + (Complex.I * s) • 1)† * (A + (Complex.I * s) • 1) =
      A * A + (s ^ 2 : ℝ) • 1 := by
  have ha : star A = A := hA
  change star (A + (Complex.I * s) • 1) * (A + (Complex.I * s) • 1) = _
  simp only [star_add, star_smul, star_one, ha, Complex.star_def,
    map_mul, Complex.conj_I, Complex.conj_ofReal, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Example 5.2's third norm equality for the real combination A of X and Z. -/
theorem xz_imaginary_norm (a b s : ℝ) :
    let A := a • X + b • Z
    ‖A + (Complex.I * (s : ℂ)) • 1‖ = Real.sqrt (‖A‖ ^ 2 + s ^ 2) := by
  dsimp only
  have hnorm := congrArg norm (imaginary_square _ (xz_hermitian a b) s)
  change ‖star (a • X + b • Z + (Complex.I * s) • 1) *
    (a • X + b • Z + (Complex.I * s) • 1)‖ =
      ‖(a • X + b • Z) * (a • X + b • Z) + (s ^ 2 : ℝ) • 1‖ at hnorm
  rw [xz_square_norm, ← add_smul, CStarRing.norm_star_mul_self,
    norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hnorm
  rw [← hnorm, ← pow_two, Real.sqrt_sq (norm_nonneg _)]

end RoundedClocks.PrecessingSpin
