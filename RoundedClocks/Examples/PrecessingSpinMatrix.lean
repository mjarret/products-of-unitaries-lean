/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Example 5.2: the Pauli matrices `X` and `Z`

The matrix identities used in the proof of Example 5.2: the relations of `X` and `Z`,
`e^{-iaA} = cos a - i sin a A` for a Hermitian involution `A`, the step `S = -iN` at `ω = π`, and
`‖A + is‖² = ‖A‖² + s²` for a real combination `A` of `X` and `Z` and real `s`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Matrix
open NormedSpace (exp)

noncomputable section
namespace RoundedClocks.PrecessingSpin

attribute [local instance] matrixCStarAlgebra

/-- The Pauli matrix `X`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `Z = diag(1, -1)`. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The relations of the Pauli matrices `X` and `Z`, checked entry by entry. -/
private theorem pauli_relations :
    X.IsHermitian ∧ Z.IsHermitian ∧ X * X = 1 ∧ Z * Z = 1 ∧ X * Z + Z * X = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [X, Z, Matrix.IsHermitian, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `X` is Hermitian. -/
theorem X_isHermitian : X.IsHermitian := pauli_relations.1

/-- `Z` is Hermitian. -/
theorem Z_isHermitian : Z.IsHermitian := pauli_relations.2.1

/-- `X² = 1`. -/
theorem X_mul_X : X * X = 1 := pauli_relations.2.2.1

/-- `Z² = 1`. -/
theorem Z_mul_Z : Z * Z = 1 := pauli_relations.2.2.2.1

/-- `X` and `Z` anticommute: `XZ + ZX = 0`. -/
theorem X_mul_Z_add_Z_mul_X : X * Z + Z * X = 0 := pauli_relations.2.2.2.2

/-- For a Hermitian involution `A`, `e^{-iaA} = cos a - i sin a A`, by the functional calculus on
the spectrum `{1, -1}`. -/
theorem exp_involution (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hAA : A * A = 1) (a : ℝ) :
    exp ((-Complex.I * (a : ℂ)) • A) =
      (Real.cos a : ℂ) • 1 - (Complex.I * Real.sin a) • A := by
  have hnormal : IsStarNormal A := hA.isSelfAdjoint.isStarNormal
  have hspectrum (z : ℂ) (hz : z ∈ spectrum ℂ A) : z = 1 ∨ z = -1 := by
    have hs := spectrum.pow_mem_pow A 2 hz
    rw [pow_two, hAA, spectrum.one_eq, Set.mem_singleton_iff] at hs
    exact sq_eq_one_iff.mp hs
  rw [← CFC.complex_exp_eq_normedSpace_exp,
    ← cfc_comp_const_mul (-Complex.I * a) Complex.exp A
      Complex.continuous_exp.continuousOn]
  calc
    _ = cfc (fun z : ℂ ↦ (Real.cos a : ℂ) - (Complex.I * Real.sin a) * z) A := by
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
        (fun z : ℂ ↦ (Complex.I * Real.sin a) * z) A continuousOn_const
        (continuous_const.mul continuous_id).continuousOn,
        cfc_const _ A hnormal, cfc_const_mul_id _ A hnormal,
        Algebra.algebraMap_eq_smul_one]

/-- `e^{-iπX/4} = (1 - iX)/√2`. -/
theorem quarter_turn_X :
    exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • X) =
      (Real.sqrt 2)⁻¹ • (1 - Complex.I • X) := by
  rw [exp_involution X X_isHermitian X_mul_X,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := Real.sqrt_div_self
  rw [hs]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_inv]
  ring

/-- At `ω = π`, `S = -iN`: `e^{-iπX/4} e^{iεZ} e^{-iπX/4} = -i(cos ε X - sin ε Z)`, as
`e^{-iπX/4} = (1 - iX)/√2`. -/
theorem half_turn_step (epsilon : ℝ) :
    let E := exp ((-Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) • X)
    E * exp ((Complex.I * (epsilon : ℂ)) • Z) * E =
      (-Complex.I) • (Real.cos epsilon • X - Real.sin epsilon • Z) := by
  dsimp only
  rw [quarter_turn_X,
    show Complex.I * (epsilon : ℂ) = -Complex.I * ((-epsilon : ℝ) : ℂ) by
      push_cast; ring,
    exp_involution Z Z_isHermitian Z_mul_Z,
    Real.cos_neg, Real.sin_neg]
  rw [show ((-Real.sin epsilon : ℝ) : ℂ) = -(Real.sin epsilon : ℂ) by norm_num,
    mul_neg, neg_smul, sub_neg_eq_add]
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num), one_div]
  have hXZ : X * Z = -(Z * X) := eq_neg_of_add_eq_zero_left X_mul_Z_add_Z_mul_X
  have hXZX : X * Z * X = -Z := by
    rw [hXZ, neg_mul, mul_assoc, X_mul_X, mul_one]
  have hII : Complex.I * Complex.I = (-1 : ℂ) := by norm_num
  let B : Matrix (Fin 2) (Fin 2) ℂ :=
    (Real.cos epsilon : ℂ) • 1 + (Complex.I * Real.sin epsilon) • Z
  let C : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • X
  have hXBX : X * B * X =
      (Real.cos epsilon : ℂ) • 1 - (Complex.I * Real.sin epsilon) • Z := by
    simp only [B, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hXZX]
    rw [mul_one, X_mul_X]
    simp only [smul_neg, sub_eq_add_neg]
  have hBX : B * X + X * B = (2 * Real.cos epsilon : ℂ) • X := by
    simp only [B, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hXZ]
    module
  have hlast : C * B * C = -(X * B * X) := by
    simp only [C, smul_mul_assoc, mul_smul_comm, smul_smul, hII, neg_smul, one_smul,
      mul_assoc]
  have hcore :
      (1 - C) * B * (1 - C) =
        2 • ((-Complex.I) • (Real.cos epsilon • X - Real.sin epsilon • Z)) := by
    rw [show (1 - C) * B * (1 - C) =
      B - B * C - C * B + C * B * C by noncomm_ring,
      hlast]
    simp only [C, mul_smul_comm, smul_mul_assoc]
    rw [show B - Complex.I • (B * X) - Complex.I • (X * B) + -(X * B * X) =
      B - Complex.I • (B * X + X * B) - X * B * X by module]
    rw [hBX, hXBX]
    dsimp only [B]
    have hcos : Real.cos epsilon • X = (Real.cos epsilon : ℂ) • X := rfl
    have hsin : Real.sin epsilon • Z = (Real.sin epsilon : ℂ) • Z := rfl
    rw [hcos, hsin]
    module
  rw [show (Real.sqrt 2)⁻¹ • (1 - Complex.I • X) *
      ((Real.cos epsilon : ℂ) • 1 + (Complex.I * Real.sin epsilon) • Z) *
      ((Real.sqrt 2)⁻¹ • (1 - Complex.I • X)) =
      (1 / 2 : ℝ) •
        ((1 - C) * B * (1 - C)) by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
        rw [hr]]
  rw [hcore]
  module

/-- A real combination `aX + bZ` is Hermitian. -/
theorem xz_hermitian (a b : ℝ) : (a • X + b • Z).IsHermitian := by
  exact ((show IsSelfAdjoint a from rfl).smul X_isHermitian.isSelfAdjoint).add
    ((show IsSelfAdjoint b from rfl).smul Z_isHermitian.isSelfAdjoint)

/-- `(aX + bZ)² = a² + b²`, as `X` and `Z` anticommute. -/
theorem xz_square (a b : ℝ) :
    (a • X + b • Z) * (a • X + b • Z) = (a ^ 2 + b ^ 2) • 1 := by
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [X_mul_X, Z_mul_Z]
  rw [show b * a = a * b by ring, add_assoc, ← add_assoc ((a * b) • (X * Z)),
    ← smul_add, X_mul_Z_add_Z_mul_X, smul_zero, zero_add, ← add_smul]
  simp only [pow_two]

/-- `A² = ‖A‖²` for a real combination `A = aX + bZ`. -/
theorem xz_square_norm (a b : ℝ) :
    (a • X + b • Z) * (a • X + b • Z) = ‖a • X + b • Z‖ ^ 2 • 1 := by
  have hnorm := congrArg norm (xz_square a b)
  rw [(xz_hermitian a b).isSelfAdjoint.norm_mul_self, norm_smul, norm_one,
    mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hnorm
  rw [hnorm, xz_square]

/-- `(A + is)†(A + is) = A² + s²` for Hermitian `A` and real `s`. -/
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

/-- Line 3 of the display in (i) uses `‖A + is‖ = (‖A‖² + s²)^{1/2}` for a real combination
`A = aX + bZ` and real `s`. -/
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
