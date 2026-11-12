/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.UnitExamples
public import UnitaryProducts.Walks.LogarithmBranch
public import UnitaryProducts.PaperProof.OddResonance

/-! # Exact computations for the precessing spin of Example 5.2. -/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Real Set Matrix Filter MeasureTheory Asymptotics
open UnitaryProducts UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof.Spin

attribute [local instance] matrixCStarAlgebra

/-- The three Pauli matrices used throughout Section 5. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- The second Pauli matrix. -/
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
/-- The third Pauli matrix. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli matrices are Hermitian involutions. -/
theorem pauli_relations :
    X.IsHermitian ∧ Y.IsHermitian ∧ Z.IsHermitian ∧
    X * X = 1 ∧ Y * Y = 1 ∧ Z * Z = 1 ∧
    X * Z + Z * X = 0 ∧ X * Z * X = -Z := by
  repeat' constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    simp [X, Y, Z, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_I]

/-- The elementary exponential formula used in the inline identity of Example 5.2.
The spectral mapping theorem reduces the calculation to the scalar values ±1. -/
theorem evol_involution {d : ℕ} [NeZero d]
    {N : Matrix (Fin d) (Fin d) ℂ} (hN : N.IsHermitian) (hNN : N * N = 1)
    (a : ℝ) :
    evol N a = (Real.cos a : ℂ) • 1 - (I * Real.sin a) • N := by
  have hnormal : IsStarNormal N := hN.isSelfAdjoint.isStarNormal
  have hspectrum (z : ℂ) (hz : z ∈ spectrum ℂ N) : z = 1 ∨ z = -1 := by
    have hs := spectrum.pow_mem_pow N 2 hz
    rw [pow_two, hNN, spectrum.one_eq, Set.mem_singleton_iff] at hs
    exact sq_eq_one_iff.mp hs
  have he : evol N a = cfc (fun z : ℂ ↦ Complex.exp ((-I * a) * z)) N := by
    rw [cfc_comp_const_mul (-I * a) Complex.exp N Complex.continuous_exp.continuousOn,
      CFC.complex_exp_eq_normedSpace_exp]
    unfold evol
    congr 1
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    ring
  rw [he]
  calc
    _ = cfc (fun z : ℂ ↦ (Real.cos a : ℂ) - (I * Real.sin a) * z) N := by
      apply cfc_congr
      intro z hz
      rcases hspectrum z hz with rfl | rfl
      · dsimp only
        rw [mul_one, show -I * (a : ℂ) = (-a : ℂ) * I by ring,
          Complex.exp_mul_I]
        simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin]
        ring
      · dsimp only
        rw [show (-I * (a : ℂ)) * (-1) = (a : ℂ) * I by ring, Complex.exp_mul_I]
        simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
        ring
    _ = _ := by
      rw [cfc_sub (fun _ : ℂ ↦ (Real.cos a : ℂ))
        (fun z : ℂ ↦ (I * Real.sin a) * z) N continuousOn_const
        (continuous_const.mul continuous_id).continuousOn,
        cfc_const _ N hnormal, cfc_const_mul_id _ N hnormal, Algebra.algebraMap_eq_smul_one]

/-- The inline identity of Example 5.2: the squared difference of two spin rotations is scalar.
This is the paper's anticommutator calculation, before taking the norm. -/
theorem spin_distance_matrix {d : ℕ} [NeZero d]
    {N M : Matrix (Fin d) (Fin d) ℂ}
    (hN : N.IsHermitian) (hM : M.IsHermitian)
    (hNN : N * N = 1) (hMM : M * M = 1)
    (φ : ℝ) (hNM : N * M + M * N = (2 * Real.cos φ : ℂ) • 1)
    (a b : ℝ) :
    star (evol N a - evol M b) * (evol N a - evol M b) =
      ((2 - 2 * Real.cos a * Real.cos b -
        2 * Real.sin a * Real.sin b * Real.cos φ : ℝ) : ℂ) • 1 := by
  have hn : star N = N := hN
  have hm : star M = M := hM
  rw [evol_involution hN hNN, evol_involution hM hMM]
  simp only [star_sub, star_smul, star_one, hn, hm, Complex.star_def,
    map_mul, Complex.conj_I, Complex.conj_ofReal, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hNN, hMM]
  have ha : (Real.cos a : ℂ) ^ 2 + (Real.sin a : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq a
  have hb : (Real.cos b : ℂ) ^ 2 + (Real.sin b : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq b
  push_cast
  ext i j
  have hnm := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ ↦ A i j) hNM
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hnm ⊢
  ring_nf
  simp only [Complex.I_sq]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at ha hb hnm
  linear_combination (1 : Matrix (Fin d) (Fin d) ℂ) i j * ha +
    (1 : Matrix (Fin d) (Fin d) ℂ) i j * hb -
    (Complex.sin (a : ℂ) * Complex.sin (b : ℂ)) * hnm

/-- The inline squared operator-norm identity in the proof of Example 5.2. -/
theorem spin_distance {d : ℕ} [NeZero d]
    {N M : Matrix (Fin d) (Fin d) ℂ}
    (hN : N.IsHermitian) (hM : M.IsHermitian)
    (hNN : N * N = 1) (hMM : M * M = 1)
    (φ : ℝ) (hNM : N * M + M * N = (2 * Real.cos φ : ℂ) • 1)
    (a b : ℝ) :
    ‖evol N a - evol M b‖ ^ 2 =
      2 - 2 * Real.cos a * Real.cos b - 2 * Real.sin a * Real.sin b * Real.cos φ := by
  let r := 2 - 2 * Real.cos a * Real.cos b -
    2 * Real.sin a * Real.sin b * Real.cos φ
  have he := spin_distance_matrix hN hM hNN hMM φ hNM a b
  have hpos : 0 ≤ ((star (evol N a - evol M b) * (evol N a - evol M b)) 0 0).re := by
    change 0 ≤ (∑ k, star ((evol N a - evol M b) k 0) *
      (evol N a - evol M b) k 0).re
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro k _
    simp only [Complex.star_def, mul_comm ((starRingEnd ℂ) _), Complex.mul_conj,
      Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  rw [he] at hpos
  have hr : 0 ≤ r := by simpa [r] using hpos
  have hn := congrArg norm he
  rw [CStarRing.norm_star_mul_self, norm_smul, norm_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hn
  simpa only [pow_two] using hn

/-- For a traceless two-dimensional matrix, determinant `-r²` identifies
exactly the two eigenvalues, including their coincidence when `r=0`. -/
theorem spectrum_pair_of_trace_det (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ)
    (ht : Matrix.trace A = 0) (hd : Matrix.det A = -r ^ 2) :
    spectrum ℂ A = {r, -r} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fin_two, ht, hd]
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
    zero_mul, sub_zero, ← sub_eq_add_neg, sub_eq_zero,
    Set.mem_insert_iff, Set.mem_singleton_iff, sq_eq_sq_iff_eq_or_eq_neg]

/-- Spectral mapping for a Hermitian matrix exponential, instantiated directly
from Mathlib's continuous functional calculus spectral-mapping theorem. -/
theorem evol_spectrum {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (t : ℝ) :
    spectrum ℂ (evol H t) = (fun z : ℂ ↦ Complex.exp ((-I * t) * z)) '' spectrum ℂ H := by
  have hn : IsStarNormal H := hH.isSelfAdjoint.isStarNormal
  have he : evol H t = cfc (fun z : ℂ ↦ Complex.exp ((-I * t) * z)) H := by
    rw [cfc_comp_const_mul (-I * t) Complex.exp H Complex.continuous_exp.continuousOn,
      CFC.complex_exp_eq_normedSpace_exp]
    unfold evol
    congr 1
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    ring
  rw [he]
  exact cfc_map_spectrum (fun z : ℂ ↦ Complex.exp ((-I * t) * z)) H hn
    ((continuous_const.mul continuous_id).cexp.continuousOn)

/-- A Pauli axis in the equatorial plane. -/
def axis (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos φ : ℂ) • X + (Real.sin φ : ℂ) • Y

/-- Every equatorial Pauli combination is a Hermitian involution. -/
theorem axis_relations (φ : ℝ) : (axis φ).IsHermitian ∧ axis φ * axis φ = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [axis, X, Y, Matrix.conjTranspose_apply, Complex.conj_I,
        -Complex.ofReal_cos, -Complex.ofReal_sin]
  · have htrig := Complex.cos_sq_add_sin_sq (φ : ℂ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [axis, X, Y, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals linear_combination htrig - Complex.sin (φ : ℂ) ^ 2 * Complex.I_sq

/-- Conjugation by the rotating frame rotates the equatorial Pauli axis. -/
theorem pauli_conj (φ : ℝ) :
    evol Z (φ / 2) * X * evol Z (-(φ / 2)) = axis φ := by
  rw [evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1,
    evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
  have hc : Real.cos φ = 2 * Real.cos (φ / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (φ / 2) using 1
    congr 1
    ring
  have hs : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    convert Real.sin_two_mul (φ / 2) using 1
    congr 1
    ring
  have ht : (Real.cos (φ / 2) : ℂ) ^ 2 + (Real.sin (φ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (φ / 2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axis, X, Y, Z, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg,
      Real.sin_neg, hc, hs, -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals ring_nf at ht ⊢
  all_goals simp only [Complex.I_sq]
  all_goals linear_combination -ht

/-- The symmetric step in the rotating frame. -/
def step (ω ε : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  evol X (ω / 4) * evol Z (-ε) * evol X (ω / 4)

/-- Multiplying out the three factors gives the axis formula in the
paragraph following Example 5.2. -/
theorem step_closed (ω ε : ℝ) :
    step ω ε = (Real.cos (ω / 2) * Real.cos ε : ℂ) • 1 -
      I • ((Real.sin (ω / 2) * Real.cos ε : ℂ) • X - (Real.sin ε : ℂ) • Z) := by
  unfold step
  rw [evol_involution pauli_relations.1 pauli_relations.2.2.2.1,
    evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
  have hc : Real.cos (ω / 2) = 2 * Real.cos (ω / 4) ^ 2 - 1 := by
    convert Real.cos_two_mul (ω / 4) using 1
    congr 1
    ring
  have hs : Real.sin (ω / 2) = 2 * Real.sin (ω / 4) * Real.cos (ω / 4) := by
    convert Real.sin_two_mul (ω / 4) using 1
    congr 1
    ring
  have ht : (Real.cos (ω / 4) : ℂ) ^ 2 + (Real.sin (ω / 4) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (ω / 4)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, Z, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg,
      Real.sin_neg, hc, hs, -Complex.ofReal_cos, -Complex.ofReal_sin]
  all_goals ring_nf at ht ⊢
  all_goals simp only [Complex.I_sq, show (I : ℂ) ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
  all_goals first
    | linear_combination (- (Real.cos ε : ℂ) + I * Real.sin ε) * ht
    | linear_combination (- (Real.cos ε : ℂ) - I * Real.sin ε) * ht

/-- The Hamiltonian in Example 5.2. -/
def family (ω θ s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (ω / 2 : ℝ) • axis (θ * s)

/-- Every sample of the precessing-spin Hamiltonian has precisely the
paper's eigenvalues `±ω/2`; at `ω=2π` these are `±π`. -/
theorem family_spectrum (ω θ s : ℝ) :
    spectrum ℂ (family ω θ s) = {((ω / 2 : ℝ) : ℂ), -((ω / 2 : ℝ) : ℂ)} := by
  apply spectrum_pair_of_trace_det
  · simp [Matrix.trace, family, axis, X, Y, Fin.sum_univ_two]
  · have htrig : (Real.cos (θ * s) : ℂ) ^ 2 + (Real.sin (θ * s) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq (θ * s)
    simp [family, axis, X, Y, Matrix.det_fin_two, Complex.real_smul]
    ring_nf
    simp only [Complex.I_sq]
    push_cast at htrig ⊢
    linear_combination ((ω : ℂ) ^ 2 / 4) * htrig

/-- Hermiticity of the precessing-spin Hamiltonian. -/
theorem family_hermitian (ω θ s : ℝ) : (family ω θ s).IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.mpr
    ((show IsSelfAdjoint (ω / 2 : ℝ) from rfl).smul (axis_relations _).1.isSelfAdjoint)

/-- Exponentiating the rotated Pauli axis commutes with the rotating frame. -/
theorem evol_axis (φ a : ℝ) :
    evol (axis φ) a = evol Z (φ / 2) * evol X a * evol Z (-(φ / 2)) := by
  have hcancel : evol Z (φ / 2) * evol Z (-(φ / 2)) = 1 := by
    rw [← evol_add, add_neg_cancel, evol_zero]
  rw [evol_involution (axis_relations φ).1 (axis_relations φ).2,
    evol_involution pauli_relations.1 pauli_relations.2.2.2.1]
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    hcancel, mul_smul_comm, smul_mul_assoc, pauli_conj]

/-- Each sampled exponential is the conjugate of the constant-axis exponential. -/
theorem evol_family (ω θ s a : ℝ) :
    evol (family ω θ s) a = evol Z (θ * s / 2) * evol X (a * (ω / 2)) *
      evol Z (-(θ * s / 2)) := by
  rw [family, Prose.localSteps_evol_smul_sharp, evol_axis]

/-- The rotating-frame telescoping identity for an arbitrary number of samples. -/
theorem sampled_product (ω θ : ℝ) (T n : ℕ) :
    pieceProduct (fun _ ↦ 1) (fun j ↦ family ω θ ((j : ℝ) / T)) n =
      evol Z (n * (θ / (2 * T))) *
        (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) ^ n := by
  induction n with
  | zero => simp [pieceProduct, evol_zero]
  | succ n ih =>
    have hang : θ * ((n : ℝ) / T) / 2 = n * (θ / (2 * T)) := by ring
    have hcancel : evol Z (-(n * (θ / (2 * T)))) *
        evol Z (n * (θ / (2 * T))) = 1 := by
      rw [← evol_add, neg_add_cancel, evol_zero]
    have hjoin : evol Z ((n + 1 : ℕ) * (θ / (2 * T))) * evol Z (-(θ / (2 * T))) =
        evol Z (n * (θ / (2 * T))) := by
      rw [← evol_add]
      congr 1
      push_cast
      ring
    rw [pieceProduct, evol_family, one_mul, hang, ih, pow_succ']
    simp only [mul_assoc]
    rw [← mul_assoc (evol Z (-(n * (θ / (2 * T))))), hcancel, one_mul]
    rw [← mul_assoc (evol Z ((n + 1 : ℕ) * (θ / (2 * T)))), hjoin]

/-- The closed form of the unit-step product in the opening computation
of Example 5.2. -/
theorem unit_product_closed (ω θ : ℝ) {T : ℕ} (hT : 0 < T) :
    (unitProduct (family ω θ) T).1 = evol Z (θ / 2) *
      (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) ^ T := by
  rw [unitProduct, sampled_product]
  have htr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  field_simp

/-- The half-step phases symmetrize the factor in the rotating frame,
giving the second closed form of the opening computation of Example 5.2. -/
theorem rounded_product_closed (ω θ : ℝ) {T : ℕ} (hT : 0 < T) :
    evol (family ω θ 1) (1 / 2) * (unitProduct (family ω θ) T).1 *
      evol (family ω θ 0) (-(1 / 2)) =
        evol Z (θ / 2) * step ω (θ / (2 * T)) ^ T := by
  let A := evol X (ω / 4)
  let B := evol X (-(ω / 4))
  have hab : A * B = 1 := by dsimp [A, B]; rw [← evol_add, add_neg_cancel, evol_zero]
  have hba : B * A = 1 := by dsimp [A, B]; rw [← evol_add, neg_add_cancel, evol_zero]
  let u : (Matrix (Fin 2) (Fin 2) ℂ)ˣ := ⟨A, B, hab, hba⟩
  have hX : evol X (ω / 2) = A * A := by
    dsimp [A]
    rw [← evol_add]
    congr 1
    ring
  have hconj : A * (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) * B =
      step ω (θ / (2 * T)) := by
    rw [hX]
    dsimp only [step, A] at *
    simp only [mul_assoc]
    rw [← mul_assoc (evol X (ω / 4)), hab, mul_one, mul_assoc]
  have hpow := u.conj_pow (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) T
  change (A * (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) * B) ^ T =
    A * (evol Z (-(θ / (2 * T))) * evol X (ω / 2)) ^ T * B at hpow
  rw [hconj] at hpow
  rw [evol_family, evol_family, unit_product_closed ω θ hT]
  simp only [mul_one, mul_zero, zero_div, neg_zero, evol_zero, one_mul]
  rw [show (1 / 2 : ℝ) * (ω / 2) = ω / 4 by ring,
    show -(1 / 2 : ℝ) * (ω / 2) = -(ω / 4) by ring]
  have hz : evol Z (-(θ / 2)) * evol Z (θ / 2) = 1 := by
    rw [← evol_add, neg_add_cancel, evol_zero]
  simp only [mul_assoc]
  rw [← mul_assoc (evol Z (-(θ / 2))), hz, one_mul]
  rw [hpow]
  simp only [A, B, mul_assoc]

/-- The sampled full-turn exponential is scalar because both spectral phases are -1. -/
theorem full_turn_factor (θ s : ℝ) :
    evol (family (2 * π) θ s) 1 = -1 := by
  have hH := family_hermitian (2 * π) θ s
  have hn := isStarNormal_of_mem_unitary (evol_mem_unitary hH 1)
  have hm : Complex.exp (-I * (π : ℂ)) = -1 := by
    rw [show -I * (π : ℂ) = ((-π : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_mul_I]
    simp
  have hp : Complex.exp (I * (π : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hspec : spectrum ℂ (evol (family (2 * π) θ s) 1) = {(-1 : ℂ)} := by
    rw [evol_spectrum _ hH, family_spectrum, Set.image_pair]
    norm_num only [Complex.ofReal_one, mul_one,
      show (2 * π / 2 : ℝ) = π by ring]
    rw [hm, show (-I) * (-(π : ℂ)) = I * (π : ℂ) by ring, hp]
    simp
  have hh := CFC.eq_algebraMap_of_spectrum_subset_singleton
    (evol (family (2 * π) θ s) 1) (-1 : ℂ) hspec.subset hn
  simpa using hh
/-- The rotating-frame solution appearing in the opening computation of Example 5.2. -/
def solution (ω θ T t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  evol Z (θ / (2 * T) * t) * evol ((ω / 2) • X - (θ / (2 * T)) • Z) t

/-- Direct differentiation verifies the rotating-frame Schrödinger equation. -/
theorem solution_derivative (ω θ T t : ℝ) :
    HasDerivAt (solution ω θ T)
      (-I • (family ω θ (t / T) * solution ω θ T t)) t := by
  let k := θ / (2 * T)
  let R := evol Z (k * t)
  let G := (ω / 2) • X - k • Z
  let E := evol G t
  have hRZ : Z * R = R * Z := (commute_evol_right (Commute.refl Z) (k * t)).eq
  have hcancel : evol Z (-(k * t)) * R = 1 := by
    dsimp [R]
    rw [← evol_add, neg_add_cancel, evol_zero]
  have hHR : family ω θ (t / T) * R = R * ((ω / 2) • X) := by
    have hang : θ * (t / T) / 2 = k * t := by dsimp [k]; ring
    rw [family, ← pauli_conj, hang]
    simp only [smul_mul_assoc, mul_assoc]
    rw [hcancel, mul_one, mul_smul_comm]
  have hRd : HasDerivAt (fun x : ℝ ↦ evol Z (k * x))
      (k • ((-I • Z) * R)) t := by
    simpa only [mul_one] using (hasDerivAt_evol Z (k * t)).scomp t
      ((hasDerivAt_id t).const_mul k)
  have hd := hRd.mul (hasDerivAt_evol G t)
  change HasDerivAt (solution ω θ T)
    (k • ((-I • Z) * R) * E + R * ((-I • G) * E)) t at hd
  convert hd using 1
  change -I • (family ω θ (t / T) * (R * E)) =
    k • ((-I • Z) * R) * E + R * ((-I • G) * E)
  rw [← mul_assoc, hHR]
  dsimp only [G]
  simp only [smul_sub, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc]
  rw [hRZ]
  module

/-- The continuous evolution has the first closed form in the opening computation of Example 5.2. -/
theorem evolution_closed (ω θ : ℝ) {T : ℕ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ family ω θ (t / T)) U 0 T) :
    U T = evol Z (θ / 2) * evol (((ω * T : ℝ) • X) - θ • Z) (1 / 2) := by
  obtain ⟨hUc, hU0, _, S, hS, hUd⟩ := hU
  have hsolc : Continuous (solution ω θ T) :=
    continuous_iff_continuousAt.mpr fun t ↦ (solution_derivative ω θ T t).continuousAt
  have hsol0 : solution ω θ T 0 = 1 := by simp [solution, evol_zero]
  have heq := evolution_eq_of_solves_off_countable S ∅ hS Set.countable_empty
    (fun t _ ↦ family_hermitian ω θ (t / T)) hUc hsolc.continuousOn hU0 hsol0
    (fun t ht hn ↦ hUd t ⟨ht.1.le, ht.2.le⟩ hn)
    (fun t _ _ ↦ (solution_derivative ω θ T t).hasDerivWithinAt)
  rw [heq (by exact ⟨Nat.cast_nonneg T, le_rfl⟩)]
  unfold solution
  have htr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hang : θ / (2 * T) * T = θ / 2 := by field_simp
  rw [hang]
  congr 1
  have hgen : (T : ℝ) • ((ω / 2) • X - (θ / (2 * T)) • Z) =
      (1 / 2 : ℝ) • ((ω * T) • X - θ • Z) := by
    simp only [smul_sub, smul_smul]
    rw [show (T : ℝ) * (ω / 2) = 1 / 2 * (ω * T) by ring,
      show (T : ℝ) * (θ / (2 * T)) = 1 / 2 * θ by field_simp]
  unfold evol
  rw [smul_comm (T : ℝ) (-I), smul_comm (1 / 2 : ℝ) (-I), hgen]

/-- A real combination of the first and third Pauli matrices. -/
def xz (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := a • X + b • Z

/-- Orthogonal Pauli axes give the Euclidean squared length. -/
theorem xz_relations (a b : ℝ) : (xz a b).IsHermitian ∧
    xz a b * xz a b = (a ^ 2 + b ^ 2 : ℝ) • 1 := by
  constructor
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (((show IsSelfAdjoint a from rfl).smul pauli_relations.1.isSelfAdjoint).add
        ((show IsSelfAdjoint b from rfl).smul pauli_relations.2.2.1.isSelfAdjoint))
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xz, X, Z, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

/-- The continuous rotating-frame generator has eigenvalues equal to the
positive and negative length of its Pauli coefficient vector. -/
theorem xz_spectrum (a b : ℝ) :
    spectrum ℂ (xz a b) =
      {((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ), -((Real.sqrt (a ^ 2 + b ^ 2) : ℝ) : ℂ)} := by
  apply spectrum_pair_of_trace_det
  · simp [Matrix.trace, xz, X, Z, Fin.sum_univ_two]
  · have hr : (Real.sqrt (a ^ 2 + b ^ 2) : ℂ) ^ 2 = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
      exact_mod_cast Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
    simp [xz, X, Z, Matrix.det_fin_two, Complex.real_smul]
    linear_combination hr

/-- The frozen frame exponential has exactly the two scalar phases used in
the proof of Example 5.2(ii), with `ρ=√(a²+b²)/2`. -/
theorem xz_evol_spectrum (a b : ℝ) :
    spectrum ℂ (evol (xz a b) (1 / 2)) =
      {Complex.exp (-I * ((Real.sqrt (a ^ 2 + b ^ 2) / 2 : ℝ) : ℂ)),
        Complex.exp (I * ((Real.sqrt (a ^ 2 + b ^ 2) / 2 : ℝ) : ℂ))} := by
  rw [evol_spectrum _ (xz_relations a b).1, xz_spectrum, Set.image_pair]
  congr 2 <;> push_cast <;> ring

/-- The exact `e^{∓iρ′}` eigenvalue assertion in the full-turn proof,
where `ρ′=√(4π²T²+θ²)/2`. -/
theorem full_turn_frozen_spectrum (θ : ℝ) (T : ℕ) :
    spectrum ℂ (evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)) =
      {Complex.exp (-I * ((Real.sqrt (4 * π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 : ℝ) : ℂ)),
        Complex.exp (I * ((Real.sqrt (4 * π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 : ℝ) : ℂ))} := by
  have hgen : ((2 * π * T : ℝ) • X) - θ • Z = xz (2 * π * T) (-θ) := by
    simp only [xz, neg_smul, sub_eq_add_neg]
  rw [hgen, xz_evol_spectrum]
  have hrad : (2 * π * (T : ℝ)) ^ 2 + (-θ) ^ 2 = 4 * π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2 := by ring
  rw [hrad]

/-- Normalizing a nonzero real Pauli combination gives a Hermitian involution. -/
theorem xz_normalized {a b : ℝ} (h : 0 < a ^ 2 + b ^ 2) :
    let N := (Real.sqrt (a ^ 2 + b ^ 2))⁻¹ • xz a b
    N.IsHermitian ∧ N * N = 1 := by
  intro N
  have hr : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  constructor
  · exact Matrix.isHermitian_iff_isSelfAdjoint.mpr
      ((show IsSelfAdjoint ((Real.sqrt (a ^ 2 + b ^ 2))⁻¹) from rfl).smul
        (xz_relations a b).1.isSelfAdjoint)
  · dsimp [N]
    rw [smul_mul_assoc, mul_smul_comm, (xz_relations a b).2, smul_smul, smul_smul]
    rw [show (Real.sqrt (a ^ 2 + b ^ 2))⁻¹ *
        (Real.sqrt (a ^ 2 + b ^ 2))⁻¹ * (a ^ 2 + b ^ 2) = 1 by
      field_simp
      exact (Real.sq_sqrt h.le).symm]
    exact one_smul ℝ _

/-- The distance between two rotations about one involutive axis. -/
theorem involution_distance {d : ℕ} [NeZero d]
    {N : Matrix (Fin d) (Fin d) ℂ} (hN : N.IsHermitian) (hNN : N * N = 1)
    (a b : ℝ) : ‖evol N a - evol N b‖ = 2 * |Real.sin ((a - b) / 2)| := by
  have hanti : N * N + N * N = (2 * Real.cos (0 : ℝ) : ℂ) • 1 := by
    rw [hNN, Real.cos_zero]
    module
  have he := spin_distance hN hN hNN hNN 0 hanti a b
  rw [Real.cos_zero, mul_one] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [he, mul_pow, sq_abs]
  have hc := Real.cos_sub a b
  have hh := Real.cos_two_mul ((a - b) / 2)
  rw [show 2 * ((a - b) / 2) = a - b by ring] at hh
  have ht := Real.cos_sq_add_sin_sq ((a - b) / 2)
  linear_combination 2 * hc - 2 * hh - 4 * ht

/-- The symmetric step at the full-turn width reverses the frame rotation. -/
theorem full_turn_step (ε : ℝ) : step (2 * π) ε = -evol Z ε := by
  rw [step_closed, show 2 * π / 2 = π by ring, Real.cos_pi, Real.sin_pi,
    evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
  module

/-- Repeated frozen evolution adds its times, the special case of
`NormedSpace.exp_nsmul` used for the spin products. -/
theorem evol_nat_mul {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a : ℝ) (T : ℕ) :
    evol N ((T : ℝ) * a) = (evol N a) ^ T := by
  induction T with
  | zero => simp [evol_zero]
  | succ T ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, evol_add, ih, pow_succ]

/-- The rounded full-turn product is the scalar sign times twice the frame rotation. -/
theorem full_turn_product (θ : ℝ) {T : ℕ} (hT : 0 < T) :
    evol (family (2 * π) θ 1) (1 / 2) * (unitProduct (family (2 * π) θ) T).1 *
      evol (family (2 * π) θ 0) (-(1 / 2)) =
      ((-1 : ℂ) ^ T) • evol Z θ := by
  rw [rounded_product_closed _ _ hT, full_turn_step, neg_pow]
  have hp : (evol Z (θ / (2 * T))) ^ T = evol Z (θ / 2) := by
    rw [← evol_nat_mul]
    congr 1
    have htr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
  rw [hp]
  have hscalar : (-1 : Matrix (Fin 2) (Fin 2) ℂ) ^ T = ((-1 : ℂ) ^ T) • 1 := by
    rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1 by simp,
      smul_pow, one_pow]
  rw [hscalar, smul_mul_assoc, one_mul, mul_smul_comm, ← evol_add]
  congr 2
  ring

/-- Rationalizing the difference of the two rotation phases avoids cancellation. -/
theorem phase_defect_rationalized {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (θ : ℝ) :
    t * (Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) / 2 - a * t / 2) =
      θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a)) := by
  have hinside : a ^ 2 * t ^ 2 + θ ^ 2 = t ^ 2 * (a ^ 2 + (θ / t) ^ 2) := by
    field_simp
  have hroot : Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) =
      t * Real.sqrt (a ^ 2 + (θ / t) ^ 2) := by
    rw [hinside, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hden : Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg (θ / t)))
  rw [hroot]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hden)).mpr
  field_simp at hs ⊢
  linear_combination hs

/-- The phase displacement used in Example 5.2(i); `a = π` gives
`T (ρ - πT/2) → θ²/(4π)`. The full-turn proof uses `a = 2π`. -/
theorem phase_defect_limit {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2))
      atTop (𝓝 (θ ^ 2 / (4 * a))) := by
  have hzero : Tendsto (fun T : ℕ ↦ θ / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat θ
  have hroot : Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2))
      atTop (𝓝 a) := by
    have harg : Tendsto (fun T : ℕ ↦ a ^ 2 + (θ / (T : ℝ)) ^ 2)
        atTop (𝓝 (a ^ 2)) := by
      simpa using (tendsto_const_nhds (x := a ^ 2)).add (hzero.pow 2)
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    rw [Real.sqrt_sq ha.le] at hs
    exact hs
  have hlim : Tendsto (fun T : ℕ ↦ θ ^ 2 /
      (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) atTop
      (𝓝 (θ ^ 2 / (2 * (a + a)))) :=
    tendsto_const_nhds.div ((hroot.add_const a).const_mul 2)
      (by positivity : 2 * (a + a) ≠ 0)
  have heq : (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)) =ᶠ[atTop]
      (fun T : ℕ ↦ θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact phase_defect_rationalized ha (by exact_mod_cast hT) θ
  simpa only [show 2 * (a + a) = 4 * a by ring] using hlim.congr' heq.symm

/-- The unscaled phase defect tends to zero; this is the small quantity in
Example 5.2(ii). -/
theorem phase_defect_tendsto_zero {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)
      atTop (𝓝 0) := by
  have hp := (phase_defect_limit ha θ).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  field_simp

/-- The distance between two scalar unitary phases. -/
theorem phase_distance (r t : ℝ) :
    ‖Complex.exp (I * (r : ℂ)) - Complex.exp (I * (t : ℂ))‖ =
      2 * |Real.sin ((r - t) / 2)| := by
  have hfactor : Complex.exp (I * (r : ℂ)) - Complex.exp (I * (t : ℂ)) =
      Complex.exp (I * (t : ℂ)) * (Complex.exp (I * ((r - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, mul_comm I (t : ℂ), Complex.norm_exp_ofReal_mul_I,
    one_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
  norm_num only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Integer full-turn phases are the scalar sign, for both spectral branches. -/
theorem integer_phase_sign (T : ℕ) :
    Complex.exp (I * ((π * T : ℝ) : ℂ)) = (-1 : ℂ) ^ T ∧
      Complex.exp (I * ((-(π * T) : ℝ) : ℂ)) = (-1 : ℂ) ^ T := by
  constructor
  · have heq : I * ((π * T : ℝ) : ℂ) = (T : ℂ) * ((π : ℂ) * I) := by
      push_cast
      ring
    rw [heq, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  · have heq : I * ((-(π * T) : ℝ) : ℂ) = (T : ℂ) * (-((π : ℂ) * I)) := by
      push_cast
      ring
    rw [heq, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

/-- The two frozen-factor eigenvalues give the full-turn residual bound by
continuous functional calculus, as in Example 5.2(ii). -/
theorem full_turn_residual (θ : ℝ) (T : ℕ) :
    ‖evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2) - ((-1 : ℂ) ^ T) • 1‖ ≤
      2 * |Real.sin ((Real.sqrt ((2 * π) ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - π * T) / 2)| := by
  let E := evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)
  let r := Real.sqrt ((2 * π) ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
  let c : ℂ := (-1) ^ T
  have hgen : (((2 * π * T : ℝ) • X) - θ • Z).IsHermitian := by
    simpa only [xz, neg_smul, sub_eq_add_neg] using (xz_relations (2 * π * T) (-θ)).1
  have hn : IsStarNormal E := isStarNormal_of_mem_unitary (evol_mem_unitary hgen (1 / 2))
  have hs : spectrum ℂ E = {Complex.exp (-I * (r : ℂ)), Complex.exp (I * (r : ℂ))} := by
    have hrad : 4 * π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2 =
        (2 * π) ^ 2 * (T : ℝ) ^ 2 + θ ^ 2 := by ring
    simpa only [hrad] using full_turn_frozen_spectrum θ T
  have hbound : ∀ z ∈ spectrum ℂ E, ‖z - c‖ ≤ 2 * |Real.sin ((r - π * T) / 2)| := by
    intro z hz
    rw [hs] at hz
    rcases hz with hz | hz
    · rw [hz]
      have hneg : -I * (r : ℂ) = I * ((-r : ℝ) : ℂ) := by push_cast; ring
      rw [hneg, show c = Complex.exp (I * ((-(π * T) : ℝ) : ℂ)) from
        (integer_phase_sign T).2.symm, phase_distance]
      have hang : (-r - -(π * (T : ℝ))) / 2 = -((r - π * T) / 2) := by ring
      rw [hang, Real.sin_neg, abs_neg]
    · have hz' : z = Complex.exp (I * (r : ℂ)) := Set.mem_singleton_iff.mp hz
      rw [hz', show c = Complex.exp (I * ((π * T : ℝ) : ℂ)) from
        (integer_phase_sign T).1.symm, phase_distance]
  have hcfc : cfc (fun z : ℂ ↦ z - c) E = E - c • 1 := by
    rw [cfc_sub (fun z : ℂ ↦ z) (fun _ ↦ c)]
    change cfc id E - cfc (fun _ : ℂ ↦ c) E = E - c • 1
    rw [cfc_id ℂ E hn, cfc_const c E hn, Algebra.algebraMap_eq_smul_one]
  have hb := norm_cfc_le (f := fun z : ℂ ↦ z - c) (a := E)
    (show 0 ≤ 2 * |Real.sin ((r - π * T) / 2)| by positivity) hbound
  rw [hcfc] at hb
  exact hb
/-- The continuous full-turn frame factor approaches the scalar sign, by the
spectral residual bound and the vanishing phase defect. -/
theorem full_turn_residual_limit (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ ‖evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2) -
      ((-1 : ℂ) ^ T) • 1‖) atTop (𝓝 0) := by
  have hd := phase_defect_tendsto_zero (show 0 < 2 * π by positivity) θ
  have hhalf : Tendsto (fun T : ℕ ↦
      (Real.sqrt ((2 * π) ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - 2 * π * T / 2) / 2)
      atTop (𝓝 0) := by simpa using hd.div_const 2
  have hs := (((Real.continuous_sin.tendsto 0).comp hhalf).abs).const_mul 2
  simp only [Real.sin_zero, abs_zero, mul_zero] at hs
  have hscalar : Tendsto (fun T : ℕ ↦
      2 * |Real.sin ((Real.sqrt ((2 * π) ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - π * T) / 2)|)
      atTop (𝓝 0) := by
    convert hs using 1
    funext T
    dsimp only [Function.comp_def]
    congr 4
    ring
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun T ↦ full_turn_residual θ T) hscalar

/-- The full-turn endpoint distance of Example 5.2(ii), for the actual
rounded product and the continuous closed form. -/
theorem full_turn_error_limit (θ : ℝ) :
    Tendsto (fun T : ℕ ↦
      ‖evol (family (2 * π) θ 1) (1 / 2) * (unitProduct (family (2 * π) θ) T).1 *
        evol (family (2 * π) θ 0) (-(1 / 2)) -
        evol Z (θ / 2) * evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)‖)
      atTop (𝓝 (2 * |Real.sin (θ / 4)|)) := by
  let R := evol Z (θ / 2)
  let F := evol Z θ
  have hdist : ‖F - R‖ = 2 * |Real.sin (θ / 4)| := by
    rw [involution_distance pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
    congr 3
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (g := fun T : ℕ ↦ ‖evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2) -
      ((-1 : ℂ) ^ T) • 1‖) ?_ (full_turn_residual_limit θ)
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [full_turn_product θ (by omega)]
  let c : ℂ := (-1) ^ T
  let E := evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)
  have hc : ‖c‖ = 1 := by simp [c]
  have hnorm : ‖c • (F - R)‖ = 2 * |Real.sin (θ / 4)| := by
    rw [norm_smul, hc, one_mul, hdist]
  have hbound := abs_norm_sub_norm_le (c • F - R * E) (c • (F - R))
  have heq : c • F - R * E - c • (F - R) = -(R * (E - c • 1)) := by
    simp only [smul_sub, mul_sub, mul_smul_comm, mul_one]
    abel
  rw [hnorm, heq, norm_neg, CStarRing.norm_mem_unitary_mul _
    (evol_mem_unitary pauli_relations.2.2.1 (θ / 2))] at hbound
  simpa only [Real.norm_eq_abs] using hbound

/-- The fixed change of basis taking `(X,Y,Z)` to `(Z,X,Y)`. -/
def cyclic : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • !![1 + I, 1 + I; -1 + I, 1 - I]

/-- The change of basis used for the Discussion's spin convention is unitary. -/
theorem cyclic_unitary : cyclic ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal (2 : ℝ)
  rw [Unitary.mem_iff]
  constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    simp [cyclic, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_I] <;> ring_nf <;> simp [Complex.I_sq, htwo] <;> norm_num

/-- Its action on the Pauli triple is the cyclic permutation. -/
theorem cyclic_pauli : cyclic * X * star cyclic = Z ∧
    cyclic * Y * star cyclic = X ∧ cyclic * Z * star cyclic = Y := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal (2 : ℝ)
  repeat' constructor
  all_goals ext i j; fin_cases i <;> fin_cases j <;>
    simp [cyclic, X, Y, Z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Complex.conj_I] <;> ring_nf <;> simp [Complex.I_sq, htwo,
        show (I : ℂ) ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring] <;> norm_num

/-- Frozen evolution is equivariant under a unitary change of basis. -/
theorem evol_conjugate {d : ℕ} (C H : Matrix (Fin d) (Fin d) ℂ)
    (hC : C ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (t : ℝ) :
    evol (C * H * star C) t = C * evol H t * star C := by
  let +nondep : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) :=
    .restrictScalars ℚ ℂ _
  let u : (Matrix (Fin d) (Fin d) ℂ)ˣ :=
    ⟨C, star C, Unitary.mul_star_self_of_mem hC, Unitary.star_mul_self_of_mem hC⟩
  have he := NormedSpace.exp_units_conj u (t • (-I • H))
  simpa only [evol, mul_smul_comm, smul_mul_assoc] using he

/-- Products of sampled evolutions respect the same fixed change of basis. -/
theorem product_conjugate {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ)
    (hC : C ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (H : ℝ → Matrix (Fin d) (Fin d) ℂ) (T : ℕ) :
    (unitProduct (fun s ↦ C * H s * star C) T).1 =
      C * (unitProduct H T).1 * star C := by
  have hp (n : ℕ) : pieceProduct (fun _ ↦ 1) (fun j ↦ C * H ((j : ℝ) / T) * star C) n =
      C * pieceProduct (fun _ ↦ 1) (fun j ↦ H ((j : ℝ) / T)) n * star C := by
    induction n with
    | zero => simp [pieceProduct, Unitary.mul_star_self_of_mem hC]
    | succ n ih =>
      rw [pieceProduct, pieceProduct, evol_conjugate C _ hC, ih]
      simp only [mul_assoc]
      rw [← mul_assoc (star C), Unitary.star_mul_self_of_mem hC, one_mul]
  exact hp T

/-- The rounded product transforms by conjugation as well. -/
theorem rounded_conjugate {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ)
    (hC : C ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (H : ℝ → Matrix (Fin d) (Fin d) ℂ) (T : ℕ) :
    evol (C * H 1 * star C) (1 / 2) *
      (unitProduct (fun s ↦ C * H s * star C) T).1 *
      evol (C * H 0 * star C) (-(1 / 2)) =
    C * (evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))) * star C := by
  rw [evol_conjugate C _ hC, evol_conjugate C _ hC, product_conjugate C hC]
  simp only [mul_assoc]
  rw [← mul_assoc (star C), Unitary.star_mul_self_of_mem hC, one_mul,
    ← mul_assoc (star C), Unitary.star_mul_self_of_mem hC, one_mul]

/-- The Discussion uses the same precessing spin, conjugated by `cyclic`. -/
theorem discussion_family (θ s : ℝ) :
    π • (evol Y (θ * s / 2) * Z * evol Y (-(θ * s / 2))) =
      cyclic * family (2 * π) θ s * star cyclic := by
  have hy (t : ℝ) : evol Y t = cyclic * evol Z t * star cyclic := by
    rw [← cyclic_pauli.2.2, evol_conjugate cyclic _ cyclic_unitary]
  have hz : Z = cyclic * X * star cyclic := cyclic_pauli.1.symm
  rw [hz, hy, hy]
  simp only [mul_assoc]
  rw [← mul_assoc (star cyclic), Unitary.star_mul_self_of_mem cyclic_unitary, one_mul,
    ← mul_assoc (star cyclic), Unitary.star_mul_self_of_mem cyclic_unitary, one_mul]
  rw [← mul_assoc (evol Z (θ * s / 2)),
    ← mul_assoc (evol Z (θ * s / 2) * X), pauli_conj]
  simp only [family, mul_smul_comm, smul_mul_assoc]
  congr 2
  ring

/-- The resonant Hamiltonian in the Discussion has exactly scalar samples. -/
theorem discussion_full_turn_factor (θ s : ℝ) :
    evol (π • (evol Y (θ * s / 2) * Z * evol Y (-(θ * s / 2)))) 1 = -1 := by
  rw [discussion_family, evol_conjugate cyclic _ cyclic_unitary, full_turn_factor]
  simp [Unitary.mul_star_self_of_mem cyclic_unitary]

/-- The resonant example in the Discussion has the same limiting error as
Example 5.2(ii); a fixed unitary change of basis preserves its operator norm. -/
theorem discussion_error_limit (θ : ℝ) :
    let H := fun s ↦ π • (evol Y (θ * s / 2) * Z * evol Y (-(θ * s / 2)))
    Tendsto (fun T : ℕ ↦
      ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) -
        cyclic * (evol Z (θ / 2) * evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)) *
          star cyclic‖) atTop (𝓝 (2 * |Real.sin (θ / 4)|)) := by
  intro H
  have hH : H = fun s ↦ cyclic * family (2 * π) θ s * star cyclic :=
    funext (discussion_family θ)
  rw [hH]
  have heq (T : ℕ) :
      ‖evol (cyclic * family (2 * π) θ 1 * star cyclic) (1 / 2) *
        (unitProduct (fun s ↦ cyclic * family (2 * π) θ s * star cyclic) T).1 *
        evol (cyclic * family (2 * π) θ 0 * star cyclic) (-(1 / 2)) -
        cyclic * (evol Z (θ / 2) * evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)) * star cyclic‖ =
      ‖evol (family (2 * π) θ 1) (1 / 2) * (unitProduct (family (2 * π) θ) T).1 *
        evol (family (2 * π) θ 0) (-(1 / 2)) -
        evol Z (θ / 2) * evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)‖ := by
    rw [rounded_conjugate cyclic cyclic_unitary]
    rw [← sub_mul, ← mul_sub, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem cyclic_unitary),
      CStarRing.norm_mem_unitary_mul _ cyclic_unitary]
  simpa only [heq] using full_turn_error_limit θ

/-- With no precession the symmetric step is the constant-field rotation. -/
theorem step_zero (ω : ℝ) : step ω 0 = evol X (ω / 2) := by
  simp only [step, neg_zero, evol_zero, mul_one]
  rw [← evol_add]
  congr 1
  ring

/-- To first order in the precession angle, the symmetric step changes only
in the third Pauli direction. -/
theorem step_derivative (ω : ℝ) (T : ℕ) :
    HasDerivAt (fun θ : ℝ ↦ step ω (θ / (2 * T)))
      ((I / (2 * T) : ℂ) • Z) 0 := by
  have hc : HasDerivAt (fun θ : ℝ ↦ Real.cos (θ / (2 * T))) 0 0 := by
    simpa using (Real.hasDerivAt_cos ((0 : ℝ) / (2 * T))).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const (2 * (T : ℝ)))
  have hs : HasDerivAt (fun θ : ℝ ↦ Real.sin (θ / (2 * T))) (1 / (2 * T)) 0 := by
    simpa using (Real.hasDerivAt_sin ((0 : ℝ) / (2 * T))).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const (2 * (T : ℝ)))
  have hd := ((hc.const_mul (Real.cos (ω / 2))).ofReal_comp.smul_const
      (1 : Matrix (Fin 2) (Fin 2) ℂ)).sub
    ((((hc.const_mul (Real.sin (ω / 2))).ofReal_comp.smul_const X).sub
      (hs.ofReal_comp.smul_const Z)).const_smul I)
  convert hd using 1
  · funext θ
    simpa only [Pi.sub_apply, Pi.smul_apply, Complex.ofReal_mul] using step_closed ω (θ / (2 * T))
  · simp only [mul_zero, Complex.ofReal_zero, zero_smul, zero_sub, smul_neg,
      neg_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_natCast, smul_smul]
    congr 1
    ring

/-- Differentiating the finite product at zero precession gives a sine
quotient. The proof follows the product rule and the sine addition formula. -/
theorem step_power_derivative (ω : ℝ) {T : ℕ} (hT : 0 < T)
    (hs : Real.sin (ω / 2) ≠ 0) (n : ℕ) :
    HasDerivAt (fun θ : ℝ ↦ step ω (θ / (2 * T)) ^ n)
      ((I * Real.sin (n * (ω / 2)) / (2 * T * Real.sin (ω / 2)) : ℂ) • Z) 0 := by
  induction n with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | succ n ih =>
    have hd := ih.mul (step_derivative ω T)
    convert hd using 1
    simp only [zero_div, step_zero]
    rw [← evol_nat_mul, evol_involution pauli_relations.1 pauli_relations.2.2.2.1,
      evol_involution pauli_relations.1 pauli_relations.2.2.2.1]
    have htr : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have hsc : (Real.sin (ω / 2) : ℂ) ≠ 0 := by exact_mod_cast hs
    rw [show ((n + 1 : ℕ) : ℝ) * (ω / 2) = n * (ω / 2) + ω / 2 by push_cast; ring,
      Real.sin_add]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Z, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Complex.real_smul, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> field_simp <;> ring


/-- Closed exponential of a nonzero real Pauli combination, obtained by
normalizing its axis in the SU(2) formula. -/
theorem evol_xz_formula {a b : ℝ} (h : 0 < a ^ 2 + b ^ 2) :
    let r := Real.sqrt (a ^ 2 + b ^ 2)
    evol (xz a b) (1 / 2) = (Real.cos (r / 2) : ℂ) • 1 -
      (I * Real.sin (r / 2) / r : ℂ) • xz a b := by
  intro r
  let N := r⁻¹ • xz a b
  obtain ⟨hN, hNN⟩ := xz_normalized h
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  have hG : xz a b = r • N := by
    dsimp [N]
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
  conv_lhs => rw [hG, Prose.localSteps_evol_smul_sharp, evol_involution hN hNN]
  rw [show (1 / 2 : ℝ) * r = r / 2 by ring]
  congr 1
  dsimp [N]
  rw [← IsScalarTower.algebraMap_smul ℂ r⁻¹ (xz a b), smul_smul]
  congr 1
  change I * (Real.sin (r / 2) : ℂ) * (↑(r⁻¹) : ℂ) =
    I * (Real.sin (r / 2) : ℂ) / (r : ℂ)
  simp only [Complex.ofReal_inv, div_eq_mul_inv]

/-- The derivative of the continuous frame factor at zero precession. -/
theorem frozen_derivative {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun θ : ℝ ↦ evol (a • X - θ • Z) (1 / 2))
      ((I * Real.sin (a / 2) / a : ℂ) • Z) 0 := by
  let r : ℝ → ℝ := fun θ ↦ Real.sqrt (a ^ 2 + θ ^ 2)
  have ha0 : a ≠ 0 := ha.ne'
  have hr0 : r 0 = a := by simp [r, Real.sqrt_sq ha.le]
  have harg : HasDerivAt (fun θ : ℝ ↦ a ^ 2 + θ ^ 2) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).const_add (a ^ 2)
  have hr : HasDerivAt r 0 0 := by
    have hh := (Real.hasDerivAt_sqrt
      (show a ^ 2 + (0 : ℝ) ^ 2 ≠ 0 by simpa using pow_ne_zero 2 ha0)).comp 0 harg
    simpa only [mul_zero] using hh
  have hc : HasDerivAt (fun θ ↦ Real.cos (r θ / 2)) 0 0 := by
    have hh := (Real.hasDerivAt_cos (r 0 / 2)).comp 0 (hr.div_const 2)
    simpa using hh
  have hs : HasDerivAt (fun θ ↦ Real.sin (r θ / 2)) 0 0 := by
    have hh := (Real.hasDerivAt_sin (r 0 / 2)).comp 0 (hr.div_const 2)
    simpa using hh
  have hratio : HasDerivAt (fun θ ↦ Real.sin (r θ / 2) / r θ) 0 0 := by
    simpa using hs.div hr (by rw [hr0]; exact ha0)
  have hx : HasDerivAt (fun θ : ℝ ↦ a • X - θ • Z) (-Z) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (a • X)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const Z)
  have hd := (hc.ofReal_comp.smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)).sub
    ((hratio.ofReal_comp.smul hx).const_smul I)
  convert hd using 1
  · funext θ
    have hp : 0 < a ^ 2 + (-θ) ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
    have he := evol_xz_formula hp
    simp only [xz, neg_smul, ← sub_eq_add_neg, neg_sq] at he
    rw [he]
    dsimp [r]
    congr 1
    rw [smul_comm I (Real.sin (Real.sqrt (a ^ 2 + θ ^ 2) / 2) / Real.sqrt (a ^ 2 + θ ^ 2)),
      ← smul_assoc, Complex.real_smul]
    congr 1
    push_cast
    ring
  · simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_sub, hr0, smul_neg,
      neg_neg, smul_smul, Complex.ofReal_div]
    congr 1
    ring

/-- The difference of the two closed forms in the rotating frame. -/
def frameError (ω θ : ℝ) (T : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  step ω (θ / (2 * T)) ^ T - evol ((ω * T) • X - θ • Z) (1 / 2)

/-- Removing the common rotating frame preserves the actual comparison error. -/
theorem error_norm_frame (ω θ : ℝ) {T : ℕ} (hT : 0 < T) :
    ‖evol (family ω θ 1) (1 / 2) * (unitProduct (family ω θ) T).1 *
      evol (family ω θ 0) (-(1 / 2)) -
      evol Z (θ / 2) * evol ((ω * T) • X - θ • Z) (1 / 2)‖ =
      ‖frameError ω θ T‖ := by
  rw [rounded_product_closed _ _ hT, ← mul_sub,
    CStarRing.norm_mem_unitary_mul _ (evol_mem_unitary pauli_relations.2.2.1 (θ / 2))]
  rfl

/-- The error vanishes when the field does not precess. -/
theorem frameError_zero (ω : ℝ) (T : ℕ) : frameError ω 0 T = 0 := by
  simp only [frameError, zero_div, step_zero, zero_smul, sub_zero]
  rw [← evol_nat_mul, Prose.localSteps_evol_smul_sharp]
  have ht : (T : ℝ) * (ω / 2) = 1 / 2 * (ω * T) := by ring
  rw [ht, sub_self]

/-- First variation of the comparison error in the precession angle.
This is the finite-product version of the axis computation after Example 5.2. -/
theorem frameError_derivative {ω : ℝ} (hω : 0 < ω) {T : ℕ} (hT : 0 < T)
    (hs : Real.sin (ω / 2) ≠ 0) :
    HasDerivAt (fun θ : ℝ ↦ frameError ω θ T)
      ((I * Real.sin (T * (ω / 2)) *
        (1 / (2 * T * Real.sin (ω / 2)) - 1 / (ω * T)) : ℂ) • Z) 0 := by
  have hd := (step_power_derivative ω hT hs T).sub
    (frozen_derivative (mul_pos hω (Nat.cast_pos.mpr hT)))
  convert hd using 1
  rw [← sub_smul]
  congr 1
  rw [show ω * (T : ℝ) / 2 = T * (ω / 2) by ring]
  push_cast
  ring

/-- The norm of the third Pauli matrix is one in the operator norm. -/
theorem norm_Z : ‖Z‖ = 1 := by
  have hh := congrArg norm pauli_relations.2.2.2.2.2.1
  rw [pauli_relations.2.2.1.isSelfAdjoint.norm_mul_self, norm_one] at hh
  exact (sq_eq_sq₀ (norm_nonneg Z) zero_le_one).mp (by simpa using hh)

/-- The leading comparison error at a fixed number of steps, before imposing
the odd-resonance condition. -/
theorem frameError_normalized_limit {ω : ℝ} (hω : 0 < ω) {T : ℕ} (hT : 0 < T)
    (hs : Real.sin (ω / 2) ≠ 0) :
    Tendsto (fun θ : ℝ ↦ (T : ℝ) * ‖frameError ω θ T‖ / (ω * |θ|)) (𝓝[≠] 0)
      (𝓝 ((T : ℝ) / ω *
        ‖((I * Real.sin (T * (ω / 2)) *
          (1 / (2 * T * Real.sin (ω / 2)) - 1 / (ω * T)) : ℂ) • Z)‖)) := by
  rw [norm_smul]
  have hh := ((frameError_derivative hω hT hs).tendsto_slope_zero.norm).const_mul
    ((T : ℝ) / ω)
  simp only [zero_add, frameError_zero, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs] at hh
  convert hh using 1
  funext θ
  dsimp
  ring

/-- The fixed-`T`, small-precession limit proving the endpoint coefficient
sharp at every odd-resonant width. The notation `m` makes "odd" precise. -/
theorem precessing_spin_every_width {ω : ℝ} (hω : 0 < ω) (hω2 : ω < 2 * π)
    {T : ℕ} (hT : 0 < T) (m : ℕ) (hodd : (T : ℝ) * ω = (2 * m + 1) * π) :
    Tendsto (fun θ : ℝ ↦ (T : ℝ) * ‖frameError ω θ T‖ / (ω * |θ|)) (𝓝[≠] 0)
      (𝓝 (1 / (2 * ω * Real.sin (ω / 2)) - 1 / ω ^ 2)) := by
  have hspos : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hTpos : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hh := frameError_normalized_limit hω hT hspos.ne'
  have hcoeff : 0 ≤ 1 / (2 * (T : ℝ) * Real.sin (ω / 2)) - 1 / (ω * T) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    have hsin := Real.sin_le (by positivity : 0 ≤ ω / 2)
    have hmul := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 2 * (T : ℝ) by positivity)
    linarith
  have hphase : (T : ℝ) * (ω / 2) = m * π + π / 2 := by
    linear_combination hodd / 2
  have hsabs : |Real.sin (T * (ω / 2))| = 1 := by
    rw [hphase, Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hnorm : ‖((I * Real.sin (T * (ω / 2)) *
      (1 / (2 * T * Real.sin (ω / 2)) - 1 / (ω * T)) : ℂ) • Z)‖ =
      1 / (2 * (T : ℝ) * Real.sin (ω / 2)) - 1 / (ω * T) := by
    rw [norm_smul, norm_Z, mul_one, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, hsabs, one_mul, one_mul]
    have hc : (1 / (2 * (T : ℂ) * Real.sin (ω / 2)) - 1 / ((ω : ℂ) * T)) =
        ((1 / (2 * (T : ℝ) * Real.sin (ω / 2)) - 1 / (ω * T) : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeff]
  rw [hnorm] at hh
  convert hh using 1
  congr 1
  field_simp


/-- Multiplying a small angle by its sine preserves its first-order limit. -/
theorem scaled_sin_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.sin (x n)) atTop (𝓝 a) := by
  have hh := ha.mul ((Real.continuous_sinc.tendsto 0).comp hx)
  simp only [Real.sinc_zero, mul_one] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  by_cases hn : x n = 0
  · simp [hn]
  · rw [Real.sinc_of_ne_zero hn]
    field_simp

/-- The quarter-turn formula used to multiply the symmetric half-turn step. -/
theorem quarter_turn_X :
    evol X (π / 4) = (Real.sqrt 2)⁻¹ • (1 - I • X) := by
  rw [evol_involution pauli_relations.1 pauli_relations.2.2.2.1,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hs : Real.sqrt 2 / 2 = (Real.sqrt 2)⁻¹ := by
    have hp : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
    exact Real.sq_sqrt (by norm_num)
  rw [hs]
  ext i j
  simp [Complex.real_smul]
  ring

/-- At width π the symmetric step has the tilted involutive Pauli axis. -/
theorem half_turn_step (ε : ℝ) :
    step π ε = evol (xz (Real.cos ε) (-Real.sin ε)) (π / 2) := by
  have hN := xz_relations (Real.cos ε) (-Real.sin ε)
  have hNN : xz (Real.cos ε) (-Real.sin ε) * xz (Real.cos ε) (-Real.sin ε) = 1 := by
    rw [hN.2, neg_sq, Real.cos_sq_add_sin_sq, one_smul]
  unfold step
  rw [quarter_turn_X,
    evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1,
    evol_involution hN.1 hNN]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xz, X, Z, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul,
      Real.cos_pi_div_two, Real.sin_pi_div_two] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq, hs] <;> ring

/-- Every equatorial Pauli axis has operator norm one. -/
theorem norm_axis (φ : ℝ) : ‖axis φ‖ = 1 := by
  have hh := congrArg norm (axis_relations φ).2
  rw [(axis_relations φ).1.isSelfAdjoint.norm_mul_self, norm_one] at hh
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hh)

/-- Differentiating a precessing field rotates its axis by π/2. -/
theorem family_derivative (ω θ s : ℝ) :
    HasDerivAt (family ω θ) ((ω * θ / 2 : ℝ) • axis (θ * s + π / 2)) s := by
  have hc := ((hasDerivAt_id s).const_mul θ).cos
  have hs := ((hasDerivAt_id s).const_mul θ).sin
  have hh := ((hc.ofReal_comp.smul_const X).add (hs.ofReal_comp.smul_const Y)).const_smul (ω / 2)
  convert hh using 1
  · ext i j
    simp [axis, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Complex.real_smul]
    ring

/-- The endpoint derivative norms used in the statement of Example 5.2(i). -/
theorem family_derivWithin_norm {ω : ℝ} (hω : 0 ≤ ω) (θ : ℝ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖derivWithin (family ω θ) (Icc (0 : ℝ) 1) s‖ = ω * |θ| / 2 := by
  rw [((family_derivative ω θ s).hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc zero_lt_one) s hs)), norm_smul, norm_axis, mul_one,
    Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hω, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Algebraic factorization of the odd-step limit into the paper's endpoint term. -/
theorem odd_limit_factored (θ : ℝ) :
    Real.sqrt ((θ ^ 2 / (4 * π)) ^ 2 + (θ / 2 - θ / π) ^ 2) =
      (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) *
        Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2)) := by
  have hp : 0 < π - 2 := by linarith [pi_gt_three]
  have hc : (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) =
      (π - 2) * |θ| / (2 * π) := by field_simp
  rw [hc]
  have ha : 0 ≤ (π - 2) * |θ| / (2 * π) := by positivity
  have hx : 0 ≤ 1 + θ ^ 2 / (4 * (π - 2) ^ 2) := by positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hx]
  simp only [div_pow, mul_pow, sq_abs]
  field_simp
  ring


/-- The first derivative of the schedule, in a notation usable by the Lipschitz estimate. -/
def familySlope (ω θ s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (ω * θ / 2 : ℝ) • axis (θ * s + π / 2)

/-- The second derivative is minus the squared angular speed times the field. -/
theorem familySlope_derivative (ω θ s : ℝ) :
    HasDerivAt (familySlope ω θ) (-(θ ^ 2) • family ω θ s) s := by
  have hd := ((hasDerivAt_id s).const_mul θ).add_const (π / 2)
  have hh := ((hd.cos.ofReal_comp.smul_const X).add
    (hd.sin.ofReal_comp.smul_const Y)).const_smul (ω * θ / 2)
  convert hh using 1
  · ext i j
    simp [axis, family, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Complex.real_smul]
    ring

/-- The derivative of the spin schedule has Lipschitz constant ωθ²/2. -/
theorem family_derivative_lipschitz {ω : ℝ} (hω : 0 ≤ ω) (θ s t : ℝ) :
    ‖familySlope ω θ t - familySlope ω θ s‖ ≤ ω * θ ^ 2 / 2 * |t - s| := by
  have hbound (x : ℝ) : ‖-(θ ^ 2) • family ω θ x‖ ≤ ω * θ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg _),
      family, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ω / 2),
      norm_axis, mul_one]
    exact le_of_eq (by ring)
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ ↦ (familySlope_derivative ω θ x).hasDerivWithinAt)
      (fun x _ ↦ hbound x) (mem_univ s) (mem_univ t)


/-- The axis-angle displacement appearing in the proof of Example 5.2(i). -/
theorem axis_angle_limit (θ : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (θ / (2 * n) - Real.arctan (θ / (π * n)))) atTop
      (𝓝 ((π - 2) * θ / (2 * π))) := by
  have hd := Real.hasDerivAt_arctan 0
  have hds := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto
  rw [dslope_same, hd.deriv] at hds
  norm_num only [zero_pow (by decide : 2 ≠ 0), add_zero, div_one] at hds
  have hx : Tendsto (fun n : ℕ ↦ θ / (π * n)) atTop (𝓝 0) := by
    simpa only [div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ / π)
  have hh := (hds.comp hx).const_mul (θ / π)
  simp only [mul_one] at hh
  have hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.arctan (θ / (π * n)))
      atTop (𝓝 (θ / π)) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [Function.comp_def]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have he := sub_smul_dslope Real.arctan 0 (θ / (π * n))
    simp only [sub_zero, Real.arctan_zero, smul_eq_mul] at he
    rw [← he]
    field_simp
  have he : Tendsto (fun n : ℕ ↦ (n : ℝ) * (θ / (2 * n))) atTop (𝓝 (θ / 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  convert he.sub hscaled using 1
  · funext n
    ring
  · congr 1
    field_simp


/-- The sine and cosine of the normalized continuous-axis angle. -/
theorem axis_arctan_coordinates {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.cos (Real.arctan (b / a)) = a / Real.sqrt (a ^ 2 + b ^ 2) ∧
    Real.sin (Real.arctan (b / a)) = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  have ha0 := ha.ne'
  have hr : Real.sqrt (1 + (b / a) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / a := by
    rw [show 1 + (b / a) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 by field_simp,
      Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sqrt_sq ha.le]
  rw [Real.cos_arctan, Real.sin_arctan, hr]
  constructor <;> field_simp

/-- Real Pauli axes parametrized by their angle are Hermitian involutions. -/
theorem xz_angle_relations (α : ℝ) :
    (xz (Real.cos α) (-Real.sin α)).IsHermitian ∧
    xz (Real.cos α) (-Real.sin α) * xz (Real.cos α) (-Real.sin α) = 1 := by
  refine ⟨(xz_relations _ _).1, ?_⟩
  rw [(xz_relations _ _).2, neg_sq, Real.cos_sq_add_sin_sq, one_smul]

/-- The continuous frame factor rotates about the normalized arctangent axis. -/
theorem frozen_axis_angle {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    evol (a • X - θ • Z) (1 / 2) =
      evol (xz (Real.cos (Real.arctan (θ / a))) (-Real.sin (Real.arctan (θ / a))))
        (Real.sqrt (a ^ 2 + θ ^ 2) / 2) := by
  have hr : Real.sqrt (a ^ 2 + θ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _))).ne'
  obtain ⟨hc, hs⟩ := axis_arctan_coordinates ha θ
  have he : a • X - θ • Z = Real.sqrt (a ^ 2 + θ ^ 2) •
      xz (Real.cos (Real.arctan (θ / a))) (-Real.sin (Real.arctan (θ / a))) := by
    rw [hc, hs]
    simp only [xz, neg_smul, smul_add, smul_neg, smul_smul,
      mul_div_cancel₀ _ hr, sub_eq_add_neg]
  rw [he, Prose.localSteps_evol_smul_sharp]
  congr 1
  ring

/-- A real Pauli combination has squared norm equal to the squared length of
its coefficient vector. -/
theorem xz_norm_sq (a b : ℝ) : ‖xz a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hh := congrArg norm (xz_relations a b).2
  rw [(xz_relations a b).1.isSelfAdjoint.norm_mul_self, norm_smul, norm_one,
    mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
  exact hh

/-- The square of the Hermitian Pauli combination is its squared norm times
the identity, as used below the norm display in Example 5.2. -/
theorem xz_square_norm (a b : ℝ) :
    xz a b * xz a b = ‖xz a b‖ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [xz_norm_sq, (xz_relations a b).2]

/-- Adding an imaginary scalar to a Hermitian matrix cancels the mixed terms
in its adjoint square. -/
theorem hermitian_imaginary_square {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) (s : ℝ) :
    star (A + (I * s) • 1) * (A + (I * s) • 1) = A * A + (s ^ 2 : ℝ) • 1 := by
  have ha : star A = A := hA
  simp only [star_add, star_smul, star_one, ha, Complex.star_def,
    map_mul, Complex.conj_I, Complex.conj_ofReal, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The norm display for a real Pauli combination plus an imaginary scalar. -/
theorem xz_imaginary_norm (a b s : ℝ) :
    ‖xz a b + (I * s) • 1‖ = Real.sqrt (‖xz a b‖ ^ 2 + s ^ 2) := by
  have hh := congrArg norm (hermitian_imaginary_square (xz_relations a b).1 s)
  rw [xz_square_norm, ← add_smul, CStarRing.norm_star_mul_self,
    norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hh
  rw [← hh, ← pow_two, Real.sqrt_sq (norm_nonneg _)]

/-- At width pi the symmetric step is minus i times its real Pauli axis. -/
theorem half_turn_step_scalar (ε : ℝ) :
    step π ε = (-I) • xz (Real.cos ε) (-Real.sin ε) := by
  rw [half_turn_step, evol_involution (xz_angle_relations _).1 (xz_angle_relations _).2]
  simp

/-- Every odd power of the symmetric half-turn retains its axis. -/
theorem odd_step_power (ε : ℝ) (k : ℕ) :
    step π ε ^ (2 * k + 1) = (-I) ^ (2 * k + 1) •
      xz (Real.cos ε) (-Real.sin ε) := by
  have hp : xz (Real.cos ε) (-Real.sin ε) ^ (2 * k + 1) =
      xz (Real.cos ε) (-Real.sin ε) := by
    rw [pow_add, pow_mul, pow_two, (xz_angle_relations _).2, one_pow, pow_one, one_mul]
  rw [half_turn_step_scalar, smul_pow, hp]

/-- The odd resonant phase factors out before expanding the residual
rotation, as in the first equality for the continuous factor in Example 5.2(i). -/
theorem odd_frozen_rotation_factor (β δ : ℝ) (k : ℕ) :
    evol (xz (Real.cos β) (-Real.sin β)) (π * (2 * k + 1) / 2 + δ) =
      (-I) ^ (2 * k + 1) •
        (xz (Real.cos β) (-Real.sin β) * evol (xz (Real.cos β) (-Real.sin β)) δ) := by
  have hp := odd_step_power β k
  rw [half_turn_step, ← evol_nat_mul] at hp
  have ht : ((2 * k + 1 : ℕ) : ℝ) * (π / 2) = π * (2 * k + 1) / 2 := by
    push_cast
    ring
  rw [ht] at hp
  rw [evol_add, hp, smul_mul_assoc]

/-- Expanding the residual rotation gives the continuous factor's real axis
part and imaginary scalar part. -/
theorem odd_frozen_rotation (β δ : ℝ) (k : ℕ) :
    evol (xz (Real.cos β) (-Real.sin β)) (π * (2 * k + 1) / 2 + δ) =
      (-I) ^ (2 * k + 1) •
        ((Real.cos δ : ℂ) • xz (Real.cos β) (-Real.sin β) - (I * Real.sin δ) • 1) := by
  rw [odd_frozen_rotation_factor,
    evol_involution (xz_angle_relations _).1 (xz_angle_relations _).2,
    mul_sub, mul_smul_comm, mul_smul_comm, mul_one, (xz_angle_relations _).2]

/-- The geometric norm display in Example 5.2(i), with the common unit
complex phase removed. -/
theorem odd_error_geometric (θ : ℝ) (k : ℕ) :
    let T : ℕ := 2 * k + 1
    let δ := Real.sqrt (π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - π * T / 2
    let α := θ / (2 * T)
    let β := Real.arctan (θ / (π * T))
    let A := xz (Real.cos α) (-Real.sin α) -
      (Real.cos δ : ℂ) • xz (Real.cos β) (-Real.sin β)
    ‖frameError π θ T‖ = ‖A + (I * Real.sin δ) • 1‖ ∧
      ‖frameError π θ T‖ = Real.sqrt (‖A‖ ^ 2 + Real.sin δ ^ 2) := by
  intro T δ α β A
  have ht : 0 < (T : ℝ) := by dsimp [T]; positivity
  have hr : Real.sqrt ((π * (T : ℝ)) ^ 2 + θ ^ 2) / 2 = π * T / 2 + δ := by
    dsimp [δ]
    rw [mul_pow]
    ring
  have he : frameError π θ T = (-I) ^ T • (A + (I * Real.sin δ) • 1) := by
    unfold frameError
    rw [odd_step_power, frozen_axis_angle (mul_pos pi_pos ht), hr]
    have htcast : (T : ℝ) = 2 * (k : ℝ) + 1 := by dsimp [T]; push_cast; rfl
    rw [htcast, odd_frozen_rotation]
    dsimp [A, α, β, T]
    push_cast
    simp only [smul_add, smul_sub]
    abel
  have hn : ‖frameError π θ T‖ = ‖A + (I * Real.sin δ) • 1‖ := by
    rw [he, norm_smul, norm_pow]
    simp
  refine ⟨hn, hn.trans ?_⟩
  have ha : A = xz (Real.cos α - Real.cos δ * Real.cos β)
      (-Real.sin α + Real.cos δ * Real.sin β) := by
    ext i j
    simp [A, xz, Complex.real_smul]
    ring
  rw [ha, xz_imaginary_norm]

/-- A small angle with bounded first-order scaling has cosine defect
negligible at first order. -/
theorem scaled_cos_sub_one_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (Real.cos (x n) - 1)) atTop (𝓝 0) := by
  have hd := Real.hasDerivAt_cos 0
  have hh := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto
  rw [dslope_same, hd.deriv] at hh
  simp only [Real.sin_zero, neg_zero] at hh
  have h := ha.mul (hh.comp hx)
  simp only [mul_zero] at h
  apply h.congr'
  apply Eventually.of_forall
  intro n
  have he := sub_smul_dslope Real.cos 0 (x n)
  simp only [sub_zero, Real.cos_zero, smul_eq_mul] at he
  dsimp only [Function.comp_def]
  rw [mul_assoc, he]

/-- The cosine defect used in Example 5.2(i) is quadratic in inverse time. -/
theorem phase_cosine_quadratic (θ : ℝ) :
    (fun n : ℕ ↦ 1 - Real.cos (Real.sqrt (π ^ 2 * (n : ℝ) ^ 2 + θ ^ 2) / 2 - π * n / 2))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹ ^ 2) := by
  let δ := fun n : ℕ ↦ Real.sqrt (π ^ 2 * (n : ℝ) ^ 2 + θ ^ 2) / 2 - π * n / 2
  have hd : Tendsto (fun n ↦ δ n / 2) atTop (𝓝 0) := by
    simpa [δ] using (phase_defect_tendsto_zero pi_pos θ).div_const 2
  have hnd : Tendsto (fun n : ℕ ↦ (n : ℝ) * (δ n / 2))
      atTop (𝓝 ((θ ^ 2 / (4 * π)) / 2)) := by
    convert (phase_defect_limit pi_pos θ).div_const 2 using 1
    funext n
    dsimp [δ]
    ring
  have hs := ((scaled_sin_limit hd hnd).pow 2).const_mul 2
  apply Asymptotics.isBigO_of_div_tendsto_nhds ?_ (2 * ((θ ^ 2 / (4 * π)) / 2) ^ 2) ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hn0]
  · apply hs.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hc : 1 - Real.cos (δ n) = 2 * Real.sin (δ n / 2) ^ 2 := by
      have hh := Real.cos_two_mul (δ n / 2)
      have ht := Real.sin_sq_add_cos_sq (δ n / 2)
      rw [show 2 * (δ n / 2) = δ n by ring] at hh
      linear_combination -hh - 2 * ht
    change 2 * ((n : ℝ) * Real.sin (δ n / 2)) ^ 2 =
      (1 - Real.cos (δ n)) / ((n : ℝ)⁻¹ ^ 2)
    rw [hc]
    field_simp

/-- The axes in the norm display have the first-order separation asserted
in Example 5.2(i); the cosine defect contributes zero at that order. -/
theorem odd_axis_norm_limit (θ : ℝ) :
    let δ := fun n : ℕ ↦ Real.sqrt (π ^ 2 * (n : ℝ) ^ 2 + θ ^ 2) / 2 - π * n / 2
    let α := fun n : ℕ ↦ θ / (2 * n)
    let β := fun n : ℕ ↦ Real.arctan (θ / (π * n))
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ‖xz (Real.cos (α n)) (-Real.sin (α n)) -
      (Real.cos (δ n) : ℂ) • xz (Real.cos (β n)) (-Real.sin (β n))‖)
      atTop (𝓝 ((π - 2) * |θ| / (2 * π))) := by
  intro δ α β
  have hα : Tendsto α atTop (𝓝 0) := by
    simpa [α, div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ / 2)
  have hnα : Tendsto (fun n : ℕ ↦ (n : ℝ) * α n) atTop (𝓝 (θ / 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [α]
    field_simp
  have hβ : Tendsto β atTop (𝓝 0) := by
    have hh := (Real.continuous_arctan.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (θ / π))
    simpa [β, div_div] using hh
  have hnβ : Tendsto (fun n : ℕ ↦ (n : ℝ) * β n) atTop (𝓝 (θ / π)) := by
    have hh := hnα.sub (axis_angle_limit θ)
    convert hh using 1
    · funext n
      dsimp [α, β]
      ring
    · congr 1
      field_simp
      ring
  have hcα := scaled_cos_sub_one_limit hα hnα
  have hcβ := scaled_cos_sub_one_limit hβ hnβ
  have hbound := ((phase_cosine_quadratic θ).mul
    (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)).neg_left
  have hscaled : (fun n : ℕ ↦ (n : ℝ) * (Real.cos (δ n) - 1))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
    apply hbound.congr
    · intro n
      dsimp [δ]
      ring
    · intro n
      by_cases hn : (n : ℝ) = 0
      · simp [hn]
      · field_simp
  have hcδ : Tendsto (fun n : ℕ ↦ (n : ℝ) * (Real.cos (δ n) - 1))
      atTop (𝓝 0) := hscaled.trans_tendsto (by
    simpa only [one_div] using tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hcβ0 : Tendsto (fun n ↦ Real.cos (β n)) atTop (𝓝 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp hβ
  have hsβ0 : Tendsto (fun n ↦ Real.sin (β n)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sin.tendsto 0).comp hβ
  have hx := (hcα.sub hcβ).sub (hcδ.mul hcβ0)
  have hz := ((scaled_sin_limit hβ hnβ).sub (scaled_sin_limit hα hnα)).add
    (hcδ.mul hsβ0)
  have hv := (hx.smul_const X).add (hz.smul_const Z)
  have hh := hv.norm
  simp only [sub_zero, zero_mul, add_zero, zero_smul, zero_add,
    norm_smul, Real.norm_eq_abs, norm_Z, mul_one] at hh
  have habs : |θ / π - θ / 2| = (π - 2) * |θ| / (2 * π) := by
    rw [show θ / π - θ / 2 = -((π - 2) * θ / (2 * π)) by field_simp; ring,
      abs_neg, abs_div, abs_mul, abs_of_pos (by linarith [pi_gt_three] : 0 < π - 2),
      abs_of_pos (by positivity : 0 < 2 * π)]
  rw [habs] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have he : ((n : ℝ) * (Real.cos (α n) - 1) - n * (Real.cos (β n) - 1) -
        n * (Real.cos (δ n) - 1) * Real.cos (β n)) • X +
      (n * Real.sin (β n) - n * Real.sin (α n) +
        n * (Real.cos (δ n) - 1) * Real.sin (β n)) • Z =
      (n : ℝ) • (xz (Real.cos (α n)) (-Real.sin (α n)) -
        (Real.cos (δ n) : ℂ) • xz (Real.cos (β n)) (-Real.sin (β n))) := by
    ext i j
    simp [xz, Complex.real_smul]
    ring
  dsimp only
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]

/-- The odd-step limit composes the geometric norm display and the separate
limits of its axis and phase terms. -/
theorem odd_error_limit (θ : ℝ) :
    Tendsto (fun k : ℕ ↦ ((2 * k + 1 : ℕ) : ℝ) * ‖frameError π θ (2 * k + 1)‖)
      atTop (𝓝 (Real.sqrt ((θ ^ 2 / (4 * π)) ^ 2 + (θ / 2 - θ / π) ^ 2))) := by
  let δ := fun n : ℕ ↦ Real.sqrt (π ^ 2 * (n : ℝ) ^ 2 + θ ^ 2) / 2 - π * n / 2
  let A := fun n : ℕ ↦ xz (Real.cos (θ / (2 * n))) (-Real.sin (θ / (2 * n))) -
    (Real.cos (δ n) : ℂ) • xz (Real.cos (Real.arctan (θ / (π * n))))
      (-Real.sin (Real.arctan (θ / (π * n))))
  have hs := scaled_sin_limit (phase_defect_tendsto_zero pi_pos θ) (phase_defect_limit pi_pos θ)
  have ha := odd_axis_norm_limit θ
  have hh := ((ha.pow 2).add (hs.pow 2)).sqrt
  have he : ((π - 2) * |θ| / (2 * π)) ^ 2 + (θ ^ 2 / (4 * π)) ^ 2 =
      (θ ^ 2 / (4 * π)) ^ 2 + (θ / 2 - θ / π) ^ 2 := by
    rw [div_pow, mul_pow, sq_abs]
    field_simp
    ring
  rw [he] at hh
  have hodd : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ show id k ≤ 2 * k + 1 by dsimp; omega) tendsto_id
  apply (hh.comp hodd).congr'
  apply Eventually.of_forall
  intro k
  change Real.sqrt ((((2 * k + 1 : ℕ) : ℝ) * ‖A (2 * k + 1)‖) ^ 2 +
    (((2 * k + 1 : ℕ) : ℝ) * Real.sin (δ (2 * k + 1))) ^ 2) = _
  rw [show (((2 * k + 1 : ℕ) : ℝ) * ‖A (2 * k + 1)‖) ^ 2 +
      (((2 * k + 1 : ℕ) : ℝ) * Real.sin (δ (2 * k + 1))) ^ 2 =
      ((2 * k + 1 : ℕ) : ℝ) ^ 2 *
        (‖A (2 * k + 1)‖ ^ 2 + Real.sin (δ (2 * k + 1)) ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  exact congrArg (fun r : ℝ ↦ ((2 * k + 1 : ℕ) : ℝ) * r)
    (odd_error_geometric θ k).2.symm

/-- Example 5.2: the two limiting comparisons, retaining their closed forms as
extra conclusions. The endpoint
norms are those of the actual derivative of the Hamiltonian in the statement. -/
theorem ex_precessing_spin (ω θ : ℝ) :
    let H := family ω θ
    let V := fun T : ℕ ↦ evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))
    let Uend := fun T : ℕ ↦ evol Z (θ / 2) * evol ((ω * T) • X - θ • Z) (1 / 2)
    (∀ T : ℕ, 0 < T → ∀ U, IsEvolution (fun t ↦ H (t / T)) U 0 T → U T = Uend T) ∧
    (∀ T : ℕ, 0 < T → V T = evol Z (θ / 2) * step ω (θ / (2 * T)) ^ T) ∧
    (ω = π → Tendsto (fun k : ℕ ↦ ((2 * k + 1 : ℕ) : ℝ) *
      ‖V (2 * k + 1) - Uend (2 * k + 1)‖) atTop
      (𝓝 ((1 / (2 * π) - 1 / π ^ 2) *
        (‖derivWithin H (Icc (0 : ℝ) 1) 0‖ + ‖derivWithin H (Icc (0 : ℝ) 1) 1‖) *
        Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2))))) ∧
    (ω = 2 * π → (∀ T j : ℕ, evol (H (j / T)) 1 = -1) ∧
      Tendsto (fun T : ℕ ↦ ‖V T - Uend T‖) atTop (𝓝 (2 * |Real.sin (θ / 4)|))) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT U hU
    exact evolution_closed ω θ hT hU
  · intro T hT
    exact rounded_product_closed ω θ hT
  · intro hω
    subst ω
    rw [family_derivWithin_norm pi_pos.le θ (by constructor <;> norm_num),
      family_derivWithin_norm pi_pos.le θ (by constructor <;> norm_num),
      show π * |θ| / 2 + π * |θ| / 2 = π * |θ| by ring,
      ← odd_limit_factored]
    apply (odd_error_limit θ).congr'
    apply Eventually.of_forall
    intro k
    dsimp only
    rw [error_norm_frame π θ (T := 2 * k + 1) (by omega)]
  · intro hω
    subst ω
    exact ⟨fun T j ↦ full_turn_factor θ (j / T), full_turn_error_limit θ⟩


/-- The norm of the first derivative is constant throughout the spin path. -/
theorem familySlope_norm {ω : ℝ} (hω : 0 ≤ ω) (θ s : ℝ) :
    ‖familySlope ω θ s‖ = ω * |θ| / 2 := by
  rw [familySlope, norm_smul, norm_axis, mul_one, Real.norm_eq_abs,
    abs_div, abs_mul, abs_of_nonneg hω, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The supremum derivative norm is the same constant as its endpoint values. -/
theorem familySlope_supNorm {ω : ℝ} (hω : 0 ≤ ω) (θ : ℝ) :
    unitSupNorm (familySlope ω θ) = ω * |θ| / 2 := by
  unfold unitSupNorm
  have he : (fun s ↦ ‖familySlope ω θ s‖) '' Icc (0 : ℝ) 1 = {ω * |θ| / 2} := by
    ext r
    constructor
    · rintro ⟨s, _, rfl⟩
      exact familySlope_norm hω θ s
    · intro hr
      have hr' : r = ω * |θ| / 2 := hr
      exact ⟨0, by constructor <;> norm_num, (familySlope_norm hω θ 0).trans hr'.symm⟩
  rw [he, csSup_singleton]

/-- Every spin Hamiltonian has spectral width at most its field strength. -/
theorem family_width {ω : ℝ} (hω : 0 ≤ ω) (θ s : ℝ) (i j : Fin 2) :
    |(family_hermitian ω θ s).eigenvalues i - (family_hermitian ω θ s).eigenvalues j| ≤ ω := by
  have hnorm : ‖family ω θ s‖ = ω / 2 := by
    rw [family, norm_smul, norm_axis, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ω / 2)]
  have hi := spectrum.norm_le_norm_of_mem ((family_hermitian ω θ s).eigenvalues_mem_spectrum_real i)
  have hj := spectrum.norm_le_norm_of_mem ((family_hermitian ω θ s).eigenvalues_mem_spectrum_real j)
  rw [hnorm, Real.norm_eq_abs] at hi hj
  exact (abs_sub _ _).trans (by linarith)

/-- The jump contribution is quadratic in the angular speed, as asserted
in the optimality paragraph following Example 5.2. -/
theorem spin_jump_quadratic {ω w : ℝ} (hω : 0 ≤ ω) (hωw : ω ≤ w)
    (hw : w < 2 * π) (θ : ℝ) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.Icc 1 T, ‖paperClockJump (family ω θ) (familySlope ω θ) T j‖) ≤
      (1 / T : ℝ) *
        (Corrector.frameMult w * ω / 2 +
          (2 * deriv Corrector.frameMult w) * ω ^ 2 / 4) * θ ^ 2 := by
  have hj := (thm_jumps hT (family ω θ) (familySlope ω θ)
    (fun s _ ↦ family_hermitian ω θ s)
    (fun s _ ↦ (family_derivative ω θ s).hasDerivWithinAt)
    (fun s _ t _ ↦ family_derivative_lipschitz hω θ s t) hw
    (fun j _ i k ↦ (family_width hω θ (j / T) i k).trans hωw)).1
  rw [familySlope_supNorm hω] at hj
  convert hj using 1
  simp only [div_pow, mul_pow, sq_abs]
  ring

/-- Odd-resonant spins force the endpoint coefficient at every positive width.
The residual term contains exactly the Lipschitz and squared-derivative terms
from the unit-step comparison, both quadratic in the angular speed. -/
theorem precessing_spin_optimal {w c A B : ℝ} (hw : 0 < w) (hw2 : w < 2 * π)
    (hcomparison : ∀ (ω : ℝ) (T : ℕ), 0 < ω → ω < w → 0 < T → ∀ θ : ℝ,
      (T : ℝ) * ‖frameError ω θ T‖ ≤
        c * (‖familySlope ω θ 0‖ + ‖familySlope ω θ 1‖) +
        A * (ω * θ ^ 2 / 2) + B * unitSupNorm (familySlope ω θ) ^ 2) :
    1 / (2 * w * Real.sin (w / 2)) - 1 / w ^ 2 ≤ c := by
  apply endpoint_coefficient_optimal (E := fun ω T θ ↦ (T : ℝ) * ‖frameError ω θ T‖) hw hw2
  · intro ω T m hω hωw hT hodd
    exact precessing_spin_every_width hω (hωw.trans hw2) hT m hodd
  · intro ω T _ hω hωw hT _
    refine ⟨A * ω / 2 + B * ω ^ 2 / 4, Eventually.of_forall (fun θ ↦ ?_)⟩
    have hh := hcomparison ω T hω hωw hT θ
    rw [familySlope_norm hω.le, familySlope_norm hω.le, familySlope_supNorm hω.le] at hh
    convert hh using 1
    simp only [div_pow, mul_pow, sq_abs]
    ring


/-- The odd-runtime limit in Example 5.2(i) forces the endpoint coefficient
at width pi. The other terms, after multiplication by the runtime, are
quadratic in the angular speed and cannot reduce this linear coefficient. -/
theorem precessing_spin_pi_optimal {c K : ℝ}
    (hcomparison : ∀ (T : ℕ), 0 < T → ∀ θ : ℝ,
      (T : ℝ) * ‖frameError π θ T‖ ≤
        c * (‖familySlope π θ 0‖ + ‖familySlope π θ 1‖) + K * θ ^ 2) :
    1 / (2 * π) - 1 / π ^ 2 ≤ c := by
  let a := 1 / (2 * π) - 1 / π ^ 2
  have hlinear (θ : ℝ) : a * (π * |θ|) ≤ c * π * |θ| + K * θ ^ 2 := by
    have hlimit := le_of_tendsto (odd_error_limit θ)
      (Eventually.of_forall (fun k : ℕ ↦ hcomparison (2 * k + 1) (by omega) θ))
    rw [familySlope_norm pi_pos.le, familySlope_norm pi_pos.le,
      show π * |θ| / 2 + π * |θ| / 2 = π * |θ| by ring,
      odd_limit_factored] at hlimit
    have hnonneg : 0 ≤ a * (π * |θ|) := by
      have he : a * (π * |θ|) = (π - 2) * |θ| / (2 * π) := by
        dsimp [a]
        field_simp
      rw [he]
      exact div_nonneg (mul_nonneg (by linarith [pi_gt_three]) (abs_nonneg _))
        (by positivity)
    have hroot : 1 ≤ Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
        (show (1 : ℝ) ≤ 1 + θ ^ 2 / (4 * (π - 2) ^ 2) from
          le_add_of_nonneg_right (by positivity))
    calc
      a * (π * |θ|) ≤ a * (π * |θ|) *
          Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2)) := le_mul_of_one_le_right hnonneg hroot
      _ ≤ c * π * |θ| + K * θ ^ 2 := by simpa only [mul_assoc] using hlimit
  apply linear_coefficient_le_of_quadratic_error (E := fun θ ↦ a * (π * |θ|)) pi_pos
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hne : θ ≠ 0 := hθ
    dsimp [a]
    field_simp [pi_ne_zero, abs_ne_zero.mpr hne]
  · exact Eventually.of_forall hlinear

end UnitaryProducts.PaperProof.Spin
