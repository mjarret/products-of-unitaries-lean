/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinEndpoints

/-! Specialization of the opening rotating-frame display in Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar normalization in the rotating frame of the first opening display. -/
theorem frame_scalar (a t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    t • (-I • (a • A)) = (-(a * t : ℂ) * I) • A := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- Dieudonné uniqueness gives the first display of Example 5.2. -/
theorem continuous_endpoint (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (ω θ : ℝ) {T : ℝ} (hT : 0 < T) :
    let H := fun s : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    evolution H T T = exp (-(θ / 2 * I) • Z) *
      exp ((-I / 2) • ((ω * T) • X - θ • Z)) := by
  dsimp only
  have hP : ((θ / (2 * T)) • Z).IsHermitian :=
    (show IsSelfAdjoint (θ / (2 * T)) from rfl).smul
      matrix_relations.2.1.isSelfAdjoint
  have hQ : ((ω / 2) • X).IsHermitian :=
    (show IsSelfAdjoint (ω / 2) from rfl).smul matrix_relations.1.isSelfAdjoint
  have h := frame_evolution dieudonne_10_5_4 dieudonne_10_6_3
    ((θ / (2 * T)) • Z) ((ω / 2) • X) hP hQ hT.le
  have hfamily :
      (fun t : ℝ ↦ (ω / 2 : ℝ) •
        (exp (-(θ * ((t / T : ℝ) : ℂ) / 2 * I) • Z) * X *
          exp ((θ * ((t / T : ℝ) : ℂ) / 2 * I) • Z))) =
      (fun t : ℝ ↦ exp (t • (-I • ((θ / (2 * T)) • Z))) *
        ((ω / 2) • X) * exp (-(t • (-I • ((θ / (2 * T)) • Z))))) := by
    funext t
    rw [frame_scalar, ← smul_mul_assoc, ← mul_smul_comm]
    have hc : (-(((θ / (2 * T) : ℝ) : ℂ) * t) * I) = -(θ * ((t / T : ℝ) : ℂ) / 2 * I) := by
      push_cast
      ring
    rw [hc, neg_smul, neg_neg]
  change evolutionOf _ T T = _
  rw [hfamily, h, frame_scalar]
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  congr 1
  · congr 1
    congr 1
    push_cast
    field_simp [hTc]
  · congr 1
    ext i j
    simp only [smul_sub, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul]
    push_cast
    field_simp [hTc]
    ring

/-- The factors following the opening displays are conjugated constant exponentials. -/
theorem sampled_factor (ω θ s : ℝ) :
    exp (-I • ((ω / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z)))) =
      exp (-(θ * s / 2 * I) • Z) * exp ((-I * (ω / 2 : ℝ)) • X) *
        exp ((θ * s / 2 * I) • Z) := by
  have hneg : -(-(θ * s / 2 * I) • Z) = (θ * s / 2 * I) • Z := by
    rw [neg_smul, neg_neg]
  have hscalar : -I • ((ω / 2 : ℝ) • X) = (-I * (ω / 2 : ℝ)) • X := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  have hmove (R V : Matrix (Fin 2) (Fin 2) ℂ) :
      -I • ((ω / 2 : ℝ) • (R * X * V)) = R * ((-I * (ω / 2 : ℝ)) • X) * V := by
    rw [← hscalar, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  rw [hmove, ← hneg]
  exact rotating_frame_sample _ _

/-- Equation (2.5) supplies the endpoint phases before the sample factors telescope. -/
theorem rounded_endpoint_phases (dieudonne_10_5_4 : Dieudonne_10_5_4) (ω θ : ℝ) {T : ℕ}
    (hT : 1 ≤ T) :
    let H := fun s : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    roundedEvolution H T T =
      exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) := by
  dsimp only
  apply roundedEvolution_end dieudonne_10_5_4 _ hT
  intro s _
  apply (show IsSelfAdjoint (ω / 2 : ℝ) from rfl).smul
  have hZ : star Z = Z := matrix_relations.2.1
  have hX : star X = X := matrix_relations.1
  change star (_ * _ * _) = _
  simp only [Matrix.star_mul, NormedSpace.star_exp, star_smul, hZ, hX,
    Complex.star_def, map_neg, map_mul, map_div₀, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat, mul_neg, neg_neg]
  rw [mul_assoc]

end RoundedClocks.PrecessingSpin
