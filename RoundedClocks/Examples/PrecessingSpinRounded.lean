/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinTelescope

/-! The second opening display of Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Example 5.2: the rounded endpoint is the rotating frame times the symmetric power. -/
theorem rounded_endpoint (dieudonne_10_5_4 : Dieudonne_10_5_4) (ω θ : ℝ) {T : ℕ}
    (hT : 1 ≤ T) :
    let H := fun s : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    let S := exp (-(ω / 4 * I) • X) * exp ((θ / (2 * T) * I) • Z) *
      exp (-(ω / 4 * I) • X)
    roundedEvolution H T T = exp (-(θ / 2 * I) • Z) * S ^ T := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := -(θ / (2 * T) * I) • Z
  let B : Matrix (Fin 2) (Fin 2) ℂ := -(ω / 4 * I) • X
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hsample (j : ℕ) :
      -(θ * ((j : ℝ) / T : ℝ) / 2 * I) • Z = (j : ℝ) • A := by
    dsimp only [A]
    ext i k
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have hwhole : (T : ℝ) • A = -(θ / 2 * I) • Z := by
    dsimp only [A]
    ext i k
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp [hTc]
  have hdouble : (-I * (ω / 2 : ℝ)) • X = B + B := by
    dsimp only [B]
    ext i k
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    push_cast
    ring
  have hprod : stepProduct (fun s : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))) T =
      exp ((T : ℝ) • A) * (exp (-A) * exp (B + B)) ^ T := by
    unfold stepProduct sampleProduct
    simp_rw [sampled_factor, hdouble]
    have hpos (j : ℕ) :
        (θ * ((j : ℝ) / T : ℝ) / 2 * I) • Z = -((j : ℝ) • A) := by
      rw [← hsample, neg_smul, neg_neg]
    simp_rw [hsample, hpos]
    exact sampled_product A (exp (B + B)) T
  have hphase :
      exp (-(I / 2) • ((ω / 2 : ℝ) •
        (exp (-(θ * 1 / 2 * I) • Z) * X * exp ((θ * 1 / 2 * I) • Z)))) =
      exp ((T : ℝ) • A) * exp B * exp (-((T : ℝ) • A)) := by
    rw [hwhole]
    have hscalar : -(I / 2) • ((ω / 2 : ℝ) • X) = B := by
      ext i k
      simp only [B, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    have hgen : -(I / 2) • ((ω / 2 : ℝ) •
        (exp (-(θ * 1 / 2 * I) • Z) * X * exp ((θ * 1 / 2 * I) • Z))) =
        exp (-(θ / 2 * I) • Z) * B * exp (-(-(θ / 2 * I) • Z)) := by
      rw [← hscalar]
      simp only [mul_one]
      rw [show -(-(θ / 2 * I) • Z) = (θ / 2 * I) • Z by
        rw [neg_smul, neg_neg]]
      rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    rw [hgen, rotating_frame_sample]
  have hzero :
      exp ((I / 2) • ((ω / 2 : ℝ) •
        (exp (-(θ * 0 / 2 * I) • Z) * X * exp ((θ * 0 / 2 * I) • Z)))) =
      exp (-B) := by
    congr 1
    simp only [mul_zero, zero_div, zero_mul, neg_zero]
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
    rw [show -B = (ω / 4 * I) • X by simp only [B, neg_smul, neg_neg]]
    ext i k
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  dsimp only
  rw [rounded_endpoint_phases dieudonne_10_5_4 ω θ hT, hprod]
  simp only [Complex.ofReal_one, Complex.ofReal_zero]
  rw [hphase, hzero]
  have hcancel := rotating_frame_cancel A (T : ℝ)
  simp only [mul_assoc]
  rw [← mul_assoc (exp (-((T : ℝ) • A))), hcancel, one_mul]
  rw [← mul_assoc (exp B), symmetrized_power, hwhole]
  simp only [A, B, neg_smul, neg_neg, mul_assoc]

end RoundedClocks.PrecessingSpin
