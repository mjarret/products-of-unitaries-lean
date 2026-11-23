/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinPowers
public import RoundedClocks.Examples.PrecessingSpinRounded
public import RoundedClocks.Examples.PrecessingSpinDerivative

/-! The second and third residual norm displays of Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Example 5.2: substituting ω = π in the symmetric step gives `S = -iN`. -/
theorem symmetric_step_eq_neg_I_N (θ : ℝ) (T : ℕ) :
    let S := exp (-((Real.pi : ℂ) / 4 * I) • X) *
      exp ((θ / (2 * T) * I) • Z) * exp (-((Real.pi : ℂ) / 4 * I) • X)
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    S = (-I) • N := by
  have hquarter : -((Real.pi : ℂ) / 4 * I) =
      -I * ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hangle : (θ : ℂ) / (2 * T) * I = I * ((θ / (2 * T) : ℝ) : ℂ) := by
    push_cast
    ring
  dsimp only
  rw [hquarter, hangle]
  exact half_turn_step (θ / (2 * T))

/-- Example 5.2, first residual display: remove the common rotating frame. -/
theorem endpoint_residual_norm (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
    let H := fun s : ℝ ↦ (Real.pi / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    let ζ := ρ - Real.pi * T / 2
    evolution H T T = exp (-(θ / 2 * I) • Z) *
      exp ((-I / 2) • ((Real.pi * T) • X - θ • Z)) →
    roundedEvolution H T T = exp (-(θ / 2 * I) • Z) *
      (exp (-(Real.pi / 4 * I) • X) * exp ((θ / (2 * T) * I) • Z) *
        exp (-(Real.pi / 4 * I) • X)) ^ T →
    ‖roundedEvolution H T T - evolution H T T‖ =
      ‖((-I) • N) ^ T - ((-I) • M) ^ T * exp ((-I * (ζ : ℂ)) • M)‖ := by
  intro H N ρ M ζ hcont hround
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hρ : ρ ≠ 0 := by dsimp [ρ]; positivity
  have hgen : (-I / 2) • ((Real.pi * T) • X - θ • Z) =
      (-I * (ρ : ℂ)) • M := by
    ext i j
    simp only [M, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    have hc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
    field_simp [hc]
  have hframe : exp (-(θ / 2 * I) • Z) ∈
      unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [one_smul] using derivative_frame_unitary θ 1
  have hstep := symmetric_step_eq_neg_I_N θ T
  have hsplit := (powered_axis_displays θ T hT hodd).2.2.1
  change ‖roundedEvolution H T T - evolution H T T‖ = _
  rw [hround, hcont, hstep, hgen, hsplit, ← mul_sub]
  exact CStarRing.norm_mem_unitary_mul _ hframe

/-- Example 5.2, second residual display: cancel the common scalar odd power. -/
theorem powered_residual_norm (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    let ζ := ρ - Real.pi * T / 2
    ‖((-I) • N) ^ T - ((-I) • M) ^ T * exp ((-I * (ζ : ℂ)) • M)‖ =
      ‖N - (Real.cos ζ : ℂ) • M + (I * Real.sin ζ) • 1‖ := by
  dsimp only
  obtain ⟨hN, hM, _, hExp⟩ := powered_axis_displays θ T hT hodd
  rw [smul_pow, smul_pow, hN, hM, smul_mul_assoc, ← smul_sub, hExp,
    norm_smul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  ring

/-- Example 5.2, third residual display: apply the adjoint-square formula to A. -/
theorem residual_sqrt_norm (θ : ℝ) (T : ℕ) :
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    let ζ := ρ - Real.pi * T / 2
    ‖N - (Real.cos ζ : ℂ) • M + (I * Real.sin ζ) • 1‖ =
      Real.sqrt (‖N - (Real.cos ζ : ℂ) • M‖ ^ 2 + Real.sin ζ ^ 2) := by
  intro N ρ M ζ
  let a := Real.cos (θ / (2 * T)) - Real.cos ζ * (2 * ρ)⁻¹ * (Real.pi * T)
  let b := -Real.sin (θ / (2 * T)) + Real.cos ζ * (2 * ρ)⁻¹ * θ
  have hA : N - (Real.cos ζ : ℂ) • M = a • X + b • Z := by
    ext i j
    simp only [N, M, a, b, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  rw [hA]
  exact xz_imaginary_norm a b (Real.sin ζ)

end RoundedClocks.PrecessingSpin
