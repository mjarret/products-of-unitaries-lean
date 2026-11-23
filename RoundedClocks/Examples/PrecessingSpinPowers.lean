/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinAxisLimit

/-! The powered axes and exponential splitting in Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction for the exponential addition and power formulas. -/
local instance poweredAxisNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- Example 5.2, second norm line: an involution raised to an odd power is itself. -/
theorem odd_power_axis (N : Matrix (Fin 2) (Fin 2) ℂ)
    (hNN : N * N = 1) (T : ℕ) (hT : Odd T) : N ^ T = N := by
  obtain ⟨k, rfl⟩ := hT
  rw [pow_succ, pow_mul, pow_two, hNN,
    one_pow, one_mul]

/-- Example 5.2, second norm line: the trigonometric axis satisfies N^T = N. -/
theorem N_odd_power (θ : ℝ) (T : ℕ) (hT : Odd T) :
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    N ^ T = N := by
  dsimp only
  apply odd_power_axis _ _ T hT
  rw [sub_eq_add_neg, ← neg_smul, xz_square, neg_sq,
    Real.cos_sq_add_sin_sq, one_smul]

/-- Example 5.2's normalized axis M is a Hermitian involution. -/
theorem M_involution (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    M.IsHermitian ∧ M * M = 1 := by
  intro ρ M
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have he : M = Real.cos (Real.arctan (θ / (Real.pi * T))) • X -
      Real.sin (Real.arctan (θ / (Real.pi * T))) • Z := by
    dsimp only [M, ρ]
    rw [show 2 * (Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2) =
        Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) by ring,
      show Real.pi ^ 2 * (T : ℝ) ^ 2 = (Real.pi * T) ^ 2 by ring]
    exact normalized_axis_angle (mul_pos Real.pi_pos ht) θ
  rw [he, sub_eq_add_neg, ← neg_smul]
  refine ⟨xz_hermitian _ _, ?_⟩
  rw [xz_square, neg_sq, Real.cos_sq_add_sin_sq, one_smul]

/-- Example 5.2, second norm line: the normalized axis satisfies M^T = M. -/
theorem M_odd_power (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    M ^ T = M := by
  exact odd_power_axis _ (M_involution θ T hT).2 T hodd

/-- Example 5.2, first norm line: split off T half turns from exp(-iρM). -/
theorem axis_exp_split (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) (hMM : M * M = 1) (ρ : ℝ) (T : ℕ) :
    let ζ := ρ - Real.pi * T / 2
    exp ((-I * (ρ : ℂ)) • M) =
      ((-I) • M) ^ T * exp ((-I * (ζ : ℂ)) • M) := by
  dsimp only
  have hhalf : exp ((-I * ((Real.pi / 2 : ℝ) : ℂ)) • M) = (-I) • M := by
    rw [exp_involution M hM hMM, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [Complex.ofReal_zero, zero_smul, Complex.ofReal_one, mul_one,
      zero_sub, neg_smul]
  have hsum : (-I * (ρ : ℂ)) • M =
      T • ((-I * ((Real.pi / 2 : ℝ) : ℂ)) • M) +
        (-I * ((ρ - Real.pi * T / 2 : ℝ) : ℂ)) • M := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [hsum, NormedSpace.exp_add_of_commute, NormedSpace.exp_nsmul, hhalf]
  exact (((Commute.refl M).smul_left _).smul_right _).smul_left T

/-- Example 5.2, second norm line: M exp(-iζM) = cos ζ M - i sin ζ. -/
theorem axis_mul_exp (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) (hMM : M * M = 1) (ζ : ℝ) :
    M * exp ((-I * (ζ : ℂ)) • M) =
      (Real.cos ζ : ℂ) • M - (I * Real.sin ζ) • 1 := by
  rw [exp_involution M hM hMM, mul_sub, mul_smul_comm, mul_one,
    mul_smul_comm, hMM]

/-- Example 5.2: the four powered-axis identities with the manuscript's N, ρ, M, ζ. -/
theorem powered_axis_displays (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
    let N := Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z
    let ρ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := (2 * ρ)⁻¹ • ((Real.pi * T) • X - θ • Z)
    let ζ := ρ - Real.pi * T / 2
    N ^ T = N ∧ M ^ T = M ∧
      exp ((-I * (ρ : ℂ)) • M) =
        ((-I) • M) ^ T * exp ((-I * (ζ : ℂ)) • M) ∧
      M * exp ((-I * (ζ : ℂ)) • M) =
        (Real.cos ζ : ℂ) • M - (I * Real.sin ζ) • 1 := by
  have hM := M_involution θ T hT
  exact ⟨N_odd_power θ T hodd, M_odd_power θ T hT hodd,
    axis_exp_split _ hM.1 hM.2 _ T, axis_mul_exp _ hM.1 hM.2 _⟩

end RoundedClocks.PrecessingSpin
