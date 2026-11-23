/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinSpecialization

/-! The finite telescoping in the second opening display of Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction for the exponential group law. -/
local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- Adjacent rotations combine in the telescope of the sampled factors. -/
theorem frame_add (A : Matrix (Fin 2) (Fin 2) ℂ) (s t : ℝ) :
    exp (s • A) * exp (t • A) = exp ((s + t) • A) := by
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl A).smul_left s).smul_right t)]

/-- The conjugated sample factors telescope to one endpoint rotation and a power. -/
theorem sampled_product (A B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    ((List.range n).reverse.map fun j : ℕ ↦
      exp ((j : ℝ) • A) * B * exp (-((j : ℝ) • A))).prod =
      exp ((n : ℝ) • A) * (exp (-A) * B) ^ n := by
  induction n with
  | zero => simp only [List.range_zero, List.reverse_nil, List.map_nil, List.prod_nil,
      Nat.cast_zero, zero_smul, NormedSpace.exp_zero, pow_zero, mul_one]
  | succ n ih =>
    have hcancel := rotating_frame_cancel A (n : ℝ)
    have hjoin : exp (((n + 1 : ℕ) : ℝ) • A) * exp (-A) = exp ((n : ℝ) • A) := by
      rw [show -A = (-1 : ℝ) • A by simp only [neg_one_smul], frame_add]
      congr 1
      push_cast
      ring_nf
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_append,
      List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih, pow_succ']
    simp only [mul_assoc]
    rw [← mul_assoc (exp (-((n : ℝ) • A))), hcancel, one_mul,
      ← mul_assoc (exp (((n + 1 : ℕ) : ℝ) • A)), hjoin]

/-- Conjugating the power by the half-step produces the symmetric factor S. -/
theorem symmetrized_power (A B : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    exp B * (exp A * exp (B + B)) ^ n * exp (-B) =
      (exp B * exp A * exp B) ^ n := by
  have hleft : exp (-B) * exp B = 1 := by
    simpa only [one_smul] using rotating_frame_cancel B 1
  have hright : exp B * exp (-B) = 1 := by
    simpa only [one_smul, neg_neg] using rotating_frame_cancel (-B) 1
  let u : (Matrix (Fin 2) (Fin 2) ℂ)ˣ := ⟨exp B, exp (-B), hright, hleft⟩
  have hconj : exp B * (exp A * exp (B + B)) * exp (-B) =
      exp B * exp A * exp B := by
    rw [NormedSpace.exp_add_of_commute (Commute.refl B)]
    simp only [mul_assoc]
    rw [hright, mul_one]
  have hpower := u.conj_pow (exp A * exp (B + B)) n
  change (exp B * (exp A * exp (B + B)) * exp (-B)) ^ n =
    exp B * (exp A * exp (B + B)) ^ n * exp (-B) at hpower
  rw [hconj] at hpower
  exact hpower.symm

end RoundedClocks.PrecessingSpin
