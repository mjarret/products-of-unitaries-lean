/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinFrame

/-! The two opening endpoint identities in Example 5.2. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)
open Set Matrix

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction for the exponential group laws. -/
local instance : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- The unitary exponential used in the rotating frame of Example 5.2. -/
theorem frame_unitary (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.IsHermitian)
    (t : ℝ) : IsUnitary (exp (t • (-I • P))) := by
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact Unitary.star_mul_self_of_mem (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem t (hP.isSelfAdjoint.smul_mem_skewAdjoint hI)))

/-- The rotating-frame product solves the equation in the first opening display. -/
theorem frame_generates (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (T : ℝ) :
    Generates
      (fun t : ℝ ↦ exp (t • (-I • P)) * Q * exp (-(t • (-I • P))))
      (fun t : ℝ ↦ exp (t • (-I • P)) * exp (t • (-I • (Q - P)))) 0 T := by
  have hd (t : ℝ) := rotating_frame_derivative (-I • P) (-I • Q) t
  simp only [← smul_sub] at hd
  refine ⟨?_, ?_, ?_, ∅, Set.countable_empty, ?_⟩
  · exact (continuous_iff_continuousAt.mpr fun t ↦ (hd t).continuousAt).continuousOn
  · simp only [zero_smul, NormedSpace.exp_zero, one_mul]
  · intro t _
    have hU := frame_unitary P hP t
    have hV := frame_unitary (Q - P) (hQ.sub hP) t
    change star (_ * _) * (_ * _) = 1
    rw [Matrix.star_mul, mul_assoc, ← mul_assoc (star (exp (t • (-I • P)))), hU,
      one_mul]
    exact hV
  · intro t _ _
    have hcancel := rotating_frame_cancel (-I • P) t
    have heq : -I • ((exp (t • (-I • P)) * Q * exp (-(t • (-I • P)))) *
        (exp (t • (-I • P)) * exp (t • (-I • (Q - P))))) =
        exp (t • (-I • P)) * (-I • Q) * exp (t • (-I • (Q - P))) := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (exp (-(t • (-I • P)))), hcancel,
        one_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [heq]
    exact (hd t).hasDerivWithinAt

/-- Cited uniqueness identifies the rotating-frame expression with the canonical evolution. -/
theorem frame_evolution (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (P Q : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    {T : ℝ} (hT : 0 ≤ T) :
    evolutionOf (fun t : ℝ ↦ exp (t • (-I • P)) * Q * exp (-(t • (-I • P)))) T T =
      exp (T • (-I • P)) * exp (T • (-I • (Q - P))) := by
  let G := fun t : ℝ ↦ exp (t • (-I • P)) * Q * exp (-(t • (-I • P)))
  have hGc : Continuous G := by unfold G; fun_prop
  have hreg : IsRegulated G 0 T := comparison_continuous_regulated hGc.continuousOn
  have hPs : star P = P := hP
  have hQs : star Q = Q := hQ
  have hHerm : IsHermitianFamily G 0 T := by
    intro t _
    have hstar : star (t • (-I • P)) = -(t • (-I • P)) := by
      rw [star_smul, star_smul, star_neg, Complex.star_def, Complex.conj_I,
        hPs, star_trivial, neg_neg, neg_smul, smul_neg, neg_neg]
    change star (G t) = G t
    dsimp only [G]
    rw [Matrix.star_mul, Matrix.star_mul, NormedSpace.star_exp, NormedSpace.star_exp,
      star_neg, hstar, neg_neg, hQs, mul_assoc]
  have hcanonical := generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3 hT hreg hHerm
  exact generates_unique dieudonne_10_5_4 hreg hcanonical
    (frame_generates P Q hP hQ T) ⟨hT, le_rfl⟩

end RoundedClocks.PrecessingSpin
