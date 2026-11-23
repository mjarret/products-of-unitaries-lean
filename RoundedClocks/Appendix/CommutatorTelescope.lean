/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueDerivative

/-! # Infinite commutator telescope

Lemma A.3 extends the finite insertion identity to the infinite commutator series and obtains the
derivative formula for the endpoint multiplier.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The insertion series defining the manuscript's `𝓕`, with fixed final input `D`. -/
def endValue_F (Ω B D : 𝕄) : 𝕄 :=
  ∑' n : ℕ, (multiplierCoeff n : ℂ) • (powDeriv (adL Ω) (adL B) n) D

/-- The insertion series is absolutely convergent inside the multiplier radius. -/
theorem endValue_summable_F [NeZero d] (Ω B D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      (multiplierCoeff n : ℂ) • (powDeriv (adL Ω) (adL B) n) D) := by
  exact (endValue_summable_norm_insertion (Ω := Ω) (B := B) (A := D)
    (w := ‖adL Ω‖) multiplierCoeff_nonneg (norm_nonneg (adL Ω)) le_rfl
    (summable_multiplierCoeff_deriv (norm_nonneg (adL Ω)) ha)).of_norm

/-- The absolutely convergent series is additive in its direction. -/
theorem endValue_F_add [NeZero d] (Ω B C D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    endValue_F Ω (B + C) D = endValue_F Ω B D + endValue_F Ω C D := by
  have hadd : adL (B + C) = adL B + adL C :=
    (endValue_adLCLM (d := d)).map_add B C
  simp only [endValue_F, hadd, powDeriv_add, ContinuousLinearMap.add_apply, smul_add]
  exact (endValue_summable_F Ω B D ha).tsum_add (endValue_summable_F Ω C D ha)

/-- Degree zero vanishes, and Jacobi telescopes every remaining insertion sum. -/
theorem endValue_F_commutator_series [NeZero d] (Ω Λ D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    endValue_F Ω (adL Ω Λ) D = ∑' n : ℕ,
      (multiplierCoeff (n + 1) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL Λ D) - adL Λ ((adL Ω ^ (n + 1)) D)) := by
  rw [endValue_F, (endValue_summable_F Ω (adL Ω Λ) D ha).tsum_eq_zero_add]
  have hz : powDeriv (adL Ω) (adL (adL Ω Λ)) 0 = 0 := by simp [powDeriv]
  rw [hz, ContinuousLinearMap.zero_apply, smul_zero, zero_add]
  apply tsum_congr
  intro n
  rw [endValue_insertion_commutator]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]

end RoundedClocks
