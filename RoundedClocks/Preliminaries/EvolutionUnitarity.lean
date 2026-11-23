/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Regulated

/-! # The solution of Schrödinger's equation is unitary

Section 2, after equation (2.1): "The solution `V` is unitary as `G` is Hermitian." Outside a
countable set `(V†V)' = 0`, and `V(a)†V(a) = 1`, so `V†V = 1` by the uniqueness theorem,
Dieudonné (10.5.4).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Assuming Dieudonné (10.5.4), let `G(t)` with `t ∈ [a,b]` be a Hermitian family. A continuous
`V` with `V(a) = 1` and `i V' = G V` for all but countably many `t` is unitary, so `G` generates
`V`. -/
theorem generates_of_hermitian_solution
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    {G V : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b)
    (hG : IsHermitianFamily G a b)
    (hV : SolvesLinearMatrixODE (fun t ↦ -I • G t) (fun _ ↦ 0)
      1 V a a b) : Generates G V a b := by
  obtain ⟨hVc, hVa, S, hS, hVd⟩ := hV
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (htS : t ∉ S) :
      HasDerivWithinAt V (-I • (G t * V t)) (Icc a b) t := by
    simpa only [add_zero, smul_mul_assoc] using hVd t ht htS
  -- The function `V†V` is continuous and equals `1` at `a`.
  let VV : ℝ → 𝕄 := fun t ↦ (V t)† * V t
  have hVVc : ContinuousOn VV (Icc a b) := hVc.star.mul hVc
  have hVVa : VV a = 1 := by simp [VV, hVa]
  -- Outside `S`, `(V†V)' = (V†)'V + V†V' = iV†GV - iV†GV = 0`, as `G` is Hermitian.
  have hVVd (t : ℝ) (ht : t ∈ Icc a b) (htS : t ∉ S) :
      HasDerivWithinAt VV 0 (Icc a b) t := by
    have hVt := hderiv t ht htS
    have hadjoint : HasDerivWithinAt (fun s ↦ (V s)†)
        (I • ((V t)† * G t)) (Icc a b) t := by
      simpa [show (G t)† = G t from (hG ht).star_eq, Complex.star_def] using hVt.star
    have hcancel :
        (I • ((V t)† * G t)) * V t + (V t)† * (-I • (G t * V t)) = 0 := by
      calc
        _ = I • ((V t)† * G t * V t) - I • ((V t)† * G t * V t) := by
          simp only [smul_mul_assoc, mul_smul_comm, mul_assoc, neg_smul, mul_neg,
            sub_eq_add_neg]
        _ = 0 := sub_self _
    simpa only [hcancel] using hadjoint.mul hVt
  -- Both `V†V` and the constant `1` solve `X' = 0` with `X(a) = 1`.
  have hVV : SolvesLinearMatrixODE (fun _ ↦ 0) (fun _ ↦ 0) 1 VV a a b := by
    refine ⟨hVVc, hVVa, S, hS, ?_⟩
    intro t ht htS
    simpa only [zero_mul, zero_add] using hVVd t ht htS
  have hOne : SolvesLinearMatrixODE (fun _ ↦ 0) (fun _ ↦ 0)
      (1 : 𝕄) (fun _ ↦ 1) a a b := by
    refine ⟨continuousOn_const, rfl, S, hS, ?_⟩
    intro t _ _
    simpa only [zero_mul, zero_add] using
      (hasDerivWithinAt_const t (Icc a b) (1 : 𝕄))
  -- By the uniqueness theorem, Dieudonné (10.5.4), `V†V = 1`.
  have hVV_eq : EqOn VV (fun _ ↦ 1) (Icc a b) :=
    dieudonne_10_5_4 d (fun _ ↦ 0) (fun _ ↦ 0) 1 VV (fun _ ↦ 1) a b
      hab (isRegulated_const 0 a b) (isRegulated_const 0 a b) hVV hOne
  exact ⟨hVc, hVa, fun t ht ↦ Matrix.mem_unitaryGroup_iff'.mpr (hVV_eq ht), S, hS, hderiv⟩

end RoundedClocks
