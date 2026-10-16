/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# Half steps and frozen comparisons for the rounded clock

## Declarations

- `norm_sub_evol_mul_le_integral`
- `pieceProduct_one_eq_half_mul`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set UnitaryProducts.Corrector Real Complex MeasureTheory

namespace UnitaryProducts
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Comparison with a constant generator, integral form.**  If `U` solves `i U' = K U` on
`[a, b]`, then `‖U(b) - e^{-i(b-a)G} U(a)‖ ≤ ∫ₐᵇ ‖K - G‖`. -/
theorem SolvesSchrodinger.norm_sub_evol_mul_le_integral {K U : ℝ → 𝕄} {G : 𝕄} {a b : ℝ}
    (hU : SolvesSchrodinger K U a b) (hab : a ≤ b) (hG : G.IsHermitian)
    (hKc : ContinuousOn K (Icc a b)) (hKh : ∀ t ∈ Icc a b, (K t).IsHermitian)
    (hUa : ‖U a‖ ≤ 1) :
    ‖U b - evol G (b - a) * U a‖ ≤ ∫ t in a..b, ‖K t - G‖ := by
  obtain ⟨W, hW, hW0⟩ := exists_solvesSchrodinger hKc
  have hV : SolvesSchrodinger (fun _ ↦ G) (fun t ↦ evol G (t - a)) a b := fun t _ ↦ by
    simpa only [Function.comp_def, id_eq, one_smul, smul_mul_assoc] using
      ((hasDerivAt_evol G (t - a)).scomp t ((hasDerivAt_id t).sub_const a)).hasDerivWithinAt
  simpa only [hU.eq_mul hKc hW hW0 b (right_mem_Icc.mpr hab), ← sub_mul, mul_one] using
    norm_mul_le_of_le (hW.norm_sub_le_integral_sub hKc continuousOn_const hKh (fun _ _ ↦ hG) hV
      hW0 (by simp [evol_zero]) (right_mem_Icc.mpr hab)) hUa

/-- The unit-step product equals the product whose first step is halved, times the other half
step $e^{-iH_0/2}$ on the right: the half-step phase of (2.5) (`eq:rounded`) at unit steps. -/
theorem pieceProduct_one_eq_half_mul (h : ℕ → 𝕄) (n : ℕ) :
    pieceProduct (fun _ ↦ 1) h (n + 1)
      = pieceProduct (fun j ↦ if j = 0 then 1 / 2 else 1) h (n + 1) * evol (h 0) (1 / 2) := by
  induction n with
  | zero => norm_num [pieceProduct, ← evol_add]
  | succ n ih =>
    rw [pieceProduct.eq_2 (fun _ ↦ 1) h (n + 1), ih, pieceProduct.eq_2 _ _ (n + 1),
      if_neg (Nat.succ_ne_zero n), mul_assoc]

end UnitaryProducts
