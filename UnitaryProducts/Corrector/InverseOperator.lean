/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.Commutator

/-!
# Commuting power series and the bound on $\Phi^{-1}$

## Declarations

- `bernSeries_mul_psiSeries`
- `norm_bernSeries_le_of_le`
-/

@[expose] public section

open Real

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The correction map, with the inverse applied on the left. -/
theorem bernSeries_mul_psiSeries (a : A) (ha : ‖a‖ < 2 * π) :
    bernSeries a * psiSeries a = corrSeries a := by
  rw [corrSeries_eq_psiSeries_mul_bernSeries a ha]; exact mul_comm_tsum_pow _ _ a

omit [CompleteSpace A] in
/-- The dimension-free bound on `Φ⁻¹`, in terms of an upper bound `w` for `‖a‖`. -/
theorem norm_bernSeries_le_of_le {a : A} {w : ℝ} (haw : ‖a‖ ≤ w) (hw : w < 2 * π) :
    ‖bernSeries a‖ ≤ ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * w ^ n / (Nat.factorial n) := by
  exact (norm_bernSeries_le a (haw.trans_lt hw)).trans (Summable.tsum_le_tsum (fun n ↦ by gcongr)
    (summable_bernoulli_majorant (norm_nonneg a) (haw.trans_lt hw))
    (summable_bernoulli_majorant ((norm_nonneg a).trans haw) hw))

end UnitaryProducts.Corrector

