/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Evolution.DuhamelIntegral
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Evolution.RegulatedExistence
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative
public import UnitaryProducts.Corrector.PowerSeries

/-!
# Duhamel's estimate for regulated families

## Declarations

- `intervalIntegrable_on`
- `translate_to_zero`
- `norm_sub_le_integral_sub_of_regulated`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set Filter MeasureTheory
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace Regulated

/-- Translating $[a,b]$ to $[0, b - a]$ preserves regulatedness. -/
theorem translate_to_zero {H : ℝ → 𝕄} {a b : ℝ}
    (hH : Regulated H a b) : Regulated (fun t ↦ H (t + a)) 0 (b - a) := by
  refine ⟨fun t ht ↦ (hH.1 (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩).imp fun L hL ↦ ?_,
    fun t ht ↦ (hH.2 (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩).imp fun L hL ↦ ?_⟩ <;>
  exact hL.comp ((continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin
    (fun _ hx ↦ add_lt_add_left hx a))

/-- A regulated family on $[a,b]$ is integrable there; this makes the integrals of Theorem 2.2
genuine. -/
theorem intervalIntegrable_on {H : ℝ → 𝕄} {a b : ℝ}
    (hH : Regulated H a b) (hab : a ≤ b) : IntervalIntegrable H volume a b := by
  have hi := (hH.translate_to_zero.intervalIntegrable (sub_nonneg.mpr hab)).comp_add_right (-a)
  simpa only [zero_sub, neg_neg, sub_neg_eq_add, sub_add_cancel, neg_add_cancel_right, zero_add]
    using hi

end Regulated

/-- Duhamel's estimate (2.3) for regulated generators $H$, $G$: the integrability of
$\|H - G\|$ follows from regulatedness. Used by `duhamel` (equation (2.3)). -/
theorem norm_sub_le_integral_sub_of_regulated {H G U V : ℝ → 𝕄} {a b : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b)
    (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hU : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U (-I • (H t * U t)) (Icc a b) t)
    (hV : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt V (-I • (G t * V t)) (Icc a b) t)
    (hUU : ∀ t ∈ Icc a b, star (U t) * U t = 1)
    (hVV : ∀ t ∈ Icc a b, star (V t) * V t = 1)
    (hUV : U a = V a)
    (hHreg : Regulated H a b) (hGreg : Regulated G a b) :
    ‖U b - V b‖ ≤ ∫ t in a..b, ‖H t - G t‖ := by
  exact norm_sub_le_integral_sub_off_countable S hS hab hUc hVc hU hV hUU hVV hUV
    (((hHreg.intervalIntegrable_on hab).sub (hGreg.intervalIntegrable_on hab)).norm)

end
end UnitaryProducts
