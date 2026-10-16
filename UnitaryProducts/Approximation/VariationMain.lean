/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.ExplicitSchedule
public import UnitaryProducts.Approximation.VariationGauge

/-!
# Equal-variation checkpoints

## Declarations

- `inverseLevelTime_variation_eq`
- `inverseLevelTime_variation_mono`
- `inverseLevelTime_variation_norm_sub_le`
- `variationGauge_self`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology NNReal ENNReal
open Complex Set MeasureTheory
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- No variation accumulates on a single point: `V(a) = 0`. -/
@[simp] theorem variationGauge_self (H : ℝ → 𝕄) (a : ℝ) : variationGauge H a a = 0 := by
  simp only [variationGauge, eVariationOn.subsingleton H ((Icc_self a).symm ▸
    subsingleton_singleton), ENNReal.toReal_zero]

/-- The inverse-level checkpoints of the variation written out: for `0 < j < n`, `t_j` is the
infimum of the times at which the variation has reached `j V_0^T(H) / n`. -/
theorem inverseLevelTime_variation_eq (H : ℝ → 𝕄) (T : ℝ) {n j : ℕ} (hj0 : j ≠ 0)
    (hjn : j < n) :
    inverseLevelTime (variationGauge H 0) T n j =
      sInf {x ∈ Icc 0 T | (j : ℝ) * variationGauge H 0 T / n ≤ variationGauge H 0 x} := by
  simp only [inverseLevelTime, if_neg hj0, if_neg (not_le.mpr hjn), variationGauge_self, sub_zero]

/-- The inverse-level checkpoints of the variation are nondecreasing (the monotonicity in Remark
3.9). -/
theorem inverseLevelTime_variation_mono (H : ℝ → 𝕄) {T : ℝ} (hT : 0 ≤ T) {n : ℕ} :
    Monotone (inverseLevelTime (variationGauge H 0) T n) := by
  exact inverseLevelTime_mono hT
    (by simpa only [variationGauge_self, sub_zero] using ENNReal.toReal_nonneg)

/-- **Checkpoint lemma for the variation** (the variation bound of Remark 3.9).  Between
consecutive inverse levels of
the total variation, `H` moves by at most `V_0^T(H) / n`, that is $\ell/n$. -/
theorem inverseLevelTime_variation_norm_sub_le {H : ℝ → 𝕄} {T : ℝ}
    (hbv : BoundedVariationOn H (Icc 0 T)) (hT : 0 ≤ T) {n j : ℕ} (hj : j < n)
    {x y : ℝ}
    (hx : x ∈ Ioo (inverseLevelTime (variationGauge H 0) T n j)
      (inverseLevelTime (variationGauge H 0) T n (j + 1)))
    (hy : y ∈ Ioo (inverseLevelTime (variationGauge H 0) T n j)
      (inverseLevelTime (variationGauge H 0) T n (j + 1))) :
    ‖H x - H y‖ ≤ variationGauge H 0 T / n := by
  simpa only [variationGauge_self, sub_zero] using
    Gauge.inverseLevelTime_norm_sub_le (gauge_of_boundedVariation hbv) hT hj hx hy

end UnitaryProducts
