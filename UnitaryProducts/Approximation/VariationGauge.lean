/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import UnitaryProducts.Approximation.LevelPartitions

/-!
# Total variation as a gauge

## Declarations

- `eVariationOn_le_lipschitz`
- `gauge_of_boundedVariation`
- `variationGauge`
- `variationGauge_sub`
-/

@[expose] public section

namespace UnitaryProducts
open Set
open scoped Matrix.Norms.L2Operator NNReal ENNReal
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The cumulative total variation $\ell(t)$ of Remark 3.9, counted from `a`, interpreted as a
real when it is finite. Junk value: `ENNReal.toReal` sends infinite variation to `0`; the results
that need it to be $\ell(t)$ assume `BoundedVariationOn`. -/
noncomputable def variationGauge (H : ℝ → 𝕄) (a t : ℝ) : ℝ :=
  (eVariationOn H (Icc a t)).toReal

/-- Each increment of cumulative variation is exactly the variation on that subinterval. -/
theorem variationGauge_sub {H : ℝ → 𝕄} {a b s t : ℝ}
    (hH : BoundedVariationOn H (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hst : s ≤ t) :
    variationGauge H a t - variationGauge H a s = (eVariationOn H (Icc s t)).toReal := by
  have h₁ := hH.mono (Icc_subset_Icc le_rfl hs.2)
  have h₂ := hH.mono (Icc_subset_Icc hs.1 ht.2)
  have he := congrArg ENNReal.toReal
    (eVariationOn.Icc_add_Icc H (s := univ) hs.1 hst (mem_univ s))
  simp only [univ_inter, ENNReal.toReal_add h₁ h₂] at he
  exact sub_eq_of_eq_add (he.symm.trans (add_comm _ _))

/-- Finite total variation produces a gauge without any continuity hypothesis:
$\|H(t)-H(s)\|\le\ell(t)-\ell(s)$ for $s\le t$, the first step of the proof of the variation bound
of Remark 3.9. -/
theorem gauge_of_boundedVariation {H : ℝ → 𝕄} {a b : ℝ}
    (hH : BoundedVariationOn H (Icc a b)) : Gauge H (variationGauge H a) a b := by
  refine ⟨fun s hs t ht hst ↦ ?_, fun s hs t ht hst ↦ ?_⟩
  · exact sub_nonneg.mp ((variationGauge_sub hH hs ht hst).symm ▸ ENNReal.toReal_nonneg)
  · rw [variationGauge_sub hH hs ht hst, ← dist_eq_norm]
    exact (hH.mono (Icc_subset_Icc hs.1 ht.2)).dist_le ⟨hst, le_rfl⟩ ⟨le_rfl, hst⟩

/-- An $L$-Lipschitz path has variation at most $L$ times the duration (auxiliary JRS
specialization after Example 3.7: a
$C^2$ path is Lipschitz, so of finite variation). -/
theorem eVariationOn_le_lipschitz {H : ℝ → 𝕄} {a b : ℝ} {L : ℝ≥0}
    (hH : LipschitzOnWith L H (Icc a b)) :
    eVariationOn H (Icc a b) ≤ ENNReal.ofReal ((L : ℝ) * (b - a)) := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty_of_lt hba, eVariationOn.subsingleton H subsingleton_empty]; exact zero_le _
  have hid : eVariationOn id (Icc a b) ≤ ENNReal.ofReal (b - a) := by
    simpa only [inter_self] using
      monotoneOn_id.eVariationOn_le (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  calc eVariationOn (H ∘ id) (Icc a b) ≤ L * eVariationOn id (Icc a b) :=
        hH.comp_eVariationOn_le (mapsTo_id _)
    _ ≤ L * ENNReal.ofReal (b - a) := by gcongr
    _ = ENNReal.ofReal ((L : ℝ) * (b - a)) := by
        rw [ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]


end UnitaryProducts
