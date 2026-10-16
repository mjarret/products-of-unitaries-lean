/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.VariationMain

/-!
# Finite variation implies regulated

## Declarations

- `exists_limit`
- `regulated_of_boundedVariation`
- `variationGauge_mono_bounded`
- `variationGauge_one_sided_limits`
-/

@[expose] public section

namespace UnitaryProducts
open Set Filter
open scoped Topology Matrix.Norms.L2Operator
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A convergent scalar gauge makes the controlled matrix family Cauchy in operator norm
along the same filter (the Cauchy step in Section 3.2), and completeness gives a limit. -/
theorem Gauge.exists_limit {H : ℝ → 𝕄} {φ : ℝ → ℝ} {a b : ℝ}
    (hg : Gauge H φ a b) {l : Filter ℝ} [NeBot l] {v : ℝ}
    (hs : ∀ᶠ x in l, x ∈ Icc a b) (hv : Tendsto φ l (𝓝 v)) :
    ∃ M, Tendsto H l (𝓝 M) := by
  -- Matrices form a complete space, so it suffices that `H` is Cauchy along `l`: eventually
  -- φ is within ε/2 of v, and ‖H x - H y‖ ≤ |φ x - φ y| < ε there.
  refine cauchy_map_iff_exists_tendsto.mp (Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε ↦ ?_⟩)
  let S := {x | x ∈ Icc a b ∧ dist (φ x) v < ε / 2}
  have hS : S ∈ l := hs.and (hv.eventually (Metric.ball_mem_nhds v (half_pos hε)))
  refine ⟨H '' S, Filter.mem_map.mpr (Filter.mem_of_superset hS (fun x hx ↦ ⟨x, hx, rfl⟩)), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy : dist (H x) (H y) ≤ dist (φ x) (φ y) := by
    rcases le_total x y with h | h
    · rw [dist_comm (H x), dist_eq_norm, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hg.1 hx.1
      hy.1 h)), neg_sub]
      exact hg.2 x hx.1 y hy.1 h
    · rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hg.1 hy.1 hx.1 h))]
      exact hg.2 y hy.1 x hx.1 h
  exact (hxy.trans (dist_triangle_right _ _ _)).trans_lt
    ((add_lt_add hx.2 hy.2).trans_eq (add_halves ε))

/-- Section 3.2: cumulative finite variation is nondecreasing and bounded by its endpoint
values on the closed interval. -/
theorem variationGauge_mono_bounded {H : ℝ → 𝕄} {a b : ℝ}
    (hH : BoundedVariationOn H (Icc a b)) :
    MonotoneOn (variationGauge H a) (Icc a b) ∧
      ∀ s ∈ Icc a b, variationGauge H a a ≤ variationGauge H a s ∧
        variationGauge H a s ≤ variationGauge H a b :=
  have hm := (gauge_of_boundedVariation hH).1
  ⟨hm, fun _ hs ↦ ⟨hm ⟨le_rfl, hs.1.trans hs.2⟩ hs hs.1, hm hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2⟩⟩

/-- Section 3.2: bounded monotone cumulative variation converges from either side. -/
theorem variationGauge_one_sided_limits {H : ℝ → 𝕄} {a b : ℝ}
    (hH : BoundedVariationOn H (Icc a b)) :
    (∀ t ∈ Ico a b, Tendsto (variationGauge H a) (𝓝[>] t)
      (𝓝 (sInf (variationGauge H a '' Ioo t b)))) ∧
    (∀ t ∈ Ioc a b, Tendsto (variationGauge H a) (𝓝[<] t)
      (𝓝 (sSup (variationGauge H a '' Ioo a t)))) := by
  have hm := (variationGauge_mono_bounded hH).1
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · exact MonotoneOn.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr ht.2)
      (hm.mono fun x hx ↦ ⟨ht.1.trans hx.1.le, hx.2.le⟩) ⟨variationGauge H a t, by
        rintro _ ⟨x, hx, rfl⟩; exact hm ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans hx.1.le, hx.2.le⟩ hx.1.le⟩
  · exact MonotoneOn.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr ht.1)
      (hm.mono fun x hx ↦ ⟨hx.1.le, hx.2.le.trans ht.2⟩) ⟨variationGauge H a t, by
        rintro _ ⟨x, hx, rfl⟩; exact hm ⟨hx.1.le, hx.2.le.trans ht.2⟩ ⟨ht.1.le, ht.2⟩ hx.2.le⟩

/-- Finite total variation gives both one-sided limits, including at the endpoints: the claim of
§3.2 that a path of finite variation is regulated (Definition 2.1). -/
theorem regulated_of_boundedVariation {H : ℝ → 𝕄} {a b : ℝ}
    (hH : BoundedVariationOn H (Icc a b)) : Regulated H a b := by
  -- The cumulative variation φ = ℓ(·) is a nondecreasing gauge for H, so it has one-sided
  -- limits, and `Gauge.exists_limit` transfers them to H.
  let φ := variationGauge H a
  have hg : Gauge H φ a b := gauge_of_boundedVariation hH
  -- Right limits at t ∈ [a,b): φ tends to its infimum over (t,b).
  -- Left limits at t ∈ (a,b]: φ tends to its supremum over (a,t).
  refine ⟨fun t ht ↦ hg.exists_limit ?_ ((variationGauge_one_sided_limits hH).1 t ht),
    fun t ht ↦ hg.exists_limit ?_ ((variationGauge_one_sided_limits hH).2 t ht)⟩
  · filter_upwards [Ioo_mem_nhdsGT ht.2] with x hx
    exact ⟨ht.1.trans hx.1.le, hx.2.le⟩
  · filter_upwards [Ioo_mem_nhdsLT ht.1] with x hx
    exact ⟨hx.1.le, hx.2.le.trans ht.2⟩

end UnitaryProducts
