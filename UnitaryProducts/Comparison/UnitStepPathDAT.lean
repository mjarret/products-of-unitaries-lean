/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import UnitaryProducts.Approximation.JRSComparison
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Evolution.DuhamelIntegral
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmBranch
public import UnitaryProducts.Corrector.PowerSeries

/-!
# Taylor remainder for a Lipschitz derivative

## Declarations

- `Dressed.norm_borrowed_taylor_left`
- `Dressed.norm_borrowed_taylor_right`
- `norm_taylor_sub_le_of_lipschitz_deriv_half_Icc`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Real UnitaryProducts.Corrector MeasureTheory

namespace UnitaryProducts

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Taylor remainder with the derivative taken at a later point $c\ge b$:
$\|K(b)-K(a)-(b-a)K'(c)\|\le M((c-a)(b-a)-(b-a)^2/2)$ when $K'$ is $M$-Lipschitz. Used for the
first half cell, which borrows the slope of the sample $K(1)$. -/
theorem Dressed.norm_borrowed_taylor_right {K Kd : ℝ → 𝕄} {A B a b c M : ℝ}
    (hder : ∀ t ∈ Icc A B, HasDerivWithinAt K (Kd t) (Icc A B) t)
    (hlip : ∀ s ∈ Icc A B, ∀ t ∈ Icc A B, ‖Kd t - Kd s‖ ≤ M * |t - s|)
    (ha : a ∈ Icc A B) (hb : b ∈ Icc A B) (hc : c ∈ Icc A B)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ‖K b-K a-(b-a) • Kd c‖ ≤ M*((c-a)*(b-a)-(b-a)^2/2) := by
  have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc ha.1 hb.2
  let F : ℝ → 𝕄 := fun t ↦ K t-(t-a) • Kd c
  have hd t (ht : t ∈ Icc a b) : HasDerivWithinAt F (Kd t-Kd c) (Icc a b) t := by
    simpa only [id_eq, one_smul] using ((hder t (hsub ht)).mono hsub).sub
      (((hasDerivAt_id t).sub_const a).smul_const (Kd c)).hasDerivWithinAt
  have hFc : ContinuousOn F (Icc a b) := fun t ht ↦ (hd t ht).continuousWithinAt
  have hnorm := norm_sub_le_integral_off_countable ∅ countable_empty hab hFc
    (fun t ht _ ↦ ((hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1
      ht.2)).differentiableAt)
    (B := fun t ↦ M*(c-t)) (fun t ht _ ↦ by
      rw [((hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have h := hlip c hc t (hsub (Ioo_subset_Icc_self ht))
      rw [abs_of_nonpos (sub_nonpos.mpr (ht.2.le.trans hbc))] at h
      exact h.trans_eq (by ring))
    ((by fun_prop : Continuous fun t:ℝ ↦ M*(c-t)).intervalIntegrable _ _)
  have he : (∫ t in a..b, M*(c-t)) = M*((c-a)*(b-a)-(b-a)^2/2) := by
    rw [show (fun t:ℝ ↦ M*(c-t)) = fun t ↦ (-M)*(t-a)+M*(c-a) by funext t; ring, integral_affine]
    ring
  simp only [F, sub_self, zero_smul, sub_zero, he] at hnorm
  rwa [sub_right_comm] at hnorm

/-- Taylor remainder with the derivative taken at a point $c\le a$:
$\|K(b)-K(a)-(b-a)K'(c)\|\le M((b-c)(b-a)-(b-a)^2/2)$ when $K'$ is $M$-Lipschitz. Used for the
last half cell, which borrows the slope of the sample $K(N-1)$. -/
theorem Dressed.norm_borrowed_taylor_left {K Kd : ℝ → 𝕄} {A B a b c M : ℝ}
    (hder : ∀ t ∈ Icc A B, HasDerivWithinAt K (Kd t) (Icc A B) t)
    (hlip : ∀ s ∈ Icc A B, ∀ t ∈ Icc A B, ‖Kd t - Kd s‖ ≤ M * |t - s|)
    (ha : a ∈ Icc A B) (hb : b ∈ Icc A B) (hc : c ∈ Icc A B)
    (hab : a ≤ b) (hca : c ≤ a) :
    ‖K b-K a-(b-a) • Kd c‖ ≤ M*((b-c)*(b-a)-(b-a)^2/2) := by
  have hsub : Icc a b ⊆ Icc A B := Icc_subset_Icc ha.1 hb.2
  let F : ℝ → 𝕄 := fun t ↦ K t-(t-a) • Kd c
  have hd t (ht : t ∈ Icc a b) : HasDerivWithinAt F (Kd t-Kd c) (Icc a b) t := by
    simpa only [id_eq, one_smul] using ((hder t (hsub ht)).mono hsub).sub
      (((hasDerivAt_id t).sub_const a).smul_const (Kd c)).hasDerivWithinAt
  have hFc : ContinuousOn F (Icc a b) := fun t ht ↦ (hd t ht).continuousWithinAt
  have hnorm := norm_sub_le_integral_off_countable ∅ countable_empty hab hFc
    (fun t ht _ ↦ ((hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1
      ht.2)).differentiableAt)
    (B := fun t ↦ M*(t-c)) (fun t ht _ ↦ by
      rw [((hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv]
      have h := hlip c hc t (hsub (Ioo_subset_Icc_self ht))
      rw [abs_of_nonneg (sub_nonneg.mpr (hca.trans ht.1.le))] at h
      exact h.trans_eq (by ring))
    ((by fun_prop : Continuous fun t:ℝ ↦ M*(t-c)).intervalIntegrable _ _)
  have he : (∫ t in a..b, M*(t-c)) = M*((b-c)*(b-a)-(b-a)^2/2) := by
    rw [show (fun t:ℝ ↦ M*(t-c)) = fun t ↦ M*(t-a)+M*(a-c) by funext t; ring, integral_affine]
    ring
  simp only [F, sub_self, zero_smul, sub_zero, he] at hnorm
  rwa [sub_right_comm] at hnorm

/-- The Taylor bound with half the Lipschitz constant of the derivative, on any interval
(`norm_taylor_sub_le_of_lipschitz_deriv_half` on `[a, b]`). -/
theorem norm_taylor_sub_le_of_lipschitz_deriv_half_Icc (G Gd : ℝ → 𝕄) {a b ℓ : ℝ}
    (hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt G (Gd s) (Icc a b) s)
    (hGdlip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖Gd t - Gd s‖ ≤ ℓ * |t - s|) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ‖G t - G s - (t - s) • Gd s‖ ≤ ℓ / 2 * (t - s) ^ 2 := by
  intro s hs t ht
  rcases le_total s t with h | h
  · exact (Dressed.norm_borrowed_taylor_left hderiv hGdlip hs ht hs h le_rfl).trans_eq (by ring)
  · rw [← norm_neg, show -(G t - G s - (t - s) • Gd s) = G s - G t - (s - t) • Gd s by module]
    exact (Dressed.norm_borrowed_taylor_right hderiv hGdlip ht hs hs h le_rfl).trans_eq (by ring)

end UnitaryProducts
