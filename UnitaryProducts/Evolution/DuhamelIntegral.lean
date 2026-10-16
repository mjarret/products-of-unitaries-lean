/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.DysonSeries

/-!
# Duhamel's estimate off a countable set

## Declarations

- `isHermitian_of_unitary_solution`
- `norm_sub_le_integral_off_countable`
- `norm_sub_le_integral_sub_off_countable`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory NormedSpace

/-- A continuous $f$ on $[a,b]$ with $\|f'\| \le B$ outside a countable set, $B$ integrable,
satisfies $\|f(b) - f(a)\| \le \int_a^b B$: the fundamental theorem of calculus off a countable set
(Dieudonné (8.7.1) in the paper), as used for Theorem 2.2. -/
theorem norm_sub_le_integral_off_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {B : ℝ → ℝ} {a b : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ S → DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo a b, t ∉ S → ‖deriv f t‖ ≤ B t)
    (hi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  have hae' : ∀ᵐ t ∂volume.restrict (uIoc a b), ‖deriv f t‖ ≤ B t := by
    rw [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ae_restrict_iff' measurableSet_Ioo]
    exact (hS.ae_notMem volume).mono fun t hn ht ↦ hb t ht hn
  rw [← integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) hab hS hc
    (fun t ht ↦ (hd t ht.1 ht.2).hasDerivAt)
    (hi.mono_fun (aestronglyMeasurable_deriv _ _) (hae'.mono fun t ht ↦ ht.trans (le_abs_self _)))]
  apply intervalIntegral.norm_integral_le_of_norm_le hab _ hi
  rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A unitary solution of the Schrödinger equation has a Hermitian generator at that time. -/
theorem isHermitian_of_unitary_solution {U : ℝ → 𝕄} {K : 𝕄} {t : ℝ}
    (hU : HasDerivAt U (-I • (K * U t)) t)
    (hu : ∀ᶠ s in nhds t, star (U s) * U s = 1) : K.IsHermitian := by
  have hright := mul_eq_one_comm.mp hu.self_of_nhds
  have hz := ((hU.star.mul hU).congr_of_eventuallyEq (hu.mono fun _ h ↦ h.symm)).unique
    (hasDerivAt_const t (1 : 𝕄))
  have he := congrArg (fun A : 𝕄 ↦ -I • (U t * A * star (U t))) hz
  simp only [Matrix.star_mul, StarModule.star_smul, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg, mul_add, add_mul,
    smul_add, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hright,
    one_mul, zero_mul, mul_zero, smul_zero] at he
  exact sub_eq_zero.mp (by simpa [mul_assoc, hright, smul_smul, sub_eq_add_neg] using he)

/-- Duhamel's estimate (2.3), the core of `duhamel` (equation (2.3)): unitary curves $U$, $V$
with $U(a) = V(a)$ that solve $iU' = HU$ and $iV' = GV$ outside a countable set satisfy
$\|U(b) - V(b)\| \le \int_a^b \|H - G\|$. Hermiticity follows from the unitary solution
when differentiating $U^\dagger$; the integrability of $\|H - G\|$ is a hypothesis. -/
theorem norm_sub_le_integral_sub_off_countable {H G U V : ℝ → 𝕄} {a b : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b)
    (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hU : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U (-I • (H t * U t)) (Icc a b) t)
    (hV : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt V (-I • (G t * V t)) (Icc a b) t)
    (hUU : ∀ t ∈ Icc a b, star (U t) * U t = 1)
    (hVV : ∀ t ∈ Icc a b, star (V t) * V t = 1)
    (hUV : U a = V a)
    (hi : IntervalIntegrable (fun t ↦ ‖H t - G t‖) volume a b) :
    ‖U b - V b‖ ≤ ∫ t in a..b, ‖H t - G t‖ := by
  -- Step 1 (paper, Theorem 2.2 with Y = 0): off S, W = U†V has derivative iU†(H - G)V.
  let W := fun t ↦ star (U t) * V t
  have hd : ∀ t ∈ Ioo a b, t ∉ S →
      HasDerivAt W (I • (star (U t) * (H t - G t) * V t)) t := by
    intro t ht hn
    have hm := Ioo_subset_Icc_self ht
    have hH := isHermitian_of_unitary_solution
      ((hU t hm hn).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hUU)
    -- The identity (U†V)' = (iU†H)V + U†(-iGV) = iU†(H - G)V uses H† = H.
    -- Expand products and normalize the scalar factors and additive order.
    convert ((hU t hm hn).star.mul (hV t hm hn)).hasDerivAt (Icc_mem_nhds ht.1 ht.2) using 1
    simp [show star (H t) = H t from hH.eq, mul_add, add_mul, mul_assoc, sub_eq_add_neg]
  -- Steps 2–3: ‖W'‖ ≤ ‖H - G‖ by unitarity, then integrate off the countable set.
  have hw := norm_sub_le_integral_off_countable (f := W) S hS hab (hUc.star.mul hVc)
    (fun t ht hn ↦ (hd t ht hn).differentiableAt) (fun t ht hn ↦ by
      have mem (A : 𝕄) := (Matrix.mem_unitaryGroup_iff' (A := A)).mpr
      rw [(hd t ht hn).deriv, norm_smul, Complex.norm_I, one_mul,
        CStarRing.norm_mul_mem_unitary _ (mem _ (hVV t ⟨ht.1.le, ht.2.le⟩)),
        CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (mem _ (hUU t ⟨ht.1.le, ht.2.le⟩)))]) hi
  -- Step 4: W(a) = 1, and multiplication by U(b)† preserves the difference norm.
  have ha : W a = 1 := by simpa only [W, ← hUV] using hUU a ⟨le_rfl, hab⟩
  rw [ha, ← hUU b ⟨hab, le_rfl⟩] at hw
  simpa only [W, ← mul_sub, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem
    (Matrix.mem_unitaryGroup_iff'.mpr (hUU b ⟨hab, le_rfl⟩))), norm_sub_rev] using hw

end UnitaryProducts
