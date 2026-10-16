/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Propagator

/-!
# Integral form of the Schrödinger equation

## Declarations

- `integral_eq`
- `norm_le_one_of_initial_one`
- `norm_sub_le_integral`
- `norm_sub_le_integral_sub`
- `norm_intervalIntegral_le`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory NormedSpace

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **The Volterra form of the Schrödinger equation.** -/
theorem SolvesSchrodinger.integral_eq {Γ Ω : ℝ → 𝕄} {a b : ℝ}
    (hΓ : ContinuousOn Γ (Icc a b)) (hΩ : SolvesSchrodinger Γ Ω a b) {t : ℝ} (ht : t ∈ Icc a b) :
    Ω t - Ω a = ∫ s in a..t, -I • (Γ s * Ω s) := by
  have hcont : ContinuousOn Ω (Icc a b) := fun s hs ↦ (hΩ s hs).continuousWithinAt
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hint : IntervalIntegrable (fun s ↦ -I • (Γ s * Ω s)) volume a t :=
    (((hΓ.mono hsub).mul (hcont.mono hsub)).const_smul _).intervalIntegrable_of_Icc ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hcont.mono hsub)
    (fun x hx ↦ ?_) hint]
  exact (hΩ x (hsub (Ioo_subset_Icc_self hx))).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGT_of_mem ⟨hx.1.le, hx.2.trans_le ht.2⟩)

/-- A constant bound on the integrand bounds the integral. -/
theorem norm_intervalIntegral_le {f : ℝ → 𝕄} {a t C : ℝ} (hat : a ≤ t)
    (h : ∀ s ∈ Icc a t, ‖f s‖ ≤ C) : ‖∫ s in a..t, f s‖ ≤ C * (t - a) := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦
    h s (Ioc_subset_Icc_self (by rwa [uIoc_of_le hat] at hs))
  rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - a)] at hn

/-- **First-order Dyson bound, integral form**: a contractive propagator moves at most by the
integral of the norm of its generator. -/
theorem SolvesSchrodinger.norm_sub_le_integral {Γ Ω : ℝ → 𝕄} {a b : ℝ}
    (hΓ : ContinuousOn Γ (Icc a b)) (hΩ : SolvesSchrodinger Γ Ω a b)
    (hΩ1 : ∀ s ∈ Icc a b, ‖Ω s‖ ≤ 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖Ω t - Ω a‖ ≤ ∫ s in a..t, ‖Γ s‖ := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  rw [hΩ.integral_eq hΓ ht]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1
    (Filter.Eventually.of_forall fun s hs ↦ ?_)
    ((hΓ.mono hsub).norm.intervalIntegrable_of_Icc ht.1)
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (hΩ1 s (hsub ⟨hs.1.le, hs.2⟩)))

/-- A Hermitian evolution starting at the identity remains a contraction. -/
theorem SolvesSchrodinger.norm_le_one_of_initial_one {K U : ℝ → 𝕄} {a b : ℝ}
    (hU : SolvesSchrodinger K U a b) (hK : ∀ t ∈ Icc a b, (K t).IsHermitian)
    (hUa : U a = 1) {t : ℝ} (ht : t ∈ Icc a b) : ‖U t‖ ≤ 1 :=
  norm_le_one_of_star_mul_self (by
    rw [hU.star_mul_self_eq hK t ht, hUa, star_one, one_mul])

/-- **Duhamel in integral form**, for two Hermitian generators and propagators from the identity:
`‖Ω(t) - Ω'(t)‖ ≤ ∫ₐᵗ ‖Γ - Γ'‖`.  Indeed `Ω⋆ Ω'` is itself a propagator from the identity, with
generator `Ω⋆ (Γ' - Γ) Ω`, to which `norm_sub_le_integral` applies. -/
theorem SolvesSchrodinger.norm_sub_le_integral_sub {Γ Γ' Ω Ω' : ℝ → 𝕄} {a b : ℝ}
    (hΓ : ContinuousOn Γ (Icc a b)) (hΓ' : ContinuousOn Γ' (Icc a b))
    (hherm : ∀ s ∈ Icc a b, (Γ s).IsHermitian)
    (hherm' : ∀ s ∈ Icc a b, (Γ' s).IsHermitian)
    (hΩ : SolvesSchrodinger Γ Ω a b) (hΩ' : SolvesSchrodinger Γ' Ω' a b)
    (hΩ0 : Ω a = 1) (hΩ0' : Ω' a = 1) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖Ω t - Ω' t‖ ≤ ∫ s in a..t, ‖Γ s - Γ' s‖ := by
  have hcΩ : ContinuousOn Ω (Icc a b) := fun s hs ↦ (hΩ s hs).continuousWithinAt
  have hsU : ∀ s ∈ Icc a b, star (Ω s) * Ω s = 1 := fun s hs ↦ by
    rw [hΩ.star_mul_self_eq hherm s hs, hΩ0, star_one, one_mul]
  have hUs : ∀ s ∈ Icc a b, Ω s * star (Ω s) = 1 := fun s hs ↦ mul_eq_one_comm.mp (hsU s hs)
  have hΩ1 : ∀ s ∈ Icc a b, ‖Ω s‖ ≤ 1 := fun s hs ↦ norm_le_one_of_star_mul_self (hsU s hs)
  have hsΩ1 : ∀ s ∈ Icc a b, ‖star (Ω s)‖ ≤ 1 := fun s hs ↦ (norm_star _).trans_le (hΩ1 s hs)
  have hZsol : SolvesSchrodinger (fun s ↦ star (Ω s) * (Γ' s - Γ s) * Ω s)
      (fun s ↦ star (Ω s) * Ω' s) a b := by
    intro s hs
    have hprod := (hΩ s hs).star.mul (hΩ' s hs)
    convert hprod using 1
    have hstar : star (-I • (Γ s * Ω s)) = I • (star (Ω s) * Γ s) := by
      simp only [star_smul, star_mul, show star (Γ s) = Γ s from (hherm s hs).eq, Complex.star_def,
        map_neg, Complex.conj_I, neg_neg]
    have hins : star (Ω s) * (Γ' s - Γ s) * Ω s * (star (Ω s) * Ω' s)
        = star (Ω s) * (Γ' s - Γ s) * Ω' s := by
      rw [mul_assoc (star (Ω s) * (Γ' s - Γ s)), ← mul_assoc (Ω s), hUs s hs, one_mul]
    rw [hins, hstar]
    simp only [smul_mul_assoc, mul_smul_comm, mul_neg, mul_sub, sub_mul, smul_sub, neg_smul,
      mul_assoc]
    abel
  have hZ1 : ∀ s ∈ Icc a b, ‖star (Ω s) * Ω' s‖ ≤ 1 := fun s hs ↦ by
    simpa only [one_mul] using
      norm_mul_le_of_le (hsΩ1 s hs) (hΩ'.norm_le_one_of_initial_one hherm' hΩ0' hs)
  have hΞc : ContinuousOn (fun s ↦ star (Ω s) * (Γ' s - Γ s) * Ω s) (Icc a b) :=
    (hcΩ.star.mul (hΓ'.sub hΓ)).mul hcΩ
  have hmove : ‖star (Ω t) * Ω' t - 1‖ ≤ ∫ s in a..t, ‖star (Ω s) * (Γ' s - Γ s) * Ω s‖ := by
    simpa only [hΩ0, hΩ0', star_one, one_mul] using hZsol.norm_sub_le_integral hΞc hZ1 ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hle : (∫ s in a..t, ‖star (Ω s) * (Γ' s - Γ s) * Ω s‖) ≤ ∫ s in a..t, ‖Γ s - Γ' s‖ := by
    refine intervalIntegral.integral_mono_on ht.1
      ((hΞc.mono hsub).norm.intervalIntegrable_of_Icc ht.1)
      (((hΓ.sub hΓ').mono hsub).norm.intervalIntegrable_of_Icc ht.1) fun s hs ↦ ?_
    rw [norm_sub_rev (Γ s) (Γ' s)]
    simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le (hsΩ1 s (hsub hs)) le_rfl) (hΩ1 s (hsub hs))
  have hkey : Ω t - Ω' t = -(Ω t * (star (Ω t) * Ω' t - 1)) := by
    rw [mul_sub, mul_one, ← mul_assoc, hUs t ht, one_mul]
    abel
  rw [hkey, norm_neg]
  exact ((norm_mul_le_of_le (hΩ1 t ht) le_rfl).trans_eq (one_mul _)).trans (hmove.trans hle)

end UnitaryProducts
