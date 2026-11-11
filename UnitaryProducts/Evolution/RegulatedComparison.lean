/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.LogarithmDerivativeBounds

/-!
# Comparison of evolutions

## Declarations

- `comparison_of_primitive`
- `comparison_with_jumps`
- `hasDerivAt_corrected_product`
- `hasDerivAt_evolution_adjoint`
- `integral_eq_piecewise_sub`
- `regulated_corrected_product_derivative`
- `residual_display_chain`
- `regulated_map₂`
- `regulated_mul`
- `regulated_of_continuousOn`
- `regulated_sub`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2, proof of Theorem 2.2: continuous binary operations preserve regulatedness. -/
theorem regulated_map₂ {H G : ℝ → 𝕄} {a b : ℝ} (hH : Regulated H a b) (hG : Regulated G a b)
    (f : 𝕄 × 𝕄 → 𝕄) (hf : Continuous f) : Regulated (fun t ↦ f (H t, G t)) a b :=
  ⟨fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
    ((hH.1 t ht).choose_spec.prodMk_nhds (hG.1 t ht).choose_spec)⟩,
    fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
      ((hH.2 t ht).choose_spec.prodMk_nhds (hG.2 t ht).choose_spec)⟩⟩

/-- Section 2, proof of Theorem 2.2: a continuous matrix family has both required one-sided
limits, including the inward limits at the endpoints. -/
theorem regulated_of_continuousOn {H : ℝ → 𝕄} {a b : ℝ}
    (hH : ContinuousOn H (Icc a b)) : Regulated H a b :=
  ⟨fun t ht ↦ ⟨H t, ((hH t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)).mono Ioi_subset_Ici_self⟩,
   fun t ht ↦ ⟨H t, ((hH t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE_of_mem ht)).mono Iio_subset_Iic_self⟩⟩

/-- Section 2, proof of Theorem 2.2: differences of regulated matrix families are regulated. -/
theorem regulated_sub {H G : ℝ → 𝕄} {a b : ℝ} (hH : Regulated H a b) (hG : Regulated G a b) :
    Regulated (fun t ↦ H t - G t) a b :=
  regulated_map₂ hH hG (fun p ↦ p.1 - p.2) (continuous_fst.sub continuous_snd)

/-- Section 2, proof of Theorem 2.2: products of regulated matrix families are regulated. -/
theorem regulated_mul {H G : ℝ → 𝕄} {a b : ℝ} (hH : Regulated H a b) (hG : Regulated G a b) :
    Regulated (fun t ↦ H t * G t) a b :=
  regulated_map₂ hH hG (fun p ↦ p.1 * p.2) (continuous_fst.mul continuous_snd)

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Theorem 2.2, integration on closed pieces and collection of interior endpoints.
The derivative is assumed interval integrable; a regulated derivative suffices by
`Regulated.intervalIntegrable_on`. Repeated partition points are allowed. -/
theorem integral_eq_piecewise_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (m : ℕ) (p : ℕ → ℝ) (hp : Monotone p)
    (F : ℕ → ℝ → E) (f : ℝ → E) (S : Set ℝ) (hS : S.Countable)
    (hc : ∀ j ≤ m, ContinuousOn (F j) (Icc (p j) (p (j + 1))))
    (hd : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S → HasDerivAt (F j) (f t) t)
    (hi : IntervalIntegrable f volume (p 0) (p (m + 1))) :
    (∫ t in p 0..p (m + 1), f t) = F m (p (m + 1)) - F 0 (p 0) -
      ∑ j ∈ Finset.range m, (F (j + 1) (p (j + 1)) - F j (p (j + 1))) := by
  have hj (j : ℕ) (h : j < m + 1) : IntervalIntegrable f volume (p j) (p (j + 1)) :=
    hi.mono_set (uIcc_subset_uIcc (hp.mapsTo_uIcc (by simpa using h.le))
      (hp.mapsTo_uIcc (by simpa using Nat.succ_le_of_lt h)))
  rw [← intervalIntegral.sum_integral_adjacent_intervals hj,
    ← sum_piece_sub (fun j ↦ F j (p j)) (fun j ↦ F j (p (j + 1))) m]
  refine Finset.sum_congr rfl fun j hj' ↦ ?_
  have h : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj')
  exact integral_eq_of_hasDerivAt_off_countable_of_le _ _ (hp (Nat.le_succ _)) hS
    (hc j h) (fun t ht ↦ hd j h t ht.1 ht.2) (hj j (by omega))

/-- Section 2.1, before (2.2): Hermiticity turns `U' = -i K U` into
`(U†)' = i U† K`. -/
theorem hasDerivAt_evolution_adjoint {U : ℝ → 𝕄} {K : 𝕄} {t : ℝ}
    (hK : K.IsHermitian) (hU : HasDerivAt U (-I • (K * U t)) t) :
    HasDerivAt (fun s ↦ star (U s)) (I • (star (U t) * K)) t := by
  simpa [show star K = K from hK.eq, Complex.star_def] using hU.star

/-- Equation (2.2): the product rule for the undressed correction `U† Y V`. -/
theorem hasDerivAt_corrected_product {U V Y : ℝ → 𝕄} {K G Yd : 𝕄} {t : ℝ}
    (hK : K.IsHermitian) (hU : HasDerivAt U (-I • (K * U t)) t)
    (hV : HasDerivAt V (-I • (G * V t)) t) (hY : HasDerivAt Y Yd t) :
    HasDerivAt (fun s ↦ star (U s) * Y s * V s)
      (star (U t) * (Yd + I • (K * Y t - Y t * G)) * V t) t := by
  convert ((hasDerivAt_evolution_adjoint hK hU).mul hY).mul hV using 1
  simp [mul_add, add_mul, mul_assoc, sub_eq_add_neg, add_comm, add_assoc]

/-- Theorem 2.2, proof: continuous factors and regulated generators and derivative
representatives make `(U† Y V)'` regulated. Thus the paper's derivative hypothesis
supplies the integrability needed by the countable-exception fundamental theorem. -/
theorem regulated_corrected_product_derivative {a b : ℝ} {K G U V Y Yd : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hYc : ContinuousOn Y (Icc a b)) (hYdr : IsRegulated Yd a b) :
    IsRegulated (fun t ↦ star (U t) * (Yd t + I • (K t * Y t - Y t * G t)) * V t) a b := by
  have hYr := Prose.regulated_of_continuousOn hYc
  have hc := Prose.regulated_sub (Prose.regulated_mul hKr hYr) (Prose.regulated_mul hYr hGr)
  exact Prose.regulated_mul (Prose.regulated_mul (Prose.regulated_of_continuousOn hUc.star)
    (Prose.regulated_map₂ hYdr (Prose.regulated_map₂ hc hc (fun p ↦ I • p.1)
      (continuous_fst.const_smul I)) (fun p ↦ p.1 + p.2) (continuous_fst.add continuous_snd)))
    (Prose.regulated_of_continuousOn hVc)

/-- Equation (2.2), `eq:residual`: add zero, expand the corrected product
rule, and collect the residual. `E` is the derivative supplied by
`hasDerivAt_corrected_product`; taking its correction to be one supplies `D`. -/
theorem residual_display_chain (K G U V Y Yd : 𝕄) :
    let D := I • (star U * (K - G) * V)
    let E := star U * (Yd + I • (K * Y - Y * G)) * V
    let E' := I • (star U * K * Y * V) + star U * Yd * V - I • (star U * Y * G * V)
    D = D - I • E + I • E ∧
    D - I • E + I • E = D - I • E' + I • E ∧
    D - I • E' + I • E =
      I • (star U * (K - G - Yd - I • (K * Y - Y * G)) * V) + I • E := by
  refine ⟨(sub_add_cancel _ _).symm, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub,
      mul_smul_comm, smul_mul_assoc, mul_assoc] <;> abel

/-- Theorem 2.2: Duhamel's identity integrated by parts against finitely many
continuous correction pieces. This is stronger than the paper's regulated-derivative
version: only interval integrability of the residual is required. The residual equation
is the derivative hypothesis, rearranged; its values at exceptional points are immaterial.
The regulated branch retains the paper's separate Duhamel integrals; otherwise integrate
the corrected product directly, requiring no regulatedness of either generator. -/
theorem comparison_with_jumps {a b : ℝ}
    (m : ℕ) (p : ℕ → ℝ) (hp : Monotone p) (ha : p 0 = a) (hb : p (m + 1) = b)
    (K G U V R : ℝ → 𝕄) (Y : ℕ → ℝ → 𝕄) (S : Set ℝ) (hS : S.Countable)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b)
    (hRi : IntervalIntegrable R volume a b)
    (hYc : ∀ j ≤ m, ContinuousOn (Y j) (Icc (p j) (p (j + 1))))
    (hYd : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S →
      HasDerivAt (Y j) (K t - G t - I • (K t * Y j t - Y j t * G t) - R t) t) :
    star (U b) * V b - 1 = (∫ t in a..b, I • (star (U t) * R t * V t)) +
      I • (star (U b) * Y m b * V b - Y 0 a) -
      I • ∑ j ∈ Finset.range m,
        star (U (p (j + 1))) * (Y (j + 1) (p (j + 1)) - Y j (p (j + 1))) *
          V (p (j + 1)) := by
  classical
  -- With regulated generators, follow the paper's separate Duhamel and correction integrals.
  -- Otherwise integrate their difference directly; only the residual must be integrable.
  by_cases hreg : IsRegulated K a b ∧ IsRegulated G a b
  · obtain ⟨hKr, hGr⟩ := hreg
    have hab : a ≤ b := ha ▸ hb ▸ hp (Nat.zero_le (m + 1))
    let D := fun t ↦ I • (star (U t) * (K t - G t) * V t)
    let C := fun t ↦ I • (star (U t) * R t * V t)
    have hDi := (regulated_corrected_product_derivative hKr hGr hU.1 hV.1
      (Y := fun _ ↦ 0) continuousOn_const (Prose.regulated_sub hKr hGr)
      |>.intervalIntegrable_on hab |>.smul I)
    simp only [mul_zero, zero_mul, sub_self, smul_zero, add_zero, Pi.smul_def] at hDi
    have hCi : IntervalIntegrable C volume a b :=
      ((hRi.continuousOn_mul (by simpa only [uIcc_of_le hab] using hU.1.star)).mul_continuousOn
        (by simpa only [uIcc_of_le hab] using hV.1)).smul I
    have hd {H W : ℝ → 𝕄} (hW : IsEvolution H W a b) :=
      hW.2.2.2.imp fun S hS ↦ And.intro hS.1 (fun t (ht : t ∈ Ioo a b) hn ↦
        (hS.2 t (Ioo_subset_Icc_self ht) hn).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    obtain ⟨SU, hSU, hUd⟩ := hd hU
    obtain ⟨SV, hSV, hVd⟩ := hd hV
    have hK t ht hn := isHermitian_of_unitary_solution (hUd t ht hn)
      (Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hU.2.2.1)
    have hE : (S ∪ SU ∪ SV).Countable := (hS.union hSU).union hSV
    -- Integrate d(U†V)/dt away from the combined countable exceptional set.
    have hD := integral_eq_of_hasDerivAt_off_countable_of_le
      (fun t ↦ star (U t) * V t) D hab hE (hU.1.star.mul hV.1) (fun t ht ↦ by
        simpa only [mul_one, one_mul, zero_add, mul_smul_comm, smul_mul_assoc] using
          hasDerivAt_corrected_product (hK t ht.1 (fun h ↦ ht.2 (Or.inl (Or.inr h))))
            (hUd t ht.1 (fun h ↦ ht.2 (Or.inl (Or.inr h))))
            (hVd t ht.1 (fun h ↦ ht.2 (Or.inr h))) (hasDerivAt_const t (1 : 𝕄))) hDi
    have hpiece (j : ℕ) (hj : j ≤ m) : Icc (p j) (p (j + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (ha ▸ hp (Nat.zero_le _)) (hb ▸ hp (Nat.add_le_add_right hj 1))
    -- Integrate each corrected product and collect its interior endpoints into the jump sum.
    have he := integral_eq_piecewise_sub m p hp
      (fun j t ↦ I • (star (U t) * Y j t * V t)) (fun t ↦ D t - C t) _ hE
      (fun j hj ↦ (((hU.1.mono (hpiece j hj)).star.mul (hYc j hj)).mul
        (hV.1.mono (hpiece j hj))).const_smul I) (fun j hj t ht hn ↦ ?_)
      (by simpa only [ha, hb] using hDi.sub hCi)
    · -- Use U(a) = V(a) = 1 and regroup the integrated identity.
      rw [ha, hb, intervalIntegral.integral_sub hDi hCi, hD] at he
      simp only [hU.2.1, hV.2.1, star_one, one_mul, mul_one, smul_sub,
        Finset.smul_sum, mul_sub, sub_mul] at he ⊢
      linear_combination (norm := abel) he
    -- Discharge the deferred derivative goal using (2.2); hn excludes S, SU and SV.
    have ht' : t ∈ Ioo a b := ⟨(ha ▸ hp (Nat.zero_le j)).trans_lt ht.1,
      ht.2.trans_le (hb ▸ hp (show j + 1 ≤ m + 1 by omega))⟩
    have hc := hasDerivAt_corrected_product (hK t ht' (fun h ↦ hn (Or.inl (Or.inr h))))
      (hUd t ht' (fun h ↦ hn (Or.inl (Or.inr h)))) (hVd t ht' (fun h ↦ hn (Or.inr h)))
      (hYd j hj t ht (fun h ↦ hn (Or.inl (Or.inl h))))
    convert hc.const_smul I using 1
    have he := residual_display_chain (K t) (G t) (U t) (V t) (Y j t)
      (K t - G t - I • (K t * Y j t - Y j t * G t) - R t)
    simpa only [sub_sub (K t - G t), sub_sub_cancel, add_sub_cancel_left] using
      sub_eq_of_eq_add' (he.1.trans (he.2.1.trans he.2.2))
  have hab : a ≤ b := ha ▸ hb ▸ hp (Nat.zero_le (m + 1))
  let C := fun t ↦ I • (star (U t) * R t * V t)
  have hCi : IntervalIntegrable C volume a b :=
    ((hRi.continuousOn_mul (by simpa only [uIcc_of_le hab] using hU.1.star)).mul_continuousOn
      (by simpa only [uIcc_of_le hab] using hV.1)).smul I
  have hd {H W : ℝ → 𝕄} (hW : IsEvolution H W a b) :=
    hW.2.2.2.imp fun S hS ↦ And.intro hS.1 (fun t (ht : t ∈ Ioo a b) hn ↦
      (hS.2 t (Ioo_subset_Icc_self ht) hn).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
  obtain ⟨⟨SU, hSU, hUd⟩, SV, hSV, hVd⟩ := And.intro (hd hU) (hd hV)
  have hK t ht hn := isHermitian_of_unitary_solution (hUd t ht hn)
    (Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2) hU.2.2.1)
  have hE : (S ∪ SU ∪ SV).Countable := (hS.union hSU).union hSV
  have hpiece (j : ℕ) (hj : j ≤ m) : Icc (p j) (p (j + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (ha ▸ hp (Nat.zero_le _)) (hb ▸ hp (Nat.add_le_add_right hj 1))
  -- Without separate generator integrals, integrate I U†YⱼV - U†V, whose derivative is -C.
  have he := integral_eq_piecewise_sub m p hp
    (fun j t ↦ I • (star (U t) * Y j t * V t) - star (U t) * V t)
    (fun t ↦ -C t) _ hE
    (by
      intro j hj
      have hu := hU.1.mono (hpiece j hj)
      have hv := hV.1.mono (hpiece j hj)
      exact (((hu.star.mul (hYc j hj)).mul hv).const_smul I).sub (hu.star.mul hv))
    (fun j hj t ht hn ↦ ?_) (by simpa only [ha, hb] using hCi.neg)
  · simp only [ha, hb, intervalIntegral.integral_neg, C, hU.2.1, hV.2.1,
      star_one, one_mul, mul_one, sub_sub_sub_cancel_right,
      ← smul_sub, ← sub_mul, ← mul_sub, ← Finset.smul_sum] at he
    simp only [smul_sub] at he ⊢
    linear_combination (norm := abel) he
  -- Subtract the plain product derivative to discharge the remaining derivative goal.
  have ht' : t ∈ Ioo a b := ⟨(ha ▸ hp (Nat.zero_le j)).trans_lt ht.1,
    ht.2.trans_le (hb ▸ hp (show j + 1 ≤ m + 1 by omega))⟩
  have hu := hUd t ht' (fun h ↦ hn (Or.inl (Or.inr h)))
  have hv := hVd t ht' (fun h ↦ hn (Or.inr h))
  have hk := hK t ht' (fun h ↦ hn (Or.inl (Or.inr h)))
  have hplain : HasDerivAt (fun s ↦ star (U s) * V s)
      (I • (star (U t) * (K t - G t) * V t)) t := by
    simpa only [mul_one, one_mul, zero_add, mul_smul_comm, smul_mul_assoc] using
      hasDerivAt_corrected_product hk hu hv (hasDerivAt_const t (1 : 𝕄))
  have hc := hasDerivAt_corrected_product hk hu hv
    (hYd j hj t ht (fun h ↦ hn (Or.inl (Or.inl h))))
  convert (hc.const_smul I).sub hplain using 1
  have heq := residual_display_chain (K t) (G t) (U t) (V t) (Y j t)
    (K t - G t - I • (K t * Y j t - Y j t * G t) - R t)
  have heq' := sub_eq_of_eq_add' (heq.1.trans (heq.2.1.trans heq.2.2))
  simp only [sub_sub (K t - G t), sub_sub_cancel, add_sub_cancel_left] at heq'
  dsimp only [C]
  linear_combination (norm := abel) heq'

/-- The Burgarth specialization of Theorem 2.2: a primitive of `K - G`
leaves only the commutator integral. Countably many derivative exceptions are allowed. -/
theorem comparison_of_primitive {a b : ℝ} (hab : a ≤ b) (K G U V Y : ℝ → 𝕄)
    (S : Set ℝ) (hS : S.Countable)
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b)
    (hYc : ContinuousOn Y (Icc a b)) (hYa : Y a = 0)
    (hYd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt Y (K t - G t) t) :
    star (U b) * (1 - I • Y b) * V b - 1 =
      ∫ t in a..b, star (U t) * (K t * Y t - Y t * G t) * V t := by
  have hYu : ContinuousOn Y (uIcc a b) := by rwa [uIcc_of_le hab]
  have hiR := (((hKr.intervalIntegrable_on hab).mul_continuousOn hYu).sub
    ((hGr.intervalIntegrable_on hab).continuousOn_mul hYu)).smul (-I)
  have hb := comparison_with_jumps 0 (fun j ↦ if j = 0 then a else b)
    (by intro i j hij; dsimp only; split_ifs <;> first | exact le_rfl | exact hab | omega)
    (by simp) (by simp) K G U V (fun t ↦ -I • (K t * Y t - Y t * G t))
    (fun _ ↦ Y) S hS hU hV hiR
    (by intro j hj; simpa [Nat.eq_zero_of_le_zero hj] using hYc)
    (by intro j hj t ht hn; simpa using hYd t (by simpa [Nat.eq_zero_of_le_zero hj] using ht) hn)
  simp [hYa, mul_sub, sub_mul, smul_smul] at hb ⊢
  linear_combination (norm := abel) hb

end UnitaryProducts.Paper
