/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Regulated
public import RoundedClocks.Preliminaries.RegulatedIntegrability

/-! # The derivatives in equation (2.2)

Outside a countable set, `(U†V)' = iU†(K - G)V` and `(U†YV)' = U†(Y' + i(KY - YG))V`, the first
and third lines of (2.2). Both derivatives are regulated, so the fundamental theorem of calculus
gives each of
`U†V` and `U†YV` is the integral of its derivative over a piece `[pⱼ, pⱼ₊₁]` of Theorem 2.2.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- First and third lines of (2.2), integrated over one piece `[a,b]`. Outside a countable set,
`(U†V)' = iU†(K - G)V` and `(U†YV)' = U†(Y' + i(KY - YG))V`. Both right sides are regulated, so by
the fundamental theorem of calculus, each of `U†V` and `U†YV` is the integral of its derivative. -/
lemma comparison_piece_primitives
    (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (K G U V Y Y' : ℝ → 𝕄) (a b : ℝ) (hab : a ≤ b)
    (hK : IsRegulated K a b) (hG : IsRegulated G a b)
    (hY' : IsRegulated Y' a b) (hKh : IsHermitianFamily K a b)
    (hU : ContinuousOn U (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hY : ContinuousOn Y (Icc a b))
    (hUd : DerivativeOffCountable U (fun t ↦ -I • (K t * U t)) a b)
    (hVd : DerivativeOffCountable V (fun t ↦ -I • (G t * V t)) a b)
    (hYd : DerivativeOffCountable Y Y' a b) :
    IsRegulated (fun t ↦ I • ((U t)† * (K t - G t) * V t)) a b ∧
      IsRegulated (fun t ↦ (U t)† * (Y' t + I • (K t * Y t - Y t * G t)) * V t) a b ∧
      ((U b)† * V b - (U a)† * V a = ∫ t in a..b, I • ((U t)† * (K t - G t) * V t)) ∧
      ((U b)† * Y b * V b - (U a)† * Y a * V a =
        ∫ t in a..b, (U t)† * (Y' t + I • (K t * Y t - Y t * G t)) * V t) := by
  -- The continuous functions `U†`, `V`, and `Y` are regulated.
  have hUr := (ContinuousOn.isRegulated hU).adjoint
  have hVr := ContinuousOn.isRegulated hV
  have hYr := ContinuousOn.isRegulated hY
  -- So `iU†(K - G)V` and `U†(Y' + i(KY - YG))V` are regulated.
  have hdUV := ((hUr.mul (hK.sub hG)).mul hVr).const_smul I
  have hdUYV := (hUr.mul (hY'.add (((hK.mul hYr).sub (hYr.mul hG)).const_smul I))).mul hVr
  -- The functions `U†V` and `U†YV` are continuous.
  have hUV := hU.star.mul hV
  have hUYV := (hU.star.mul hY).mul hV
  obtain ⟨DU, hDU, hUd⟩ := hUd
  obtain ⟨DV, hDV, hVd⟩ := hVd
  obtain ⟨DY, hDY, hYd⟩ := hYd
  -- Outside the countable set where `U`, `V`, or `Y` fails to be differentiable:
  have hderivs : ∀ t ∈ Icc a b, t ∉ DU ∪ DV ∪ DY →
      HasDerivWithinAt (fun s ↦ (U s)† * V s)
        (I • ((U t)† * (K t - G t) * V t)) (Icc a b) t ∧
      HasDerivWithinAt (fun s ↦ (U s)† * Y s * V s)
        ((U t)† * (Y' t + I • (K t * Y t - Y t * G t)) * V t)
        (Icc a b) t := by
    intro t ht hnot
    have hn : (t ∉ DU ∧ t ∉ DV) ∧ t ∉ DY := by
      simpa only [mem_union, not_or] using hnot
    have hUt := hUd t ht hn.1.1
    have hVt := hVd t ht hn.1.2
    have hYt := hYd t ht hn.2
    -- `(U†)' = iU†K`, as `K` is Hermitian.
    have hstar : HasDerivWithinAt (fun s ↦ (U s)†)
        (I • ((U t)† * K t)) (Icc a b) t := by
      simpa [show (K t)† = K t from (hKh ht).star_eq, Complex.star_def] using hUt.star
    constructor
    · -- The product rule: `(U†V)' = iU†KV - iU†GV`, the first line of (2.2).
      convert hstar.mul hVt using 1
      simp [mul_add, add_mul, mul_assoc, sub_eq_add_neg]
    · -- The product rule: `(U†YV)' = iU†KYV + U†Y'V - iU†YGV`, the third line of (2.2).
      convert (hstar.mul hYt).mul hVt using 1
      simp [mul_add, add_mul, mul_assoc, sub_eq_add_neg, add_comm, add_assoc]
  -- A continuous function whose derivative is regulated outside a countable set is the integral
  -- of its derivative, by Mathlib’s fundamental theorem off a countable set.
  refine ⟨hdUV, hdUYV, ?_, ?_⟩
  · exact (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab
      ((hDU.union hDV).union hDY) hUV
      (fun t ht ↦ ((hderivs t (Ioo_subset_Icc_self ht.1) ht.2).1.hasDerivAt
        (Icc_mem_nhds ht.1.1 ht.1.2)))
      (hdUV.intervalIntegrable dieudonne_7_6_1 hab)).symm
  · exact (MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab
      ((hDU.union hDV).union hDY) hUYV
      (fun t ht ↦ ((hderivs t (Ioo_subset_Icc_self ht.1) ht.2).2.hasDerivAt
        (Icc_mem_nhds ht.1.1 ht.1.2)))
      (hdUYV.intervalIntegrable dieudonne_7_6_1 hab)).symm

end RoundedClocks
