/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Citations

/-! # Differential identities for evolution comparison

Theorem 2.2 uses one-sided differentiation, adjoint differentiation, and the product rule to
compute the residual of the relative evolution.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Continuity on a closed interval supplies both one-sided limits. -/
lemma comparison_continuous_regulated {F : ℝ → 𝕄} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) : IsRegulated F a b := by
  constructor
  · intro t ht
    refine ⟨F t, (hF t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Icc_mem_nhdsGT ht.2) fun x hx ↦ ⟨ht.1.trans hx.1, hx.2⟩
  · intro t ht
    refine ⟨F t, (hF t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Icc_mem_nhdsLT ht.1) fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩

/-- Regulated matrix functions are closed under addition. -/
lemma comparison_regulated_add {F G : ℝ → 𝕄} {a b : ℝ}
    (hF : IsRegulated F a b) (hG : IsRegulated G a b) :
    IsRegulated (fun t ↦ F t + G t) a b := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hF.1 t ht
    obtain ⟨N, hN⟩ := hG.1 t ht
    exact ⟨L + N, hL.add hN⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hF.2 t ht
    obtain ⟨N, hN⟩ := hG.2 t ht
    exact ⟨L + N, hL.add hN⟩

/-- Regulated matrix functions are closed under subtraction. -/
lemma comparison_regulated_sub {F G : ℝ → 𝕄} {a b : ℝ}
    (hF : IsRegulated F a b) (hG : IsRegulated G a b) :
    IsRegulated (fun t ↦ F t - G t) a b := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hF.1 t ht
    obtain ⟨N, hN⟩ := hG.1 t ht
    exact ⟨L - N, hL.sub hN⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hF.2 t ht
    obtain ⟨N, hN⟩ := hG.2 t ht
    exact ⟨L - N, hL.sub hN⟩

/-- Regulated matrix functions are closed under multiplication. -/
lemma comparison_regulated_mul {F G : ℝ → 𝕄} {a b : ℝ}
    (hF : IsRegulated F a b) (hG : IsRegulated G a b) :
    IsRegulated (fun t ↦ F t * G t) a b := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hF.1 t ht
    obtain ⟨N, hN⟩ := hG.1 t ht
    exact ⟨L * N, hL.mul hN⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hF.2 t ht
    obtain ⟨N, hN⟩ := hG.2 t ht
    exact ⟨L * N, hL.mul hN⟩

/-- Taking adjoints preserves regulatedness. -/
lemma comparison_regulated_adjoint {F : ℝ → 𝕄} {a b : ℝ}
    (hF : IsRegulated F a b) : IsRegulated (fun t ↦ (F t)†) a b := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hF.1 t ht
    exact ⟨L†, hL.star⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hF.2 t ht
    exact ⟨L†, hL.star⟩

/-- Constant complex scalar multiplication preserves regulatedness. -/
lemma comparison_regulated_smul {F : ℝ → 𝕄} {a b : ℝ}
    (c : ℂ) (hF : IsRegulated F a b) : IsRegulated (fun t ↦ c • F t) a b := by
  constructor
  · intro t ht
    obtain ⟨L, hL⟩ := hF.1 t ht
    exact ⟨c • L, tendsto_const_nhds.smul hL⟩
  · intro t ht
    obtain ⟨L, hL⟩ := hF.2 t ht
    exact ⟨c • L, tendsto_const_nhds.smul hL⟩

/-- The two primitives on a correction interval follow from Dieudonné, Section 8.7. -/
lemma comparison_piece_primitives
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (K G U V Y Y' : ℝ → 𝕄) (a b : ℝ) (hab : a ≤ b)
    (hK : IsRegulated K a b) (hG : IsRegulated G a b)
    (hY' : IsRegulated Y' a b) (hKh : IsHermitianFamily K a b)
    (hU : ContinuousOn U (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hY : ContinuousOn Y (Icc a b))
    (hUd : DerivativeOffCountable U (fun t ↦ -I • (K t * U t)) a b)
    (hVd : DerivativeOffCountable V (fun t ↦ -I • (G t * V t)) a b)
    (hYd : DerivativeOffCountable Y Y' a b) :
    let P := fun t ↦ (U t)† * V t
    let Q := fun t ↦ (U t)† * Y t * V t
    let A := fun t ↦ I • ((U t)† * (K t - G t) * V t)
    let B := fun t ↦ (U t)† * (Y' t + I • (K t * Y t - Y t * G t)) * V t
    IsRegulated A a b ∧ IsRegulated B a b ∧
      (P b - P a = ∫ t in a..b, A t) ∧ (Q b - Q a = ∫ t in a..b, B t) := by
  dsimp only
  have hUr := comparison_regulated_adjoint (comparison_continuous_regulated hU)
  have hVr := comparison_continuous_regulated hV
  have hYr := comparison_continuous_regulated hY
  have hA := comparison_regulated_smul I
    (comparison_regulated_mul (comparison_regulated_mul hUr
      (comparison_regulated_sub hK hG)) hVr)
  have hB := comparison_regulated_mul (comparison_regulated_mul hUr
    (comparison_regulated_add hY' (comparison_regulated_smul I
      (comparison_regulated_sub (comparison_regulated_mul hK hYr)
        (comparison_regulated_mul hYr hG))))) hVr
  have hP := hU.star.mul hV
  have hQ := (hU.star.mul hY).mul hV
  obtain ⟨DU, hDU, hUd⟩ := hUd
  obtain ⟨DV, hDV, hVd⟩ := hVd
  obtain ⟨DY, hDY, hYd⟩ := hYd
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
    have hstar : HasDerivWithinAt (fun s ↦ (U s)†)
        (I • ((U t)† * K t)) (Icc a b) t := by
      simpa [show (K t)† = K t from (hKh t ht).eq, Complex.star_def] using hUt.star
    constructor
    · convert hstar.mul hVt using 1
      simp [mul_add, add_mul, mul_assoc, sub_eq_add_neg]
    · convert (hstar.mul hYt).mul hVt using 1
      simp [mul_add, add_mul, mul_assoc, sub_eq_add_neg, add_comm, add_assoc]
  refine ⟨hA, hB, ?_, ?_⟩
  · apply dieudonne_section_8_7 d _ _ a b hab hP hA
    exact ⟨DU ∪ DV ∪ DY, (hDU.union hDV).union hDY,
      fun t ht hn ↦ (hderivs t ht hn).1⟩
  · apply dieudonne_section_8_7 d _ _ a b hab hQ hB
    exact ⟨DU ∪ DV ∪ DY, (hDU.union hDV).union hDY,
      fun t ht hn ↦ (hderivs t ht hn).2⟩

end RoundedClocks
