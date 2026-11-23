/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.EvolutionComparisonCalculus

/-! # Bookkeeping for the proof of Theorem 2.2

The differentiability hypotheses of Theorem 2.2 restricted to one piece `[pⱼ, pⱼ₊₁]`, the last
line of (2.2) as an identity for almost every `t`, and the two rearrangements of finite sums in
the display of the proof: `∑ⱼ [f]_{pⱼ}^{pⱼ₊₁} = f(b) - f(a)` in its first equality, and
`∑ⱼ [fⱼ]_{pⱼ}^{pⱼ₊₁} = f_m(b) - f₀(a) - ∑ⱼ (fⱼ(pⱼ) - fⱼ₋₁(pⱼ))` in its last.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory
open Complex (I)

noncomputable section
namespace RoundedClocks
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A derivative outside a countable set of `[a,b]` is one outside a countable set of every
subinterval `[c,e]`. -/
lemma DerivativeOffCountable.mono {F D : ℝ → 𝕄} {a b c e : ℝ}
    (h : DerivativeOffCountable F D a b) (hsub : Icc c e ⊆ Icc a b) :
    DerivativeOffCountable F D c e := by
  obtain ⟨S, hS, hd⟩ := h
  exact ⟨S, hS, fun t ht hn ↦ (hd t (hsub ht) hn).mono hsub⟩

/-- If `Y'(t) = D(t)` for all `t` with `a < t < b` outside a countable set, then `Y` has
derivative `D` on `[a,b]` outside a countable set, which now also contains `a` and `b`. -/
lemma DerivativeOffCountable.of_Ioo {Y D : ℝ → 𝕄} {a b : ℝ}
    {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt Y (D t) t) :
    DerivativeOffCountable Y D a b := by
  refine ⟨insert b (insert a S), (hS.insert a).insert b, ?_⟩
  intro t ht hn
  have ha : a < t := lt_of_le_of_ne ht.1 fun h ↦ hn (Or.inr (Or.inl h.symm))
  have hb : t < b := lt_of_le_of_ne ht.2 fun h ↦ hn (Or.inl h)
  exact (hd t ⟨ha, hb⟩ fun h ↦ hn (Or.inr (Or.inr h))).hasDerivWithinAt

/-- Last line of (2.2). With `R = K - G - Y' - i(KY - YG)`, where `D` stands for `Y'`,
`iU†RV = iU†(K - G)V - i U†(Y' + i(KY - YG))V` for every `t` with `a < t < b` outside the
countable set `S`, hence for almost every `t`. -/
lemma comparison_residual_ae (K G U V Y D R : ℝ → 𝕄) {a b : ℝ}
    (hab : a ≤ b) {S : Set ℝ} (hS : S.Countable)
    (hR : ∀ t ∈ Ioo a b, t ∉ S →
      R t = K t - G t - D t - I • (K t * Y t - Y t * G t)) :
    (fun t ↦ I • ((U t)† * R t * V t)) =ᵐ[volume.restrict (uIoc a b)]
      (fun t ↦ I • ((U t)† * (K t - G t) * V t) -
        I • ((U t)† * (D t + I • (K t * Y t - Y t * G t)) * V t)) := by
  rw [uIoc_of_le hab]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ((hS.insert a).insert b).ae_notMem (volume.restrict (Ioc a b))] with t ht hn
  have htb : t < b := lt_of_le_of_ne ht.2 fun h ↦ hn (Or.inl h)
  rw [hR t ⟨ht.1, htb⟩ fun h ↦ hn (Or.inr (Or.inr h))]
  simp only [mul_sub, sub_mul, mul_add, add_mul, smul_sub, smul_add]
  module

/-- First equality in the display of the proof of Theorem 2.2:
`∑ⱼ (f(pⱼ₊₁) - f(pⱼ)) = f(pₙ₊₁) - f(p₀)`, also when some `pⱼ = pⱼ₊₁`. -/
lemma comparison_telescope {E : Type*} [AddCommGroup E] (F : ℝ → E)
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (F (p (j + 1)) - F (p j))) =
      F (p (n + 1)) - F (p 0) := Finset.sum_range_sub (fun j ↦ F (p j)) (n + 1)

/-- Last equality in the display of the proof of Theorem 2.2, regrouping the sum at each `pⱼ`:
`∑ⱼ (fⱼ(pⱼ₊₁) - fⱼ(pⱼ)) = fₙ(pₙ₊₁) - f₀(p₀) - ∑ⱼ (fⱼ₊₁(pⱼ₊₁) - fⱼ(pⱼ₊₁))`. -/
lemma comparison_boundaries {E : Type*} [AddCommGroup E] (F : ℕ → ℝ → E)
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (F j (p (j + 1)) - F j (p j))) =
      F n (p (n + 1)) - F 0 (p 0) -
        ∑ j ∈ Finset.range n, (F (j + 1) (p (j + 1)) - F j (p (j + 1))) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; abel

end RoundedClocks
