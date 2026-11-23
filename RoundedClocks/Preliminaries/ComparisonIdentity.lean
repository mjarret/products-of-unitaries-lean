/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.EvolutionComparisonCalculus
public import RoundedClocks.Preliminaries.PiecewiseEvolution

/-! # Evolution comparison identity

Theorem 2.2 follows by differentiating the relative evolution, integrating its residual, and
bounding the resulting integral in operator norm.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory
open Complex (I)

noncomputable section
namespace RoundedClocks
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Restriction preserves the one-sided limits of a regulated family. -/
lemma comparison_regulated_restrict {F : ℝ → 𝕄} {a b c e : ℝ}
    (hF : IsRegulated F a b) (hac : a ≤ c) (heb : e ≤ b) : IsRegulated F c e := by
  exact ⟨fun t ht ↦ hF.1 t ⟨hac.trans ht.1, ht.2.trans_le heb⟩,
    fun t ht ↦ hF.2 t ⟨hac.trans_lt ht.1, ht.2.trans heb⟩⟩

/-- Derivative data restrict to any closed subinterval without an initial-value assumption. -/
lemma comparison_derivative_restrict {F D : ℝ → 𝕄} {a b c e : ℝ}
    (h : DerivativeOffCountable F D a b) (hsub : Icc c e ⊆ Icc a b) :
    DerivativeOffCountable F D c e := by
  obtain ⟨S, hS, hd⟩ := h
  exact ⟨S, hS, fun t ht hn ↦ (hd t (hsub ht) hn).mono hsub⟩

/-- Adding both endpoints turns interior correction data into closed-cell derivative data. -/
lemma comparison_correction_derivative {Y D : ℝ → 𝕄} {a b : ℝ}
    {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt Y (D t) t) :
    DerivativeOffCountable Y D a b := by
  refine ⟨insert b (insert a S), (hS.insert a).insert b, ?_⟩
  intro t ht hn
  have ha : a < t := lt_of_le_of_ne ht.1 fun h ↦ hn (Or.inr (Or.inl h.symm))
  have hb : t < b := lt_of_le_of_ne ht.2 fun h ↦ hn (Or.inl h)
  exact (hd t ⟨ha, hb⟩ fun h ↦ hn (Or.inr (Or.inr h))).hasDerivWithinAt

/-- The residual agrees almost everywhere with the difference of the two cited derivatives. -/
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

/-- Adjacent endpoint values telescope, including zero-length cells. -/
lemma comparison_telescope {E : Type*} [AddCommGroup E] (F : ℝ → E)
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (F (p (j + 1)) - F (p j))) =
      F (p (n + 1)) - F (p 0) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

/-- The sum of correction boundaries is its outer boundary minus its interior jumps. -/
lemma comparison_boundaries {E : Type*} [AddCommGroup E] (F : ℕ → ℝ → E)
    (p : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (F j (p (j + 1)) - F j (p j))) =
      F n (p (n + 1)) - F 0 (p 0) -
        ∑ j ∈ Finset.range n, (F (j + 1) (p (j + 1)) - F j (p (j + 1))) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; abel

/-- Weakly ordered partition points stay ordered at arbitrary indices. -/
lemma comparison_partition_mono {p : ℕ → ℝ} {m : ℕ}
    (hp : ∀ j ≤ m, p j ≤ p (j + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1) :
    p i ≤ p j := by
  induction j generalizing i with
  | zero => have hi : i = 0 := by omega
            subst i
            exact le_rfl
  | succ j ih =>
      rcases hij.eq_or_lt with rfl | hij
      · exact le_rfl
      · exact (ih (Nat.le_of_lt_succ hij) (by omega)).trans (hp j (by omega))

end RoundedClocks
