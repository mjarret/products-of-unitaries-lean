/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.EvolutionAndFineSteps

/-!
# Evolutions on an arbitrary closed interval

The unnumbered existence paragraph in §2 starts its evolution at `a` on `[a,b]`.
Translation transports the zero-based construction and its continuous-solution
uniqueness and unitarity results to precisely that interval.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Set
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

private theorem continuousOn_translate {U : ℝ → 𝕄} {a b : ℝ}
    (hU : ContinuousOn U (Icc a b)) (c : ℝ) :
    ContinuousOn (fun t ↦ U (t + c)) (Icc (a - c) (b - c)) :=
  hU.comp (continuous_id.add continuous_const).continuousOn fun t ht ↦
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

private theorem schrodinger_translate {H U : ℝ → 𝕄} {a b c t : ℝ}
    (hd : HasDerivWithinAt U (-I • (H (t + c) * U (t + c))) (Icc a b) (t + c)) :
    HasDerivWithinAt (fun x ↦ U (x + c)) (-I • (H (t + c) * U (t + c)))
      (Icc (a - c) (b - c)) t := by
  have hm : MapsTo (fun x : ℝ ↦ x + c) (Icc (a - c) (b - c)) (Icc a b) :=
    fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simpa only [Function.comp_def, one_smul] using
    hd.scomp t ((hasDerivAt_id t).add_const c).hasDerivWithinAt hm

/-- Translating the generator and evolution by the same amount translates their interval.
The exceptional set is translated as an image, so it remains countable. -/
theorem IsEvolution.translate {H U : ℝ → 𝕄} {a b : ℝ}
    (hU : IsEvolution H U a b) (c : ℝ) :
    IsEvolution (fun t ↦ H (t + c)) (fun t ↦ U (t + c)) (a - c) (b - c) := by
  obtain ⟨hUc, hUa, hUU, S, hS, hUd⟩ := hU
  refine ⟨continuousOn_translate hUc c, by simpa only [sub_add_cancel] using hUa,
    fun t ht ↦ hUU (t + c) ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    (fun x : ℝ ↦ x - c) '' S, hS.image _, ?_⟩
  intro t ht hnot
  have htc : t + c ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnot' : t + c ∉ S := fun hs ↦ hnot ⟨t + c, hs, by ring⟩
  exact schrodinger_translate (hUd (t + c) htc hnot')

/-- The unnumbered existence claim in §2 on the paper's interval `[a,b]`:
every regulated Hermitian family generates a unique evolution starting at `a`. -/
theorem exists_unique_evolution_interval (H : ℝ → 𝕄) (a b : ℝ) (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hreg : IsRegulated H a b) :
    ∃ U : ℝ → 𝕄, IsEvolution H U a b ∧
      ∀ V : ℝ → 𝕄, IsEvolution H V a b → EqOn V U (Icc a b) := by
  rcases hab.eq_or_lt with heq | hab
  · subst b
    refine ⟨fun _ ↦ 1, ⟨continuousOn_const, rfl, ?_, {a}, countable_singleton a, ?_⟩, ?_⟩
    · intro t _
      simp
    · intro t ht hn
      have hta : t = a := le_antisymm ht.2 ht.1
      exact (hn (by simp only [mem_singleton_iff, hta])).elim
    · intro V hV t ht
      have hta : t = a := le_antisymm ht.2 ht.1
      simpa only [hta] using hV.2.1
  have hH0 : ∀ t ∈ Icc (0 : ℝ) (b - a), (H (t + a)).IsHermitian :=
    fun t ht ↦ hH (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hreg0 : IsRegulated (fun t ↦ H (t + a)) 0 (b - a) :=
    (show UnitaryProducts.Regulated H a b from hreg).translate_to_zero
  obtain ⟨U, hU, huniq⟩ := exists_unique_evolution (fun t ↦ H (t + a))
    (b - a) (sub_pos.mpr hab) hH0 hreg0
  refine ⟨fun t ↦ U (t - a), ?_, ?_⟩
  · simpa [sub_eq_add_neg, add_assoc] using hU.translate (-a)
  · intro V hV t ht
    have hV0 : IsEvolution (fun t ↦ H (t + a)) (fun t ↦ V (t + a)) 0 (b - a) := by
      simpa only [sub_self] using hV.translate a
    have h := huniq (fun t ↦ V (t + a)) hV0 (x := t - a)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [sub_add_cancel] using h

/-- The uniqueness assertion in §2 applies to continuous solutions before unitarity is known.
Neither candidate is assumed unitary, and Hermiticity alone suffices for uniqueness. -/
theorem evolution_eq_of_solves_off_countable_interval {H U V : ℝ → 𝕄} {a b : ℝ}
    (S R : Set ℝ) (hS : S.Countable) (hR : R.Countable)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hUa : U a = 1) (hVa : V a = 1)
    (hU : ∀ t ∈ Ioo a b, t ∉ S →
      HasDerivWithinAt U (-I • (H t * U t)) (Icc a b) t)
    (hV : ∀ t ∈ Ioo a b, t ∉ R →
      HasDerivWithinAt V (-I • (H t * V t)) (Icc a b) t) :
    EqOn U V (Icc a b) := by
  have hH0 : ∀ t ∈ Icc (0 : ℝ) (b - a), (H (t + a)).IsHermitian :=
    fun t ht ↦ hH (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hUc0 : ContinuousOn (fun t ↦ U (t + a)) (Icc 0 (b - a)) := by
    simpa only [sub_self] using continuousOn_translate hUc a
  have hVc0 : ContinuousOn (fun t ↦ V (t + a)) (Icc 0 (b - a)) := by
    simpa only [sub_self] using continuousOn_translate hVc a
  have hU0 : ∀ t ∈ Ioo (0 : ℝ) (b - a), t ∉ (fun x : ℝ ↦ x - a) '' S →
      HasDerivWithinAt (fun x ↦ U (x + a)) (-I • (H (t + a) * U (t + a)))
        (Icc 0 (b - a)) t := by
    intro t ht hnot
    have hnot' : t + a ∉ S := fun hs ↦ hnot ⟨t + a, hs, by ring⟩
    simpa only [sub_self] using schrodinger_translate
      (hU (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ hnot')
  have hV0 : ∀ t ∈ Ioo (0 : ℝ) (b - a), t ∉ (fun x : ℝ ↦ x - a) '' R →
      HasDerivWithinAt (fun x ↦ V (x + a)) (-I • (H (t + a) * V (t + a)))
        (Icc 0 (b - a)) t := by
    intro t ht hnot
    have hnot' : t + a ∉ R := fun hs ↦ hnot ⟨t + a, hs, by ring⟩
    simpa only [sub_self] using schrodinger_translate
      (hV (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ hnot')
  have h := UnitaryProducts.evolution_eq_of_solves_off_countable
    ((fun x : ℝ ↦ x - a) '' S) ((fun x : ℝ ↦ x - a) '' R) (hS.image _) (hR.image _)
    hH0 hUc0 hVc0 (by simpa only [zero_add] using hUa)
    (by simpa only [zero_add] using hVa) hU0 hV0
  intro t ht
  simpa only [sub_add_cancel] using h (x := t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The next sentence of §2: every continuous solution of the Hermitian equation with
`U(a)=1` is unitary, on an arbitrary interval `[a,b]`. -/
theorem star_mul_self_of_solves_off_countable_interval {H U : ℝ → 𝕄} {a b : ℝ}
    (S : Set ℝ) (hS : S.Countable)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian)
    (hUc : ContinuousOn U (Icc a b)) (hUa : U a = 1)
    (hU : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt U (-I • (H t * U t)) t) :
    ∀ t ∈ Icc a b, star (U t) * U t = 1 := by
  have hH0 : ∀ t ∈ Icc (0 : ℝ) (b - a), (H (t + a)).IsHermitian :=
    fun t ht ↦ hH (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hUc0 : ContinuousOn (fun t ↦ U (t + a)) (Icc 0 (b - a)) := by
    simpa only [sub_self] using continuousOn_translate hUc a
  have hU0 : ∀ t ∈ Ioo (0 : ℝ) (b - a), t ∉ (fun x : ℝ ↦ x - a) '' S →
      HasDerivAt (fun x ↦ U (x + a)) (-I • (H (t + a) * U (t + a))) t := by
    intro t ht hnot
    have hnot' : t + a ∉ S := fun hs ↦ hnot ⟨t + a, hs, by ring⟩
    simpa only [Function.comp_def, one_smul] using
      (hU (t + a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ hnot').scomp t
        ((hasDerivAt_id t).add_const a)
  have h := UnitaryProducts.star_mul_self_of_solves_off_countable
    ((fun x : ℝ ↦ x - a) '' S) (hS.image _) hH0 hUc0
    (by simpa only [zero_add] using hUa) hU0
  intro t ht
  simpa only [sub_add_cancel] using h (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Existence and uniqueness among continuous matrix solutions, before their unitarity is
imposed, as asserted in the existence paragraph of §2. -/
theorem exists_unique_continuous_evolution_interval (H : ℝ → 𝕄) (a b : ℝ) (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hreg : IsRegulated H a b) :
    ∃ U : ℝ → 𝕄, IsEvolution H U a b ∧
      ∀ (V : ℝ → 𝕄) (S : Set ℝ), S.Countable → ContinuousOn V (Icc a b) → V a = 1 →
        (∀ t ∈ Ioo a b, t ∉ S → HasDerivWithinAt V (-I • (H t * V t)) (Icc a b) t) →
        EqOn V U (Icc a b) := by
  obtain ⟨U, hU, _⟩ := exists_unique_evolution_interval H a b hab hH hreg
  refine ⟨U, hU, ?_⟩
  intro V S hS hVc hVa hV
  obtain ⟨hUc, hUa, _, R, hR, hUd⟩ := hU
  exact evolution_eq_of_solves_off_countable_interval S R hS hR hH hVc hUc hVa hUa hV
    (fun t ht hn ↦ hUd t (Ioo_subset_Icc_self ht) hn)

end UnitaryProducts.Paper
