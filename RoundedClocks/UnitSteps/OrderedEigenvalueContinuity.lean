/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Citations

/-! # Ordered Hermitian eigenvalues

Corollary 4.7 uses the decreasing eigenvalue list and its continuity to choose spectral phases
continuously along the unitary path.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Matrix

noncomputable section
namespace RoundedClocks.WalkLeakageBhatia

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Mathlib's sorted eigenvalues give Bhatia's list, including root multiplicities. -/
theorem exists_sorted_list {A : 𝕄} (hA : A.IsHermitian) :
    ∃ e : Fin d → ℝ, IsDecreasingEigenvalueList A e ∧ spectrum ℝ A = range e := by
  classical
  have hrange : spectrum ℝ A = range hA.eigenvalues₀ := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    let e : Fin (Fintype.card (Fin d)) ≃ Fin d :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e j, ?_⟩
      exact congrArg hA.eigenvalues₀ (e.symm_apply_apply j)
  have h : ∃ e : Fin (Fintype.card (Fin d)) → ℝ,
      (Antitone e ∧ A.charpoly.roots = Finset.univ.val.map (fun j ↦ (e j : ℂ))) ∧
        spectrum ℝ A = range e := by
    exact ⟨hA.eigenvalues₀, ⟨hA.eigenvalues₀_antitone,
      hA.roots_charpoly_eq_eigenvalues₀⟩, hrange⟩
  generalize hk : Fintype.card (Fin d) = k at h
  have hkd : k = d := hk.symm.trans (Fintype.card_fin d)
  clear hk
  subst k
  exact h

/-- The last entry of a decreasing spectral list is the real spectral infimum. -/
theorem sInf_eq_last [NeZero d] {A : 𝕄} {e : Fin d → ℝ}
    (he : Antitone e) (hs : spectrum ℝ A = range e) :
    sInf (spectrum ℝ A) = e ⟨d - 1, Nat.sub_lt (NeZero.pos d) (by omega)⟩ := by
  rw [hs]
  apply le_antisymm
  · exact csInf_le (Set.finite_range _).bddBelow ⟨_, rfl⟩
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨j, rfl⟩
    apply he
    change j.val ≤ d - 1
    omega

/-- Bhatia's estimate at the last index controls the least eigenvalue. -/
theorem sInf_sub_le [NeZero d] (bhatia : Bhatia_Corollary_III_2_6)
    {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |sInf (spectrum ℝ A) - sInf (spectrum ℝ B)| ≤ ‖A - B‖ := by
  obtain ⟨eA, heA, hsA⟩ := exists_sorted_list hA
  obtain ⟨eB, heB, hsB⟩ := exists_sorted_list hB
  rw [sInf_eq_last heA.1 hsA, sInf_eq_last heB.1 hsB]
  exact bhatia d A B eA eB hA hB heA heB _

/-- The least eigenvalue of a continuous Hermitian family is continuous by Bhatia. -/
theorem continuous_sInf [NeZero d] (bhatia : Bhatia_Corollary_III_2_6)
    {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) (hc : IsContinuousFamily H) :
    IsContinuousFamily (fun s ↦ sInf (spectrum ℝ (H s))) := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  have hcAt := Metric.continuousWithinAt_iff.mp (hc s hs)
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := hcAt ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht hts
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (sInf_sub_le bhatia (hH t ht) (hH s hs))
    (by simpa only [dist_eq_norm] using hclose ht hts)

end RoundedClocks.WalkLeakageBhatia
