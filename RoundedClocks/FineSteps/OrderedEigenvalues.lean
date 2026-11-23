/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.SpectralProjectorRank
public import RoundedClocks.Citations

/-! # Ordered eigenvalues at truncated endpoints

The truncated-endpoint statement reindexes the Hermitian eigenvalues in decreasing order and
identifies the ranks selected by the two endpoint projectors.
-/

@[expose] public section

noncomputable section

namespace RoundedClocks

open scoped Matrix.Norms.L2Operator

/-- Sorting in the dual order reindexes the eigenvalues in decreasing order. -/
def truncated_endpoints_eigenvalueOrder {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : Equiv.Perm (Fin d) :=
  Tuple.sort (α := OrderDual ℝ) hA.eigenvalues

/-- The decreasing eigenvalue list retains every eigenvalue with its multiplicity. -/
theorem truncated_endpoints_decreasingEigenvalues {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    IsDecreasingEigenvalueList A
      (fun j => hA.eigenvalues (truncated_endpoints_eigenvalueOrder hA j)) := by
  constructor
  · exact Tuple.monotone_sort (α := OrderDual ℝ) hA.eigenvalues
  · rw [hA.roots_charpoly_eq_eigenvalues]
    have h := Multiset.map_univ_val_equiv (truncated_endpoints_eigenvalueOrder hA)
    have hm := congrArg
      (Multiset.map (fun j => (hA.eigenvalues j : ℂ))) h
    simpa only [Multiset.map_map, Function.comp_def] using hm.symm

open Classical in
/-- Permuting eigenvalue indices preserves the cardinality of every spectral filter. -/
theorem truncated_endpoints_filter_card_reindex {d : ℕ} (e : Fin d → ℝ)
    (σ : Equiv.Perm (Fin d)) (S : Set ℂ) :
    (Finset.univ.filter (fun j => (e (σ j) : ℂ) ∈ S)).card =
      (Finset.univ.filter (fun j => (e j : ℂ) ∈ S)).card := by
  classical
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, σ.apply_symm_apply] using hj

open Classical in
/-- The spectral rank is also the filter count in decreasing eigenvalue order. -/
theorem truncated_endpoints_spectralProjector_rank_ordered {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (S : Set ℂ) :
    (spectralProjector A S).rank =
      (Finset.univ.filter (fun j =>
        (hA.eigenvalues (truncated_endpoints_eigenvalueOrder hA j) : ℂ) ∈ S)).card := by
  rw [truncated_endpoints_filter_card_reindex]
  exact truncated_endpoints_spectralProjector_rank hA S

/-- Bhatia's supplied Weyl bound pairs the two decreasing lists index by index. -/
theorem truncated_endpoints_paired_eigenvalue_bound
    (hW : Bhatia_Corollary_III_2_6) {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (j : Fin d) :
    |hA.eigenvalues (truncated_endpoints_eigenvalueOrder hA j) -
      hB.eigenvalues (truncated_endpoints_eigenvalueOrder hB j)| ≤ ‖A - B‖ := by
  exact hW d A B _ _ hA hB
    (truncated_endpoints_decreasingEigenvalues hA)
    (truncated_endpoints_decreasingEigenvalues hB) j

end RoundedClocks
