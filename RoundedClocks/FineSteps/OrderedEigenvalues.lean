/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.SpectralProjectorRank
public import RoundedClocks.Citations
public import RoundedClocks.Preliminaries.Basic

/-! # Eigenvalues in decreasing order and Weyl's perturbation theorem (Remark 3.8)

"By Weyl's perturbation theorem [Bhatia, Corollary III.2.6], truncation moves each ordered
eigenvalue by at most `ε_s`" (`weyl_decreasingOrder`). The shared preliminary construction lists
the eigenvalues of a Hermitian matrix in decreasing order, as Bhatia's corollary requires; this
file counts the eigenvalues in a set along that list and applies Weyl's theorem.
-/

@[expose] public section

noncomputable section

namespace RoundedClocks

open scoped Matrix.Norms.L2Operator

open Classical in
/-- The rank of the spectral projector for the eigenvalues in `S` is the number of indices `j`
with `λⱼ↓ ∈ S`. -/
theorem rank_spectralProjector_decreasingOrder {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (S : Set ℂ) :
    (spectralProjector A S).rank =
      (Finset.univ.filter (fun j =>
        (hA.eigenvalues (decreasingOrder hA j) : ℂ) ∈ S)).card := by
  exact (rank_spectralProjector hA S).trans
    (Finset.card_equiv (decreasingOrder hA) (by simp)).symm

/-- Remark 3.8: assuming Weyl's perturbation theorem (Bhatia, Corollary III.2.6), a perturbation
moves each ordered eigenvalue by at most its norm, `|λⱼ↓(A) - λⱼ↓(B)| ≤ ‖A - B‖`. -/
theorem weyl_decreasingOrder
    (hW : Bhatia_Corollary_III_2_6) {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (j : Fin d) :
    |hA.eigenvalues (decreasingOrder hA j) -
      hB.eigenvalues (decreasingOrder hB j)| ≤ ‖A - B‖ := by
  exact hW d A B _ _ hA hB
    (isDecreasingEigenvalueList_decreasingOrder hA)
    (isDecreasingEigenvalueList_decreasingOrder hB) j

end RoundedClocks
