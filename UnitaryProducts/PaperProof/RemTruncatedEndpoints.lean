/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.PropTransfer

public import UnitaryProducts.PaperProof.ThmTransfer
public import UnitaryProducts.PaperProof.ExTruncationBits

/-!
# Truncated endpoint projectors

## Declarations

- `bandProj_finrank`
- `truncated_endpoint_weyl_separation`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Set UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- An index projector has rank equal to the number of selected eigenvalues,
counting multiplicity. Here rank is the dimension of its range, which is precisely the span
of the selected eigenvectors. -/
theorem bandProj_finrank {A : 𝕄} (hA : A.IsHermitian) (S : Finset (Fin d)) :
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S
      A)).toLinearMap.range = S.card := by
  classical
  let b := hA.eigenvectorBasis
  have hr : ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S A)).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun i : S ↦ b i)) := by
    have happ (x : EuclideanSpace ℂ (Fin d)) :
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S A) x = ∑ i ∈ S, ⟪b i, x⟫_ℂ • b i
          := by
      simp [bandProj, dif_pos hA, b, ContinuousLinearMap.sum_apply,
        InnerProductSpace.rankOne_apply]
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      rw [show ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S A)).toLinearMap y =
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S A) y from rfl, happ]
      refine Submodule.sum_mem _ fun i hi ↦ ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      refine ⟨b i, ?_⟩
      change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (bandProj S A) (b i) = b i
      rw [happ]
      simp [orthonormal_iff_ite.mp b.orthonormal, Finset.sum_ite_eq', i.property]
  rw [hr]
  have hi : LinearIndependent ℂ (fun i : S ↦ hA.eigenvectorBasis i) :=
    (hA.eigenvectorBasis.orthonormal.comp _ Subtype.val_injective).linearIndependent
  simpa only [Fintype.card_coe] using finrank_span_eq_card hi

/-- Remark 3.8: every eigenvalue outside the band is separated from its entire
hull by `Γ`; Weyl leaves the other perturbed eigenvalues at distance at least
`Γ-ε > ε`, while precisely the original indices lie in the `ε` collar. -/
theorem truncated_endpoint_weyl_separation {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {S : Finset (Fin d)}
    (hS : IsBand hA S) (he : ‖A - D‖ < bandGap hA hS / 2) :
    let a := S.inf' hS.1 hA.eigenvalues
    let b := S.sup' hS.1 hA.eigenvalues
    let ε := ‖A - D‖
    let Γ := bandGap hA hS
    (∀ i, i ∈ S ↔ hD.eigenvalues i ∈ Icc (a - ε) (b + ε)) ∧
    (∀ i, i ∉ S → ∀ x ∈ Icc a b, Γ ≤ |hA.eigenvalues i - x| ∧
      Γ - ε ≤ |hD.eigenvalues i - x|) ∧ ε < Γ - ε := by
  intro a b ε Γ
  obtain ⟨m₀, r₀, hm₀⟩ := hS.2.2
  obtain ⟨hr, hm, hleft, hright⟩ := transfer_hull hA.eigenvalues hS.1 hm₀
  let m := (a + b) / 2
  let r := (b - a) / 2
  have hg := UnitaryProducts.hasGap_of_exact_distance hA S hS.1 hS.2.1 hm hleft hright
  have hw (i) : |hA.eigenvalues i - hD.eigenvalues i| ≤ ε :=
    UnitaryProducts.abs_eigenvalues_sub_le hA hD i
  have hout (i) (hi : i ∉ S) : r + Γ ≤ |hA.eigenvalues i - m| :=
    (hg i).resolve_left fun hin ↦ hi ((hm i).mpr hin)
  have hdist (i) (hi : i ∉ S) (x) (hx : x ∈ Icc a b) : Γ ≤ |hA.eigenvalues i - x| := by
    have hx' : |x - m| ≤ r := abs_le.mpr ⟨by dsimp [m, r]; linarith [hx.1],
      by dsimp [m, r]; linarith [hx.2]⟩
    linarith [abs_sub_le (hA.eigenvalues i) x m, hout i hi]
  refine ⟨?_, ?_, by dsimp [ε, Γ]; linarith⟩
  · intro i
    constructor
    · intro hi
      have h₁ := S.inf'_le hA.eigenvalues hi
      have h₂ := S.le_sup' hA.eigenvalues hi
      have hw' := abs_le.mp (hw i)
      exact ⟨by dsimp [a]; linarith [hw'.1, hw'.2], by dsimp [b]; linarith [hw'.1, hw'.2]⟩
    · intro hi
      by_contra hn
      have hx : |hD.eigenvalues i - m| ≤ r + ε := abs_le.mpr
        ⟨by dsimp [m, r]; linarith [hi.1], by dsimp [m, r]; linarith [hi.2]⟩
      have ht := abs_sub_le (hA.eigenvalues i) (hD.eigenvalues i) m
      have ho := hout i hn
      change ε < Γ / 2 at he
      linarith [hw i]
  · intro i hi x hx
    refine ⟨hdist i hi x hx, ?_⟩
    have ht := abs_sub_le (hA.eigenvalues i) (hD.eigenvalues i) x
    linarith [hw i, hdist i hi x hx]

end UnitaryProducts.PaperProof
