/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.PropTransfer

public import UnitaryProducts.PaperProof.ThmTransfer
public import UnitaryProducts.PaperProof.ExTruncationBits

/-!
# Truncated endpoint projectors

## Declarations

- `bandProj_finrank`
- `rem_truncated_endpoints`
- `truncated_endpoint_equal_rank`
- `truncated_endpoint_norm_identity`
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

/-- Remark 3.9: Weyl preserves the ordered indices in the actual error collar.
Both hull projectors therefore have rank `S.card`. -/
theorem truncated_endpoint_equal_rank {A D : 𝕄} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {S : Finset (Fin d)} (hS : IsBand hA S) (he : ‖A - D‖ < bandGap hA hS / 2) :
    let a := S.inf' hS.1 hA.eigenvalues
    let b := S.sup' hS.1 hA.eigenvalues
    let P := UnitaryProducts.windowProj ((a + b) / 2) ((b - a) / 2) A
    let Q := UnitaryProducts.windowProj ((a + b) / 2) ((b - a) / 2 + ‖A - D‖) D
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P).toLinearMap.range = S.card ∧
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) Q).toLinearMap.range = S.card
      := by
  intro a b P Q
  obtain ⟨hp, hq⟩ := hull_windowProj_eq_bandProj hA hD hS he
  change Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
    (UnitaryProducts.windowProj _ _ A)).toLinearMap.range = _ ∧
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (UnitaryProducts.windowProj _
      _ D)).toLinearMap.range = _
  rw [hp, hq]
  exact ⟨bandProj_finrank hA S, bandProj_finrank hD S⟩

/-- Remark 3.9: every eigenvalue outside the band is separated from its entire
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

/-- Remark 3.9, Exercise VII.1.11 and Davis–Kahan in the stated endpoint setting:
the full projector difference equals the directed difference, followed by its
`ε/(Γ-ε)` bound. The companion rank theorem verifies the equal-rank premise. -/
theorem truncated_endpoint_norm_identity {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {S : Finset (Fin d)}
    (hS : IsBand hA S) (he : ‖A - D‖ < bandGap hA hS / 2) :
    let a := S.inf' hS.1 hA.eigenvalues
    let b := S.sup' hS.1 hA.eigenvalues
    let P := UnitaryProducts.windowProj ((a + b) / 2) ((b - a) / 2) A
    let Q := UnitaryProducts.windowProj ((a + b) / 2) ((b - a) / 2 + ‖A - D‖) D
    ‖P - Q‖ = ‖(1 - Q) * P‖ ∧
      ‖(1 - Q) * P‖ ≤ ‖A - D‖ / (bandGap hA hS - ‖A - D‖) := by
  intro a b P Q
  obtain ⟨hp, hq⟩ := hull_windowProj_eq_bandProj hA hD hS he
  change ‖UnitaryProducts.windowProj _ _ A - UnitaryProducts.windowProj _ _ D‖ = _ ∧ _
  dsimp [P, Q]
  rw [hp, hq]
  exact UnitaryProducts.Prose.endpoint_projector_eq_directed_and_le hA hD hS he

/-- Remark 3.9: at both endpoints, Weyl gives the spectral collar, separation
from the band hull, and equal projector ranks. The full and directed projector
distances agree and satisfy Davis–Kahan; the leakage difference is bounded by
the evolution error plus both endpoint bounds. -/
theorem rem_truncated_endpoints {H U : ℝ → 𝕄} {T : ℝ}
    (hT : 0 < T) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    {S₀ S₁ : Finset (Fin d)}
    (hS₀ : IsBand (hH 0 ⟨le_rfl, zero_le_one⟩) S₀)
    (hS₁ : IsBand (hH 1 ⟨zero_le_one, le_rfl⟩) S₁)
    (k : ℕ)
    (he₀ : ‖H 0 - (truncation k).2.2.1 (H 0)‖ < bandGap _ hS₀ / 2)
    (he₁ : ‖H 1 - (truncation k).2.2.1 (H 1)‖ < bandGap _ hS₁ / 2) (W : 𝕄) :
    let ε₀ := ‖H 0 - ((truncation k).2.2.1 (H 0))‖
    let ε₁ := ‖H 1 - ((truncation k).2.2.1 (H 1))‖
    let Γ₀ := bandGap _ hS₀
    let Γ₁ := bandGap _ hS₁
    let a₀ := S₀.inf' hS₀.1 (hH 0 ⟨le_rfl, zero_le_one⟩).eigenvalues
    let b₀ := S₀.sup' hS₀.1 (hH 0 ⟨le_rfl, zero_le_one⟩).eigenvalues
    let a₁ := S₁.inf' hS₁.1 (hH 1 ⟨zero_le_one, le_rfl⟩).eigenvalues
    let b₁ := S₁.sup' hS₁.1 (hH 1 ⟨zero_le_one, le_rfl⟩).eigenvalues
    let P₀ := UnitaryProducts.windowProj ((a₀ + b₀) / 2) ((b₀ - a₀) / 2) (H 0)
    let P₁ := UnitaryProducts.windowProj ((a₁ + b₁) / 2) ((b₁ - a₁) / 2) (H 1)
    let P'₀ := UnitaryProducts.windowProj ((a₀ + b₀) / 2) ((b₀ - a₀) / 2 + ε₀)
      ((truncation k).2.2.1 (H 0))
    let P'₁ := UnitaryProducts.windowProj ((a₁ + b₁) / 2) ((b₁ - a₁) / 2 + ε₁)
      ((truncation k).2.2.1 (H 1))
    let hD₀ := (scalarEntryMap_and_error_isHermitian _ (ex_truncation_bits (d := d) k).1
      (hH 0 ⟨le_rfl, zero_le_one⟩)).1
    let hD₁ := (scalarEntryMap_and_error_isHermitian _ (ex_truncation_bits (d := d) k).1
      (hH 1 ⟨zero_le_one, le_rfl⟩)).1
    ‖P₀ - P'₀‖ ≤ ε₀ / (Γ₀ - ε₀) ∧
    ‖P₁ - P'₁‖ ≤ ε₁ / (Γ₁ - ε₁) ∧
    (∀ i, i ∈ S₀ ↔ hD₀.eigenvalues i ∈ Icc (a₀ - ε₀) (b₀ + ε₀)) ∧
    (∀ i, i ∈ S₁ ↔ hD₁.eigenvalues i ∈ Icc (a₁ - ε₁) (b₁ + ε₁)) ∧
    (∀ i, i ∉ S₀ → ∀ x ∈ Icc a₀ b₀,
      Γ₀ ≤ |(hH 0 ⟨le_rfl, zero_le_one⟩).eigenvalues i - x| ∧
      Γ₀ - ε₀ ≤ |hD₀.eigenvalues i - x|) ∧
    (∀ i, i ∉ S₁ → ∀ x ∈ Icc a₁ b₁,
      Γ₁ ≤ |(hH 1 ⟨zero_le_one, le_rfl⟩).eigenvalues i - x| ∧
      Γ₁ - ε₁ ≤ |hD₁.eigenvalues i - x|) ∧
    ε₀ < Γ₀ - ε₀ ∧ ε₁ < Γ₁ - ε₁ ∧
    (∀ i, |(hH 0 ⟨le_rfl, zero_le_one⟩).eigenvalues i - hD₀.eigenvalues i| ≤ ε₀) ∧
    (∀ i, |(hH 1 ⟨zero_le_one, le_rfl⟩).eigenvalues i - hD₁.eigenvalues i| ≤ ε₁) ∧
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P₀).toLinearMap.range =
      Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P'₀).toLinearMap.range ∧
    Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P₁).toLinearMap.range =
      Module.finrank ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P'₁).toLinearMap.range ∧
    (‖P₀ - P'₀‖ = ‖(1 - P'₀) * P₀‖ ∧ ‖(1 - P'₀) * P₀‖ ≤ ε₀ / (Γ₀ - ε₀)) ∧
    (‖P₁ - P'₁‖ = ‖(1 - P'₁) * P₁‖ ∧ ‖(1 - P'₁) * P₁‖ ≤ ε₁ / (Γ₁ - ε₁)) ∧
    |‖(1 - P'₁) * W * P'₀‖ - ‖(1 - P₁) * U T * P₀‖| ≤
      ‖W - U T‖ + ε₀ / (Γ₀ - ε₀) + ε₁ / (Γ₁ - ε₁) := by
  intro ε₀ ε₁ Γ₀ Γ₁ a₀ b₀ a₁ b₁ P₀ P₁ P'₀ P'₁ hD₀ hD₁
  have hsep₀ := truncated_endpoint_weyl_separation (hH 0 ⟨le_rfl, zero_le_one⟩) hD₀ hS₀ he₀
  have hsep₁ := truncated_endpoint_weyl_separation (hH 1 ⟨zero_le_one, le_rfl⟩) hD₁ hS₁ he₁
  have hrank₀ := truncated_endpoint_equal_rank (hH 0 ⟨le_rfl, zero_le_one⟩) hD₀ hS₀ he₀
  have hrank₁ := truncated_endpoint_equal_rank (hH 1 ⟨zero_le_one, le_rfl⟩) hD₁ hS₁ he₁
  have hnorm₀ := truncated_endpoint_norm_identity (hH 0 ⟨le_rfl, zero_le_one⟩) hD₀ hS₀ he₀
  have hnorm₁ := truncated_endpoint_norm_identity (hH 1 ⟨zero_le_one, le_rfl⟩) hD₁ hS₁ he₁
  have hbound₀ : ‖P₀ - P'₀‖ ≤ ε₀ / (Γ₀ - ε₀) := hnorm₀.1.trans_le hnorm₀.2
  have hbound₁ : ‖P₁ - P'₁‖ ≤ ε₁ / (Γ₁ - ε₁) := hnorm₁.1.trans_le hnorm₁.2
  have htransfer := prop_transfer (P := P₀) (Q := P₁) (Pt := P'₀) (Qt := P'₁)
    (U := U T) (W := W)
    (isStarProjection_windowProj _ _ _) (isStarProjection_windowProj _ _ _)
    (isStarProjection_windowProj _ _ _) (isStarProjection_windowProj _ _ _)
    (show (1 : 𝕄) ∈ unitary 𝕄 from one_mem _) (one_mem _)
    (Commute.one_left P'₁) (Commute.one_left P'₀)
  have hUT : ‖U T‖ ≤ 1 :=
    norm_le_one_of_star_mul_self (hU.2.2.1 T ⟨hT.le, le_rfl⟩)
  have hleft : ‖P'₀ - P₀‖ ≤ ε₀ / (Γ₀ - ε₀) := by
    rw [norm_sub_rev]
    exact hbound₀
  have hright : ‖P'₁ - P₁‖ ≤ ε₁ / (Γ₁ - ε₁) := by
    rw [norm_sub_rev]
    exact hbound₁
  refine ⟨hbound₀, hbound₁, hsep₀.1, hsep₁.1, hsep₀.2.1, hsep₁.2.1,
    hsep₀.2.2, hsep₁.2.2, ?_, ?_, hrank₀.1.trans hrank₀.2.symm,
    hrank₁.1.trans hrank₁.2.symm, hnorm₀, hnorm₁, ?_⟩
  · exact fun i ↦ UnitaryProducts.abs_eigenvalues_sub_le
      (hH 0 ⟨le_rfl, zero_le_one⟩) hD₀ i
  · exact fun i ↦ UnitaryProducts.abs_eigenvalues_sub_le
      (hH 1 ⟨zero_le_one, le_rfl⟩) hD₁ i
  · calc
      _ ≤ ‖W - U T‖ + ‖U T‖ * (‖P'₀ - P₀‖ + ‖P'₁ - P₁‖) := by
        simpa only [one_mul, mul_one] using htransfer
      _ ≤ ‖W - U T‖ + 1 * (‖P'₀ - P₀‖ + ‖P'₁ - P₁‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hUT
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤ ‖W - U T‖ + ε₀ / (Γ₀ - ε₀) + ε₁ / (Γ₁ - ε₁) := by
        rw [one_mul]
        linarith

end UnitaryProducts.PaperProof
