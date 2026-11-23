/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.OrderedEigenvalues

/-! # Remark 3.8, second paragraph: separation of eigenvalues and equal rank

In the paper's words, for `A = H(s)` with band `S`, spectral gap `Γ`, and `I = [min S, max S]`,
and for `B = H^{(k)}(s)` with `ε = ‖A - B‖ < Γ/2`:

* "The eigenvalues of `H(s)` outside `S_s` lie at distance at least `Γ` from `I_s`":
  `truncated_endpoints_original_separation`;
* "truncation moves each ordered eigenvalue by at most `ε_s`, so `P̃_s` and `P_s` have equal rank":
  `truncated_endpoints_index_membership`, `truncated_endpoints_equal_rank`;
* "the other eigenvalues of `H^{(k)}(s)` lie at distance at least `Γ - ε_s > ε_s` from `I_s`":
  `truncated_endpoints_perturbed_separation`.
-/

@[expose] public section

noncomputable section

namespace RoundedClocks

open Set
open scoped Matrix.Norms.L2Operator

/-- A real `x` belongs to `interval a b`, the complex numbers `{λ : a < λ < b}`, exactly when
`a < x < b`. -/
theorem ofReal_mem_interval {a b x : ℝ} :
    (x : ℂ) ∈ interval a b ↔ x ∈ Ioo a b := by
  simp [interval]

/-- The set `S` of eigenvalues in a band is finite and nonempty, so it has a least and a greatest
element. -/
theorem band_finite_nonempty {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ} (hband : IsBand A a b) :
    let S := {x : ℝ | (x : ℂ) ∈ spectrum ℂ A ∩ interval a b}
    S.Finite ∧ S.Nonempty := by
  dsimp
  constructor
  · exact ((Matrix.finite_spectrum A).inter_of_left _).preimage
      Complex.ofReal_injective.injOn
  · obtain ⟨z, hz, x, hx, rfl⟩ := hband.2.1
    exact ⟨x, hz, ⟨x, hx, rfl⟩⟩

/-- Remark 3.8: the eigenvalues of `A` outside the band `S` lie at distance at least the spectral
gap `Γ` from `I = [min S, max S]`. -/
theorem truncated_endpoints_original_separation {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ} (hband : IsBand A a b)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ A \ interval a b) :
    ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
      (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b ≤ |μ - x| := by
  let S := {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}
  obtain ⟨hfin, hne⟩ := band_finite_nonempty hband
  -- `min S` and `max S` are eigenvalues in the band, so `μ` is at distance at least `Γ` from
  -- each of them.
  have hlo : sInf S ∈ S := hne.csInf_mem hfin
  have hhi : sSup S ∈ S := hne.csSup_mem hfin
  have hgap (y : ℝ) (hy : y ∈ S) : spectralGap A a b ≤ |y - μ| := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨u, v, hu, hv, rfl⟩
      exact abs_nonneg _
    · exact ⟨y, μ, hy, hμ, rfl⟩
  have hnot : ¬ (a < μ ∧ μ < b) := by
    simpa [ofReal_mem_interval] using hμ.2
  intro x hx
  change sInf S ≤ x ∧ x ≤ sSup S at hx
  have hl := (ofReal_mem_interval.mp hlo.2).1
  have hu := (ofReal_mem_interval.mp hhi.2).2
  -- `μ` is not in `(a,b)`. If `μ ≤ a`, then `μ < min S ≤ x`, so `|μ - x| ≥ min S - μ ≥ Γ`.
  -- Otherwise `μ ≥ b`, and `|μ - x| ≥ μ - max S ≥ Γ`.
  by_cases hleft : μ ≤ a
  · have hg := hgap _ hlo
    rw [abs_of_nonneg (by linarith)] at hg
    rw [abs_of_nonpos (by linarith)]
    linarith [hx.1]
  · have hright : b ≤ μ := by
      by_contra h
      exact hnot ⟨lt_of_not_ge hleft, lt_of_not_ge h⟩
    have hg := hgap _ hhi
    rw [abs_of_nonpos (by linarith)] at hg
    rw [abs_of_nonneg (by linarith)]
    linarith [hx.2]

/-- Let `|ξ - μ| ≤ ε < Γ/2`, and let `ξ` be either in `[l,u]` or at distance at least `Γ` from
it. Then `ξ ∈ [l,u]` exactly when `μ` is within `ε` of `[l,u]`. -/
theorem truncated_endpoints_scalar_membership {l u Γ ε ξ μ : ℝ}
    (hlu : l ≤ u) (hsmall : ε < Γ / 2)
    (hpair : |ξ - μ| ≤ ε)
    (hsep : ξ ∉ Icc l u → ∀ x ∈ Icc l u, Γ ≤ |ξ - x|) :
    ξ ∈ Icc l u ↔ μ ∈ Icc (l - ε) (u + ε) := by
  obtain ⟨hp, hm⟩ := abs_le.mp hpair
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · -- If `ξ ∉ [l,u]`, it is at distance at least `Γ > 2ε` from `l` and from `u`, so `μ` is not
    -- within `ε` of `[l,u]`.
    intro h
    by_contra hn
    have hl := hsep hn l ⟨le_rfl, hlu⟩
    have hu := hsep hn u ⟨hlu, le_rfl⟩
    by_cases hlow : ξ < l
    · rw [abs_of_nonpos (by linarith)] at hl
      linarith [h.1]
    · have hhigh : u < ξ := by
        by_contra hh
        exact hn ⟨le_of_not_gt hlow, le_of_not_gt hh⟩
      rw [abs_of_nonneg (by linarith)] at hu
      linarith [h.2]

/-- If `|ξ - μ| ≤ ε` and `ξ` is at distance at least `Γ` from `x`, then `μ` is at distance at
least `Γ - ε` from `x`. -/
theorem truncated_endpoints_scalar_separation {Γ ε ξ μ x : ℝ}
    (hpair : |ξ - μ| ≤ ε) (hsep : Γ ≤ |ξ - x|) :
    Γ - ε ≤ |μ - x| := by
  have htriangle : |ξ - x| ≤ |ξ - μ| + |μ - x| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (ξ - μ) (μ - x)
  linarith

/-- An eigenvalue of `A` is in the band `{λ : a < λ < b}` exactly when it lies in
`I = [min S, max S]`. -/
theorem truncated_endpoints_mem_band_iff {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b ξ : ℝ} (hband : IsBand A a b)
    (hξ : (ξ : ℂ) ∈ spectrum ℂ A) :
    (ξ : ℂ) ∈ interval a b ↔
      ξ ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
        (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}) := by
  obtain ⟨hf, hn⟩ := band_finite_nonempty hband
  constructor
  · intro hi
    exact ⟨csInf_le hf.bddBelow ⟨hξ, hi⟩, le_csSup hf.bddAbove ⟨hξ, hi⟩⟩
  · intro hi
    have hl := ofReal_mem_interval.mp (hn.csInf_mem hf).2
    have hu := ofReal_mem_interval.mp (hn.csSup_mem hf).2
    apply ofReal_mem_interval.mpr
    exact ⟨lt_of_lt_of_le hl.1 hi.1, lt_of_le_of_lt hi.2 hu.2⟩

/-- If `ξ` is an eigenvalue of `A`, `|ξ - μ| ≤ ε`, and `ε < Γ/2`, then `ξ` is in the band exactly
when `μ` is within `ε` of `I = [min S, max S]`. -/
theorem truncated_endpoints_paired_membership {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b ε ξ μ : ℝ}
    (hband : IsBand A a b) (hξ : (ξ : ℂ) ∈ spectrum ℂ A)
    (hsmall : ε < spectralGap A a b / 2) (hpair : |ξ - μ| ≤ ε) :
    (ξ : ℂ) ∈ interval a b ↔ (μ : ℂ) ∈ nearBand A a b ε := by
  obtain ⟨hf, hn⟩ := band_finite_nonempty hband
  have he := truncated_endpoints_mem_band_iff hband hξ
  rw [he]
  have hlu := csInf_le hf.bddBelow (hn.csSup_mem hf)
  have hm := truncated_endpoints_scalar_membership hlu hsmall hpair
    (fun hnot => truncated_endpoints_original_separation hband
      ⟨hξ, fun hi => hnot (he.mp hi)⟩)
  simpa [nearBand] using hm

/-- Assuming Weyl's perturbation theorem, the `j`th largest eigenvalue of `A` is in the band
exactly when the `j`th largest eigenvalue of `B` is within `ε = ‖A - B‖` of `I = [min S, max S]`. -/
theorem truncated_endpoints_index_membership (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2) (j : Fin d) :
    (hband.1.eigenvalues (decreasingOrder hband.1 j) : ℂ)
        ∈ interval a b ↔
      (hB.eigenvalues (decreasingOrder hB j) : ℂ)
        ∈ nearBand A a b ‖A - B‖ := by
  apply truncated_endpoints_paired_membership hband _ hsmall
    (weyl_decreasingOrder hW hband.1 hB j)
  apply Set.mem_of_mem_of_subset ?_ (le_of_eq hband.1.spectrum_eq_image_range.symm)
  exact ⟨_, ⟨_, rfl⟩, rfl⟩

/-- Remark 3.8: assuming Weyl's perturbation theorem, `P` and `P̃` have equal rank. The rank of
`P` counts the `j` with `λⱼ↓(A)` in the band, and the rank of `P̃` counts the `j` with `λⱼ↓(B)`
within `ε` of `I`. -/
theorem truncated_endpoints_equal_rank (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2) :
    HasEqualRank (bandProjector A a b) (spectralProjector B (nearBand A a b ‖A - B‖)) := by
  classical
  -- Each rank counts the indices `j` of the eigenvalues, in decreasing order, that the projector
  -- selects, and the two conditions on `j` agree.
  unfold HasEqualRank bandProjector
  rw [rank_spectralProjector_decreasingOrder hband.1,
    rank_spectralProjector_decreasingOrder hB]
  congr 1
  apply Finset.filter_congr
  intro j hj
  exact truncated_endpoints_index_membership hW hband hB hsmall j

/-- Remark 3.8: assuming Weyl's perturbation theorem, the eigenvalues of `B` that are not within
`ε = ‖A - B‖` of `I = [min S, max S]` lie at distance at least `Γ - ε` from `I`. -/
theorem truncated_endpoints_perturbed_separation (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ B \ nearBand A a b ‖A - B‖) :
    ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
      (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b - ‖A - B‖ ≤ |μ - x| := by
  -- `μ` is the `j`th largest eigenvalue of `B` for some `j`.
  have hm := hμ.1
  rw [hB.spectrum_eq_image_range] at hm
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hm
  have hi' : hB.eigenvalues i = μ := Complex.ofReal_injective hi
  let j := (decreasingOrder hB).symm i
  have hj : hB.eigenvalues (decreasingOrder hB j) = μ := by
    simpa [j] using hi'
  -- By Weyl's perturbation theorem, the `j`th largest eigenvalue `ξ` of `A` has `|ξ - μ| ≤ ε`.
  have hp := weyl_decreasingOrder hW hband.1 hB j
  rw [hj] at hp
  -- `ξ` is outside the band, as `μ` is not within `ε` of `I`.
  have hs : (hband.1.eigenvalues
      (decreasingOrder hband.1 j) : ℂ) ∈ spectrum ℂ A := by
    apply Set.mem_of_mem_of_subset ?_ (le_of_eq hband.1.spectrum_eq_image_range.symm)
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hout : (hband.1.eigenvalues
      (decreasingOrder hband.1 j) : ℂ) ∉ interval a b := by
    intro hin
    have hn := (truncated_endpoints_index_membership hW hband hB hsmall j).mp hin
    rw [hj] at hn
    exact hμ.2 hn
  -- So `ξ` is at distance at least `Γ` from `I`, and `μ` at distance at least `Γ - ε`.
  intro x hx
  exact truncated_endpoints_scalar_separation hp
    (truncated_endpoints_original_separation hband ⟨hs, hout⟩ x hx)

end RoundedClocks
