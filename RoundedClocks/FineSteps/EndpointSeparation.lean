/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.OrderedEigenvalues

/-! # Separation of truncated endpoints

The truncated-endpoint statement converts separation from a closed interval into strict
inequalities for the ordered eigenvalues on both sides of the truncation window.
-/

@[expose] public section

noncomputable section

namespace RoundedClocks

open Set
open scoped Matrix.Norms.L2Operator

/-- Real membership in the complex interval is ordinary interval membership. -/
theorem truncated_endpoints_mem_interval {a b x : ℝ} :
    (x : ℂ) ∈ interval a b ↔ x ∈ Ioo a b := by
  simp [interval]

/-- The finite nonempty band contains its minimum and maximum. -/
theorem truncated_endpoints_band_extrema {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ} (hband : IsBand A a b) :
    let S := {x : ℝ | (x : ℂ) ∈ spectrum ℂ A ∩ interval a b}
    S.Finite ∧ S.Nonempty := by
  dsimp
  constructor
  · exact ((Matrix.finite_spectrum A).inter_of_left _).preimage
      Complex.ofReal_injective.injOn
  · obtain ⟨z, hz, x, hx, rfl⟩ := hband.2.1
    exact ⟨x, hz, ⟨x, hx, rfl⟩⟩

/-- An eigenvalue outside the band is separated from its whole convex interval. -/
theorem truncated_endpoints_original_separation {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ} (hband : IsBand A a b)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ A \ interval a b) :
    ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
      (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b ≤ |μ - x| := by
  let S := {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}
  obtain ⟨hfin, hne⟩ := truncated_endpoints_band_extrema hband
  have hlo : sInf S ∈ S := hne.csInf_mem hfin
  have hhi : sSup S ∈ S := hne.csSup_mem hfin
  have hgap (y : ℝ) (hy : y ∈ S) : spectralGap A a b ≤ |y - μ| := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨u, v, hu, hv, rfl⟩
      exact abs_nonneg _
    · exact ⟨y, μ, hy, hμ, rfl⟩
  have hnot : ¬ (a < μ ∧ μ < b) := by
    simpa [truncated_endpoints_mem_interval] using hμ.2
  intro x hx
  change sInf S ≤ x ∧ x ≤ sSup S at hx
  have hl := (truncated_endpoints_mem_interval.mp hlo.2).1
  have hu := (truncated_endpoints_mem_interval.mp hhi.2).2
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

/-- Weyl's bound preserves interval membership when the outside gap exceeds twice the error. -/
theorem truncated_endpoints_scalar_membership {l u Γ ε ξ μ : ℝ}
    (hlu : l ≤ u) (hsmall : ε < Γ / 2)
    (hpair : |ξ - μ| ≤ ε)
    (hsep : ξ ∉ Icc l u → ∀ x ∈ Icc l u, Γ ≤ |ξ - x|) :
    ξ ∈ Icc l u ↔ μ ∈ Icc (l - ε) (u + ε) := by
  obtain ⟨hp, hm⟩ := abs_le.mp hpair
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
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

/-- The perturbed outside eigenvalue loses at most the Weyl error in its separation. -/
theorem truncated_endpoints_scalar_separation {Γ ε ξ μ x : ℝ}
    (hpair : |ξ - μ| ≤ ε) (hsep : Γ ≤ |ξ - x|) :
    Γ - ε ≤ |μ - x| := by
  have htriangle : |ξ - x| ≤ |ξ - μ| + |μ - x| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (ξ - μ) (μ - x)
  linarith

/-- The half-gap hypothesis leaves a residual gap strictly larger than the error. -/
theorem truncated_endpoints_residual_gap {Γ ε : ℝ} (hsmall : ε < Γ / 2) :
    ε < Γ - ε := by
  linarith

/-- For spectral points, the band's open interval and its extremal closed interval agree. -/
theorem truncated_endpoints_band_iff_hull {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b ξ : ℝ} (hband : IsBand A a b)
    (hξ : (ξ : ℂ) ∈ spectrum ℂ A) :
    (ξ : ℂ) ∈ interval a b ↔
      ξ ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
        (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}) := by
  obtain ⟨hf, hn⟩ := truncated_endpoints_band_extrema hband
  constructor
  · intro hi
    exact ⟨csInf_le hf.bddBelow ⟨hξ, hi⟩, le_csSup hf.bddAbove ⟨hξ, hi⟩⟩
  · intro hi
    have hl := truncated_endpoints_mem_interval.mp (hn.csInf_mem hf).2
    have hu := truncated_endpoints_mem_interval.mp (hn.csSup_mem hf).2
    apply truncated_endpoints_mem_interval.mpr
    exact ⟨lt_of_lt_of_le hl.1 hi.1, lt_of_le_of_lt hi.2 hu.2⟩

/-- Paired spectral points belong to the original band and expanded band simultaneously. -/
theorem truncated_endpoints_paired_membership {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} {a b ε ξ μ : ℝ}
    (hband : IsBand A a b) (hξ : (ξ : ℂ) ∈ spectrum ℂ A)
    (hsmall : ε < spectralGap A a b / 2) (hpair : |ξ - μ| ≤ ε) :
    (ξ : ℂ) ∈ interval a b ↔ (μ : ℂ) ∈ nearBand A a b ε := by
  obtain ⟨hf, hn⟩ := truncated_endpoints_band_extrema hband
  have he := truncated_endpoints_band_iff_hull hband hξ
  rw [he]
  have hlu := csInf_le hf.bddBelow (hn.csSup_mem hf)
  have hm := truncated_endpoints_scalar_membership hlu hsmall hpair
    (fun hnot => truncated_endpoints_original_separation hband
      ⟨hξ, fun hi => hnot (he.mp hi)⟩)
  simpa [nearBand] using hm

/-- Bhatia's ordered pairing identifies the two spectral filters index by index. -/
theorem truncated_endpoints_index_membership (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2) (j : Fin d) :
    (hband.1.eigenvalues (truncated_endpoints_eigenvalueOrder hband.1 j) : ℂ)
        ∈ interval a b ↔
      (hB.eigenvalues (truncated_endpoints_eigenvalueOrder hB j) : ℂ)
        ∈ nearBand A a b ‖A - B‖ := by
  apply truncated_endpoints_paired_membership hband _ hsmall
    (truncated_endpoints_paired_eigenvalue_bound hW hband.1 hB j)
  apply Set.mem_of_mem_of_subset ?_ (le_of_eq hband.1.spectrum_eq_image_range.symm)
  exact ⟨_, ⟨_, rfl⟩, rfl⟩

/-- Equal ordered filter counts give equal ranks for the two endpoint projectors. -/
theorem truncated_endpoints_equal_rank (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2) :
    HasEqualRank (bandProjector A a b) (spectralProjector B (nearBand A a b ‖A - B‖)) := by
  classical
  unfold HasEqualRank bandProjector
  rw [truncated_endpoints_spectralProjector_rank_ordered hband.1,
    truncated_endpoints_spectralProjector_rank_ordered hB]
  congr 1
  apply Finset.filter_congr
  intro j hj
  exact truncated_endpoints_index_membership hW hband hB hsmall j

/-- Every excluded perturbed eigenvalue retains the original gap minus the Weyl error. -/
theorem truncated_endpoints_perturbed_separation (hW : Bhatia_Corollary_III_2_6)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ}
    (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ B \ nearBand A a b ‖A - B‖) :
    ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
      (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b - ‖A - B‖ ≤ |μ - x| := by
  have hm := hμ.1
  rw [hB.spectrum_eq_image_range] at hm
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hm
  have hi' : hB.eigenvalues i = μ := Complex.ofReal_injective hi
  let j := (truncated_endpoints_eigenvalueOrder hB).symm i
  have hj : hB.eigenvalues (truncated_endpoints_eigenvalueOrder hB j) = μ := by
    simpa [j] using hi'
  have hp := truncated_endpoints_paired_eigenvalue_bound hW hband.1 hB j
  rw [hj] at hp
  have hs : (hband.1.eigenvalues
      (truncated_endpoints_eigenvalueOrder hband.1 j) : ℂ) ∈ spectrum ℂ A := by
    apply Set.mem_of_mem_of_subset ?_ (le_of_eq hband.1.spectrum_eq_image_range.symm)
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hout : (hband.1.eigenvalues
      (truncated_endpoints_eigenvalueOrder hband.1 j) : ℂ) ∉ interval a b := by
    intro hin
    have hn := (truncated_endpoints_index_membership hW hband hB hsmall j).mp hin
    rw [hj] at hn
    exact hμ.2 hn
  intro x hx
  exact truncated_endpoints_scalar_separation hp
    (truncated_endpoints_original_separation hband ⟨hs, hout⟩ x hx)

end RoundedClocks
