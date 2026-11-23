/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic

/-! # Spectral projectors

For Example 5.3, a continuous family of projectors that is a spectral projector of `H(s)` for every
`s` other than one point is, at that point too, an orthogonal projector commuting with `H(s)`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The interval `[0,1]` with one point removed is dense in `[0,1]`. -/
theorem crossing_interval_dense (s₀ : ℝ) :
    Icc (0 : ℝ) 1 ⊆ closure (Icc (0 : ℝ) 1 \ {s₀}) := by
  intro s hs
  by_cases h : s = s₀
  · subst h
    exact mem_closure_ne_iff_frequently_within.mpr (frequently_mem_iff_neBot.mpr
      (isPreconnected_Icc.preperfect_of_nontrivial ⟨0, by simp, 1, by simp, by norm_num⟩ s hs))
  · exact subset_closure ⟨hs, h⟩

/-- Example 5.3, "by continuity": if `P(s)` is continuous and, for every `s ∈ [0,1]` other than
`s₀`, a spectral projector of `H(s)` for one eigenvalue, then every `P(s)` is an orthogonal
projector commuting with `H(s)`. -/
theorem crossing_projectors_extend (H P : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hcH : ContinuousOn H (Icc (0 : ℝ) 1)) (hcP : IsContinuousFamily P) (s₀ : ℝ)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ s₀ → IsOneEigenvalueProjector (P s) (H s)) :
    ∀ s ∈ Icc (0 : ℝ) 1, IsOrthogonalProjector (P s) ∧ Commute (P s) (H s) := by
  have hoff : ∀ s ∈ Icc (0 : ℝ) 1 \ {s₀},
      IsOrthogonalProjector (P s) ∧ Commute (P s) (H s) := by
    intro s hs
    obtain ⟨mu, heq⟩ := hP s hs.1 (by simpa using hs.2)
    rw [IsSpectralProjector] at heq
    rw [heq]
    exact ⟨spectralProjector_isOrthogonal _ _,
      spectralProjector_commute (hH hs.1) _⟩
  have hsub : Icc (0 : ℝ) 1 \ {s₀} ⊆ Icc (0 : ℝ) 1 := diff_subset
  have hid : EqOn (fun s ↦ P s * P s) P (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isIdempotentElem.eq)
      (hcP.mul hcP) hcP hsub (crossing_interval_dense s₀)
  have hstar : EqOn (fun s ↦ star (P s)) P (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isSelfAdjoint.star_eq)
      hcP.star hcP hsub (crossing_interval_dense s₀)
  have hcomm : EqOn (fun s ↦ P s * H s) (fun s ↦ H s * P s)
      (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).2.eq)
      (hcP.mul hcH) (hcH.mul hcP) hsub (crossing_interval_dense s₀)
  intro s hs
  exact ⟨⟨hid hs, hstar hs⟩, hcomm hs⟩

end RoundedClocks
