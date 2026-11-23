/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.EndpointSeparation
public import RoundedClocks.Preliminaries.Basic

/-! # Remark 3.8: the projectors at one endpoint

The second paragraph of Remark 3.8 for one Hermitian matrix `A = H(s)` and its truncation
`B = H^{(k)}(s)`: the spectral projectors `P` of `A` and `P̃` of `B` have equal rank, by Weyl's
perturbation theorem, so `‖P - P̃‖ = ‖(1 - P̃) P‖` by Bhatia, Exercise VII.1.11, and
`‖(1 - P̃) P‖ ≤ ε/(Γ - ε)` by the Davis–Kahan `sin Θ` theorem (`truncated_endpoint_projectors`).
The last paragraph of the remark uses `‖U(T)‖ = 1` (`norm_evolution_end`).
-/

@[expose] public section

noncomputable section
namespace RoundedClocks
open Set
open scoped Matrix.Norms.L2Operator

/-- A real `μ` at distance at least `δ > 0` from every point of `[l,u]` satisfies `μ ≤ l - δ` or
`u + δ ≤ μ`. This is the form in which Bhatia's Theorem VII.3.1 takes the separation of the two
sets of eigenvalues. -/
theorem truncated_endpoints_outside_strip {l u δ μ : ℝ} (hlu : l ≤ u)
    (hδ : 0 < δ) (hsep : ∀ x ∈ Icc l u, δ ≤ |μ - x|) :
    μ ≤ l - δ ∨ u + δ ≤ μ := by
  by_cases hl : μ < l
  · have h := hsep l ⟨le_rfl, hlu⟩
    rw [abs_of_nonpos (by linarith)] at h
    exact Or.inl (by linarith)
  · have hu : u < μ := by
      by_contra hn
      have h := hsep μ ⟨le_of_not_gt hl, le_of_not_gt hn⟩
      simp only [sub_self, abs_zero] at h
      exact (not_le_of_gt hδ) h
    have h := hsep u ⟨hlu, le_rfl⟩
    rw [abs_of_nonneg (by linarith)] at h
    exact Or.inr (by linarith)

/-- Remark 3.8, second paragraph, at one endpoint. Assuming Weyl's perturbation theorem (Bhatia,
Corollary III.2.6), Bhatia, Exercise VII.1.11, and the Davis–Kahan `sin Θ` theorem (Bhatia,
Theorem VII.3.1), let `A` be Hermitian with a band `{λ : a < λ < b}`, spectral gap `Γ`, and
spectral projector `P`. Let `B` be Hermitian with `ε = ‖A - B‖ < Γ/2`, and let `P̃` be the spectral
projector of `B` for its eigenvalues within `ε` of `I = [min S, max S]`, where `S` is the set of
eigenvalues of `A` in the band. Then `P` and `P̃` have equal rank, and
`‖P - P̃‖ = ‖(1 - P̃) P‖ ≤ ε/(Γ - ε)`. -/
theorem truncated_endpoint_projectors {d : ℕ}
    (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    (bhatia_exercise_VII_1_11 : Bhatia_Exercise_VII_1_11)
    (bhatia_theorem_VII_3_1 : Bhatia_Theorem_VII_3_1)
    {A B : Matrix (Fin d) (Fin d) ℂ} {a b : ℝ} (hband : IsBand A a b) (hB : B.IsHermitian)
    (hsmall : ‖A - B‖ < spectralGap A a b / 2) :
    HasEqualRank (bandProjector A a b) (spectralProjector B (nearBand A a b ‖A - B‖)) ∧
      ‖bandProjector A a b - spectralProjector B (nearBand A a b ‖A - B‖)‖ =
        ‖(1 - spectralProjector B (nearBand A a b ‖A - B‖)) * bandProjector A a b‖ ∧
      ‖(1 - spectralProjector B (nearBand A a b ‖A - B‖)) * bandProjector A a b‖ ≤
        ‖A - B‖ / (spectralGap A a b - ‖A - B‖) := by
  -- By Weyl's perturbation theorem, `P` and `P̃` have equal rank.
  have hrank := truncated_endpoints_equal_rank bhatia_corollary_III_2_6 hband hB hsmall
  -- At equal rank, `‖P - P̃‖ = ‖(1 - P̃) P‖` (Bhatia, Exercise VII.1.11).
  have heq := bhatia_exercise_VII_1_11 d _ _
    (spectralProjector_isOrthogonal _ _) (spectralProjector_isOrthogonal _ _) hrank
  refine ⟨hrank, heq, ?_⟩
  -- The Davis–Kahan theorem with `δ = Γ - ε > 0` bounds `‖(1 - P̃) P‖` by `ε/(Γ - ε)`: the
  -- eigenvalues of `A` in the band lie in `I`, and the eigenvalues of `B` that are not within `ε`
  -- of `I` lie at distance at least `Γ - ε` from `I`.
  have hδ : 0 < spectralGap A a b - ‖A - B‖ := by linarith [norm_nonneg (A - B)]
  obtain ⟨hf, hn⟩ := band_finite_nonempty hband
  apply bhatia_theorem_VII_3_1 d A B _ _ (interval a b) _ _ hband.1 hB rfl rfl hδ
    (sInf {x : ℝ | (x : ℂ) ∈ spectrum ℂ A ∩ interval a b})
    (sSup {x : ℝ | (x : ℂ) ∈ spectrum ℂ A ∩ interval a b})
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz.2
    exact ⟨csInf_le hf.bddBelow ⟨hz.1, ⟨x, hx, rfl⟩⟩,
      le_csSup hf.bddAbove ⟨hz.1, ⟨x, hx, rfl⟩⟩⟩
  · intro z hz
    have hzspec := hz.1
    rw [hB.spectrum_eq_image_range] at hzspec
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hzspec
    exact truncated_endpoints_outside_strip
      (csInf_le hf.bddBelow (hn.csSup_mem hf)) hδ
      (truncated_endpoints_perturbed_separation bhatia_corollary_III_2_6 hband hB hsmall hz)

/-- The evolution of `H` over time `T` ends at a unitary matrix, so `‖U(T)‖ = 1`. -/
theorem norm_evolution_end {d : ℕ} [NeZero d]
    (H : ℝ → Matrix (Fin d) (Fin d) ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖evolution H T T‖ = 1 := by
  have hU : IsUnitary (evolution H T T) := by
    unfold evolution evolutionOf
    split_ifs with h
    · exact h.choose_spec.isUnitary T ⟨hT, le_rfl⟩
    · simp [IsUnitary]
  nontriviality Matrix (Fin d) (Fin d) ℂ
  exact CStarRing.norm_of_mem_unitary hU

end RoundedClocks
