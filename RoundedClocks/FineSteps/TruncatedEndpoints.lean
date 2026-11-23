/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.FineSteps.EndpointSeparation
public import RoundedClocks.Examples.Spectral
public import RoundedClocks.Appendix.MatrixSeries

/-! # Truncated spectral endpoints

The truncated-endpoint statement combines spectral separation, projector rank, and the ordered
eigenvalue description to locate the two truncation boundaries.
-/

@[expose] public section

noncomputable section
namespace RoundedClocks
open Set
open scoped Matrix.Norms.L2Operator

/-- Separation from every point of a closed interval gives the outside-strip condition. -/
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

/-- The endpoint evolution is unitary, and hence has operator norm one. -/
theorem truncated_endpoints_evolution_norm {d : ℕ} [NeZero d]
    (H : ℝ → Matrix (Fin d) (Fin d) ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖evolution H T T‖ = 1 := by
  apply norm_eq_one_of_unitary
  unfold evolution evolutionOf
  split_ifs with h
  · exact h.choose_spec.2.2.1 T ⟨hT, le_rfl⟩
  · simp

end RoundedClocks
