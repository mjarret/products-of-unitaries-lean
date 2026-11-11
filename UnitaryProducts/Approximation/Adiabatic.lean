/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Simulation

/-!
# Projectors are contractions; leakage comparison

## Declarations

- `norm_le_one_of_isStarProjection`
- `norm_leak_le_norm`
- `norm_leak_sub_le_of_contraction`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- An orthogonal projector has operator norm at most $1$ (by the C*-identity
$\|p\|^2=\|p^\dagger p\|=\|p\|$). -/
theorem norm_le_one_of_isStarProjection {p : 𝕄} (hp : IsStarProjection p) : ‖p‖ ≤ 1 := by
  have hn : ‖p‖ * ‖p‖ = ‖p‖ := by
    rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  by_contra h
  linarith [mul_lt_mul_of_pos_left (not_le.mp h) (zero_lt_one.trans (not_le.mp h))]

/-- **Leakage comparison with one contraction** (the unnumbered leakage comparison).  For projectors
`P₀`, `P₀'`,
`Pₜ'` and a contraction `U`, every matrix `U'` satisfies
$\|(1-P'_t)U'P'_0-(1-P_t)UP_0\|\le\|P_t-P'_t\|+\|U'-U\|+\|P'_0-P_0\|$. The proof is the paper's
three-term identity, each term bounded using that projectors and `U` are contractions. -/
theorem norm_leak_sub_le_of_contraction {P₀ P₀' Pₜ Pₜ' U U' : 𝕄} (hP₀ : IsStarProjection P₀)
    (hP₀' : IsStarProjection P₀') (hPₜ' : IsStarProjection Pₜ') (hU : ‖U‖ ≤ 1) :
    ‖(1 - Pₜ') * U' * P₀' - (1 - Pₜ) * U * P₀‖
      ≤ ‖Pₜ - Pₜ'‖ + ‖U' - U‖ + ‖P₀' - P₀‖ := by
  have hsplit : (1 - Pₜ') * U' * P₀' - (1 - Pₜ) * U * P₀ = (Pₜ - Pₜ') * U * P₀
      + (1 - Pₜ') * (U' - U) * P₀' + (1 - Pₜ') * U * (P₀' - P₀) := by noncomm_ring
  have h1 := norm_le_one_of_isStarProjection hP₀
  have h1' := norm_le_one_of_isStarProjection hP₀'
  have h2 := norm_le_one_of_isStarProjection hPₜ'.one_sub
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ?_ ?_)) ?_)
  · simpa using norm_mul_le_of_le (norm_mul_le_of_le le_rfl hU) h1
  · simpa using norm_mul_le_of_le (norm_mul_le_of_le h2 le_rfl) h1'
  · simpa using norm_mul_le_of_le (norm_mul_le_of_le h2 hU) le_rfl

/-- Compressing a matrix between the complement of one projector and another projector does not
increase its norm: $\|(1-P_t)UP_0\|\le\|U\|$ (a step of the proof of the unnumbered Davis–Kahan
estimate). -/
theorem norm_leak_le_norm {P₀ Pₜ : 𝕄} (hP₀ : IsStarProjection P₀) (hPₜ : IsStarProjection Pₜ)
    (U : 𝕄) : ‖(1 - Pₜ) * U * P₀‖ ≤ ‖U‖ := by
  simpa using norm_mul_le_of_le (norm_mul_le_of_le (norm_le_one_of_isStarProjection hPₜ.one_sub)
    le_rfl) (norm_le_one_of_isStarProjection hP₀)

end UnitaryProducts
