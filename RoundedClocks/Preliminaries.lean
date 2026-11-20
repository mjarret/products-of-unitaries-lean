/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

/-!
# Section 2: preliminaries

The comparison of evolutions (Theorem 2.2), the rounded-clock identity (2.5), and the transfer of
leakage bounds (Proposition 2.4).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Theorem 2.2** (comparison of evolutions). Let regulated families `K(t)` and `G(t)` with
`t ∈ [a,b]` generate `U` and `V`, and let `a = p_0 ≤ p_1 ≤ ⋯ ≤ p_{m+1} = b`. For `0 ≤ j ≤ m` let the
piece `Y_j(t)` with `t ∈ [p_j, p_{j+1}]` be continuous, with derivative `Y_j'(t)` for all `t`
outside a countable set `S`, where `Y_j'` is regulated. Let `R(t)` be the residual
`R = K - G - Y_j' - i(K Y_j - Y_j G)` wherever `p_j < t < p_{j+1}` and `t ∉ S`, with arbitrary
values elsewhere. Then
`U(b)† V(b) - 1 = ∫_a^b i U† R V dt + i U(b)† Y_m(b) V(b) - i Y_0(a)
- i Σ_{j=1}^m U(p_j)† Δ_j V(p_j)`
with `Δ_j = Y_j(p_j) - Y_{j-1}(p_j)`. Hermiticity of `K` and `G` is not needed. -/
theorem comparison {a b : ℝ} (m : ℕ) (p : ℕ → ℝ) (hp : Monotone p) (ha : p 0 = a)
    (hb : p (m + 1) = b) (K G U V R : ℝ → 𝕄) (Y : ℕ → ℝ → 𝕄) (S : Set ℝ) (hS : S.Countable)
    (hU : Generates K U a b) (hV : Generates G V a b)
    (hK : IsRegulated K a b) (hG : IsRegulated G a b)
    (hYc : ∀ j ≤ m, ContinuousOn (Y j) (Icc (p j) (p (j + 1))))
    (Y' : ℕ → ℝ → 𝕄) (hY' : ∀ j ≤ m, IsRegulated (Y' j) (p j) (p (j + 1)))
    (hYd : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S → HasDerivAt (Y j) (Y' j t) t)
    (hR : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S →
      R t = K t - G t - Y' j t - I • (K t * Y j t - Y j t * G t)) :
    (U b)† * V b - 1 = (∫ t in a..b, I • ((U t)† * R t * V t)) +
      I • ((U b)† * Y m b * V b) - I • Y 0 a -
      I • ∑ j ∈ Finset.Icc 1 m, (U (p j))† * (Y j (p j) - Y (j - 1) (p j)) * V (p j) := by
  have hYd' : ∀ j ≤ m, ∃ Yd : ℝ → 𝕄, IsRegulated Yd (p j) (p (j + 1)) ∧
      ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S → HasDerivAt (Y j) (Yd t) t :=
    fun j hj ↦ ⟨Y' j, hY' j hj, hYd j hj⟩
  have hR' : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S →
      HasDerivAt (Y j) (K t - G t - I • (K t * Y j t - Y j t * G t) - R t) t :=
    fun j hj t ht htS ↦ (hYd j hj t ht htS).congr_deriv (by rw [hR j hj t ht htS]; abel)
  rw [UnitaryProducts.PaperProof.thm_comparison m p hp ha hb K G U V R Y S hS hU hV hK hG hYd' hYc
    hR', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [add_comm 1, Nat.add_sub_cancel]

/-- **Equation (2.5)** (the rounded-clock identity). For an integer `T ≥ 1`, the evolution of
`H(⌊t+1/2⌋/T)` ends at `e^{-iH(1)/2} W_T e^{iH(0)/2}`, where `W_T` is the `T`-step product. -/
theorem roundedEvolution_end {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {T : ℕ} (hT : 1 ≤ T) :
    roundedEvolution H T T = exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) := by
  have h₁ : -((((1 / 2 : ℝ)) : ℂ) * I) = -(I / 2) := by push_cast; ring
  have h₂ : -((((-(1 / 2) : ℝ)) : ℂ) * I) = I / 2 := by push_cast; ring
  rw [Bridge.roundedEvolution_eq, UnitaryProducts.Paper.roundedEvolution_endpoint hT hH,
    Bridge.stepProduct_eq, Bridge.evol_eq, Bridge.evol_eq, h₁, h₂]

/-- **Proposition 2.4** (transfer of leakage bounds). Let `P`, `Q`, `P'`, and `Q'` be orthogonal
projectors, let `U` and `W` be matrices, and let `A` and `B` be unitary matrices that commute with
`Q'` and `P'`, respectively. Then
`|‖(1 - Q') W P'‖ - ‖(1 - Q) U P‖| ≤ ‖A W B - U‖ + ‖U‖ (‖P' - P‖ + ‖Q' - Q‖)`. -/
theorem transfer {P Q P' Q' U W A B : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hP' : IsOrthogonalProjector P')
    (hQ' : IsOrthogonalProjector Q') (hA : IsUnitary A) (hB : IsUnitary B)
    (hAQ' : Commute A Q') (hBP' : Commute B P') :
    |‖(1 - Q') * W * P'‖ - ‖(1 - Q) * U * P‖| ≤
      ‖A * W * B - U‖ + ‖U‖ * (‖P' - P‖ + ‖Q' - Q‖) := by
  exact UnitaryProducts.PaperProof.prop_transfer hP hQ hP' hQ' (Bridge.isUnitary_iff.mp hA)
    (Bridge.isUnitary_iff.mp hB) hAQ' hBP'

end RoundedClocks
