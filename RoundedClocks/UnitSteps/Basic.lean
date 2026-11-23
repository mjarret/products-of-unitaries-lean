/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries

/-! # Facts used throughout Section 4

End phases: the half-step phases `e^{-iA/2}` and `e^{iA/2}` of the rounded-clock identity (2.5)
are unitary, and Proposition 2.4 transfers leakage through these phases.

Calculus: a continuously differentiable `F(s)` for `s ∈ [0,1]` satisfies
`F(r) - F(l) = ∫_l^r F'(s) ds` for `0 ≤ l ≤ r ≤ 1`.

Eigenvectors: a Hermitian `A` maps each vector `ψ_j` of its eigenbasis to `λ_j ψ_j`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ### End phases -/

/-- The half-step phase `e^{-iA/2}` of (2.5) is unitary for Hermitian `A`. -/
theorem exp_neg_half_isUnitary {A : 𝕄} (hA : IsHermitian A) :
    IsUnitary (exp (-(I / 2) • A)) := by
  have he : -(I / 2) • A = ((1 / 2 : ℝ) : ℂ) • (-I • A) := by module
  rw [he]
  exact exp_neg_I_smul_isUnitary hA (1 / 2)

/-- The half-step phase `e^{iA/2}` of (2.5) is unitary for Hermitian `A`. -/
theorem exp_half_isUnitary {A : 𝕄} (hA : IsHermitian A) :
    IsUnitary (exp ((I / 2) • A)) := by
  have he : (I / 2) • A = ((-(1 / 2) : ℝ) : ℂ) • (-I • A) := by module
  rw [he]
  exact exp_neg_I_smul_isUnitary hA (-(1 / 2))

/-- Proposition 2.4 with the end phases `A = e^{-iH₁/2}` and `B = e^{iH₀/2}`: if `P`
commutes with `H₀` and `Q` commutes with `H₁`, the end phases do not change the leakage norm. -/
theorem transfer_end_phases [NeZero d] {H₀ H₁ P Q U W : 𝕄}
    (hH₀ : IsHermitian H₀) (hH₁ : IsHermitian H₁)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q)
    (hPH₀ : Commute P H₀) (hQH₁ : Commute Q H₁) :
    |‖(1 - Q) * W * P‖ - ‖(1 - Q) * U * P‖| ≤
      ‖exp (-(I / 2) • H₁) * W * exp ((I / 2) • H₀) - U‖ := by
  have hA := exp_neg_half_isUnitary hH₁
  have hB := exp_half_isUnitary hH₀
  have hAQ : Commute (exp (-(I / 2) • H₁)) Q :=
    (hQH₁.symm.smul_left (-(I / 2))).exp_left
  have hBP : Commute (exp ((I / 2) • H₀)) P :=
    (hPH₀.symm.smul_left (I / 2)).exp_left
  simpa only [sub_self, norm_zero, add_zero, mul_zero] using
    transfer (Q := Q) hP hP hQ hA hB hAQ hBP (U := U) (W := W)

/-! ### Calculus -/

/-- For `F(s)` differentiable for `s ∈ [0,1]`, with a continuous derivative `F'` that is one-sided
at `0` and `1`, and for `0 ≤ l ≤ r ≤ 1`, `F(r) - F(l) = ∫_l^r F'(s) ds`. -/
theorem sub_eq_integral_deriv01 {F : ℝ → 𝕄} (hF : DifferentiableOn ℝ F (Icc 0 1))
    (hF' : ContinuousOn (∂F) (Icc 0 1)) {l r : ℝ} (hl : l ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Icc (0 : ℝ) 1) (hlr : l ≤ r) :
    F r - F l = ∫ s in l..r, ∂F s := by
  have hsub : Icc l r ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hl.1 hr.2
  have hi : IntervalIntegrable (∂F) MeasureTheory.volume l r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact hF'.mono hsub
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (hF.continuousOn.mono hsub) _ hi
  intro s hs
  have hsJ : s ∈ Ioo (0 : ℝ) 1 := ⟨hl.1.trans_lt hs.1, hs.2.trans_le hr.2⟩
  exact ((hF s (Ioo_subset_Icc_self hsJ)).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds hsJ.1 hsJ.2)

/-! ### Eigenvectors -/

/-- A Hermitian `A`, acting on `ℂ^d`, maps the vector `ψ_j` of its eigenbasis to `λ_j ψ_j`. -/
theorem toEuclideanCLM_eigenvectorBasis {A : 𝕄} (hA : A.IsHermitian) (j : Fin d) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A (hA.eigenvectorBasis j) =
      (hA.eigenvalues j : ℂ) • hA.eigenvectorBasis j := by
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, hA.mulVec_eigenvectorBasis j,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end RoundedClocks
