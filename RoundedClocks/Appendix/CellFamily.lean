/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CellMultiplier
public import RoundedClocks.Appendix.MatrixSeries

/-! # Lemma A.1(i): the guess `Y(τ) = 𝒩_τ([Ω,·])D`

In an orthonormal eigenbasis of `Ω`, the guess has entries `𝒩_τ(λ_p - λ_q) D_pq`. The identities
`∂_τ𝒩_τ(x) + ix𝒩_τ(x) = τ` and `𝒩_{±1/2}(x) = 𝒩(x)` give `Y' + i[Ω,Y] = τD` and
`Y(±1/2) = 𝒩([Ω,·])D`. Here `cellGuess Ω hΩ D τ` is `Y(τ)`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Real
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The guess Y(τ) = 𝒩_τ([Ω,·])D of Lemma A.1, written in an eigenbasis of Ω. -/
def cellGuess (Ω : 𝕄) (hΩ : IsHermitian Ω) (D : 𝕄) (τ : ℝ) : 𝕄 :=
  (hΩ.eigenvectorUnitary : 𝕄) * Matrix.of (fun p q ↦
    cellMultiplier τ (hΩ.eigenvalues p - hΩ.eigenvalues q) *
      ((hΩ.eigenvectorUnitary : 𝕄)† * D * (hΩ.eigenvectorUnitary : 𝕄)) p q) *
    (hΩ.eigenvectorUnitary : 𝕄)†

/-- `[Ω,A]_pq = (λ_p - λ_q) A_pq` in the eigenbasis of `Ω`. -/
theorem cell_commutator_entry (Ω : 𝕄) (hΩ : IsHermitian Ω) (A : 𝕄) (p q : Fin d) :
    ((hΩ.eigenvectorUnitary : 𝕄)† * (Ω * A - A * Ω) *
      (hΩ.eigenvectorUnitary : 𝕄)) p q =
    ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) *
      ((hΩ.eigenvectorUnitary : 𝕄)† * A * (hΩ.eigenvectorUnitary : 𝕄)) p q := by
  simpa only [pow_one, adL_apply] using
    adL_pow_eigenbasis_entry Ω A hΩ.eigenvectorUnitary hΩ.eigenvalues
      (eigenvectorUnitary_conj_eq_diagonal hΩ) 1 p q

/-- Entry arrays map continuously to matrices with the operator norm. -/
private def cellMatrixCLM : (Fin d → Fin d → ℂ) →L[ℝ] 𝕄 :=
  LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap

/-- Differentiating the guess: `Y' + i[Ω,Y] = τD`, as `∂_τ𝒩_τ(x) + ix𝒩_τ(x) = τ`. -/
theorem cellGuess_hasDerivAt (Ω : 𝕄) (hΩ : IsHermitian Ω) (D : 𝕄) (τ : ℝ) :
    HasDerivAt (cellGuess Ω hΩ D)
      (τ • D - I • (Ω * cellGuess Ω hΩ D τ - cellGuess Ω hΩ D τ * Ω)) τ := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let A : 𝕄 := U† * D * U
  let F : ℝ → Fin d → Fin d → ℂ := fun t p q ↦
    cellMultiplier t (hΩ.eigenvalues p - hΩ.eigenvalues q) * A p q
  let F' : Fin d → Fin d → ℂ := fun p q ↦
    ((τ : ℂ) - I * (hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) *
      cellMultiplier τ (hΩ.eigenvalues p - hΩ.eigenvalues q)) * A p q
  -- Entrywise in the eigenbasis, `(𝒩_τ(x) D_pq)' = (τ - ix𝒩_τ(x)) D_pq`.
  have hF : HasDerivAt F F' τ := by
    apply hasDerivAt_pi.mpr
    intro p
    apply hasDerivAt_pi.mpr
    intro q
    exact (cellMultiplier_derivative _ τ).mul_const (A p q)
  -- Conjugating back, `Y'(τ) = Ψ F' Ψ†`.
  let L := (ContinuousLinearMap.mulLeftRight ℝ 𝕄 U U†).comp cellMatrixCLM
  have h := L.hasFDerivAt.comp_hasDerivAt τ hF
  change HasDerivAt (cellGuess Ω hΩ D) (U * Matrix.of F' * U†) τ at h
  convert h using 1
  -- `Ψ F' Ψ† = τD - i[Ω,Y]`: compare entries in the eigenbasis, where `[Ω,Y]_pq = x Y_pq`.
  let e := Unitary.conjStarAlgAut ℂ 𝕄 (star hΩ.eigenvectorUnitary)
  have he (X : 𝕄) : e X = U† * X * U := by
    simp only [e, U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
  have hU : U† * U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hΩ.eigenvectorUnitary.property
  have hcancel (X : 𝕄) : e (U * X * U†) = X := by
    rw [he]
    simp only [← mul_assoc, hU, one_mul]
    rw [mul_assoc, hU, mul_one]
  have hguess : e (cellGuess Ω hΩ D τ) = Matrix.of (F τ) := hcancel _
  apply (show Function.Injective (fun X : 𝕄 ↦ e X) from e.injective)
  dsimp only
  have hreal : e (τ • D) = τ • e D := by
    simp only [he, mul_smul_comm, smul_mul_assoc]
  rw [map_sub, hreal, map_smul, hcancel]
  ext p q
  have hc := cell_commutator_entry Ω hΩ (cellGuess Ω hΩ D τ) p q
  rw [← he, ← he, hguess] at hc
  simp only [Matrix.sub_apply, Matrix.smul_apply, he D, hc]
  change (τ : ℂ) * A p q - I *
    (((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) * F τ p q) = F' p q
  dsimp [F, F']
  ring

/-- The guessed matrix family is continuously differentiable. -/
theorem cellGuess_contDiff (Ω : 𝕄) (hΩ : IsHermitian Ω) (D : 𝕄) :
    ContDiff ℝ 1 (cellGuess Ω hΩ D) := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let F : ℝ → Fin d → Fin d → ℂ := fun t p q ↦
    cellMultiplier t (hΩ.eigenvalues p - hΩ.eigenvalues q) * (U† * D * U) p q
  have hF : ContDiff ℝ 1 F := by
    apply contDiff_pi.mpr
    intro p
    apply contDiff_pi.mpr
    intro q
    exact (cellMultiplier_contDiff _).mul contDiff_const
  exact ((ContinuousLinearMap.mulLeftRight ℝ 𝕄 U U†).comp
    cellMatrixCLM).contDiff.comp hF

/-- The end values of the guess: `Y(±1/2) = 𝒩([Ω,·])D`, as `𝒩_{±1/2}(x) = 𝒩(x)`. -/
theorem cellGuess_endpoints {Ω : 𝕄} (hΩ : IsHermitian Ω) (D : 𝕄) {w : ℝ}
    (hw : w < 2 * π) (hwidth : HasEigenvalueDifferences Ω w) :
    cellGuess Ω hΩ D (-1 / 2) = 𝒩ad Ω D ∧
      cellGuess Ω hΩ D (1 / 2) = 𝒩ad Ω D := by
  have hx := abs_eigenvalues_sub_lt_two_pi hΩ hw hwidth
  rw [𝒩ad, dif_pos hΩ, if_pos hx]
  constructor
  · simp only [cellGuess, (cellMultiplier_endpoints (hx _ _)).1]
  · simp only [cellGuess, (cellMultiplier_endpoints (hx _ _)).2]

end RoundedClocks
