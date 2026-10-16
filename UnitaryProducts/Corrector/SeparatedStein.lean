/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Data.Matrix.Basis
public import UnitaryProducts.Corrector.SeparatedScalarStein

/-!
# Stein's equation for the separated frame

## Declarations

- `HasSeparatedSpectrum`
- `cellPrimitive_add`
- `eigenbasis_matrix_unit`
- `separatedFrame_stein`
- `separatedFrame_stein_of_eigen`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex MeasureTheory Set Matrix
noncomputable section
namespace UnitaryProducts.Separation

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The Stein identity on an eigenoperator at an allowed difference. -/
theorem separatedFrame_stein_of_eigen (ε W : ℝ) (hε : 0 < ε) {h E : 𝕄} {p q : ℝ}
    (hp : h * E = (p : ℂ) • E) (hq : E * h = (q : ℂ) • E)
    (hpq : p - q ∈ allowedDifferences ε W) :
    evol h (-1) * separatedFrame ε W hε h E * evol h 1 - separatedFrame ε W hε h E =
      Dressed.cellPrimitive h E 1 := by
  rw [separatedFrame_of_eigen ε W hε hp hq hpq, mul_smul_comm, smul_mul_assoc,
    evol_conj_of_eigen hp hq 1]
  simp only [ofReal_one, mul_one]
  rw [smul_smul, ← sub_smul, ← mul_sub_one, frameMult_stein_scalar (nonresonant_of_allowed hε hpq),
    Dressed.cellPrimitive, ← intervalIntegral.integral_smul_const]
  exact intervalIntegral.integral_congr fun s _ ↦ by
    simp only [evol_conj_of_eigen hp hq, smul_assoc]

/-- Additivity of the centered primitive. -/
theorem cellPrimitive_add (h D E : 𝕄) : Dressed.cellPrimitive h (D+E) 1 =
    Dressed.cellPrimitive h D 1 + Dressed.cellPrimitive h E 1 := by
  have hc (D : 𝕄) : Continuous (fun s : ℝ ↦ (s-1/2) • (evol h (-s) * D * evol h s)) :=
    (continuous_id.sub continuous_const).smul
      ((((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h))
  unfold Dressed.cellPrimitive
  simp only [mul_add, add_mul, smul_add]
  refine intervalIntegral.integral_add ?_ ?_ <;> exact (hc _).intervalIntegrable _ _

/-- Every eigenvalue difference $\lambda_p - \lambda_q$ of the Hermitian $h$ lies in
`allowedDifferences ε W`. For $\varepsilon > 0$ the differences then avoid
$2\pi\mathbb Z \setminus \{0\}$ with margin $\varepsilon$; every non-resonant $h$ satisfies it for
some $\varepsilon > 0$ and $W$ (`exists_hasSeparatedSpectrum_of_nonresonant`). -/
def HasSeparatedSpectrum {h : 𝕄} (hh : h.IsHermitian) (ε W : ℝ) : Prop :=
  ∀ p q, hh.eigenvalues p - hh.eigenvalues q ∈ allowedDifferences ε W

/-- Conjugated matrix units are simultaneous left and right eigenoperators. -/
theorem eigenbasis_matrix_unit {h : 𝕄} (hh : h.IsHermitian) (p q : Fin d) (z : ℂ) :
    let V : 𝕄 := hh.eigenvectorUnitary
    h * (V * single p q z * star V) =
        (hh.eigenvalues p : ℂ) • (V * single p q z * star V) ∧
      (V * single p q z * star V) * h =
        (hh.eigenvalues q : ℂ) • (V * single p q z * star V) := by
  intro V
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary
  have hd : e.symm h = diagonal (fun p ↦ (hh.eigenvalues p : ℂ)) := by
    simpa only [e, Unitary.conjStarAlgAut_symm_apply, Unitary.conjStarAlgAut_apply,
      Unitary.coe_star, star_star] using hh.conjStarAlgAut_star_eigenvectorUnitary
  constructor
  · apply e.symm.injective
    change e.symm (h * e (single p q z)) = e.symm ((hh.eigenvalues p : ℂ) • e _)
    rw [map_mul, map_smul, e.symm_apply_apply, hd]
    ext i j
    simp +contextual [Matrix.single_apply, mul_ite]
  · apply e.symm.injective
    change e.symm (e (single p q z) * h) = e.symm ((hh.eigenvalues q : ℂ) • e _)
    rw [map_mul, map_smul, e.symm_apply_apply, hd]
    ext i j
    simp +contextual [Matrix.single_apply, ite_mul, mul_comm]

/-- **Stein's equation** for `separatedFrame` (equal end values): under separation,
$e^{ih} S e^{-ih} - S = \int_0^1 (\tau - \tfrac12)\, e^{i\tau h} D e^{-i\tau h}\, d\tau$ for
$S$ = `separatedFrame ε W hε h D`, with no width hypothesis. -/
theorem separatedFrame_stein (ε W : ℝ) (hε : 0 < ε) {h : 𝕄}
    (hh : h.IsHermitian) (hsep : HasSeparatedSpectrum hh ε W) (D : 𝕄) :
    evol h (-1) * separatedFrame ε W hε h D * evol h 1 - separatedFrame ε W hε h D =
      Dressed.cellPrimitive h D 1 := by
  -- Diagonalize: $h = U A U^\dagger$, with $A$ the diagonal matrix of eigenvalues.
  let U : 𝕄 := hh.eigenvectorUnitary
  have hfin : U * (star U * D * U) * star U = D :=
    (Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary).apply_symm_apply D
  -- The identity for $U M U^\dagger$, by induction over the matrix units $M$.
  let P : 𝕄 → Prop := fun M ↦
    evol h (-1) * separatedFrame ε W hε h (U*M*star U) * evol h 1 -
      separatedFrame ε W hε h (U*M*star U) = Dressed.cellPrimitive h (U*M*star U) 1
  have hP (M : 𝕄) : P M := by
    refine Matrix.induction_on' (P := P) M ?_ ?_ ?_
    -- $M = 0$: both sides vanish.
    · simp [P, separatedFrame, kernelFrame, Dressed.cellPrimitive]
    -- Sums: both sides are additive.
    · intro X Y hX hY
      dsimp only [P] at hX hY ⊢
      rw [mul_add, add_mul, separatedFrame_add ε W hε hh, cellPrimitive_add, mul_add, add_mul,
        ← hX, ← hY]
      abel
    -- A matrix unit: $U E_{pq} U^\dagger$ is an eigenoperator with difference
    -- $\lambda_p - \lambda_q$, allowed by `hsep`.
    · intro p q z
      obtain ⟨hp, hq⟩ := eigenbasis_matrix_unit hh p q z
      exact separatedFrame_stein_of_eigen ε W hε hp hq (hsep p q)
  -- Conclude at $M = U^\dagger D U$.
  simpa only [P, hfin] using hP (star U * D * U)

end UnitaryProducts.Separation
