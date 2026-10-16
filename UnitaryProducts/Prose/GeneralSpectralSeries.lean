/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# Arbitrary power series of the adjoint map

The opening of Appendix A.1 uses arbitrary coefficients. Absolute scalar
convergence at a spectral width ensures convergence of the operator series;
the eigenbasis formula then identifies its sum with the spectral multiplier.
All Banach-algebra series estimates are proved generically before instantiation
at the algebra of continuous linear maps.

## Declarations

- `summable_complex_operator_series`
- `spectralMultiplier_eq_series_signed`
- `spectralMultiplier_eq_series_signed_radius`
- `complexSpectralMultiplier`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
open Complex Real Set Matrix
open UnitaryProducts UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.Paper.UnitStepsProse

/-- Absolute scalar convergence at an operator-norm bound implies convergence
of the Banach-algebra series, without a sign or reality condition on coefficients. -/
theorem summable_complex_operator_series {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [NormOneClass A] [CompleteSpace A]
    {a : A} {w : ℝ} (ha : ‖a‖ ≤ w) {c : ℕ → ℂ}
    (hs : Summable (fun n ↦ ‖c n‖ * w ^ n)) :
    Summable (fun n ↦ c n • a ^ n) := by
  refine hs.of_norm_bounded fun n ↦ ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le_width ha n) (norm_nonneg _)

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The spectral multiplier equals the adjoint-map series for arbitrary real
coefficients. The norm majorant, not coefficient positivity, controls convergence. -/
theorem spectralMultiplier_eq_series_signed [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ}
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    {c : ℕ → ℝ} (hs : Summable (fun n ↦ |c n| * w ^ n)) :
    spectralMultiplier Ω hΩ (fun x ↦ ∑' n, c n * x ^ n) =
      ∑' n, (c n : ℂ) • (adL Ω) ^ n := by
  have ha : ‖adL Ω‖ ≤ w := by simpa using ad_power_norm_le hΩ hw 1
  have hsum : Summable (fun n ↦ (c n : ℂ) • (adL Ω) ^ n) :=
    summable_complex_operator_series (A := 𝕄 →L[ℂ] 𝕄) ha
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hs)
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  ext D : 1
  apply e.symm.injective
  change e.symm (e (Matrix.of _)) = _
  rw [e.symm_apply_apply]
  ext p q
  change _ = (star U * ((∑' n, (c n : ℂ) • (adL Ω) ^ n) D) * U) p q
  have hsD := (ContinuousLinearMap.apply ℂ 𝕄 D).summable hsum
  have he := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).map_tsum hsD
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.apply_apply,
    show ∀ X : 𝕄, entryCLM p q X = X p q from fun _ ↦ rfl] at he
  rw [Matrix.of_apply, tsum_apply_of_summable hsum, he, Complex.ofReal_tsum,
    ← tsum_mul_right]
  refine tsum_congr fun n ↦ ?_
  simp only [ContinuousLinearMap.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [ad_power_eigenbasis_entry]
  ring

/-- Radius-at-least-`2π` formulation: absolute convergence at every nonnegative
radius below `2π` supplies the series bridge at every spectral width below `2π`. -/
theorem spectralMultiplier_eq_series_signed_radius [NeZero d] {Ω : 𝕄}
    (hΩ : Ω.IsHermitian) {w : ℝ} (hwπ : w < 2 * π)
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w)
    {c : ℕ → ℝ}
    (hconv : ∀ r : ℝ, 0 ≤ r → r < 2 * π →
      Summable (fun n ↦ |c n| * r ^ n)) :
    spectralMultiplier Ω hΩ (fun x ↦ ∑' n, c n * x ^ n) =
      ∑' n, (c n : ℂ) • (adL Ω) ^ n := by
  have hw₀ : 0 ≤ w := by simpa using hw 0 0
  exact spectralMultiplier_eq_series_signed hΩ hw (hconv w hw₀ hwπ)

/-- the spectral-multiplier definition before Lemma A.1 with complex-valued multipliers. The
real-valued
`spectralMultiplier` is its special case after composing with `Complex.ofReal`. -/
def complexSpectralMultiplier (Ω : 𝕄) (hΩ : Ω.IsHermitian)
    (f : ℝ → ℂ) : 𝕄 →L[ℂ] 𝕄 :=
  let U : 𝕄 := hΩ.eigenvectorUnitary
  LinearMap.toContinuousLinearMap
    { toFun := fun D ↦ U * Matrix.of (fun p q ↦
        f (hΩ.eigenvalues p - hΩ.eigenvalues q) * (star U * D * U) p q) * star U
      map_add' := fun D E ↦ by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        rw [← Matrix.add_mul, ← Matrix.mul_add]
        congr 2
        ext p q
        exact mul_add _ _ _
      map_smul' := fun z D ↦ by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2
        ext p q
        exact mul_left_comm _ _ _ }


end UnitaryProducts.Paper.UnitStepsProse
