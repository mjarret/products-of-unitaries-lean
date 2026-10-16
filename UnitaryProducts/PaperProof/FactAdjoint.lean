/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Prose.UnitStepsWalks

/-!
# Adjoint identities

## Declarations

- `fact_adjoint`
- `hasDerivAt_conjugation`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Real Complex Set UnitaryProducts.Corrector
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse UnitaryProducts.Prose

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Product rule for exponential conjugation; `evol Ω (-t)` is `exp(i t Ω)`. -/
theorem hasDerivAt_conjugation (Ω : 𝕄) {Y : ℝ → 𝕄} {Y' : 𝕄} {t : ℝ}
    (hY : HasDerivAt Y Y' t) :
    HasDerivAt (fun s ↦ evol Ω (-s) * Y s * evol Ω s)
      (evol Ω (-t) * (Y' + I • adL Ω (Y t)) * evol Ω t) t := by
  have hn : HasDerivAt (fun s : ℝ ↦ evol Ω (-s)) (I • (Ω * evol Ω (-t))) t := by
    convert (hasDerivAt_evol Ω (-t)).scomp t (hasDerivAt_neg t) using 1
    simp only [smul_mul_assoc, neg_smul, neg_neg, one_smul, neg_mul]
  have hc : Ω * evol Ω (-t) = evol Ω (-t) * Ω := by
    have hh := (commute_evol Ω (-t)).eq
    simp only [smul_mul_assoc, mul_smul_comm] at hh
    exact (smul_right_injective 𝕄 (neg_ne_zero.mpr I_ne_zero)) hh
  convert (hn.mul hY).mul (hasDerivAt_evol Ω t) using 1
  simp only [adL_apply, Pi.mul_apply, sub_mul, mul_sub, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, smul_sub, neg_smul, neg_mul, mul_neg]
  rw [hc]
  simp only [mul_assoc]
  abel

/-- Adjoint identities used in Lemma A.1: the three adjoint identities, with complex linearity,
scalar-shift invariance, both operator-norm bounds, the telescoped difference of powers,
and the derivative of the exponentially conjugated path. The power identity also holds
for `n = 0`. -/
theorem fact_adjoint [NeZero d] (X X₁ Ω : 𝕄) (hΩ : Ω.IsHermitian) {w : ℝ}
    (hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (n : ℕ) :
    ((∀ A B : 𝕄, adL (A + B) = adL A + adL B) ∧
      (∀ (c : ℂ) (A : 𝕄), adL (c • A) = c • adL A) ∧
      (∀ μ : ℂ, adL (X + μ • 1) = adL X) ∧
      ‖adL X‖ ≤ 2 * ‖X‖ ∧ ‖adL Ω‖ ≤ w) ∧
    (adL X₁ ^ n - adL X ^ n =
      ∑ k ∈ Finset.range n, adL X₁ ^ k * adL (X₁ - X) * adL X ^ (n - 1 - k)) ∧
    (∀ (Y : ℝ → 𝕄) (Y' : 𝕄) (t : ℝ), HasDerivAt Y Y' t →
      HasDerivAt (fun s ↦ evol Ω (-s) * Y s * evol Ω s)
        (evol Ω (-t) * (Y' + I • adL Ω (Y t)) * evol Ω t) t) := by
  -- The commutator estimate ‖XE - EX‖ ≤ 2‖X‖‖E‖ gives the operator norm bound.
  have hnorm : ‖adL X‖ ≤ 2 * ‖X‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_adL_apply_le_twice X)
  -- The spectral-width bound is the n = 1 case of the power estimate.
  have hwidth : ‖adL Ω‖ ≤ w := by simpa using ad_power_norm_le hΩ hw 1
  refine ⟨⟨?_, ?_, ?_, hnorm, hwidth⟩, ?_, ?_⟩
  · -- Additivity of the commutator.
    exact fun A B ↦ (adLCLM d).map_add A B
  · -- Complex homogeneity of the commutator.
    exact fun c A ↦ (adLCLM d).map_smul c A
  · -- Adding a scalar matrix leaves the commutator unchanged.
    refine fun μ ↦ ContinuousLinearMap.ext fun E ↦ ?_
    simp only [adL_apply, add_mul, mul_add, smul_one_mul, mul_smul_one]
    abel
  · -- Telescope the difference of the two operator powers.
    rw [show adL (X₁ - X) = adL X₁ - adL X from (adLCLM d).map_sub X₁ X]
    exact pow_sub_pow_sum _ _ n
  · -- Differentiate conjugation by the fixed-generator evolution.
    exact fun Y Y' t hY ↦ hasDerivAt_conjugation Ω hY

end UnitaryProducts.PaperProof
