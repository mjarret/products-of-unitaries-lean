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

- `complexSpectralMultiplier`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
open Complex Real Set Matrix
open UnitaryProducts UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.Paper.UnitStepsProse

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

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
