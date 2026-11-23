/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CommutatorSeriesDerivative

/-! # Jacobi's identity and the telescoping sum

The first two lines of (A.4). Jacobi's identity `[[Ω,Λ],B] = [Ω,[Λ,B]] - [Λ,[Ω,B]]` says that
`[[Ω,Λ],·]` is the commutator of the operators `[Ω,·]` and `[Λ,·]`, so the sum over `k` in
`𝓕([Ω,Λ])` telescopes to `[Ω,·]ⁿ[Λ,·] - [Λ,·][Ω,·]ⁿ`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Real scalar multiplication on complex-linear operators is jointly continuous. -/
theorem continuousSMul_real_clm : ContinuousSMul ℝ (𝕄 →L[ℂ] 𝕄) :=
  IsScalarTower.continuousSMul ℂ

attribute [local instance] continuousSMul_real_clm

/-- Jacobi's identity `[[Ω,Λ],A] = [Ω,[Λ,A]] - [Λ,[Ω,A]]`, as an identity of operators:
`[[Ω,Λ],·] = [Ω,·][Λ,·] - [Λ,·][Ω,·]`. -/
theorem adL_commutator (Ω Λ : 𝕄) :
    adL (adL Ω Λ) = adL Ω * adL Λ - adL Λ * adL Ω :=
  ContinuousLinearMap.coe_injective ((LieAlgebra.ad ℂ 𝕄).map_lie Ω Λ)

/-- Lines 1 and 2 of (A.4) for one `n`: after Jacobi's identity the sum over `k` telescopes,
`∑_{k<n} [Ω,·]^k [[Ω,Λ],·] [Ω,·]^{n-1-k} = [Ω,·]ⁿ[Λ,·] - [Λ,·][Ω,·]ⁿ`. -/
theorem powDeriv_adL_commutator (Ω Λ : 𝕄) (n : ℕ) :
    powDeriv (adL Ω) (adL (adL Ω Λ)) n =
      adL Ω ^ n * adL Λ - adL Λ * adL Ω ^ n := by
  rw [adL_commutator, powDeriv_commutator]

end RoundedClocks
