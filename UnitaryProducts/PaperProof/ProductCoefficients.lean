/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.WalkCoefficients

/-! # The cost of using the first endpoint derivative bound

The lead-in to Lemma A.3 compares the coefficient obtained from (i) with the
coefficient supplied by (ii) in Theorem 4.5.
-/
@[expose] public section
open Real Filter
open scoped Topology
open UnitaryProducts.Corrector
noncomputable section
namespace UnitaryProducts.PaperProof

/-- Substituting `‖H′‖ ≤ κ ‖W′‖` into the first endpoint bound replaces exactly
the two endpoint contributions of `c₂` by `2 N′ κ²`; all other terms agree. -/
theorem first_bound_collect (w E L M : ℝ) :
    uniform_c0 w * (walkLogSlope w * E) +
      (1 / 24 + frameBound w) *
        (walkLogSlope w * M + L ^ 2 / Real.cos (w / 4) ^ 2) +
      (uniform_c1 w + 2 * frameLip w) * (walkLogSlope w * L) ^ 2 =
    uniform_c0 w * walkLogSlope w * E + walkUniformSecond w * M +
      (walk_square w -
        (2 * frameLip w * walkLogSlope w +
          (frameBound w - frameBound 0) * walkLogSlope w ^ 2) +
        2 * frameLip w * walkLogSlope w ^ 2) * L ^ 2 := by
  dsimp [walkUniformSecond, walk_square]
  ring

/-- The endpoint contribution from Lemma A.3(i) has fourth-order growth as
`w = 2π - θ` approaches `2π` from below: `2 N′(w) κ(w)² ∼ 4π / θ⁴`. -/
theorem first_bound_equivalent :
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun θ ↦ 2 * frameLip (2 * π - θ) * walkLogSlope (2 * π - θ) ^ 2)
      (fun θ ↦ 4 * π / θ ^ 4) := by
  obtain ⟨hκ, _, hN, _, _⟩ := scalar_edge_limits
  have hproduct := (hN.mul (hκ.pow 2)).const_mul 2
  have hconstant : 2 * (1 / (2 * π) * (2 * π) ^ 2) = 4 * π := by
    field_simp
    ring
  rw [hconstant] at hproduct
  have hlimit : Tendsto
      (fun θ ↦ (2 * frameLip (2 * π - θ) * walkLogSlope (2 * π - θ) ^ 2) * θ ^ 4)
      (𝓝[>] 0) (𝓝 (4 * π)) := by
    convert hproduct using 1
    exact funext fun θ ↦ by ring
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hratio := hlimit.div_const (4 * π)
  rw [div_self (by positivity : 4 * π ≠ 0)] at hratio
  simpa only [Pi.div_def, div_div_eq_mul_div] using hratio

end UnitaryProducts.PaperProof
