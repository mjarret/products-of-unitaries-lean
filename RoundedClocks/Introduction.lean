/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

/-!
# Section 1: the two informal theorems

Theorem A (unit steps at width `π`) and Theorem B (fine steps with truncated entries).
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

/-- **Theorem A.** Let `T ≥ 1` be an integer, let `H` be a time-dependent Hamiltonian whose
derivative `H'` has Lipschitz constant `L`, and let `U` be its evolution over time `T`. If every
sample `H(j/T)` with `0 ≤ j ≤ T` has eigenvalue differences of modulus at most `π`, then
`‖e^{-iH(1)/2} W_T e^{iH(0)/2} - U(T)‖ ≤ (0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²)/T`. -/
theorem theorem_A {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L : ℝ}
    (hL : HasLipschitzDerivative H L) (hwidth : HasSampleWidth H T π) :
    ‖exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      (0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2) / T := by
  have h := UnitaryProducts.PaperProof.introthm_unit H T hT hH L
    (Bridge.HasLipschitzDerivative.paper hL) hwidth
  dsimp only at h
  have h₁ : -((((1 / 2 : ℝ)) : ℂ) * I) = -(I / 2) := by push_cast; ring
  have h₂ : -((((-(1 / 2) : ℝ)) : ℂ) * I) = I / 2 := by push_cast; ring
  rw [Bridge.evol_eq, Bridge.evol_eq, h₁, h₂] at h
  rw [Bridge.stepProduct_eq]
  refine h.trans_eq ?_
  rw [Bridge.supNorm_eq, Bridge.deriv01_eq]
  norm_num

/-- **Theorem B.** Let `H` be a regulated time-dependent Hamiltonian with evolution `U` over time
`T > 0`, and let `ε > 0`. There are checkpoints whose midpoint error is at most `ε`, and for every
such checkpoints the midpoint product of the truncation `H^{(k)}` over time `T` is within
`T (ε + √2 σ_k 2^{-k})` of `U(T)`. -/
theorem theorem_B {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1) (hH : IsTimeDepHamiltonian H)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (k : ℕ) :
    (∃ (N : ℕ) (s : ℕ → ℝ), IsCheckpoints N s ∧ HasMidpointError H N s ε) ∧
      ∀ (N : ℕ) (s : ℕ → ℝ), IsCheckpoints N s → HasMidpointError H N s ε →
        ‖midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s - evolution H T T‖ ≤
          T * (ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
  have h := UnitaryProducts.PaperProof.introthm_fine_oscillation hT hreg hH hε k (sparsity k H)
    fun x hx ↦ by
      have hx' := Bridge.rowSparse_sparsity k H hx
      rwa [← Bridge.truncHerm_eq] at hx'
  refine ⟨?_, fun N s hs hmid ↦ ?_⟩
  · obtain ⟨N, s, hs, hm⟩ := h.1
    exact ⟨N, s, Bridge.checkpoints_of_partition hs, hm⟩
  have hfun : (fun x ↦ entrywise (bitTruncation k) (H x)) =
      (UnitaryProducts.Paper.truncation k).2.2.2 H :=
    funext fun x ↦ (Bridge.truncHerm_eq k (H x)).symm
  rw [← Bridge.midpointProduct_freeze, Bridge.midpointProduct_eq, hfun]
  exact (h.2 N _ (Bridge.checkpoints_partition hs)
    ((Bridge.hasMidpointError_freeze H N s ε).2 hmid)).2

end RoundedClocks
