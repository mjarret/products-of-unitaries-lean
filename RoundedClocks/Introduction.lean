/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.FineSteps
public import RoundedClocks.UnitSteps

/-!
# Section 1: Discretizing unitary evolution

The two theorems of the introduction. Theorem A (unit steps at width `π`) is Theorem 4.4 at width
`w = π`, through the rounded-clock identity (2.5) and with the constants of Fact B.1. Theorem B
(fine steps with truncated entries) is Lemma 3.4 together with equation (3.1), which follows from
Theorem 3.6.
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

/-- **Theorem A.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), let `T ≥ 1` be an integer, let `H(s)` for `s ∈ [0,1]` be a
time-dependent Hamiltonian whose derivative `H'` has Lipschitz constant `L`, and let `U` be its
evolution over time `T`. If every sample `H(j/T)` with `0 ≤ j ≤ T` has eigenvalue differences of
modulus at most `π`, then
`‖e^{-iH(1)/2} W_T e^{iH(0)/2} - U(T)‖ ≤ (0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²)/T`. -/
theorem theorem_A (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L : ℝ}
    (hL : HasLipschitzDerivative H L) (hwidth : HasSampleWidth H T π) :
    ‖exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      (0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2) / T := by
  -- The rounded-clock identity (2.5): the left side is the distance between the evolutions of
  -- `H` on the rounded clock and on the true clock.
  rw [← roundedEvolution_end dieudonne_10_5_4 hH hT]
  -- Theorem 4.4 at width `w = π` bounds this distance by `ℰ_π(H)/T`.
  refine (rounded_clock_bound dieudonne_7_6_1 dieudonne_10_5_4 dieudonne_10_6_3
    hT hH hL (by linarith [Real.pi_pos]) hwidth).trans ?_
  -- Fact B.1: `ℰ_π(H) ≤ 0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²`.
  exact div_le_div_of_nonneg_right ((constants_at_pi.2.2.2 H L) hL)
    (Nat.cast_nonneg T)

/-- **Theorem B.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with the
remark (10.4.6), let `H(s)` for `s ∈ [0,1]` be a regulated time-dependent Hamiltonian with
evolution `U` over time `T > 0`, and let `ε > 0`. Take checkpoints such that, inside each interval
between them, `H(s)` is within `ε` of the sample at the interval's midpoint, which every regulated
`H` admits. Inside each interval, replace `H` by that sample with every entry's real and imaginary
parts truncated toward zero at the `k`th binary place. The resulting product is within
`T (ε + √2 σ_k 2^{-k})` of `U(T)`. -/
theorem theorem_B (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3) [NeZero d] {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (k : ℕ) :
    (∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧ HasMidpointError H N s ε) ∧
      ∀ (N : ℕ) (s : ℕ → ℝ), IsCheckpoints N s → HasMidpointError H N s ε →
        ‖midpointProduct (truncation k H) T N s - evolution H T T‖ ≤
          T * (ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
  constructor
  · -- Lemma 3.4: every regulated `H` admits such checkpoints.
    obtain ⟨N, s, hs, -, hmid⟩ := exists_checkpoints dieudonne_7_6_1 hH hε
    exact ⟨N, s, hs, hmid⟩
  · -- Equation (3.1), which follows from Theorem 3.6.
    intro N s hs hmid
    exact fine_steps_bits dieudonne_7_6_1 dieudonne_10_5_4
      dieudonne_10_6_3 hH hT hε.le k hs hmid

end RoundedClocks
