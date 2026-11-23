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

/-- **Theorem A.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3) with
the remark (10.4.6),
and DLMF 4.22.5, let `T ≥ 1` be an integer, let `H(s)` for `s ∈ [0,1]` be a
time-dependent Hamiltonian whose derivative `H'` has Lipschitz constant `L`, and let `U` be its
evolution over time `T`. If every sample `H(j/T)` with `0 ≤ j ≤ T` has eigenvalue differences of
modulus at most `π`, then
`‖e^{-iH(1)/2} W_T e^{iH(0)/2} - U(T)‖ ≤ (0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²)/T`. -/
theorem theorem_A (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L : ℝ}
    (hL : HasLipschitzDerivative H L) (hwidth : HasSampleWidth H T π) :
    ‖exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      (0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2) / T := by
  rw [← roundedEvolution_end dieudonne_10_5_4 hH hT]
  refine (rounded_clock_bound dieudonne_7_6_1 dieudonne_section_8_7 dieudonne_8_6_4
    dlmf_4_22_5 dieudonne_10_5_4 dieudonne_10_6_3
    hT hH hL (by linarith [Real.pi_pos]) hwidth).trans ?_
  exact div_le_div_of_nonneg_right ((constants_at_pi.2.2.2 H L) hL)
    (Nat.cast_nonneg T)

/-- **Theorem B.** Assuming Dieudonné (7.6.1), Section 8.7, (10.5.4) and (10.6.3) with the remark
(10.4.6),
let `H(s)` for `s ∈ [0,1]` be a regulated time-dependent Hamiltonian with evolution `U` over time
`T > 0`, and let `ε > 0`. Take checkpoints such that, inside each interval between them, `H(s)` is
within `ε` of the sample at the interval's midpoint, which every regulated `H` admits. Inside each
interval, replace `H` by that sample with every entry's real and imaginary parts truncated toward
zero at the `k`th binary place. The resulting product is within
`T (ε + √2 σ_k 2^{-k})` of `U(T)`. -/
theorem theorem_B (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3) [NeZero d] {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) (k : ℕ) :
    (∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧ HasMidpointError H N s ε) ∧
      ∀ (N : ℕ) (s : ℕ → ℝ), IsCheckpoints N s → HasMidpointError H N s ε →
        ‖midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s - evolution H T T‖ ≤
          T * (ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
  have htrunc := truncation_bits (d := d) k
  constructor
  · obtain ⟨N, s, hs, -, hmid⟩ := exists_checkpoints dieudonne_7_6_1 hH hε
    exact ⟨N, s, hs, hmid⟩
  intro N s hs hmid
  let η := √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    positivity
  have hs_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) : s a ≤ s b := by
    induction b with
    | zero =>
        have : a = 0 := by omega
        subst a
        exact le_rfl
    | succ b ih =>
        by_cases ha : a = b + 1
        · subst a
          exact le_rfl
        · have hab' : a ≤ b := by omega
          exact (ih hab' (by omega)).trans (hs.1 b (by omega))
  have hmidpoint {j : ℕ} (hj : j < N) :
      (s j + s (j + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
    have hj0 : 0 ≤ s j := by
      rw [← hs.2.1]
      exact hs_mono (Nat.zero_le j) (by omega)
    have hj1 : s (j + 1) ≤ 1 := by
      rw [← hs.2.2]
      exact hs_mono (by omega) le_rfl
    have hjstep : s j ≤ s (j + 1) := hs.1 j hj
    constructor <;> linarith
  have herr : midpointApproximationError (bitTruncation k) H N s ≤ ε + η := by
    apply csSup_le
    · exact ⟨0, Set.mem_union_left _ (Set.mem_singleton 0)⟩
    · intro r hr
      rcases hr with hr | hr
      · rw [Set.mem_singleton_iff.mp hr]
        positivity
      · obtain ⟨j, hj, x, hx, rfl⟩ := hr
        let m := (s j + s (j + 1)) / 2
        calc
          ‖H x - entrywise (bitTruncation k) (H m)‖ ≤
              ‖H x - H m‖ + ‖H m - entrywise (bitTruncation k) (H m)‖ := by
            rw [show H x - entrywise (bitTruncation k) (H m) =
              (H x - H m) + (H m - entrywise (bitTruncation k) (H m)) by abel]
            exact norm_add_le _ _
          _ ≤ ε + η := add_le_add (hmid j hj x hx) (htrunc.2 H hH.2 m (hmidpoint hj))
  exact (fine_steps dieudonne_7_6_1 dieudonne_section_8_7 dieudonne_10_5_4
    dieudonne_10_6_3 htrunc.1 hH hT hs).trans
    (mul_le_mul_of_nonneg_left herr hT.le)

end RoundedClocks
