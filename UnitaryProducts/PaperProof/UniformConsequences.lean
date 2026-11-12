/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.PropTransfer
public import UnitaryProducts.PaperProof.UnitRounded

public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.UniformTruncation
public import UnitaryProducts.PaperProof.UniformConstants
public import UnitaryProducts.PaperProof.CenteredUnitSteps
public import UnitaryProducts.PaperProof.FrameUnitSteps
public import UnitaryProducts.PaperProof.PropJumps
public import UnitaryProducts.PaperProof.CanonicalCell
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.PaperProof.ClosedCellCorrector

/-!
# UniformConsequences

## Declarations

- `cor_unit_transfer`
- `ex_unit_transfer_chain`
- `ex_unit_transfer_bounds`
- `cor_unit_transfer_bounds`
- `thm_unit_steps`
- `thm_unit_steps_bounds`
- `clock_series_bound`
- `endpoint_series_bound`
- `thm_unit_steps_endpoint_max`
- `thm_unit_steps_coarse`
- `cor_unit_transfer_min`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
open UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.Paper

/-- The coefficient `𝓔_w(H)` defined before (4.6). The parameter `L` is the
Lipschitz constant of the derivative on the unit interval. -/
def hamiltonianEnergy {d : ℕ} (w L : ℝ)
    (H : ℝ → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  let c₀ := PaperProof.cellConstant w
  let c₁ := c₀ / 4 + 1 / 64
  c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + frameMult w) * L +
    (c₁ + 2 * deriv frameMult w) * unitSupNorm Hd ^ 2

end UnitaryProducts.Paper

namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The operator-series comparison: compare the rounded-clock and original
 evolutions, retaining the finite sum of corrector end-value changes.
 `Hd` is the derivative, including its one-sided values at the endpoints.
 The proof applies Theorem 2.2, retains the jump sum, and bounds the
 endpoints and residual integral using Lemma A.1(ii) and Theorem 4.2 residual computation. -/
theorem clock_series_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ}
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    let Δ := unitClockJump H Hd T
    ‖V T - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
      L / 24 + c₁ * unitSupNorm Hd ^ 2) + ∑ j ∈ Finset.Icc 1 T, ‖Δ j‖ := by
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ unitSupNorm Hd :=
    fun _ hs ↦ norm_le_unitSupNorm (continuousOn_of_norm_sub_le hlip) hs
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hwidth' : AllSampleWidth T T H hH w := by
    intro r hr p q
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hr.1
    simpa only [div_self ht.ne', one_smul, Int.cast_natCast] using
      hwidth j (by exact_mod_cast hr.2) p q
  have hcomparison := unit_steps_uncentred hT H Hd U V hH hd hbd hlip hw hwidth' hU hV
  dsimp only at hcomparison ⊢
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  rw [cellConstant_eq_frameBound hw0 hw, unitClockJump_norm_sum]
  exact hcomparison.trans_eq (by ring)

/-- **Theorem 4.2** (`thm:clocks`): the comparison with the
entrywise multiplier and closed constants of Definition 4.1. -/
theorem thm_clocks [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ}
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    let Δ := paperClockJump H Hd T
    ‖V T - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
      L / 24 + c₁ * unitSupNorm Hd ^ 2) + ∑ j ∈ Finset.Icc 1 T, ‖Δ j‖ := by
  dsimp only
  rw [paperClockJump_sum_eq H Hd hH hw hwidth]
  exact clock_series_bound hT H Hd U V hH hd hlip hw hwidth hU hV

/-- The operator-series endpoint bound: insert Theorem 4.4(i)
into Theorem 4.2 (`thm:clocks`).
The derivative uses its compact-interval supremum, and the endpoint norms remain exact. -/
theorem endpoint_series_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ}
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    let c₀ := frameBound w - frameBound (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    ‖V T - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
      (1 / 24 + frameBound w) * L + (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2) := by
  have hclock := thm_clocks hT H Hd U V hH hd hlip hw hwidth hU hV
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  dsimp only at hclock
  rw [cellConstant_eq_frameBound hw0 hw, paperClockJump_sum_eq H Hd hH hw hwidth] at hclock
  have hsum := (thm_jumps hT H Hd hH hd hlip hw hwidth).1
  rw [paperClockJump_sum_eq H Hd hH hw hwidth, paperFrameMult_eq_series hw0 hw,
    paperFrameMult_deriv_eq_series hw0 hw] at hsum
  exact hclock.trans ((add_le_add_right hsum _).trans_eq (by ring))

/-- Evaluate the coefficient in (4.6) using a prescribed derivative. Uniqueness
of the one-sided derivative identifies the two endpoints and its supremum. -/
theorem hamiltonianEnergy_eq_of_hasDerivWithinAt (w L : ℝ) (H Hd : ℝ → 𝕄)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s) :
    hamiltonianEnergy w L H = cellConstant w * (‖Hd 0‖ + ‖Hd 1‖) +
      (1 / 24 + frameMult w) * L +
      (cellConstant w / 4 + 1 / 64 + 2 * deriv frameMult w) * unitSupNorm Hd ^ 2 := by
  have heq : EqOn (derivWithin H (Icc (0 : ℝ) 1)) Hd (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).derivWithin (uniqueDiffOn_Icc_zero_one s hs)
  have hsup : unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) = unitSupNorm Hd := by
    unfold unitSupNorm
    congr 1
    exact Set.image_congr fun s hs ↦ congrArg norm (heq hs)
  simp only [hamiltonianEnergy, heq (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num),
    heq (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num), hsup]

/-- Equation (4.6) (`eq:products`): the comparison with the
entrywise multiplier and closed constants of Definition 4.1. -/
theorem unit_steps_endpoint_bounds [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ}
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    ‖V T - U T‖ ≤ hamiltonianEnergy w L H / T := by
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt w L H Hd hd,
    div_eq_mul_one_div, mul_comm _ (1 / (T : ℝ))]
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) 0
  rw [cellConstant_eq_frameBound hw0 hw, paperFrameMult_eq_series hw0 hw,
    paperFrameMult_deriv_eq_series hw0 hw]
  exact endpoint_series_bound hT H Hd U V hH hd hlip hw hwidth hU hV

set_option maxHeartbeats 800000 in
-- The comparison combines rounded evolution, endpoint constants, and entrywise truncation.
/-- Auxiliary comparison for an odd entrywise truncation:
differentiability on the closed interval means one-sided differentiability at its endpoints. The
cell proof retains the
endpoint derivative norms and uses the derivative supremum and Lipschitz bound.
Duhamel adds precisely the sample truncation sum. -/
theorem thm_unit_steps_bounds [NeZero d] (H U : ℝ → 𝕄) (T : ℕ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1))
    (L w : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (F : ℝ → ℝ) (hF : ∀ x, F (-x) = -F x) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let c₀ := Nf w - Nf (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let A := fun s ↦ scalarEntryMap F (H s)
    ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      (∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖) +
      (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * L +
        (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2) := by
  intro Nf c₀ c₁ Hd A
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hw₀ : 0 ≤ w := by simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hcell := unit_steps_endpoint_bounds hT H Hd U V hH
    (fun s hs ↦ (hdiff s hs).hasDerivWithinAt) hlip hw hwidth hU hV
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt w L H Hd (fun s hs ↦ (hdiff s hs).hasDerivWithinAt),
    div_eq_mul_one_div, mul_comm _ (1 / (T : ℝ))] at hcell
  rw [cellConstant_eq_frameBound hw₀ hw, paperFrameMult_eq_series hw₀ hw,
    paperFrameMult_deriv_eq_series hw₀ hw] at hcell
  obtain ⟨hN, _⟩ := paper_series_eq hw₀ hw
  have hNhalf := (paper_series_eq (by linarith : 0 ≤ w / 2)
    (by linarith [pi_pos] : w / 2 < 2 * π)).1
  have hexact : ‖evol (H 1) (1 / 2) * (unitProduct H T).1 *
      evol (H 0) (-(1 / 2)) - U T‖ ≤
      (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * L +
        (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2) := by
    have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
    simpa only [heV, div_self ht.ne', one_smul, hhalf, c₀, c₁, Nf, hN, hNhalf]
      using hcell
  have htrunc := unitProduct_truncation_comparison
    (B := (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * L +
      (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2)) T hH
    (fun s hs ↦ scalarEntryMap_isHermitian F hF (hH s hs)) (U T)
    (by
      rw [uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))]
      exact hexact)
  simpa only [add_comm] using htrunc

/-- The transfer paragraph in Section 4.3: Proposition 2.4 transports the
endpoint-norm comparison (4.6) to the two leakage norms. -/
theorem cor_unit_transfer_bounds [NeZero d] (H U : ℝ → 𝕄) (T : ℕ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1))
    (L w : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ L * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (F : ℝ → ℝ) (hF : ∀ x, F (-x) = -F x)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1)) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let c₀ := Nf w - Nf (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let A := fun s ↦ scalarEntryMap F (H s)
    |‖(1 - Q) * (unitProduct A T).1 * P‖ - ‖(1 - Q) * U T * P‖| ≤
      (∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖) +
      (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * L +
        (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2) := by
  intro Nf c₀ c₁ Hd A
  have htransfer := prop_transfer (U := U T) (W := (unitProduct A T).1)
    hP hQ hP hQ
    (evol_mem_unitary (hH 1 (by norm_num)) (1 / 2))
    (evol_mem_unitary (hH 0 (by norm_num)) (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simp only [sub_self, norm_zero, add_zero, mul_zero] at htransfer
  exact htransfer.trans (thm_unit_steps_bounds H U T hT hH hdiff L w
    hlip hw hwidth hU F hF)


/-- The endpoint average at any attaining scalar center is at most the centered maximum. -/
theorem centered_endpoint_average_le (Hd : ℝ → 𝕄)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) (b : ℝ)
    (hb : unitSupNorm (fun s ↦ Hd s - b • (1 : 𝕄)) = unitCenteredNorm Hd) :
    (‖Hd 0 - b • (1 : 𝕄)‖ + ‖Hd 1 - b • (1 : 𝕄)‖) / 2 ≤ unitCenteredNorm Hd := by
  have hzero := (norm_le_unitSupNorm (hc.sub continuousOn_const)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)).trans_eq hb
  have hone := (norm_le_unitSupNorm (hc.sub continuousOn_const)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)).trans_eq hb
  linarith

/-- Closed-bound auxiliary for the unit-step comparison: the two-line inequality chain for every
odd entry map,
with the attained scalar-centered derivative minimum and its least Lipschitz constant.
The proof centers the path, applies both clauses of the canonical cell Lemma A.1,
and adds Duhamel's error on exactly the `T` samples in the product.
In positive dimension, equal eigenvalue indices in the sampled width bound imply `0 ≤ w`. -/
theorem thm_unit_steps_endpoint_max (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    ∃ c₀ c₁ : ℝ,
    (c₀ = Nf w - Nf (w / 2) / 2 ∧ c₁ = c₀ / 4 + 1 / 64) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℕ) (_ : 0 < T)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (_ : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ hjN : j ≤ T, ∀ p q,
        |(hH _ (walkCubic_sample hjN)).eigenvalues p -
          (hH _ (walkCubic_sample hjN)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T)
      (F : ℝ → ℝ) (_ : ∀ x, F (-x) = -F x),
      let A := fun s ↦ scalarEntryMap F (H s)
      let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp (H s) (Hd s)
      let J := ∑ j ∈ Finset.range T, ‖Yb (((j : ℝ) + 1) / T) - Yb ((j : ℝ) / T)‖
      let L := unitCenteredNorm Hd
      let M := unitLip Hd
      ∀ bstar : ℝ, unitSupNorm (fun s ↦ Hd s - bstar • (1 : 𝕄)) = L →
      let Lbar := (‖Hd 0 - bstar • (1 : 𝕄)‖ + ‖Hd 1 - bstar • (1 : 𝕄)‖) / 2
      ‖UnitaryProducts.evol (H 1) (1 / 2) * (unitProduct A T).1 *
        UnitaryProducts.evol (H 0) (-(1 / 2)) - U T‖ ≤
        (1 / T : ℝ) * (2 * c₀ * Lbar + (1 / 24) * M + c₁ * L ^ 2 + J) + ε ∧
      (1 / T : ℝ) * (2 * c₀ * Lbar + (1 / 24) * M + c₁ * L ^ 2 + J) + ε ≤
        (1 / T : ℝ) * (2 * c₀ * Lbar + (1 / 24 + Nf w) * M +
          (c₁ + 2 * deriv Nf w) * L ^ 2) + ε := by
  intro Nf
  let c₀ := Nf w - Nf (w / 2) / 2
  let c₁ := c₀ / 4 + 1 / 64
  refine ⟨c₀, c₁, ⟨rfl, rfl⟩, ?_⟩
  intro H U T hT hH hc hlip hdiff hU F hF A ε Hd Yb J L M
  have hdc := hc.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  intro b hb Lbar
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    have hL : L = 0 := by simp [L, unitCenteredNorm, unitSupNorm, hz]
    have hm := unitLip_spec Hd (M := 0) (by intros; simp [hz])
    have hM : M = 0 := le_antisymm hm.2.1 hm.1
    simp [hz, hL, hM, ε, J, Yb, Lbar]
  letI : NeZero d := ⟨hdpos.ne'⟩
  have hw0 : 0 ≤ w := by simpa using hdiff 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  obtain ⟨hNf, hDf⟩ := paper_series_eq hw0 hw
  have hNhalf := (paper_series_eq (x := w / 2) (by linarith) (by linarith [pi_pos])).1
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have ht := hTr.ne'
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  let K : ℝ → 𝕄 := fun s ↦ H s - (b * s) • (1 : 𝕄)
  let D : ℝ → 𝕄 := fun s ↦ Hd s - b • (1 : 𝕄)
  have hK : ∀ s ∈ Icc (0 : ℝ) 1, (K s).IsHermitian := fun s hs ↦
    (hH s hs).sub (Separation.isHermitian_real_smul Matrix.isHermitian_one (b * s))
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ (hc.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hdK : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt K (D s) (Icc 0 1) s := by
    intro s hs
    have hscalar : HasDerivWithinAt (fun x : ℝ ↦ (b * x) • (1 : 𝕄))
        (b • (1 : 𝕄)) (Icc (0 : ℝ) 1) s := by
      simpa only [mul_one, id_eq] using
        (((hasDerivAt_id s).const_mul b).smul_const (1 : 𝕄)).hasDerivWithinAt
    exact (hd s hs).sub hscalar
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖D s‖ ≤ L := by
    intro s hs
    exact (norm_le_unitSupNorm (hdc.sub continuousOn_const) hs).trans_eq hb
  obtain ⟨m, hm⟩ := hlip
  have hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖D t - D s‖ ≤ M * |t - s| := by
    simpa only [D, sub_sub_sub_cancel_right] using (unitLip_spec Hd hm).2.2
  have hwidthK : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hK _ (walkCubic_sample hj)).eigenvalues p -
        (hK _ (walkCubic_sample hj)).eigenvalues q| ≤ w := by
    intro j hj p q
    exact (scalar_shift_sample_width (hH _ (walkCubic_sample hj))
      (hdiff j hj) (b * ((j : ℝ) / T))).choose_spec p q
  have hwidth : AllSampleWidth T T K hK w := by
    intro r hr p q
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hr.1
    simpa only [div_self ht, one_smul, Int.cast_natCast] using
      hwidthK j (by exact_mod_cast hr.2) p q
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution hTr hT H hH
  obtain ⟨Ub, Vb, hUb, hVb, hedist, _hVphase⟩ := centered_evolution_pair hT hU hV b
  have hcell := unit_steps_uncentred hT K D Ub Vb hK hdK hbd hLip hw hwidth hUb hVb
  dsimp only at hcell
  rw [hedist] at hcell
  have hSigma : (∑ j ∈ Finset.range T,
      ‖frameOp (K (((j : ℝ) + 1) / T)) (D (((j : ℝ) + 1) / T)) -
        frameOp (K ((j : ℝ) / T)) (D ((j : ℝ) / T))‖) = J := by
    simpa only [K, D, J, Yb, Nat.cast_add, Nat.cast_one] using centered_sigma H Hd T b hw hH hdiff
  rw [hSigma] at hcell
  have hexact : ‖V T - U T‖ ≤
      (1 / T : ℝ) * (2 * c₀ * Lbar + (1 / 24) * M + c₁ * L ^ 2 + J) := by
    apply hcell.trans_eq
    dsimp [c₀, c₁, Nf, Lbar, D]
    rw [hNf, hNhalf]
    ring
  have hσ : J ≤ frameBound w * M + 2 * frameLip w * L ^ 2 := by
    rw [← hSigma]
    calc
      _ ≤ ∑ _j ∈ Finset.range T, (frameBound w * M + 2 * frameLip w * L ^ 2) / T := by
        apply Finset.sum_le_sum
        intro j hj
        have hjT := Finset.mem_range.mp hj
        have ha := walkCubic_sample (show j ≤ T by omega)
        have hb' := walkCubic_sample (show j + 1 ≤ T by omega)
        have hh := canonical_cell_variation K D hK hdK hw0 hw hbd hLip ha hb'
          (hwidthK j (by omega)) (hwidthK (j + 1) (by omega))
        have hstep : |((j + 1 : ℕ) : ℝ) / T - (j : ℝ) / T| = 1 / T := by
          rw [Nat.cast_add, Nat.cast_one, ← sub_div]
          simp [abs_of_pos hTr]
        rw [hstep] at hh
        simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using hh
      _ = _ := by simp; field_simp
  constructor
  · apply unitProduct_truncation_comparison T hH
      (fun s hs ↦ scalarEntryMap_isHermitian F hF (hH s hs)) (U T)
    rw [uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))]
    simpa only [heV, div_self ht, one_smul, hhalf] using hexact
  · rw [← hNf, ← hDf] at hσ
    refine add_le_add ?_ (le_refl ε)
    have hbnd := mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (2 * c₀ * Lbar + (1 / 24) * M + c₁ * L ^ 2)) hσ)
      (by positivity : 0 ≤ (1 / T : ℝ))
    exact hbnd.trans_eq (by ring)

/-- Centered minimum comparison for a path with a
Lipschitz derivative and sampled spectral width below `2π`. For every scalar
center, the error is bounded by truncation plus the minimum of the rotating-frame estimate
and the canonical-cell bound, then by the explicit upper bound.
The quantities are those defined before the theorem in Section 4.1;
`unitCenteredNorm_attained` separately justifies the minimum defining `L`. -/
theorem thm_unit_steps (H U V : ℝ → 𝕄) (T : ℕ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    ∀ (w : ℝ) (_ : w < 2 * π)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (_ : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
        |(hH _ (walkCubic_sample hj)).eigenvalues p -
          (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
      (F : ℝ → ℝ) (_ : ∀ x, F (-x) = -F x),
      let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
      let c₀ := Nf w - Nf (w / 2) / 2
      let c₁ := c₀ / 4 + 1 / 64
      let A := fun s ↦ scalarEntryMap F (H s)
      let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Φ := fun s ↦ frameOp (H s) (Hd s)
      let J := ∑ j ∈ Finset.range T, ‖Φ (((j : ℝ) + 1) / T) - Φ ((j : ℝ) / T)‖
      let L := unitCenteredNorm Hd
      let M := unitLip Hd
      ∀ bstar : ℝ, unitSupNorm (fun s ↦ Hd s - bstar • (1 : 𝕄)) = L →
      let Lbar := (‖Hd 0 - bstar • (1 : 𝕄)‖ + ‖Hd 1 - bstar • (1 : 𝕄)‖) / 2
      ∀ b : ℝ,
        let B := ‖centeredUnitFrameIntegral H V T b T‖ +
          ∫ t in (0 : ℝ)..T,
            ‖deriv (centeredUnitFrameIntegral H V T b) t * centeredUnitFrameIntegral H V T b t‖
        ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
          ε + min B ((1 / T : ℝ) * (2 * c₀ * Lbar + M / 24 + c₁ * L ^ 2 + J)) ∧
        ε + min B ((1 / T : ℝ) * (2 * c₀ * Lbar + M / 24 + c₁ * L ^ 2 + J)) ≤
          ε + (1 / T : ℝ) * (2 * c₀ * Lbar + (1 / 24 + Nf w) * M +
            (c₁ + 2 * deriv Nf w) * L ^ 2) := by
  intro w hw hc hlip hwidth F hF Nf c₀ c₁ A ε Hd Φ J L M
  have hHr := Prose.regulated_of_continuousOn hc.continuousOn
  have hframe := fun b ↦ frame_unit hT hHr hH hU hV b
  intro bstar hbstar Lbar
  obtain ⟨a₀, a₁, hcs, hclosed⟩ := thm_unit_steps_endpoint_max (d := d) w hw
  obtain ⟨hbound, hchain⟩ := hclosed H U T hT hH hc hlip hwidth hU F hF bstar hbstar
  have ha₀ : a₀ = c₀ := hcs.1
  have ha₁ : a₁ = c₁ := by rw [hcs.2, ha₀]
  rw [ha₀, ha₁] at hbound hchain
  intro b B
  have hexact : ‖evol (H 1) (1 / 2) * (unitProduct H T).1 *
      evol (H 0) (-(1 / 2)) - U T‖ ≤ B := by
    have hupper := (abs_le.mp (hframe b)).2
    exact sub_le_iff_le_add'.mp hupper
  have htrunc := unitProduct_truncation_comparison (B := B) T hH
    (fun s hs ↦ scalarEntryMap_isHermitian F hF (hH s hs)) (U T)
    (by
      rw [uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))]
      exact hexact)
  constructor
  · rw [add_min]
    apply le_min
    · simpa only [add_comm] using htrunc
    · simpa only [one_div_mul_eq_div, add_comm ε] using hbound
  · calc
      _ ≤ ε + (1 / T : ℝ) * (2 * c₀ * Lbar + M / 24 + c₁ * L ^ 2 + J) :=
        add_le_add (le_refl ε) (min_le_right _ _)
      _ ≤ _ := by simpa only [one_div_mul_eq_div, add_comm ε] using hchain

/-- Centered bound: replace the endpoint average by the centered maximum.
This monotonicity specialization preserves the transfer and bits bounds. -/
theorem thm_unit_steps_coarse (H U V : ℝ → 𝕄) (T : ℕ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    ∀ (w : ℝ) (_ : w < 2 * π)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (_ : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
        |(hH _ (walkCubic_sample hj)).eigenvalues p -
          (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
      (F : ℝ → ℝ) (_ : ∀ x, F (-x) = -F x),
      let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
      let c₀ := Nf w - Nf (w / 2) / 2
      let c₁ := c₀ / 4 + 1 / 64
      let A := fun s ↦ scalarEntryMap F (H s)
      let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Φ := fun s ↦ frameOp (H s) (Hd s)
      let J := ∑ j ∈ Finset.range T, ‖Φ (((j : ℝ) + 1) / T) - Φ ((j : ℝ) / T)‖
      let L := unitCenteredNorm Hd
      let M := unitLip Hd
      ∀ b : ℝ,
        let B := ‖centeredUnitFrameIntegral H V T b T‖ +
          ∫ t in (0 : ℝ)..T,
            ‖deriv (centeredUnitFrameIntegral H V T b) t * centeredUnitFrameIntegral H V T b t‖
        ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
          ε + min B ((1 / T : ℝ) * (2 * c₀ * L + M / 24 + c₁ * L ^ 2 + J)) ∧
        ε + min B ((1 / T : ℝ) * (2 * c₀ * L + M / 24 + c₁ * L ^ 2 + J)) ≤
          ε + (1 / T : ℝ) * (2 * c₀ * L + (1 / 24 + Nf w) * M +
            (c₁ + 2 * deriv Nf w) * L ^ 2) := by
  intro w hw hc hlip hwidth F hF Nf c₀ c₁ A ε Hd Φ J L M
  have hdc := hc.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  obtain ⟨bstar, hbstar⟩ := (unitCenteredNorm_attained hdc).1
  let Lbar := (‖Hd 0 - bstar • (1 : 𝕄)‖ + ‖Hd 1 - bstar • (1 : 𝕄)‖) / 2
  have hbar : Lbar ≤ L := centered_endpoint_average_le Hd hdc bstar hbstar
  have hfine := thm_unit_steps H U V T hT hH hU hV w hw hc hlip hwidth F hF bstar hbstar
  intro b B
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    have hL : L = 0 := by simp [L, unitCenteredNorm, unitSupNorm, hz]
    have hm := unitLip_spec Hd (M := 0) (by intros; simp [hz])
    have hM : M = 0 := le_antisymm hm.2.1 hm.1
    simp [hz, hL, hM, ε, J, Φ, B]
  letI : NeZero d := ⟨hdpos.ne'⟩
  have hw0 : 0 ≤ w := by simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  have hc₀ : 0 ≤ c₀ := by
    dsimp only [c₀, Nf]
    rw [(paper_series_eq hw0 hw).1,
      (paper_series_eq (by linarith : 0 ≤ w / 2) (by linarith : w / 2 < 2 * π)).1]
    exact UnitStepsProse.center_bound_nonneg hw0 hw
  have hlinear := mul_le_mul_of_nonneg_left hbar (show 0 ≤ 2 * c₀ by positivity)
  have hscale : 0 ≤ (1 / T : ℝ) := by positivity
  constructor
  · apply (hfine b).1.trans
    apply add_le_add (le_refl ε)
    apply min_le_min_left
    exact mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add hlinear (le_refl (M / 24)))
        (le_refl (c₁ * L ^ 2))) (le_refl J)) hscale
  · calc
      _ ≤ ε + (1 / T : ℝ) * (2 * c₀ * L + M / 24 + c₁ * L ^ 2 + J) :=
        add_le_add (le_refl ε) (min_le_right _ _)
      _ ≤ _ := by
        -- The endpoint term cancels from the closed inequality.
        obtain ⟨a₀, a₁, hcs, hall⟩ := thm_unit_steps_endpoint_max (d := d) w hw
        have hs := (hall H U T hT hH hc hlip hwidth hU F hF bstar hbstar).2
        have ha₀ : a₀ = c₀ := hcs.1
        have ha₁ : a₁ = c₁ := by rw [hcs.2, ha₀]
        rw [ha₀, ha₁] at hs
        dsimp only at hs
        have hshift := add_le_add_left hs ((1 / T : ℝ) * (2 * c₀ * (L - Lbar)))
        convert hshift using 1 <;> dsimp only [Lbar] <;> ring


/-- Section 4.3: the absolute leakage difference is bounded by the complete
centered minimum, for every scalar center and with the exact sample
truncation sum. The endpoint projectors commute with the original Hamiltonians. -/
theorem cor_unit_transfer_min (H U V : ℝ → 𝕄) (T : ℕ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hlip : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
    (w : ℝ) (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T)
    (F : ℝ → ℝ) (hF : ∀ x, F (-x) = -F x)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1)) (b : ℝ) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let c₀ := Nf w - Nf (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    let A := fun s ↦ scalarEntryMap F (H s)
    let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Φ := fun s ↦ frameOp (H s) (Hd s)
    let J := ∑ j ∈ Finset.range T, ‖Φ (((j : ℝ) + 1) / T) - Φ ((j : ℝ) / T)‖
    let L := unitCenteredNorm Hd
    let M := unitLip Hd
    |‖(1 - Q) * (unitProduct A T).1 * P‖ - ‖(1 - Q) * U T * P‖| ≤
      ε + min (‖centeredUnitFrameIntegral H V T b T‖ +
        ∫ t in (0 : ℝ)..T,
          ‖deriv (centeredUnitFrameIntegral H V T b) t * centeredUnitFrameIntegral H V T b t‖)
        ((1 / T : ℝ) * (2 * c₀ * L + M / 24 + c₁ * L ^ 2 + J)) := by
  intro Nf c₀ c₁ A ε Hd Φ J L M
  have hle := prop_transfer (U := U T) (W := (unitProduct A T).1)
    hP hQ hP hQ
    (evol_mem_unitary (hH 1 (by norm_num)) (1 / 2))
    (evol_mem_unitary (hH 0 (by norm_num)) (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simp only [sub_self, norm_zero, add_zero, mul_zero] at hle
  exact hle.trans ((thm_unit_steps_coarse H U V T hT hH hU hV
      w hw hc hlip hwidth F hF) b).1

set_option maxHeartbeats 1200000 in
-- The expanded theorem and both endpoint-projector transports require a larger elaboration budget.
/-- Centered transfer auxiliary: both centered comparison bounds
transfer to projectors commuting with the exact endpoint Hamiltonians,
with the exact sample-error sum included in the centered comparison. -/
theorem cor_unit_transfer (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    ∃ c₀ c₁ : ℝ,
    (c₀ = Nf w - Nf (w / 2) / 2 ∧ c₁ = c₀ / 4 + 1 / 64) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℕ) (_ : 0 < T)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (_ : ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ hjN : j ≤ T, ∀ p q,
        |(hH _ (walkCubic_sample hjN)).eigenvalues p -
          (hH _ (walkCubic_sample hjN)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T)
      (F : ℝ → ℝ) (_ : ∀ x, F (-x) = -F x)
      (P Q : 𝕄) (_ : IsStarProjection P) (_ : IsStarProjection Q)
      (_ : Commute P (H 0))
      (_ : Commute Q (H 1)),
      let A := fun s ↦ scalarEntryMap F (H s)
      let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp (H s) (Hd s)
      let J := ∑ j ∈ Finset.range T, ‖Yb (((j : ℝ) + 1) / T) - Yb ((j : ℝ) / T)‖
      let L := unitCenteredNorm Hd
      let M := unitLip Hd
      |‖(1 - Q) * (unitProduct A T).1 * P‖ -
        ‖(1 - Q) * U T * P‖| ≤
        (1 / T : ℝ) * (2 * c₀ * L + (1 / 24 + Nf w) * M + (c₁ + 2 * deriv Nf w) * L ^ 2) + ε ∧
      |‖(1 - Q) * (unitProduct A T).1 * P‖ -
        ‖(1 - Q) * U T * P‖| ≤
        (1 / T : ℝ) * (2 * c₀ * L + (1 / 24) * M + (c₁) * L ^ 2 + J) + ε := by
  intro Nf
  let c₀ := Nf w - Nf (w / 2) / 2
  let c₁ := c₀ / 4 + 1 / 64
  have hcs : c₀ = Nf w - Nf (w / 2) / 2 ∧ c₁ = c₀ / 4 + 1 / 64 := ⟨rfl, rfl⟩
  refine ⟨c₀, c₁, hcs, ?_⟩
  intro H U T hT hH hc hlip hdiff hU F hF P Q hP hQ hPc hQc A ε Hd Yb J L M
  obtain ⟨V, hV, _⟩ := exists_rounded_evolution (Nat.cast_pos.mpr hT) hT H hH
  have hmin := thm_unit_steps_coarse H U V T hT hH hU hV
      w hw hc hlip hdiff F hF
  have htransfer := cor_unit_transfer_min H U V T hT hH hc hlip w hw hdiff
    hU hV F hF P Q hP hQ hPc hQc 0
  have hexplicit := htransfer.trans (hmin 0).2
  have hclosed := htransfer.trans (add_le_add (le_refl _) (min_le_right _ _))
  dsimp only at hexplicit hclosed
  rw [add_comm] at hexplicit hclosed
  constructor
  · exact hexplicit
  · simpa only [one_div_mul_eq_div] using hclosed

set_option maxHeartbeats 800000 in
-- The exact sparsity supremum and two real budget calculations expand the transfer theorem.
/-- The series calculation of the bit budget: choose both the unit-step count
and binary precision with quadratic coefficient c₁ + η(w). Endpoint projectors
commute with the Hamiltonians. The proof uses Proposition 2.4, the rounded-clock
identity, Duhamel with Example 3.2, and (4.6). -/
theorem bit_transfer_series_bound [NeZero d] (w : ℝ)
   (hw : w < 2 * π)
   (H U : ℝ → 𝕄)
   (T k : ℕ)
   (hT1 : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
   (hc : DifferentiableOn ℝ H (Icc (0 : ℝ) 1))
    (h : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ hjT : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hjT)).eigenvalues p -
        (hH _ (walkCubic_sample hjT)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (P Q : 𝕄)
   (hP : IsStarProjection P)
   (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0))
   (hQc : Commute Q (H 1))
    (C : NNReal) (δ : ℝ)
   (hδ : 0 < δ)
   (hcont : ‖(1 - Q) * U T * P‖ ≤ (C : ℝ) / T) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let M := (C : ℝ) + T * ((1 / T) *
      (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * h +
        (c₁ + (2 * frameLip w)) * unitSupNorm Hd ^ 2))
    let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
    let W := (unitProduct (fun s ↦ scalarEntryMap (truncBits k) (H s)) T).1
    let Z := evol (H 1) (1 / 2) * W * evol (H 0) (-(1 / 2))
    let V_T := evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))
    2 * M / δ ≤ T → Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
      (‖(1 - Q) * W * P‖ ≤ (C : ℝ) / T + ‖Z - U T‖) ∧
      ((C : ℝ) / T + ‖Z - U T‖ ≤
        (C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V_T - U T‖) ∧
      ((C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V_T - U T‖ ≤
        M / T + T * (Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹)) ∧
      (M / T + T * (Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) ≤ δ / 2 + δ / 2) ∧
      δ / 2 + δ / 2 = δ := by
  classical
  intro Nf c₀ c₁ Hd M σ W Z V_T hbudget hbits
  have hT : (0 : ℝ) < T := Nat.cast_pos.mpr hT1
  let B := fun s ↦ scalarEntryMap (truncBits k) (H s)
  let ε := ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - B ((j : ℝ) / T)‖
  let e := Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹
  have he : ε ≤ T * e := by
    calc
      _ ≤ ∑ _j ∈ Finset.range T, e := by
        apply Finset.sum_le_sum
        intro j hj
        have hpoint : ‖H ((j : ℝ) / T) - B ((j : ℝ) / T)‖ ≤
            ⨆ j : Fin (T + 1), ‖H ((j : ℝ) / T) - B ((j : ℝ) / T)‖ :=
          Finite.le_ciSup (fun j : Fin (T + 1) ↦ ‖H ((j : ℝ) / T) - B ((j : ℝ) / T)‖)
            ⟨j, by have := Finset.mem_range.mp hj; omega⟩
        exact hpoint.trans (uniform_bit_sample_error_sigma hH k)
      _ = T * e := by simp
  -- Proposition 2.4 gives the first line, with the endpoint phases fixed.
  have htransfer := prop_transfer (U := U T) (W := W) hP hQ hP hQ
    (evol_mem_unitary (hH 1 (by norm_num)) (1 / 2))
    (evol_mem_unitary (hH 0 (by norm_num)) (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simp only [sub_self, norm_zero, add_zero, mul_zero] at htransfer
  have hleak : ‖(1 - Q) * W * P‖ ≤ (C : ℝ) / T + ‖Z - U T‖ := by
    have hh := (abs_le.mp htransfer).2
    change ‖(1 - Q) * W * P‖ - ‖(1 - Q) * U T * P‖ ≤ ‖Z - U T‖ at hh
    linarith
  -- The rounded endpoint identity and triangle inequality give the second line.
  obtain ⟨V, hV, _⟩ := exists_rounded_evolution hT hT1 H hH
  have heV := unit_rounded_clock_endpoint H hH T hT1 V (by
    simpa only [sample, clock, mul_div_cancel₀ _ hT.ne'] using hV)
  have hsplit : ‖Z - U T‖ ≤ ‖W - (unitProduct H T).1‖ + ‖V T - U T‖ := by
    simpa only [heV] using unitProduct_truncation_split (A := B) T hH (U T)
  -- Oddness, the held-path identity, Duhamel and the bit estimate bound truncation.
  have htrunc : ‖W - (unitProduct H T).1‖ ≤ T * e :=
    (unitProduct_sample_error T hH
      (fun s hs ↦ scalarEntryMap_isHermitian (truncBits k) (truncBits_neg k) (hH s hs))).trans he
  -- Equation (4.6) bounds the untruncated evolution error.
  have hclock := unit_steps_endpoint_bounds hT1 H Hd U V hH
    (fun s hs ↦ (hc s hs).hasDerivWithinAt) hlip hw hdiff hU hV
  have hw₀ : 0 ≤ w := by simpa using hdiff 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt w h H Hd (fun s hs ↦ (hc s hs).hasDerivWithinAt),
    div_eq_mul_one_div, mul_comm _ (1 / (T : ℝ))] at hclock
  rw [cellConstant_eq_frameBound hw₀ hw, paperFrameMult_eq_series hw₀ hw,
    paperFrameMult_deriv_eq_series hw₀ hw] at hclock
  obtain ⟨hN, _⟩ := paper_series_eq hw₀ hw
  have hNhalf := (paper_series_eq (by linarith : 0 ≤ w / 2)
    (by linarith [pi_pos] : w / 2 < 2 * π)).1
  have hexact : ‖V T - U T‖ ≤ (M - (C : ℝ)) / T := by
    have hb := hclock
    rw [← hN, ← hNhalf] at hb
    have hcancel : (T : ℝ) * (1 / T) = 1 := mul_one_div_cancel hT.ne'
    exact hb.trans_eq (by
      dsimp only [M]
      rw [← mul_assoc, hcancel, one_mul]
      dsimp only [c₀, c₁]
      rw [cellConstant_eq_frameBound hw₀ hw, ← hN, ← hNhalf]
      dsimp only [Nf]
      ring)
  have hA : M / T ≤ δ / 2 := by
    have hh := (div_le_iff₀ hδ).mp hbudget
    apply (div_le_iff₀ hT).mpr
    ring_nf at hh ⊢
    linarith
  have hke : T * e ≤ δ / 2 := by
    have hh := mul_le_mul_of_nonneg_left hbits hT.le
    have ht : (T : ℝ) ≠ 0 := hT.ne'
    exact hh.trans_eq (by field_simp)
  have hsecond : (C : ℝ) / T + ‖Z - U T‖ ≤
      (C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V T - U T‖ := by
    simpa only [add_assoc] using add_le_add (le_refl ((C : ℝ) / T)) hsplit
  have hthird : (C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V T - U T‖ ≤
      M / T + T * e := by
    calc
      _ ≤ (C : ℝ) / T + T * e + (M - (C : ℝ)) / T :=
        add_le_add (add_le_add (le_refl ((C : ℝ) / T)) htrunc) hexact
      _ = _ := by ring
  refine ⟨hleak, ?_, ?_, add_le_add hA hke, by ring⟩
  · simpa only [heV] using hsecond
  · simpa only [heV] using hthird

/-- The intermediate transfer chain in the proof of Example 4.6: commuting
endpoint phases, the product-error split, and both half-budget estimates. The
rounded evolution at the terminal time is written using its endpoint identity. -/
theorem ex_unit_transfer_chain [NeZero d] (w : ℝ)
   (hw : w < 2 * π)
   (H U : ℝ → 𝕄)
   (T k : ℕ)
   (hT1 : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
   (hc : DifferentiableOn ℝ H (Icc (0 : ℝ) 1))
    (h : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ hjT : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hjT)).eigenvalues p -
        (hH _ (walkCubic_sample hjT)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (P Q : 𝕄)
   (hP : IsStarProjection P)
   (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0))
   (hQc : Commute Q (H 1))
    (C : NNReal) (δ : ℝ)
   (hδ : 0 < δ)
   (hcont : ‖(1 - Q) * U T * P‖ ≤ (C : ℝ) / T) :
    let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
    let W := (unitProduct (fun s ↦ scalarEntryMap (truncBits k) (H s)) T).1
    let Z := evol (H 1) (1 / 2) * W * evol (H 0) (-(1 / 2))
    let V_T := evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))
    2 * ((C : ℝ) + hamiltonianEnergy w h H) / δ ≤ T →
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
      (‖(1 - Q) * W * P‖ ≤ (C : ℝ) / T + ‖Z - U T‖) ∧
      ((C : ℝ) / T + ‖Z - U T‖ ≤
        (C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V_T - U T‖) ∧
      ((C : ℝ) / T + ‖W - (unitProduct H T).1‖ + ‖V_T - U T‖ ≤
        ((C : ℝ) + hamiltonianEnergy w h H) / T + T * (Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹)) ∧
      (((C : ℝ) + hamiltonianEnergy w h H) / T +
        T * (Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹) ≤ δ / 2 + δ / 2) ∧
      δ / 2 + δ / 2 = δ := by
  have hw0 : 0 ≤ w := by
    simpa using hdiff 0 (Nat.zero_le T) (0 : Fin d) 0
  dsimp only
  unfold hamiltonianEnergy
  rw [paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw]
  have h := bit_transfer_series_bound w hw H U T k hT1 hH hc h hlip hdiff hU
    P Q hP hQ hPc hQc C δ hδ hcont
  dsimp only at h
  rw [(paper_series_eq hw0 hw).1] at h
  have ht : (T : ℝ) ≠ 0 := (Nat.cast_pos.mpr hT1).ne'
  simpa only [← mul_assoc, mul_one_div_cancel ht, one_mul] using h

/-- **Example 4.6** (`ex:unit-transfer`): the bit budget with the closed
scalar constants in Definition 4.1 and Theorem 4.2. -/
theorem ex_unit_transfer_bounds [NeZero d] (w : ℝ)
   (hw : w < 2 * π)
   (H U : ℝ → 𝕄)
   (T k : ℕ)
   (hT1 : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
   (hc : DifferentiableOn ℝ H (Icc (0 : ℝ) 1))
    (L : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ L * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ hjT : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hjT)).eigenvalues p -
        (hH _ (walkCubic_sample hjT)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (P Q : 𝕄)
   (hP : IsStarProjection P)
   (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0))
   (hQc : Commute Q (H 1))
    (C : NNReal) (δ : ℝ)
   (hδ : 0 < δ)
   (hcont : ‖(1 - Q) * U T * P‖ ≤ (C : ℝ) / T) :
    let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
    2 * ((C : ℝ) + hamiltonianEnergy w L H) / δ ≤ T →
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
      ‖(1 - Q) * (unitProduct (fun s ↦ scalarEntryMap (truncBits k) (H s)) T).1 * P‖ ≤ δ := by
  intro σ hbudget hbits
  have hchain := ex_unit_transfer_chain w hw H U T k hT1 hH hc L hlip hdiff hU
    P Q hP hQ hPc hQc C δ hδ hcont hbudget hbits
  exact (hchain.1.trans (hchain.2.1.trans
    (hchain.2.2.1.trans hchain.2.2.2.1))).trans_eq hchain.2.2.2.2

end UnitaryProducts.PaperProof
