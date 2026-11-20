/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.PropTransfer
public import UnitaryProducts.PaperProof.UnitRounded

public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.UniformTruncation
public import UnitaryProducts.PaperProof.UniformConstants
public import UnitaryProducts.PaperProof.CenteredUnitSteps
public import UnitaryProducts.PaperProof.PropJumps
public import UnitaryProducts.PaperProof.CanonicalCell
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.PaperProof.ClosedCellCorrector

/-!
# UniformConsequences

## Declarations

- `ex_unit_transfer_chain`
- `ex_unit_transfer_bounds`
- `clock_series_bound`
- `endpoint_series_bound`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
open UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.Paper

/-- The coefficient `𝓔_w(H)` defined in Appendix B. The parameter `L` is the
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
    (H Hd U V : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
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
entrywise multiplier of Definition 4.1 and constants of Appendix B. -/
theorem thm_clocks [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hder : HasLipschitzDerivative H Hd L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    let Δ := paperClockJump H Hd T
    ‖roundedEvolution H T T - evolution H T T‖ ≤
      (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
        L / 24 + c₁ * unitSupNorm Hd ^ 2) + ∑ j ∈ Finset.Icc 1 T, ‖Δ j‖ := by
  have hwidth := (hasSampleWidth_iff hH).1 hwidth
  dsimp only
  rw [paperClockJump_sum_eq H Hd hH hw hwidth]
  exact clock_series_bound hT H Hd _ _ hH hder.1 hder.2 hw hwidth
    (evolution_spec (Nat.cast_pos.mpr hT) hH
      (UnitaryProducts.Prose.regulated_of_continuousOn hder.continuousOn))
    (roundedEvolution_spec hT hH)

/-- The operator-series endpoint bound: insert the affine jump bound in Theorem 4.4
into Theorem 4.2 (`thm:clocks`).
The derivative uses its compact-interval supremum, and the endpoint norms remain exact. -/
theorem endpoint_series_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
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
  have hreg := UnitaryProducts.Prose.regulated_of_continuousOn
    (HasLipschitzDerivative.continuousOn (show HasLipschitzDerivative H Hd L from ⟨hd, hlip⟩))
  have hclock := thm_clocks hT H Hd hH ⟨hd, hlip⟩ hw ((hasSampleWidth_iff hH).2 hwidth)
  rw [← roundedEvolution_eqOn hT hH hV (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩),
    ← evolution_eqOn (Nat.cast_pos.mpr hT) hH hreg hU
      (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩)] at hclock
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) (0 : Fin d)
  dsimp only at hclock
  rw [cellConstant_eq_frameBound hw0 hw, paperClockJump_sum_eq H Hd hH hw hwidth] at hclock
  have hsum := hamiltonian_jump_sum_integral hT H Hd hH hd hlip hw hwidth
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

/-- **Theorem 4.4** (`thm:jumps`), equation (4.6) (`eq:products`): the comparison with the
entrywise multiplier of Definition 4.1 and constants of Appendix B. -/
theorem thm_jumps [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hder : HasLipschitzDerivative H Hd L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤ hamiltonianEnergy w L H / T := by
  have hwidth := (hasSampleWidth_iff hH).1 hwidth
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt w L H Hd hder.1,
    div_eq_mul_one_div, mul_comm _ (1 / (T : ℝ))]
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (Nat.zero_le T) (0 : Fin d) 0
  rw [cellConstant_eq_frameBound hw0 hw, paperFrameMult_eq_series hw0 hw,
    paperFrameMult_deriv_eq_series hw0 hw]
  exact endpoint_series_bound hT H Hd _ _ hH hder.1 hder.2 hw hwidth
    (evolution_spec (Nat.cast_pos.mpr hT) hH
      (UnitaryProducts.Prose.regulated_of_continuousOn hder.continuousOn))
    (roundedEvolution_spec hT hH)

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
    (hH : IsTimeDepHamiltonian H)
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
  have hclock := thm_jumps hT1 H Hd hH
    ⟨fun s hs ↦ (hc s hs).hasDerivWithinAt, hlip⟩ hw ((hasSampleWidth_iff hH).2 hdiff)
  rw [← roundedEvolution_eqOn hT1 hH hV (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩),
    ← evolution_eqOn hT hH (UnitaryProducts.Prose.regulated_of_continuousOn hc.continuousOn) hU
      (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩)] at hclock
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

/-- The intermediate transfer chain in the proof of Example 4.5: commuting
endpoint phases, the product-error split, and both half-budget estimates. The
rounded evolution at the terminal time is written using its endpoint identity. -/
theorem ex_unit_transfer_chain [NeZero d] (w : ℝ)
   (hw : w < 2 * π)
   (H U : ℝ → 𝕄)
   (T k : ℕ)
   (hT1 : 0 < T)
    (hH : IsTimeDepHamiltonian H)
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

/-- **Example 4.5** (`ex:unit-transfer`): the bit budget with the closed
scalar constants in Appendix B. -/
theorem ex_unit_transfer_bounds [NeZero d] (w : ℝ) (hw : w < 2 * π)
    (H U : ℝ → 𝕄) (T k : ℕ) (hT1 : 0 < T) (hH : IsTimeDepHamiltonian H)
    (L : ℝ) (hder : HasLipschitzDerivative H (derivWithin H (Icc (0 : ℝ) 1)) L)
    (hdiff : HasSampleWidth H T w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1))
    (C : NNReal) (δ : ℝ) (hδ : 0 < δ)
    (hcont : ‖(1 - Q) * U T * P‖ ≤ (C : ℝ) / T) :
    let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
    2 * ((C : ℝ) + hamiltonianEnergy w L H) / δ ≤ T →
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
      ‖(1 - Q) * (unitProduct (fun s ↦ scalarEntryMap (truncBits k) (H s)) T).1 * P‖ ≤ δ := by
  have hc : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hder.1 s hs).differentiableWithinAt
  have hlip := hder.2
  have hdiff := (hasSampleWidth_iff hH).1 hdiff
  intro σ hbudget hbits
  have hchain := ex_unit_transfer_chain w hw H U T k hT1 hH hc L hlip hdiff hU
    P Q hP hQ hPc hQc C δ hδ hcont hbudget hbits
  exact (hchain.1.trans (hchain.2.1.trans
    (hchain.2.2.1.trans hchain.2.2.2.1))).trans_eq hchain.2.2.2.2

end UnitaryProducts.PaperProof
