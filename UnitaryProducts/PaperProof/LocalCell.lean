/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.ClosedCellConstruction
public import UnitaryProducts.Prose.ResidualAlgebra
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.PaperProof.CenteredDuhamel
public import UnitaryProducts.PaperProof.UniformDerivativeSeries
public import UnitaryProducts.Paper.UnitComparisonObjects
/-! # The canonical cell lemma in Appendix A -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, equation `eq:corrected-residual`: split the global residual
into the corrector equation, Taylor remainder, and generator-error product.
The identity is pointwise and imposes no differentiability assumptions. -/
theorem global_residual_split (K G L Y Yd : 𝕄) :
    K - G - Yd - I • (K * Y - Y * G) =
      (L - Yd - I • (G * Y - Y * G)) + (K - G - L) -
        I • ((K - G) * Y) := by
  rw [Prose.local_residual_at_sample]
  abel

/-- The Taylor remainder identity on an arbitrary interval containing the sample.
Restricting to the closed segment between `0` and `τ` includes endpoint half-cells. -/
theorem cell_taylor_remainder {J : Set ℝ} (hJ : J.OrdConnected) (h0 : 0 ∈ J)
    {K Kd : ℝ → 𝕄}
    (hd : ∀ s ∈ J, HasDerivWithinAt K (Kd s) J s)
    (hc : ContinuousOn Kd J) {τ : ℝ} (hτ : τ ∈ J) :
    K τ - K 0 - τ • Kd 0 = ∫ s in (0 : ℝ)..τ, Kd s - Kd 0 := by
  have hsub : uIcc (0 : ℝ) τ ⊆ J := hJ.uIcc_subset h0 hτ
  have hder (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) τ) := (hd s (hsub hs)).mono hsub
  simpa only [sub_zero] using taylor_remainder_eq_integral hder (hc.mono hsub)
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 τ) (right_mem_uIcc : τ ∈ uIcc 0 τ)

/-- The uncancelled residual decomposition precedes any choice of corrector:
the bracket, the Taylor remainder, and the changing-generator product. -/
theorem cell_residual_split {J : Set ℝ} (hJ : J.OrdConnected) (h0 : 0 ∈ J)
    {K Kd : ℝ → 𝕄} {Ω D Y Yd : 𝕄}
    (hd : ∀ s ∈ J, HasDerivWithinAt K (Kd s) J s)
    (hc : ContinuousOn Kd J) (hK : K 0 = Ω) (hKd : Kd 0 = D)
    {τ : ℝ} (hτ : τ ∈ J) :
    K τ - Ω - Yd - I • (K τ * Y - Y * Ω) =
      (τ • D - Yd - I • (Ω * Y - Y * Ω)) +
        (∫ s in (0 : ℝ)..τ, Kd s - D) - I • ((K τ - Ω) * Y) := by
  have hrem := cell_taylor_remainder hJ h0 hd hc hτ
  rw [hK, hKd] at hrem
  rw [global_residual_split, hrem]

/-- Section 4, equation `eq:corrected-residual`: first split the frozen
commutator, then cancel the scalar cell equation against the Taylor term.
This identity is independent of the norm bounds of Lemma A.1. -/
theorem cell_corrected_residual {J : Set ℝ} (hJ : J.OrdConnected) (h0 : 0 ∈ J)
    {K Kd Y : ℝ → 𝕄} {Ω D : 𝕄}
    (hd : ∀ s ∈ J, HasDerivWithinAt K (Kd s) J s)
    (hc : ContinuousOn Kd J) (hK : K 0 = Ω) (hKd : Kd 0 = D)
    {τ : ℝ} (hτ : τ ∈ J)
    (hY : HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ) :
    K τ - Ω - deriv Y τ - I • (K τ * Y τ - Y τ * Ω) =
      (∫ s in (0 : ℝ)..τ, Kd s - D) - I • ((K τ - Ω) * Y τ) := by
  rw [cell_residual_split hJ h0 hd hc hK hKd hτ, hY.deriv]
  simp only [sub_sub_cancel, sub_self, zero_add]


/-- The operator-series construction gives a continuously differentiable local corrector,
its equation, equal end values, center bound, and growth from its actual center. The residual
identity is stated separately in Section 4.
`frameOp Ω D` is the single multiplier defined in Section 4.1;
`frameOp_eq_paper_value` identifies it with its eigenbasis entries.
The center constant uses the cosecant formula of Theorem 4.2, including its
continuous value at zero; its positive Taylor series supplies the norm bound. -/
theorem cell_series_solution {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    let Φ := frameOp Ω D
    let c₀ := cellConstant w
    ∃ Y : ℝ → 𝕄,
      ContDiffOn ℝ 1 Y (Icc (-1 / 2 : ℝ) (1 / 2)) ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ) ∧
      Y (-1 / 2) = Φ ∧ Y (1 / 2) = Φ ∧
      ‖Y 0‖ ≤ c₀ * ‖D‖ ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2) := by
  intro Φ c₀
  let Y := closedCell Ω hΩ D
  have heq : Y = integralCell Ω D := funext (closedCell_eq_integralCell hw hΩ hwidth D)
  have hY : ∀ τ, HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ := by
    rw [heq]
    exact integralCell_hasDerivAt Ω D
  have hC1 : ContDiff ℝ 1 Y := heq ▸ (integralCell_spec hw hΩ hwidth D).1
  refine ⟨Y, hC1.contDiffOn, fun τ _ ↦ hY τ,
    (closedCell_endpoints hw hΩ hwidth D).1,
    (closedCell_endpoints hw hΩ hwidth D).2, ?_⟩
  constructor
  · have hc := cell_center_multiplier_bound hw₀ hw hΩ hwidth D
    change ‖closedCell Ω hΩ D 0‖ ≤ cellConstant w * ‖D‖
    rw [hc.1, ← hc.2.2]
    exact hc.2.1
  · intro τ _
    rw [heq]
    exact integralCell_norm hΩ D τ

/-- **Lemma A.1** (`lem:cell`): the corrector has the end value of Definition 4.1
and the closed cosecant center bound, including its value at width zero. The chosen extension is
differentiable also at the two cell endpoints. -/
theorem lem_cell {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwidth : HasSpectralWidth Ω w) (D : 𝕄) :
    let Φ := paperFrameOp Ω D
    let c₀ := cellConstant w
    ∃ Y : ℝ → 𝕄,
      ContDiffOn ℝ 1 Y (Icc (-1 / 2 : ℝ) (1 / 2)) ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ) ∧
      Y (-1 / 2) = Φ ∧ Y (1 / 2) = Φ ∧
      ‖Y 0‖ ≤ c₀ * ‖D‖ ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2) := by
  have hwidth := (hasSpectralWidth_iff hΩ).1 hwidth
  rw [paperFrameOp_eq_series hΩ hw hwidth D]
  exact cell_series_solution hw₀ hw hΩ hwidth D

/-- The derivative-series estimate: the self-input multiplier is continuously
 differentiable and satisfies both estimates, including the one-sided endpoints.
 The first estimate specializes the general derivative-series inequality, and
 the second uses the centered Duhamel decomposition and Jacobi telescope. -/
theorem self_frame_series_curve {Ω : ℝ → 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 2 Ω (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (derivWithin Ω (Icc (0 : ℝ) 1) s))
      (Icc (0 : ℝ) 1) ∧
    ∀ s ∈ Icc (0 : ℝ) 1,
      (‖derivWithin (fun t ↦ frameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameBound w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * frameLip w * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) ∧
      (‖derivWithin (fun t ↦ frameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameBound w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * frameLip w * ‖derivWithin (fun t ↦ evol (Ω t) 1) (Icc (0 : ℝ) 1) s‖ *
            ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ +
          (frameBound w - frameBound 0) * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdim
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    refine ⟨contDiffOn_of_subsingleton, ?_⟩
    intro s _
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, le_refl, and_self]
  · letI : NeZero d := ⟨hdim.ne'⟩
    -- The uniformly convergent derivative series supplies continuous differentiability.
    refine ⟨self_frame_series_contDiffOn hw hΩ hwidth hcΩ, ?_⟩
    intro s hs
    let K := Icc (0 : ℝ) 1
    let D := derivWithin Ω K s
    let Dd := derivWithin (derivWithin Ω K) K s
    have hcD : ContDiffOn ℝ 1 (derivWithin Ω K) K :=
      hcΩ.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
    have hdΩ := (hcΩ.differentiableOn (by norm_num) s hs).hasDerivWithinAt
    have hdD := (hcD.differentiableOn (by norm_num) s hs).hasDerivWithinAt
    have ha : ‖I • adL (Ω s)‖ < 2 * π := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact (show ‖adL (Ω s)‖ ≤ w by
        simpa only [pow_one] using ad_power_norm_le (hΩ s hs) (hwidth s hs) 1).trans_lt hw
    have hder := (hasDerivWithinAt_frameOp hdΩ hdD ha).derivWithin
      (uniqueDiffOn_Icc_zero_one s hs)
    have hinput : ‖frameOp (Ω s) Dd‖ ≤ frameBound w * ‖Dd‖ :=
      general_series_bound frame_nonnegativeSeries (hΩ s hs) hw0 hw (hwidth s hs) Dd
    have hbase := (norm_add_le (unifiedFrameError (Ω s) D D) (frameOp (Ω s) Dd))
    -- Case (i) specializes the general derivative bound to the input Ω'.
    have hfirst := frame_series_derivative_bound hdΩ hdD
      (uniqueDiffOn_Icc_zero_one s hs) (hΩ s hs) hw0 hw (hwidth s hs)
    -- Case (ii) uses the same split with the centered integral decomposition.
    have hsplit := norm_unifiedFrameError_split_le (hΩ s hs) hw0 hw (hwidth s hs)
      D (centeredDuhamel (Ω s) D) (centeredRemainder (Ω s) D)
      (centeredDuhamel_add_commutator (Ω s) D)
    have hsecond : ‖unifiedFrameError (Ω s) D D‖ ≤
        2 * frameLip w * ‖evolDeriv (Ω s) D‖ * ‖D‖ +
          (frameBound w - frameBound 0) * ‖D‖ ^ 2 := by
      have htail := frameBound_sub_zero_nonneg hw0 hw
      have hB := norm_centeredRemainder_le (hΩ s hs) D
      rw [norm_centeredDuhamel (hΩ s hs)] at hsplit
      refine hsplit.trans ?_
      calc
        _ ≤ 2 * frameLip w * ‖evolDeriv (Ω s) D‖ * ‖D‖ +
            4 * (frameBound w - frameBound 0) * (‖D‖ / 4) * ‖D‖ := by gcongr
        _ = _ := by ring
    have hExp := ((hasFDerivAt_evol_one (hΩ s hs)).restrictScalars ℝ).comp_hasDerivWithinAt s hdΩ
    have hX := hExp.derivWithin (uniqueDiffOn_Icc_zero_one s hs)
    change derivWithin (fun t ↦ evol (Ω t) 1) K s = evolDeriv (Ω s) D at hX
    constructor
    · simpa only [D, Dd, K, pow_two, mul_assoc] using hfirst
    · rw [hder, hX]
      exact hbase.trans ((add_le_add hsecond hinput).trans_eq (by dsimp [D, Dd, K]; ring))

/-- **Lemma A.3** (`lem:end-value`): both derivative estimates for the
entrywise multiplier of Definition 4.1, with its closed scalar constants. -/
theorem canonical_cell_curve {Ω : ℝ → 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : HasWidth Ω w)
    (hcΩ : ContDiffOn ℝ 2 Ω (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun s ↦ paperFrameOp (Ω s) (derivWithin Ω (Icc (0 : ℝ) 1) s))
      (Icc (0 : ℝ) 1) ∧
    ∀ s ∈ Icc (0 : ℝ) 1,
      (‖derivWithin (fun t ↦ paperFrameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameMult w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * deriv frameMult w * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) ∧
      (‖derivWithin (fun t ↦ paperFrameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameMult w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * deriv frameMult w * ‖derivWithin (fun t ↦ evol (Ω t) 1) (Icc (0 : ℝ) 1) s‖ *
            ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ +
          (frameMult w - frameMult 0) * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) := by
  have hwidth := (hasWidth_iff hΩ).1 hwidth
  let K := Icc (0 : ℝ) 1
  have heq : EqOn (fun s ↦ paperFrameOp (Ω s) (derivWithin Ω K s))
      (fun s ↦ frameOp (Ω s) (derivWithin Ω K s)) K := by
    intro s hs
    exact paperFrameOp_eq_series (hΩ s hs) hw (hwidth s hs) _
  have hseries := self_frame_series_curve hw0 hw hΩ hwidth hcΩ
  have hder (s : ℝ) (hs : s ∈ K) := derivWithin_congr heq (heq hs)
  refine ⟨hseries.1.congr heq, ?_⟩
  intro s hs
  rw [hder s hs, paperFrameMult_eq_series hw0 hw,
    paperFrameMult_deriv_eq_series hw0 hw,
    paperFrameMult_eq_series (le_refl 0) (by positivity)]
  exact hseries.2 s hs

/-- Lemma A.3 expressed through its convergent series for integration along a mesh. -/
theorem canonical_cell_series_bounds {Ω : ℝ → 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 2 Ω (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (derivWithin Ω (Icc (0 : ℝ) 1) s))
      (Icc (0 : ℝ) 1) ∧
    ∀ s ∈ Icc (0 : ℝ) 1,
      (‖derivWithin (fun t ↦ frameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameBound w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * frameLip w * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) ∧
      (‖derivWithin (fun t ↦ frameOp (Ω t) (derivWithin Ω (Icc (0 : ℝ) 1) t))
        (Icc (0 : ℝ) 1) s‖ ≤
        frameBound w * ‖derivWithin (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) s‖ +
          2 * frameLip w * ‖derivWithin (fun t ↦ evol (Ω t) 1) (Icc (0 : ℝ) 1) s‖ *
            ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ +
          (frameBound w - frameBound 0) * ‖derivWithin Ω (Icc (0 : ℝ) 1) s‖ ^ 2) := by
  let K := Icc (0 : ℝ) 1
  have heq : EqOn (fun s ↦ paperFrameOp (Ω s) (derivWithin Ω K s))
      (fun s ↦ frameOp (Ω s) (derivWithin Ω K s)) K := by
    intro s hs
    exact paperFrameOp_eq_series (hΩ s hs) hw (hwidth s hs) _
  have hpaper := canonical_cell_curve hw0 hw hΩ ((hasWidth_iff hΩ).2 hwidth) hcΩ
  refine ⟨hpaper.1.congr heq.symm, ?_⟩
  intro s hs
  have hb := hpaper.2 s hs
  rw [derivWithin_congr heq (heq hs), paperFrameMult_eq_series hw0 hw,
    paperFrameMult_deriv_eq_series hw0 hw,
    paperFrameMult_eq_series (le_refl 0) (by positivity)] at hb
  exact hb

/-- Solutions of the local corrector equation with the prescribed left value
agree with the canonical corrector on the closed cell, by ODE uniqueness. -/
theorem cell_solution_eq_canonical {Ω D : 𝕄} (hΩ : Ω.IsHermitian)
    {Y : ℝ → 𝕄} (hc : ContinuousOn Y (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hd : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω)) τ)
    (hi : Y (-1 / 2) = (exponentialOperators Ω hΩ D).2.2.1) :
    EqOn Y (periodicCorrectorData Ω hΩ D).2.2 (Icc (-1 / 2 : ℝ) (1 / 2)) := by
  let Z := (periodicCorrectorData Ω hΩ D).2.2
  let L : 𝕄 →L[ℂ] 𝕄 := I • adL Ω
  have hZ := hasDerivAt_periodic_corrector Ω hΩ D
  have hinit : Y (-1 / 2) = Z (-1 / 2) := by
    simpa [Z, periodicCorrectorData, exponentialOperators, neg_div,
      frameExtension_zero] using hi
  refine ODE_solution_unique_of_mem_Icc_right
    (v := fun τ X ↦ τ • D - L X) (s := fun _ ↦ univ) (K := ‖L‖₊)
    (fun τ _ ↦ ?_) hc (fun τ hτ ↦ (hd τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (fun _ _ ↦ mem_univ _) (fun τ _ ↦ (hZ τ).continuousAt.continuousWithinAt)
    (fun τ _ ↦ (hZ τ).hasDerivWithinAt) (fun _ _ ↦ mem_univ _) hinit
  simpa only [zero_add] using
    ((LipschitzWith.const (τ • D)).sub L.lipschitz).lipschitzOnWith

/-- Clause (i) of Lemma A.1 supplies the actual canonical end values. -/
theorem canonical_cell_endpoints {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π)
    {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    (periodicCorrectorData Ω hΩ D).2.2 (-1 / 2) = (exponentialOperators Ω hΩ D).2.2.1 ∧
    (periodicCorrectorData Ω hΩ D).2.2 (1 / 2) = (exponentialOperators Ω hΩ D).2.2.1 := by
  obtain ⟨Y, hc, hd, hl, hr, _⟩ :=
    lem_cell hw₀ hw hΩ ((hasSpectralWidth_iff hΩ).2 hwidth) D
  rw [paperFrameOp_eq_series hΩ hw hwidth D] at hl hr
  rw [frameOp_eq_paper_value hΩ hw hwidth D] at hl
  have he := cell_solution_eq_canonical hΩ hc.continuousOn hd hl
  exact ⟨(he (by constructor <;> norm_num)).symm.trans hl,
    (he (by constructor <;> norm_num)).symm.trans
      (hr.trans (frameOp_eq_paper_value hΩ hw hwidth D))⟩

/-- Clause (ii) of Lemma A.1 fixes the canonical center bound; conjugated
integration extends its quadratic profile to all real local times. -/
theorem canonical_cell_norm {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π)
    {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) (τ : ℝ) :
    ‖(periodicCorrectorData Ω hΩ D).2.2 τ‖ ≤
      (frameBound w - frameBound (w / 2) / 2 + τ ^ 2 / 2) * ‖D‖ := by
  obtain ⟨Y, hc, hd, hl, _, hcenter, hgrowth⟩ :=
    lem_cell hw₀ hw hΩ ((hasSpectralWidth_iff hΩ).2 hwidth) D
  rw [paperFrameOp_eq_series hΩ hw hwidth D] at hl
  rw [frameOp_eq_paper_value hΩ hw hwidth D] at hl
  have he := cell_solution_eq_canonical hΩ hc.continuousOn hd hl
  have h0 : (0 : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by constructor <;> norm_num
  by_cases hτ : τ ∈ Icc (-1 / 2 : ℝ) (1 / 2)
  · rw [cellConstant_eq_frameBound hw₀ hw] at hcenter
    have hsize := (hgrowth τ hτ).trans (add_le_add hcenter le_rfl)
    rw [he hτ] at hsize
    exact hsize.trans_eq (by ring)
  rw [cellConstant_eq_frameBound hw₀ hw] at hcenter
  rw [he h0] at hcenter
  have hc' : ‖frameExtension Ω D (periodicCorrectorData Ω hΩ D).2.1 (1 / 2)‖ ≤
      (frameBound w - frameBound (w / 2) / 2) * ‖D‖ := by
    simpa only [periodicCorrectorData, exponentialOperators, zero_add] using hcenter
  exact norm_frameExtension_le_center_profile hΩ le_rfl hc' τ

/-- The Section 4 residual identity for the canonical corrector, including
both endpoint half-cells. It follows directly from its cell equation. -/
theorem canonical_cell_residual {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄)
    (J : Set ℝ) (hJ : J.OrdConnected) (h0 : 0 ∈ J)
    (K Kd : ℝ → 𝕄)
    (hd : ∀ s ∈ J, HasDerivWithinAt K (Kd s) J s) (hc : ContinuousOn Kd J)
    (hK0 : K 0 = Ω) (hKd0 : Kd 0 = D) {τ : ℝ} (hτ : τ ∈ J) :
    let Y := (periodicCorrectorData Ω hΩ D).2.2
    K τ - Ω - deriv Y τ - I • (K τ * Y τ - Y τ * Ω) =
      (∫ s in (0 : ℝ)..τ, Kd s - D) - I • ((K τ - Ω) * Y τ) := by
  exact cell_corrected_residual hJ h0 hd hc hK0 hKd0 hτ
    (hasDerivAt_periodic_corrector Ω hΩ D τ)


end UnitaryProducts.PaperProof
