/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.UniformConsequences

/-! # Transfer through eigenvalue crossings -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
open Set Real Filter
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 5: Proposition 2.4 removes the endpoint half-step phases when the
orthogonal endpoint projectors commute with the Hamiltonian. -/
theorem commuting_endpoint_transfer (H : ℝ → 𝕄) (T : ℕ) (U P Q : 𝕄)
    (hH0 : (H 0).IsHermitian) (hH1 : (H 1).IsHermitian)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1)) :
    |‖(1 - Q) * (unitProduct H T).1 * P‖ - ‖(1 - Q) * U * P‖| ≤
      ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U‖ := by
  have htransfer := prop_transfer (U := U) (W := (unitProduct H T).1)
    hP hQ hP hQ (evol_mem_unitary hH1 (1 / 2))
    (evol_mem_unitary hH0 (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simpa only [sub_self, norm_zero, add_zero, mul_zero] using htransfer

/-- The crossing proof: the endpoint transfer and the explicit `1/T`
comparison from (4.6), with a coefficient independent of the step count. -/
theorem crossing_comparison_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U P : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L w : ℝ} (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ L * |t - s|) (hw : w < 2 * π)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, IsStarProjection (P s))
    (hPc : ∀ s ∈ Icc (0 : ℝ) 1, Commute (P s) (H s)) :
    let V := evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2))
    let c₀ := cellConstant w
    let c₁ := c₀ / 4 + 1 / 64
    ‖(1 - P 1) * (unitProduct H T).1 * P 0‖ ≤
      ‖(1 - P 1) * U T * P 0‖ + ‖V - U T‖ ∧
    ‖V - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) +
      (1 / 24 + frameMult w) * L + (c₁ + 2 * deriv frameMult w) * unitSupNorm Hd ^ 2) := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have htransfer := commuting_endpoint_transfer H T (U T) (P 0) (P 1)
    (hH 0 hzero) (hH 1 hone) (hP 0 hzero) (hP 1 hone) (hPc 0 hzero) (hPc 1 hone)
  have hdifference := (le_abs_self _).trans htransfer
  have hleak : ‖(1 - P 1) * (unitProduct H T).1 * P 0‖ ≤
      ‖(1 - P 1) * U T * P 0‖ +
        ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ := by
    linarith only [hdifference]
  refine ⟨hleak, ?_⟩
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
  have hbound := thm_jumps hT H Hd hH ⟨hd, hlip⟩ hw ((hasSampleWidth_iff hH).2 hwidth)
  have hreg := UnitaryProducts.Prose.regulated_of_continuousOn
    (HasLipschitzDerivative.continuousOn (show HasLipschitzDerivative H Hd L from ⟨hd, hlip⟩))
  rw [← roundedEvolution_eqOn hT hH hV (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩),
    ← evolution_eqOn ht hH hreg hU
      (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩)] at hbound
  rw [hamiltonianEnergy_eq_of_hasDerivWithinAt w L H Hd hd,
    div_eq_mul_one_div, mul_comm _ (1 / (T : ℝ))] at hbound
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simpa only [heV, div_self ht.ne', one_smul, hhalf] using hbound

/-- The final implication in Section 5: a continuous leakage tending to zero
transfers through an operator comparison tending to zero. The cited
Avron--Elgart theorem supplies the continuous limit, not a new project axiom. -/
theorem crossing_leakage_tendsto_zero {a b e : ℕ → ℝ}
    (ha : ∀ T, 0 ≤ a T) (hbound : ∀ᶠ T in atTop, a T ≤ b T + e T)
    (hb : Tendsto b atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  have hsum : Tendsto (fun T ↦ b T + e T) atTop (𝓝 0) := by
    simpa only [zero_add] using hb.add he
  exact squeeze_zero' (Eventually.of_forall ha) hbound hsum

/-- Removing one point from the unit interval leaves a set dense in that
interval; this is the continuity step at a possibly exceptional endpoint. -/
theorem crossing_interval_dense (s₀ : ℝ) :
    Icc (0 : ℝ) 1 ⊆ closure (Icc (0 : ℝ) 1 \ {s₀}) := by
  have hinner : Ioo (0 : ℝ) 1 ⊆ closure (Icc (0 : ℝ) 1 \ {s₀}) := by
    apply ((dense_compl_singleton s₀).open_subset_closure_inter isOpen_Ioo).trans
    apply closure_mono
    intro s hs
    exact ⟨⟨hs.1.1.le, hs.1.2.le⟩, hs.2⟩
  have hclosed := closure_minimal hinner isClosed_closure
  simpa only [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using hclosed

/-- A continuous family that is a spectral projector away from one crossing
is an orthogonal projector commuting with the Hamiltonian at the crossing too.
In particular this justifies both endpoint commutations in Example 5.3. -/
theorem crossing_projectors_extend (H P : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hcH : ContinuousOn H (Icc (0 : ℝ) 1))
    (hcP : ContinuousOn P (Icc (0 : ℝ) 1)) (s₀ : ℝ)
    (hP : ∀ s, ∀ hs : s ∈ Icc (0 : ℝ) 1, s ≠ s₀ →
      ∃ μ : ℝ, P s = specProj (hH s hs) {μ}) :
    ∀ s ∈ Icc (0 : ℝ) 1, IsStarProjection (P s) ∧ Commute (P s) (H s) := by
  have hoff : ∀ s ∈ Icc (0 : ℝ) 1 \ {s₀},
      IsStarProjection (P s) ∧ Commute (P s) (H s) := by
    intro s hs
    obtain ⟨μ, heq⟩ := hP s hs.1 (by simpa using hs.2)
    rw [heq]
    exact ⟨isStarProjection_specProj (hH s hs.1) {μ},
      commute_specProj (hH s hs.1) {μ}⟩
  have hsub : Icc (0 : ℝ) 1 \ {s₀} ⊆ Icc (0 : ℝ) 1 := diff_subset
  have hid : EqOn (fun s ↦ P s * P s) P (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isIdempotentElem.eq)
      (hcP.mul hcP) hcP hsub (crossing_interval_dense s₀)
  have hstar : EqOn (fun s ↦ star (P s)) P (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).1.isSelfAdjoint.star_eq)
      hcP.star hcP hsub (crossing_interval_dense s₀)
  have hcomm : EqOn (fun s ↦ P s * H s) (fun s ↦ H s * P s)
      (Icc (0 : ℝ) 1) :=
    Set.EqOn.of_subset_closure (fun s hs ↦ (hoff s hs).2.eq)
      (hcP.mul hcH) (hcH.mul hcP) hsub (crossing_interval_dense s₀)
  intro s hs
  exact ⟨⟨hid hs, hstar hs⟩, hcomm hs⟩

/-- **Example 5.3** (`ex:crossings`): a continuous spectral projector through
one crossing transfers the assumed continuous leakage limit to the discrete
product. The proof derives endpoint commutation by continuity, applies
Proposition 2.4 with endpoint half-step phases, then (4.6) with one coefficient
independent of `T`. -/
theorem ex_crossings [NeZero d] (H Hd P : ℝ → 𝕄) (U : ℕ → ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hder : HasLipschitzDerivative H Hd L) (hw : w < 2 * π)
    (hwidth : ∀ T : ℕ, 0 < T → HasSampleWidth H T w)
    (hU : ∀ T : ℕ, 0 < T → IsEvolution (fun t ↦ H (t / T)) (U T) 0 T)
    (hcP : ContinuousOn P (Icc (0 : ℝ) 1)) (s₀ : ℝ)
    (hP : ∀ s, ∀ hs : s ∈ Icc (0 : ℝ) 1, s ≠ s₀ →
      ∃ μ : ℝ, P s = specProj (hH s hs) {μ})
    (hcontinuous : Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * U T T * P 0‖)
      atTop (𝓝 0)) :
    Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * (unitProduct H T).1 * P 0‖)
      atTop (𝓝 0) := by
  obtain ⟨hd, hlip⟩ := hder
  have hwidth := fun T hT ↦ (hasSampleWidth_iff hH).1 (hwidth T hT)
  have hcH : ContinuousOn H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).continuousWithinAt
  have hprojectors := crossing_projectors_extend H P hH hcH hcP s₀ hP
  let C := cellConstant w * (‖Hd 0‖ + ‖Hd 1‖) +
    (1 / 24 + frameMult w) * L +
    (cellConstant w / 4 + 1 / 64 + 2 * deriv frameMult w) * unitSupNorm Hd ^ 2
  have hcomparison : ∀ᶠ T : ℕ in atTop,
      ‖(1 - P 1) * (unitProduct H T).1 * P 0‖ ≤
        ‖(1 - P 1) * U T T * P 0‖ + (1 / T : ℝ) * C := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with T hT
    have hbound := crossing_comparison_bound hT H Hd (U T) P hH hd hlip hw
      (hwidth T hT) (hU T hT)
      (fun s hs ↦ (hprojectors s hs).1) (fun s hs ↦ (hprojectors s hs).2)
    have hleak := hbound.1
    have herror := hbound.2
    change _ ≤ (1 / T : ℝ) * C at herror
    linarith only [hleak, herror]
  have hvanishing : Tendsto (fun T : ℕ ↦ (1 / T : ℝ) * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).mul_const C
  exact crossing_leakage_tendsto_zero (fun _ ↦ norm_nonneg _)
    hcomparison hcontinuous hvanishing

/-- Section 5's opening to the crossing example: two diagonal eigenvalues cross
while their rank-one coordinate projectors extend continuously through the crossing. -/
theorem diagonal_crossing_witness :
    let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun s ↦ (s - 1 / 2) • Matrix.diagonal ![1, -1]
    Continuous H ∧ Continuous (fun _ : ℝ ↦ P) ∧ IsStarProjection P ∧
      (∀ s, (H s).IsHermitian ∧ Commute (H s) P ∧
        H s * P = (s - 1 / 2) • P ∧
        H s * (1 - P) = -(s - 1 / 2) • (1 - P)) ∧ H (1 / 2) = 0 := by
  intro P H
  have hdiag : (Matrix.diagonal ![(1 : ℂ), -1]).IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    change star ![(1 : ℂ), -1] = ![1, -1]
    ext i
    fin_cases i <;> simp
  have hP : IsStarProjection P := by
    constructor
    · change P * P = P
      simp [P, Matrix.diagonal_mul_diagonal]
    · change star P = P
      simp [P, Matrix.star_eq_conjTranspose]
  refine ⟨(continuous_id.sub continuous_const).smul continuous_const,
    continuous_const, hP, ?_, ?_⟩
  · intro s
    refine ⟨UnitaryProducts.Separation.isHermitian_real_smul hdiag _, ?_, ?_, ?_⟩
    all_goals ext i j; fin_cases i <;> fin_cases j <;>
      simp [H, P, Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  · simp [H]


end UnitaryProducts.PaperProof
