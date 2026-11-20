/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

/-!
# Section 4: unit steps

The rounded-clock comparison (Theorems 4.2 and 4.4), its examples (Examples 4.3 and 4.5), and
products of given unitaries (Theorems 4.6 and 4.7).
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

/-- **Theorem 4.2.** Let `T ≥ 1` be an integer and `H` a time-dependent Hamiltonian whose derivative
`H'` exists on `[0,1]` (one-sided at the ends) with `‖H'(s₁) - H'(s₂)‖ ≤ L |s₁ - s₂|`, and whose
samples `H(j/T)`, `0 ≤ j ≤ T`, have eigenvalue differences of modulus at most a width `w < 2π`.
Then the evolutions `U` of `H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy
`‖V(T) - U(T)‖ ≤ (c₀ (‖H'(0)‖ + ‖H'(1)‖) + L/24 + c₁ ‖H'‖∞²)/T + Σ_{j=1}^T ‖Δ_j‖`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem rounded_clock_comparison [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
  have h := UnitaryProducts.PaperProof.thm_clocks (T := T) (by omega) H (∂H) hH
    (Bridge.HasLipschitzDerivative.paper hL) hw hwidth
  dsimp only at h
  rw [Bridge.roundedEvolution_eq, Bridge.evolution_eq]
  simp only [Bridge.Δ_eq]
  calc _ ≤ _ := h
    _ = _ := by rw [one_div_mul_eq_div]; rfl

/-- The derivative bound of the proofs, taken at the derivative `∂H`, is the paper's. -/
private theorem hasLipschitzDerivative_of_paper {n : ℕ} {H : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {L : ℝ} (h : UnitaryProducts.Paper.HasLipschitzDerivative H (∂H) L) :
    HasLipschitzDerivative H L :=
  ⟨fun s hs ↦ (h.1 s hs).differentiableWithinAt, fun s₁ hs₁ s₂ hs₂ ↦ h.2 s₂ hs₂ s₁ hs₁⟩

/-- **Example 4.3.** For an integer `T ≥ 2`, `H(s) = s² Z` with `Z = diag(1,-1)` satisfies the
hypotheses of Theorem 4.2 with `L = 2` and `w = 2`, and its evolutions `U` and `V` satisfy
(i) `‖V(T) - U(T)‖ = 2 sin(1/(12T))`, asymptotic to `1/(6T)`, and
(ii) `‖W_T - U(T)‖ = 2 sin(1/4 - 1/(12T))`, with limit `2 sin(1/4)`. -/
theorem unit_sharp (T : ℕ) (hT : 2 ≤ T) :
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s ↦ (s ^ 2 : ℝ) • Matrix.diagonal ![1, -1]
    IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H 2 ∧ HasSampleWidth H T 2 ∧
      ‖roundedEvolution H T T - evolution H T T‖ = 2 * Real.sin (1 / (12 * T)) ∧
      (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * N))) ~[atTop] (fun N : ℕ ↦ 1 / (6 * N)) ∧
      ‖stepProduct H T - evolution H T T‖ = 2 * Real.sin (1 / 4 - 1 / (12 * T)) ∧
      Tendsto (fun N : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * N))) atTop
        (𝓝 (2 * Real.sin (1 / 4))) := by
  intro H
  have h := UnitaryProducts.PaperProof.ex_unit_sharp T hT
  dsimp only at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨h₁, hasLipschitzDerivative_of_paper h₂, h₃, ?_, h₆, ?_, h₇⟩
  · rw [Bridge.roundedEvolution_eq]
    exact h₄
  · rw [Bridge.stepProduct_eq]
    exact h₅

/-- **Theorem 4.4**, equation (4.6). Under the hypotheses of Theorem 4.2, the evolutions `U` of
`H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy `‖V(T) - U(T)‖ ≤ ℰ_w(H)/T`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem rounded_clock_bound [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤ ℰ w L H / T := by
  rw [Bridge.roundedEvolution_eq]
  exact UnitaryProducts.PaperProof.thm_jumps (T := T) (by omega) H (∂H) hH
    (Bridge.HasLipschitzDerivative.paper hL) hw hwidth

/-- **Example 4.5.** Under the hypotheses of Theorem 4.2, let `P` and `Q` be orthogonal projectors
commuting with `H(0)` and `H(1)`, and let `C ≥ 0` and `δ > 0`. If `‖(1 - Q) U(T) P‖ ≤ C/T`,
`T ≥ 2(C + ℰ_w(H))/δ`, and `√2 σ_k 2^{-k} ≤ δ/(2T)`, then the `T`-step product `W^{(k)}_T` of the
truncation `H^{(k)}` satisfies `‖(1 - Q) W^{(k)}_T P‖ ≤ δ`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem unit_transfer [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) {P Q : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hPH : Commute P (H 0)) (hQH : Commute Q (H 1)) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T)
    (hTδ : 2 * (C + ℰ w L H) / δ ≤ T) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T)) :
    ‖(1 - Q) * stepProduct (fun s ↦ entrywise (bitTruncation k) (H s)) T * P‖ ≤ δ := by
  have hT₀ : 0 < T := hT
  have hr : UnitaryProducts.Paper.IsRegulated H 0 1 :=
    UnitaryProducts.Prose.regulated_of_continuousOn
      (Bridge.HasLipschitzDerivative.continuousOn hL)
  have h := UnitaryProducts.PaperProof.ex_unit_transfer_bounds w hw H (evolution H T) T k hT₀
    hH L (Bridge.HasLipschitzDerivative.paper hL) hwidth
    (UnitaryProducts.Paper.evolution_spec (Nat.cast_pos.mpr hT₀) hH hr) P Q hP hQ hPH hQH
    ⟨C, hC⟩ δ hδ hU
  simp only [Bridge.truncHerm_eq] at h
  rw [Bridge.stepProduct_eq, Bridge.bitTruncation_eq]
  exact h hTδ hk

/-- `e^{-iG}` in the paper's notation is `evol G 1` in the proofs. -/
private theorem evol_one (G : 𝕄) : UnitaryProducts.evol G 1 = exp (-I • G) := by
  rw [Bridge.evol_eq]
  simp

/-- **Theorem 4.6.** Let `T ≥ 1` be an integer and `H` a twice continuously differentiable
time-dependent Hamiltonian whose every value `H(s)` has eigenvalue differences of modulus at most a
width `w < 2π`, and let `W = e^{-iH}`. Then the evolution `U` of `H(t/T)` satisfies
`‖e^{-iH(1)/2} W((T-1)/T) ⋯ W(0) e^{iH(0)/2} - U(T)‖ ≤ ℰ̃_w(W)/T`.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem unitary_products [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {w : ℝ} (hw : w < 2 * π) (hC2 : ContDiffOn ℝ 2 H (Icc 0 1))
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasWidth (H s) w) :
    let W := fun s ↦ exp (-I • H s)
    ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      ℰtilde w W / T := by
  intro W
  have h := UnitaryProducts.PaperProof.thm_unitary_products T (by omega) H hH hw hC2 hwidth
  dsimp only at h
  obtain ⟨h₁, -, -, -, h₅⟩ := h
  have hW : (fun s ↦ UnitaryProducts.evol (H s) 1) = W := funext fun s ↦ evol_one (H s)
  have e₁ : UnitaryProducts.evol (H 1) (1 / 2) = exp (-(I / 2) • H 1) := by
    rw [Bridge.evol_eq]
    congr 2
    push_cast
    ring
  have e₀ : UnitaryProducts.evol (H 0) (-(1 / 2)) = exp ((I / 2) • H 0) := by
    rw [Bridge.evol_eq]
    congr 2
    push_cast
    ring
  rw [hW] at h₁ h₅
  rw [h₅, e₁, e₀, ← Bridge.sampleProduct_eq_walk] at h₁
  exact h₁

/-- The arc of the proofs is the arc `{e^{-iθ} : a < θ < b}`. -/
private theorem spectralWindowSet_true (a b : ℝ) :
    UnitaryProducts.Paper.spectralWindowSet true a b = arc a b := by
  ext z
  simp [UnitaryProducts.Paper.spectralWindowSet, arc]

/-- The spectral projector of an arc in the proofs is the paper's. -/
private theorem spectralWindowProjector_true (A : 𝕄) (a b : ℝ) :
    UnitaryProducts.Paper.spectralWindowProjector true A a b = spectralProjector A (arc a b) := by
  unfold UnitaryProducts.Paper.spectralWindowProjector spectralProjector
  simp only [spectralWindowSet_true]

/-- The distance along the circle is the least `|θ - φ + 2πk|`, attained at some `k`. -/
private theorem circleDistance_eq (θ φ : ℝ) :
    circleDistance θ φ = UnitaryProducts.Paper.angularDistance θ φ :=
  (UnitaryProducts.Paper.angularDistance_isLeast θ φ).csInf_eq

/-- The eigenphase gap of the paper is the circular gap of the proofs. -/
private theorem eigenphaseGap_eq (A : 𝕄) (a b : ℝ) :
    eigenphaseGap A a b = UnitaryProducts.Paper.spectralWindowGap true A a b := by
  rw [UnitaryProducts.Paper.spectralWindowGap, if_pos rfl, spectralWindowSet_true]
  simp only [eigenphaseGap, circleDistance_eq]

/-- An evolution on `[0,T]` depends only on its generator on `[0,T]`. -/
private theorem evolutionOf_congr {G G' : ℝ → 𝕄} {T : ℝ} (h : EqOn G G' (Icc 0 T)) :
    evolutionOf G T = evolutionOf G' T := by
  have hgen : (fun V ↦ Generates G V 0 T) = fun V ↦ Generates G' V 0 T := by
    funext V
    apply propext
    constructor <;> rintro ⟨h₁, h₂, h₃, S, hS, hd⟩ <;> refine ⟨h₁, h₂, h₃, S, hS, fun t ht htS ↦ ?_⟩
    · rw [← h ht]
      exact hd t ht htS
    · rw [h ht]
      exact hd t ht htS
  have key : ∀ p p' : (ℝ → 𝕄) → Prop, p = p' →
      (open Classical in if h : ∃ V, p V then h.choose else fun _ ↦ 1) =
        (open Classical in if h : ∃ V, p' V then h.choose else fun _ ↦ (1 : 𝕄)) := by
    rintro p _ rfl
    rfl
  exact key _ _ hgen

/-- **Theorem 4.7.** Let a twice continuously differentiable unitary family `W` have a band
`{e^{-iθ} : α(s) < θ < β(s)}` whose eigenphase gap is continuous in `s`, with endpoint projectors
`P` and `Q`, and let `ϑ` be the least eigenphase gap over `s ∈ [0,1]`. There is a Hermitian `H(s)`
with `e^{-iH(s)} = W(s)` and spectrum in `(α(s), α(s) + 2π)`, and for every such `H` and every
integer `T ≥ 1`, with `w = 2π - ϑ`, the evolution `U` of `H(t/T)` satisfies
`‖(1 - Q) W((T-1)/T) ⋯ W(0) P‖ ≤ ‖(1 - Q) U(T) P‖ + ℰ̃_w(W)/T`. -/
theorem walk_leakage {W : ℝ → 𝕄} {α β : ℝ → ℝ} (hband : IsArcBandFamily W α β)
    (hgap : ContinuousOn (fun s ↦ eigenphaseGap (W s) (α s) (β s)) (Icc 0 1))
    (hC2 : ContDiffOn ℝ 2 W (Icc 0 1)) :
    let ϑ := sInf ((fun s ↦ eigenphaseGap (W s) (α s) (β s)) '' Icc 0 1)
    let P := spectralProjector (W 0) (arc (α 0) (β 0))
    let Q := spectralProjector (W 1) (arc (α 1) (β 1))
    (∃ H, IsLogarithm W α H) ∧
      ∀ H, IsLogarithm W α H → ∀ T : ℕ, 1 ≤ T →
        ‖(1 - Q) * sampleProduct W T * P‖ ≤
          ‖(1 - Q) * evolution H T T * P‖ + ℰtilde (2 * π - ϑ) W / T := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨z, hz⟩ := (hband.2.2 0 ⟨le_rfl, zero_le_one⟩).2.2.2.1
    simp [spectrum.of_subsingleton] at hz
  haveI : NeZero d := ⟨hd.ne'⟩
  have hband' : UnitaryProducts.Paper.HasUnitaryBand W α β := by
    refine ⟨fun s hs ↦ (hband.2.2 s hs).1,
      fun s hs ↦ ⟨(hband.2.2 s hs).2.1, (hband.2.2 s hs).2.2.1⟩,
      ⟨hband.1, hband.2.1, fun s hs ↦ ?_⟩, ?_⟩
    · obtain ⟨h₁, -, -, h₄, h₅, h₆, h₇⟩ := hband.2.2 s hs
      refine ⟨h₁, ?_, ?_, h₆, h₇⟩ <;> rwa [spectralWindowSet_true]
    · simpa only [eigenphaseGap_eq] using hgap
  have hold := UnitaryProducts.PaperProof.cor_walk_leakage W α β hband' hC2
  dsimp only at hold ⊢
  simp only [eigenphaseGap_eq, ← spectralWindowProjector_true]
  obtain ⟨H₀, ⟨hH₀, hlog₀, hspec₀, huniq₀⟩, -, -, hbound⟩ := hold
  refine ⟨⟨H₀, hH₀, fun s hs ↦ (evol_one _).symm.trans (hlog₀ s hs), hspec₀⟩, ?_⟩
  rintro H ⟨hH, hlog, hspec⟩ T hT
  have hT₀ : (0 : ℝ) < T := by exact_mod_cast hT
  have hev : evolution H T = evolution H₀ T := by
    unfold evolution
    refine evolutionOf_congr fun t ht ↦ ?_
    have hs : t / T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hT₀.le, (div_le_one hT₀).mpr ht.2⟩
    exact huniq₀ _ hs _ (hH _ hs) (hspec _ hs) ((evol_one _).trans (hlog _ hs))
  rw [hev, Bridge.sampleProduct_eq_walk]
  exact hbound T hT

end RoundedClocks
