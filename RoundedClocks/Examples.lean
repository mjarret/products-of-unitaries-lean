/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

/-!
# Section 5: examples

Gap-adapted schedules (Example 5.1), a precessing spin (Example 5.2), and eigenvalue crossings
(Example 5.3).
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

/-- A real number is an eigenvalue of a Hermitian `A` exactly when it is a sorted eigenvalue. -/
private theorem ofReal_mem_spectrum_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (x : ℝ) :
    (x : ℂ) ∈ spectrum ℂ A ↔ ∃ j : Fin (Fintype.card (Fin n)), hA.eigenvalues₀ j = x := by
  rw [show (x : ℂ) = algebraMap ℝ ℂ x from rfl, spectrum.algebraMap_mem_iff,
    hA.spectrum_real_eq_range_eigenvalues]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(UnitaryProducts.sortIdx n).symm i, ?_⟩
    rw [← UnitaryProducts.eigenvalues_sortIdx hA, Equiv.apply_symm_apply]
  · rintro ⟨j, rfl⟩
    exact ⟨UnitaryProducts.sortIdx n j, UnitaryProducts.eigenvalues_sortIdx hA j⟩

/-- The spectral projector of a Hermitian `A` for `S` is the eigenbasis projector for the real
points of `S`. -/
private theorem spectralProjector_eq_specProj {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (S : Set ℂ) :
    spectralProjector A S = UnitaryProducts.specProj hA {x : ℝ | (x : ℂ) ∈ S} := by
  unfold spectralProjector UnitaryProducts.specProj
  congr 1
  exact UnitaryProducts.PaperProof.starProjection_eigenspaces_eq_proj hA.eigenvectorBasis
    hA.eigenvalues (fun x : ℝ ↦ (x : ℂ)) _ S (UnitaryProducts.isDiag_eigenvectorBasis hA)

/-- The spectral projector of a Hermitian `A` for one real eigenvalue `μ`. -/
private theorem spectralProjector_singleton {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (μ : ℝ) :
    spectralProjector A {(μ : ℂ)} = UnitaryProducts.specProj hA {μ} := by
  rw [spectralProjector_eq_specProj hA]
  congr 1
  ext x
  simp

/-- The least eigenvalue of a Hermitian `A` is the last sorted eigenvalue. -/
private theorem leastEigenvalue_eq {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hA : A.IsHermitian) : leastEigenvalue A = hA.eigenvalues₀ ⟨Fin.last d, by simp⟩ := by
  have hset : {x : ℝ | (x : ℂ) ∈ spectrum ℂ A} = Set.range hA.eigenvalues₀ := by
    ext x
    exact ofReal_mem_spectrum_iff hA x
  rw [leastEigenvalue, hset]
  apply le_antisymm
  · exact csInf_le (Set.finite_range _).bddBelow ⟨_, rfl⟩
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨j, rfl⟩
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_iff_val_le_val]
    have hj := j.isLt
    simp only [Fintype.card_fin] at hj
    simp only [Fin.val_last]
    omega

/-- A positive gap of the least eigenvalue is attained at a sorted eigenvalue and bounds every
larger eigenvalue's distance from the least one. -/
private theorem leastGap_of_pos {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hA : A.IsHermitian) (hpos : 0 < leastEigenvalueGap A) :
    let e : Fin (d + 1) → ℝ := fun k ↦ hA.eigenvalues₀ ⟨k, by simpa using k.isLt⟩
    (∃ k, 0 < e k - e (Fin.last d) ∧ leastEigenvalueGap A = e k - e (Fin.last d)) ∧
      ∀ k, e (Fin.last d) < e k → leastEigenvalueGap A ≤ e k - e (Fin.last d) := by
  intro e
  have hm : leastEigenvalue A = e (Fin.last d) := leastEigenvalue_eq hA
  have hmem : ∀ y : ℝ, (y : ℂ) ∈ spectrum ℂ A ↔ ∃ k : Fin (d + 1), e k = y := by
    intro y
    rw [ofReal_mem_spectrum_iff hA]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j, by simpa using j.isLt⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  let S := {r : ℝ | ∃ y : ℝ, (y : ℂ) ∈ spectrum ℂ A ∧ leastEigenvalue A < y ∧
    r = y - leastEigenvalue A}
  have hgap : leastEigenvalueGap A = sInf S := rfl
  have hSfin : S.Finite := by
    apply (Set.finite_range fun k : Fin (d + 1) ↦ e k - leastEigenvalue A).subset
    rintro _ ⟨y, hy, -, rfl⟩
    obtain ⟨k, rfl⟩ := (hmem y).1 hy
    exact ⟨k, rfl⟩
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hgap, h, Real.sInf_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨y, hy, hlt, hg⟩ := hne.csInf_mem hSfin
  obtain ⟨k, rfl⟩ := (hmem y).1 hy
  rw [hm] at hlt hg
  refine ⟨⟨k, sub_pos.mpr hlt, hgap.trans hg⟩, fun j hj ↦ ?_⟩
  rw [hgap]
  refine csInf_le hSfin.bddBelow ⟨e j, (hmem _).2 ⟨j, rfl⟩, ?_, ?_⟩
  · rwa [hm]
  · rw [hm]

/-- **Example 5.1.** Let `H₀` and `H₁` be Hermitian of norm at most `1`, let `Γ(x)` be the spectral
gap of the least eigenvalue of `(1-x)H₀ + xH₁`, with `Γ(x) ≥ Γ_* > 0` for `x ∈ [0,1]`, let `p > 1`
and `c_p = ∫_0^1 Γ(x)^{-p} dx`, let `u : [0,1] → [0,1]` solve `u' = c_p Γ(u)^p` with `u(0) = 0`,
and let `H = (1-u)H₀ + uH₁`. Then `u(1) = 1`, and `H` satisfies the hypotheses of Theorem 4.2 at
width `2` with `L = p 4^p c_p² ‖H₁ - H₀‖²`, `‖H'(0)‖ + ‖H'(1)‖ = c_p ‖H₁ - H₀‖ (Γ(0)^p + Γ(1)^p)`,
and `‖H'‖∞ ≤ 2^p c_p ‖H₁ - H₀‖`. So Example 4.5 applies to every bound `‖(1-Q) U(T) P‖ ≤ C/T`
for the spectral projectors `P` and `Q` of `H₀` and `H₁` for their least eigenvalues.
The dimension `d` is at least `1`, as throughout the paper. -/
theorem gap_adapted [NeZero d] {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {Γstar : ℝ} (hΓstar : 0 < Γstar)
    (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, Γstar ≤ leastEigenvalueGap ((1 - x) • H₀ + x • H₁))
    {p : ℝ} (hp : 1 < p) {u : ℝ → ℝ} (hu0 : u 0 = 0) (hu : MapsTo u (Icc 0 1) (Icc 0 1))
    (hu' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u
      ((∫ x in (0 : ℝ)..1, leastEigenvalueGap ((1 - x) • H₀ + x • H₁) ^ (-p)) *
        leastEigenvalueGap ((1 - u s) • H₀ + u s • H₁) ^ p) (Icc 0 1) s) :
    let Γ := fun x : ℝ ↦ leastEigenvalueGap ((1 - x) • H₀ + x • H₁)
    let cₚ := ∫ x in (0 : ℝ)..1, Γ x ^ (-p)
    let H := fun s ↦ (1 - u s) • H₀ + u s • H₁
    let L := p * 4 ^ p * cₚ ^ 2 * ‖H₁ - H₀‖ ^ 2
    let P := spectralProjector H₀ {(leastEigenvalue H₀ : ℂ)}
    let Q := spectralProjector H₁ {(leastEigenvalue H₁ : ℂ)}
    u 1 = 1 ∧ IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H L ∧
      (∀ s ∈ Icc (0 : ℝ) 1, HasWidth (H s) 2) ∧
      ‖∂H 0‖ + ‖∂H 1‖ = cₚ * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) ∧
      ‖∂H‖∞ ≤ 2 ^ p * cₚ * ‖H₁ - H₀‖ ∧
      IsOrthogonalProjector P ∧ IsOrthogonalProjector Q ∧ Commute P (H 0) ∧ Commute Q (H 1) ∧
      ∀ (T k : ℕ) (C δ : ℝ), 1 ≤ T → 0 ≤ C → 0 < δ →
        ‖(1 - Q) * evolution H T T * P‖ ≤ C / T → 2 * (C + ℰ 2 L H) / δ ≤ T →
        √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
        ‖(1 - Q) * stepProduct (fun s ↦ entrywise (bitTruncation k) (H s)) T * P‖ ≤ δ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 :=
    ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  intro Γ cₚ H L P Q
  have hΓ' : ∀ x ∈ Icc (0 : ℝ) 1,
      UnitaryProducts.PaperProof.IsLeastGap H₀ H₁ h₀ h₁ x (Γ x) := fun x hx ↦
    leastGap_of_pos (UnitaryProducts.PaperProof.gapInterp_hermitian h₀ h₁ x)
      (hΓstar.trans_le (hΓ x hx))
  obtain ⟨hu1, -, -, hHerm, -, hdiff, -, hderiv, hwid, -, hends, hsup, hlip, hP, hQ, hPc, hQc,
    hfin⟩ := UnitaryProducts.PaperProof.ex_gap_adapted H₀ H₁ h₀ h₁ hn₀ hn₁ Γ hΓ' Γstar hΓstar
      hΓ p hp u hu0 hu hu'
  have hder : ∀ s ∈ Icc (0 : ℝ) 1, ∂H s = (cₚ * Γ (u s) ^ p) • (H₁ - H₀) := hderiv
  have hPeq : P = UnitaryProducts.specProj h₀ {h₀.eigenvalues₀ ⟨Fin.last n, by simp⟩} := by
    simp only [P, leastEigenvalue_eq h₀, spectralProjector_singleton h₀]
  have hQeq : Q = UnitaryProducts.specProj h₁ {h₁.eigenvalues₀ ⟨Fin.last n, by simp⟩} := by
    simp only [Q, leastEigenvalue_eq h₁, spectralProjector_singleton h₁]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hsupeq : ‖∂H‖∞ = UnitaryProducts.Paper.unitSupNorm
      (fun s ↦ (cₚ * Γ (u s) ^ p) • (H₁ - H₀)) := by
    unfold supNorm UnitaryProducts.Paper.unitSupNorm
    congr 1
    exact Set.image_congr fun s hs ↦ by rw [hder s hs]
  rw [hPeq, hQeq]
  refine ⟨hu1, hHerm, ⟨hdiff, fun s₁ hs₁ s₂ hs₂ ↦ ?_⟩, fun s hs ↦
    (UnitaryProducts.Paper.hasSpectralWidth_iff
      (UnitaryProducts.PaperProof.gapInterp_hermitian h₀ h₁ (u s))).2 (hwid s hs), ?_,
    hsupeq ▸ hsup, hP, hQ, hPc, hQc, ?_⟩
  · rw [hder s₁ hs₁, hder s₂ hs₂]
    exact hlip s₂ hs₂ s₁ hs₁
  · rw [hder 0 h0, hder 1 h1]
    exact hends
  · intro T k C δ hT hC hδ hleak hTlarge hσ
    have hT0 : 0 < T := hT
    have hU := UnitaryProducts.Paper.evolution_spec (H := H) (T := T) (Nat.cast_pos.mpr hT0)
      hHerm (UnitaryProducts.Prose.regulated_of_continuousOn hdiff.continuousOn)
    have hbound := hfin (evolution H T) T k hT0 hU ⟨C, hC⟩ δ hδ hleak hTlarge
      (by simpa only [sparsity, Bridge.truncHerm_eq] using hσ)
    rw [Bridge.stepProduct_eq]
    have hent : ∀ {m : ℕ} (F : ℝ → ℝ) (A : Matrix (Fin m) (Fin m) ℂ),
        entrywise F A = UnitaryProducts.scalarEntryMap F A :=
      fun _ _ ↦ rfl
    simpa only [hent, Bridge.bitTruncation_eq] using hbound

/-- **Example 5.2.** Let `ω` and `θ` be real, and let `H(s) = (ω/2) e^{-iθsZ/2} X e^{iθsZ/2}` for
`s ∈ [0,1]`, with the Pauli matrices `X` and `Z`. Let `U` and `V` be the evolutions of `H(t/T)` and
`H(⌊t+1/2⌋/T)`. (i) If `ω = π`, then as `T → ∞` through odd integers, `T ‖V(T) - U(T)‖` tends to
`c₀ (‖H'(0)‖ + ‖H'(1)‖) (1 + θ²/(4(π-2)²))^{1/2}` with `c₀` at width `π`. (ii) If `ω = 2π`, then
`‖V(T) - U(T)‖` tends to `2 |sin(θ/4)|`. -/
theorem precessing_spin (ω θ : ℝ) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let H := fun s : ℝ ↦
      (ω / 2 : ℝ) • (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    (ω = π → Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) *
        ‖roundedEvolution H (2 * n + 1) (2 * n + 1) - evolution H (2 * n + 1) (2 * n + 1)‖)
      atTop (𝓝 (c₀ π * (‖∂H 0‖ + ‖∂H 1‖) * √(1 + θ ^ 2 / (4 * (π - 2) ^ 2))))) ∧
    (ω = 2 * π → Tendsto (fun T : ℕ ↦ ‖roundedEvolution H T T - evolution H T T‖) atTop
      (𝓝 (2 * |Real.sin (θ / 4)|))) := by
  intro X Z H
  have hH : H = fun s : ℝ ↦ (ω / 2 : ℝ) • (UnitaryProducts.evol UnitaryProducts.PaperProof.Spin.Z
      (θ * s / 2) * UnitaryProducts.PaperProof.Spin.X *
      UnitaryProducts.evol UnitaryProducts.PaperProof.Spin.Z (-(θ * s / 2))) := by
    funext s
    rw [Bridge.evol_eq, Bridge.evol_eq]
    have a₁ : (-(((θ * s / 2 : ℝ) : ℂ) * I)) = -(θ * s / 2 * I) := by push_cast; ring
    have a₂ : (-(((-(θ * s / 2) : ℝ) : ℂ) * I)) = θ * s / 2 * I := by push_cast; ring
    rw [a₁, a₂]
    rfl
  have hHerm : IsTimeDepHamiltonian H := by
    rw [hH]
    intro s _
    beta_reduce
    rw [← UnitaryProducts.PaperProof.Spin.family_rotated]
    exact UnitaryProducts.PaperProof.Spin.family_hermitian ω θ s
  have h := UnitaryProducts.PaperProof.Spin.ex_precessing_spin ω θ
  extract_lets H' V Uend at h
  have hH' : H' = H := hH.symm
  obtain ⟨h₁, -, h₃, h₄⟩ := h
  have hdiff : ∀ T : ℕ, 0 < T →
      roundedEvolution H T T - evolution H T T = V T - Uend T := by
    intro T hT
    rw [Bridge.roundedEvolution_eq, Bridge.evolution_eq,
      UnitaryProducts.Paper.roundedEvolution_endpoint hT hHerm, ← h₁ T hT]
    simp only [V, hH']
  refine ⟨fun hω ↦ ?_, fun hω ↦ ?_⟩
  · have hc : c₀ π = 1 / (2 * π) - 1 / π ^ 2 := by
      simp [c₀, Real.pi_ne_zero, Real.sin_pi_div_two]
    rw [hc]
    rw [hH'] at h₃
    refine (h₃ hω).congr' (Eventually.of_forall fun k ↦ ?_)
    have hk := hdiff (2 * k + 1) (by omega)
    rw [← hk]
    push_cast
    rfl
  · refine (h₄ hω).2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [hdiff T hT]

/-- **Example 5.3.** Let `H`, `L`, and `w` satisfy the hypotheses of Theorem 4.2 for every integer
`T ≥ 1`, and let `P(s)` for `s ∈ [0,1]` be continuous and, for every `s` other than one point `s₀`,
a spectral projector of `H(s)` for one eigenvalue. If `‖(1 - P(1)) U(T) P(0)‖ → 0` as `T → ∞`,
then `‖(1 - P(1)) W_T P(0)‖ → 0`. The dimension `d` is at least `1`, as throughout the paper. -/
theorem crossings [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : ∀ T : ℕ, 1 ≤ T → HasSampleWidth H T w) {P : ℝ → 𝕄}
    (hPc : ContinuousOn P (Icc 0 1)) (s₀ : ℝ)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ s₀ → ∃ μ : ℝ, P s = spectralProjector (H s) {(μ : ℂ)})
    (hlim : Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * evolution H T T * P 0‖) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * stepProduct H T * P 0‖) atTop (𝓝 0) := by
  have hU : ∀ T : ℕ, 0 < T →
      UnitaryProducts.Paper.IsEvolution (fun t ↦ H (t / T)) (evolution H T) 0 T :=
    fun T hT ↦ UnitaryProducts.Paper.evolution_spec (Nat.cast_pos.mpr hT) hH
      (UnitaryProducts.Prose.regulated_of_continuousOn
        (Bridge.HasLipschitzDerivative.continuousOn hL))
  have h := UnitaryProducts.PaperProof.ex_crossings H (∂H) P (fun T ↦ evolution H T) hH
    (Bridge.HasLipschitzDerivative.paper hL) hw (fun T hT ↦ hwidth T hT) hU hPc s₀
    (fun s hs hne ↦ by
      obtain ⟨μ, hμ⟩ := hP s hs hne
      exact ⟨μ, hμ.trans (spectralProjector_singleton (hH s hs) μ)⟩) hlim
  simpa only [Bridge.stepProduct_eq] using h

end RoundedClocks
