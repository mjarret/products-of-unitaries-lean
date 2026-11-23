/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps
public import RoundedClocks.UnitSteps
public import RoundedClocks.Appendix
public import RoundedClocks.Examples.Spectral
public import RoundedClocks.Examples.GapAdapted
public import RoundedClocks.Examples.GapAdaptedSpectralGap
public import RoundedClocks.Examples.PrecessingSpinFullTurn
public import RoundedClocks.Examples.PrecessingSpinResidual

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

/-- **Example 5.1.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3) with
the remark (10.4.6),
DLMF 4.22.5 and Bhatia Corollary III.2.6, let `H₀` and `H₁` be Hermitian matrices of
norm at most `1`. For `x ∈ [0,1]`, let `Γ(x)`
be the spectral gap of the least eigenvalue of `(1-x)H₀ + xH₁`, with
`Γ_* = inf_{x∈[0,1]} Γ(x) > 0`. Let `1 < p < 2` and `c_p = ∫_0^1 Γ(x)^{-p} dx`, let
`u : [0,1] → [0,1]` solve `u' = c_p Γ(u)^p` with `u(0) = 0`, and let
`H = (1-u)H₀ + uH₁`. Then `H` satisfies the hypotheses of Theorem 4.2 at width `2`, with
`‖H'(0)‖ + ‖H'(1)‖ = c_p ‖H₁-H₀‖ (Γ(0)^p + Γ(1)^p)`,
`‖H'‖∞ ≤ 2^p c_p ‖H₁-H₀‖`, and `L ≤ p 4^p c_p² ‖H₁-H₀‖²`, so Example 4.5 applies to every
bound `‖(1-Q) U(T) P‖ ≤ C/T` for the spectral projectors `P` and `Q` of `H₀` and `H₁` for their
least eigenvalues. -/
theorem gap_adapted (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6) [NeZero d]
    {H₀ H₁ : 𝕄} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    (hΓstar : 0 < sInf ((fun x : ℝ ↦
      leastEigenvalueGap ((1 - x) • H₀ + x • H₁)) '' Icc 0 1))
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : MapsTo u (Icc 0 1) (Icc 0 1))
    (hu' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u
      ((∫ x in (0 : ℝ)..1, leastEigenvalueGap ((1 - x) • H₀ + x • H₁) ^ (-p)) *
        leastEigenvalueGap ((1 - u s) • H₀ + u s • H₁) ^ p) (Icc 0 1) s) :
    let Γ := fun x : ℝ ↦ leastEigenvalueGap ((1 - x) • H₀ + x • H₁)
    let cₚ := ∫ x in (0 : ℝ)..1, Γ x ^ (-p)
    let H := fun s ↦ (1 - u s) • H₀ + u s • H₁
    let Lbound := p * 4 ^ p * cₚ ^ 2 * ‖H₁ - H₀‖ ^ 2
    let P := leastEigenvalueProjector H₀
    let Q := leastEigenvalueProjector H₁
    IsTimeDepHamiltonian H ∧
      ∃ L, HasLipschitzDerivative H L ∧ L ≤ Lbound ∧
        (∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) 2) ∧
        ‖∂H 0‖ + ‖∂H 1‖ = cₚ * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) ∧
        ‖∂H‖∞ ≤ 2 ^ p * cₚ * ‖H₁ - H₀‖ ∧
        IsOrthogonalProjector P ∧ IsOrthogonalProjector Q ∧ Commute P (H 0) ∧ Commute Q (H 1) ∧
        ∀ (T k : ℕ) (C δ : ℝ), 1 ≤ T → 0 ≤ C → 0 < δ →
          ‖(1 - Q) * evolution H T T * P‖ ≤ C / T →
          2 * (C + ℰ 2 L H) / δ ≤ T →
          √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
          ‖(1 - Q) * stepProduct (fun s ↦ entrywise (bitTruncation k) (H s)) T * P‖ ≤ δ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 :=
    ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  intro Γ cₚ H Lbound P Q
  let D := H₁ - H₀
  have hGamma_bdd : BddBelow (Γ '' Icc (0 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact gap_leastEigenvalueGap_nonneg (gapInterp H₀ H₁ x)
  have hΓ : ∀ x ∈ Icc (0 : ℝ) 1, sInf (Γ '' Icc (0 : ℝ) 1) ≤ Γ x :=
    fun x hx ↦ csInf_le hGamma_bdd ⟨x, hx, rfl⟩
  have hGammaleast : ∀ x ∈ Icc (0 : ℝ) 1,
      IsLeastGap H₀ H₁ h₀ h₁ x (Γ x) := fun x hx ↦
    leastGap_of_pos (gapInterp_hermitian h₀ h₁ x)
      (hΓstar.trans_le (hΓ x hx))
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x := fun x hx ↦
    hΓstar.trans_le (hΓ x hx)
  have hbounds : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2 := fun x hx ↦
    ⟨(hpos x hx).le, interp_gap_le_two h₀ h₁ hn₀ hn₁ hx (hGammaleast x hx)⟩
  have hGammalip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |Γ x - Γ y| ≤ 2 * ‖D‖ * |x - y| := fun x hx y hy ↦
    GapAdaptedSpectralGap.interp_gap_lipschitz bhatia_corollary_III_2_6 h₀ h₁ Γ
      hΓstar hGammaleast hΓ hx hy
  have hGammac : ContinuousOn Γ (Icc (0 : ℝ) 1) :=
    (LipschitzOnWith.of_dist_le_mul
      (K := ⟨2 * ‖D‖, mul_nonneg (by norm_num) (norm_nonneg _)⟩) (by
        intro x hx y hy
        simpa only [Real.dist_eq] using hGammalip x hx y hy)).continuousOn
  have hwidthAll : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) 2 := by
    intro s hs
    change HasEigenvalueDifferences (gapInterp H₀ H₁ (u s)) 2
    intro x hx y hy
    have hHerm := gapInterp_hermitian h₀ h₁ (u s)
    rw [hHerm.spectrum_real_eq_range_eigenvalues] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact gapInterp_width h₀ h₁ hn₀ hn₁ (hu hs) i j
  have hcp : 0 ≤ cₚ := (gap_normalization_pos hGammac hpos p).le
  have hu1 : u 1 = 1 := gap_schedule_endpoint hGammac hpos hu0 hu hu'
  have hH0 : H 0 = H₀ := by simp only [H, hu0, sub_zero, one_smul, zero_smul, add_zero]
  have hH1 : H 1 = H₁ := by simp only [H, hu1, sub_self, zero_smul, one_smul, zero_add]
  have hH : IsTimeDepHamiltonian H := fun s _ ↦ gapInterp_hermitian h₀ h₁ (u s)
  let Hd := fun s ↦ (cₚ * Γ (u s) ^ p) • D
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ gap_schedule_derivative H₀ H₁ (hu' s hs)
  have hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, ∂H s = Hd s := fun s hs ↦
    (hd s hs).derivWithin ((uniqueDiffOn_Icc (by norm_num)) s hs)
  have hends : ‖∂H 0‖ + ‖∂H 1‖ =
      cₚ * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) := by
    rw [hderiv 0 (by norm_num), hderiv 1 (by norm_num)]
    exact gap_derivative_endpoints D hcp (hpos 0 (by norm_num)).le
      (hpos 1 (by norm_num)).le hu0 hu1
  have hsupeq : ‖∂H‖∞ = supNorm Hd := by
    unfold supNorm
    congr 1
    exact Set.image_congr fun s hs ↦ by rw [hderiv s hs]
  have hsup : ‖∂H‖∞ ≤ 2 ^ p * cₚ * ‖H₁ - H₀‖ := by
    rw [hsupeq]
    exact gap_derivative_supNorm_le D (by linarith) hcp hbounds hu
  have hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ Lbound * |t - s| := fun s hs t ht ↦
    gap_derivative_lipschitz D hp₁.le hcp hbounds hGammalip hu hu' hs ht
  have hL : HasLipschitzDerivative H Lbound := ⟨hdiff, fun s hs t ht ↦ by
    rw [hderiv s hs, hderiv t ht]
    exact hlip t ht s hs⟩
  have hPorth : IsOrthogonalProjector P := by
    exact spectralProjector_isOrthogonal H₀ {(leastEigenvalue H₀ : ℂ)}
  have hQorth : IsOrthogonalProjector Q := by
    exact spectralProjector_isOrthogonal H₁ {(leastEigenvalue H₁ : ℂ)}
  have hPcomm : Commute P (H 0) := by
    rw [hH0]
    exact spectralProjector_commute h₀ {(leastEigenvalue H₀ : ℂ)}
  have hQcomm : Commute Q (H 1) := by
    rw [hH1]
    exact spectralProjector_commute h₁ {(leastEigenvalue H₁ : ℂ)}
  refine ⟨hH, Lbound, hL, le_rfl, hwidthAll, hends, hsup, hPorth, hQorth, hPcomm, hQcomm, ?_⟩
  intro T k C delta hT hC hdelta hU hTlarge hsigma
  have hsample : HasSampleWidth H T 2 := by
    intro j hj
    apply hwidthAll
    have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    constructor
    · positivity
    · exact (div_le_one hTpos).2 (by exact_mod_cast hj)
  exact unit_transfer dieudonne_7_6_1 dieudonne_section_8_7 dieudonne_8_6_4 dlmf_4_22_5
    dieudonne_10_5_4 dieudonne_10_6_3
    hT hH hL (by linarith [Real.pi_gt_three]) hsample
    hPorth hQorth hPcomm hQcomm hC hdelta hU hTlarge hsigma

/-- **Example 5.2.** Assuming Dieudonné (10.5.4) and (10.6.3) with the remark (10.4.6), let
`0 < ω ≤ 2π` and `θ` be real, and let `H(s) = (ω/2) e^{-iθsZ/2} X e^{iθsZ/2}` for
`s ∈ [0,1]`, with the Pauli matrices `X` and `Z`. Let `U` and `V` be the evolutions of `H(t/T)` and
`H(⌊t+1/2⌋/T)`. (i) If `ω = π`, then as `T → ∞` through odd integers, `T ‖V(T) - U(T)‖` tends to
`c₀ (‖H'(0)‖ + ‖H'(1)‖) (1 + θ²/(4(π-2)²))^{1/2}` with `c₀` at width `π`. (ii) If `ω = 2π`, then
`‖V(T) - U(T)‖` tends to `2 |sin(θ/4)|`. -/
theorem precessing_spin (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (ω θ : ℝ) (hω₀ : 0 < ω) (hω : ω ≤ 2 * π) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let H := fun s : ℝ ↦
      (ω / 2 : ℝ) • (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    (ω = π → c₀ π = 1 / (2 * π) - 1 / π ^ 2 ∧
      Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) *
          ‖roundedEvolution H (2 * n + 1) (2 * n + 1) -
            evolution H (2 * n + 1) (2 * n + 1)‖)
        atTop (𝓝 (c₀ π * (‖∂H 0‖ + ‖∂H 1‖) * √(1 + θ ^ 2 / (4 * (π - 2) ^ 2))))) ∧
    (ω = 2 * π → Tendsto (fun T : ℕ ↦ ‖roundedEvolution H T T - evolution H T T‖) atTop
      (𝓝 (2 * |Real.sin (θ / 4)|))) := by
  dsimp only
  let H := fun s : ℝ ↦ (ω / 2 : ℝ) •
    (exp (-(θ * s / 2 * I) • PrecessingSpin.Z) *
      PrecessingSpin.X * exp ((θ * s / 2 * I) • PrecessingSpin.Z))
  change (ω = π → c₀ π = _ ∧ Tendsto (fun n : ℕ ↦ ((2 * n + 1 : ℕ) : ℝ) *
    ‖roundedEvolution H (2 * n + 1) (2 * n + 1) -
      evolution H (2 * n + 1) (2 * n + 1)‖) atTop
      (𝓝 (c₀ π * (‖∂H 0‖ + ‖∂H 1‖) * √(1 + θ ^ 2 / (4 * (π - 2) ^ 2))))) ∧
    (ω = 2 * π → Tendsto (fun T : ℕ ↦ ‖roundedEvolution H T T - evolution H T T‖)
      atTop (𝓝 (2 * |Real.sin (θ / 4)|)))
  -- The opening displays identify the continuous endpoint and the symmetric product.
  have hU (T : ℕ) (hT : 0 < (T : ℝ)) :=
    PrecessingSpin.continuous_endpoint dieudonne_10_5_4 dieudonne_10_6_3 ω θ hT
  have hV (T : ℕ) (hT : 1 ≤ T) :=
    PrecessingSpin.rounded_endpoint dieudonne_10_5_4 ω θ hT
  constructor
  · intro hω
    subst ω
    refine ⟨(constants_at_pi (d := 2)).1, ?_⟩
    let N := fun T : ℕ ↦ Real.cos (θ / (2 * T)) • PrecessingSpin.X -
      Real.sin (θ / (2 * T)) • PrecessingSpin.Z
    let ρ := fun T : ℕ ↦ Real.sqrt (π ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2
    let M := fun T : ℕ ↦ (2 * ρ T)⁻¹ • ((π * T) • PrecessingSpin.X -
      θ • PrecessingSpin.Z)
    let ζ := fun T : ℕ ↦ ρ T - π * T / 2
    -- The three residual displays: remove the frame, cancel odd powers, take the norm.
    have hnorm (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
        ‖roundedEvolution H T T - evolution H T T‖ =
          √(‖N T - (Real.cos (ζ T) : ℂ) • M T‖ ^ 2 + Real.sin (ζ T) ^ 2) := by
      calc
        _ = ‖((-I) • N T) ^ T - ((-I) • M T) ^ T *
            exp ((-I * (ζ T : ℂ)) • M T)‖ :=
          PrecessingSpin.endpoint_residual_norm θ T hT hodd
            (hU T (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT))) (hV T hT)
        _ = ‖N T - (Real.cos (ζ T) : ℂ) • M T + (I * Real.sin (ζ T)) • 1‖ :=
          PrecessingSpin.powered_residual_norm θ T hT hodd
        _ = _ := PrecessingSpin.residual_sqrt_norm θ T
    -- The fourth display gives the axis separation and the endpoint derivative norms.
    have haxis := PrecessingSpin.matrix_residual_norm_limit θ
    have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖∂H s‖ = π * |θ| / 2 :=
      PrecessingSpin.hamiltonian_derivWithin_norm Real.pi_pos.le θ hs
    -- The fifth display rationalizes the phase defect before taking its limit.
    have hphase := PrecessingSpin.phase_defect_limit Real.pi_pos θ
    have hsin := PrecessingSpin.scaled_sin_limit
      (PrecessingSpin.phase_defect_tendsto_zero Real.pi_pos θ) hphase
    have hlim := ((haxis.pow 2).add (hsin.pow 2)).sqrt
    rw [PrecessingSpin.odd_limit_factored] at hlim
    rw [(constants_at_pi (d := 2)).1, hderiv 0 (by simp), hderiv 1 (by simp),
      show π * |θ| / 2 + π * |θ| / 2 = π * |θ| by ring]
    have hodd : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ show id n ≤ 2 * n + 1 by dsimp; omega) tendsto_id
    apply (hlim.comp hodd).congr'
    apply Eventually.of_forall
    intro n
    let T := 2 * n + 1
    change √(((T : ℝ) * ‖N T - (Real.cos (ζ T) : ℂ) • M T‖) ^ 2 +
      ((T : ℝ) * Real.sin (ζ T)) ^ 2) = _
    have he := hnorm (2 * n + 1) (by omega) ⟨n, rfl⟩
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at he
    dsimp only
    rw [he]
    rw [show ((T : ℝ) * ‖N T - (Real.cos (ζ T) : ℂ) • M T‖) ^ 2 +
        ((T : ℝ) * Real.sin (ζ T)) ^ 2 = (T : ℝ) ^ 2 *
          (‖N T - (Real.cos (ζ T) : ℂ) • M T‖ ^ 2 + Real.sin (ζ T) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  · intro hω
    subst ω
    -- Every factor is -1; the vanishing exponential residual gives the final display.
    exact PrecessingSpin.full_turn_error_limit dieudonne_10_5_4 θ hU

/-- **Example 5.3.** Assuming Dieudonné (7.6.1), Section 8.7, (8.6.4), (10.5.4) and (10.6.3) with
the remark (10.4.6),
and DLMF 4.22.5, let `H`, `L`, and `w` satisfy the hypotheses of Theorem 4.2 for every
integer
`T ≥ 1`, and let `P(s)` for `s ∈ [0,1]` be continuous and, for every `s` other than one point `s₀`,
a spectral projector of `H(s)` for one eigenvalue. If `‖(1 - P(1)) U(T) P(0)‖ → 0` as `T → ∞`,
then `‖(1 - P(1)) W_T P(0)‖ → 0`. The dimension `d` is at least `1`, as throughout the paper. -/
theorem crossings (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_8_6_4 : Dieudonne_8_6_4) (dlmf_4_22_5 : DLMF_4_22_5)
    (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : ∀ T : ℕ, 1 ≤ T → HasSampleWidth H T w) {P : ℝ → 𝕄}
    (hPc : IsContinuousFamily P) (s₀ : ℝ) (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ s₀ → IsOneEigenvalueProjector (P s) (H s))
    (hlim : Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * evolution H T T * P 0‖) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * stepProduct H T * P 0‖) atTop (𝓝 0) := by
  have hcH : ContinuousOn H (Icc (0 : ℝ) 1) := hL.1.continuousOn
  have hprojectors := crossing_projectors_extend H P hH hcH hPc s₀ hP
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hP0 := (hprojectors 0 h0).1
  have hP1 := (hprojectors 1 h1).1
  have hcomm0 := (hprojectors 0 h0).2
  have hcomm1 := (hprojectors 1 h1).2
  let A := exp (-(I / 2) • H 1)
  let B := exp ((I / 2) • H 0)
  have hA : IsUnitary A := by
    dsimp only [A]
    convert exp_neg_I_smul_isUnitary (hH 1 h1) (1 / 2 : ℝ) using 1
    simp only [smul_smul]
    congr 2
    push_cast
    ring
  have hB : IsUnitary B := by
    dsimp only [B]
    convert exp_neg_I_smul_isUnitary (hH 0 h0) (-1 / 2 : ℝ) using 1
    simp only [smul_smul]
    congr 2
    push_cast
    ring
  have hAQ : Commute A (P 1) := by
    apply Commute.symm
    dsimp only [A]
    exact (hcomm1.smul_right (-(I / 2))).exp_right
  have hBP : Commute B (P 0) := by
    apply Commute.symm
    dsimp only [B]
    exact (hcomm0.smul_right (I / 2)).exp_right
  have hbound : ∀ᶠ T : ℕ in atTop,
      ‖(1 - P 1) * stepProduct H T * P 0‖ ≤
        ‖(1 - P 1) * evolution H T T * P 0‖ + ℰ w L H / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have htransfer := transfer (U := evolution H T T) (W := stepProduct H T)
      (A := A) (B := B) hP0 hP1 hP0 hP1 hA hB hAQ hBP
    have hclock := rounded_clock_bound dieudonne_7_6_1 dieudonne_section_8_7
      dieudonne_8_6_4 dlmf_4_22_5 dieudonne_10_5_4 dieudonne_10_6_3
      hT hH hL hw (hwidth T hT)
    rw [roundedEvolution_end dieudonne_10_5_4 hH hT] at hclock
    change ‖A * stepProduct H T * B - evolution H T T‖ ≤ ℰ w L H / T at hclock
    have hdifference := (le_abs_self
      (‖(1 - P 1) * stepProduct H T * P 0‖ -
        ‖(1 - P 1) * evolution H T T * P 0‖)).trans htransfer
    simp only [sub_self, norm_zero, add_zero, mul_zero] at hdifference
    linarith
  have hvanishing : Tendsto (fun T : ℕ ↦ ℰ w L H / T) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (ℰ w L H)
  have hupper : Tendsto
      (fun T : ℕ ↦ ‖(1 - P 1) * evolution H T T * P 0‖ + ℰ w L H / T)
      atTop (nhds 0) := by
    simpa only [zero_add] using hlim.add hvanishing
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hupper

end RoundedClocks
