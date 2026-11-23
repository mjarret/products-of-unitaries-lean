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
public import RoundedClocks.Examples.PrecessingSpinOpeningDisplays
public import RoundedClocks.Examples.PrecessingSpinWidthPi
public import RoundedClocks.Examples.PrecessingSpinWidthTwoPi

/-!
# Section 5: Examples

Gap-adapted schedules (Example 5.1), a precessing spin (Example 5.2), and eigenvalue crossings
(Example 5.3). The terms of Example 5.1 are in `Definitions.lean`.

## Where each step is proved

The supporting lemmas are in `RoundedClocks/Examples/`.

* Example 5.1 (`GapAdapted.lean`, `GapAdaptedSpectralGap.lean`). Weyl's theorem for the ordered
  eigenvalues: `GapAdaptedSpectralGap.eigen_lipschitz`. The least eigenvalue keeps its
  multiplicity: `GapAdaptedSpectralGap.ground_indices_constant`. `Γ` is Lipschitz with constant
  `2‖H₁ - H₀‖`: `GapAdaptedSpectralGap.leastEigenvalueGap_lipschitz`. `Γ ≤ 2`:
  `leastEigenvalueGap_le_two`. Eigenvalue differences of modulus at most `2`: `gapInterp_width`.
  `u(1) = 1`: `gap_schedule_endpoint`. `H' = c_p Γ(u)^p (H₁ - H₀)`: `gap_schedule_derivative`. The
  three displayed lines: `gap_derivative_endpoints`, `gap_derivative_supNorm_le`,
  `gap_derivative_lipschitz`.
* Example 5.2 (`PrecessingSpinMatrix.lean`, `PrecessingSpinOpeningDisplays.lean`,
  `PrecessingSpinWidthPi.lean`, `PrecessingSpinWidthTwoPi.lean`; namespace `PrecessingSpin`). The
  two opening displays: `evolution_end_eq`, `roundedEvolution_end_eq`. Part (i), lines 1 to 5 of
  the display: `norm_difference_eq_norm_powers`, `norm_powers_eq_norm_axes`, `norm_axes_eq_sqrt`,
  `tendsto_axes_distance` with `hamiltonian_derivWithin_norm`, and `tendsto_mul_ζ`. Part (ii):
  `full_turn_factor`, `full_turn_product`, `full_turn_exp_sub_tendsto_zero`,
  `Z_rotation_distance`, `full_turn_error_limit`.
* Example 5.3 (`Spectral.lean`). "By continuity": `crossing_projectors_extend`.
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

/-- **Example 5.1.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), and Bhatia, Corollary III.2.6, let `H₀` and `H₁` be Hermitian
matrices of norm at most `1`, and for `x ∈ [0,1]` let `Γ(x)` be the spectral gap of the least
eigenvalue of `(1-x)H₀ + xH₁`, with `Γ_* = inf_{x∈[0,1]} Γ(x) > 0`. Let `1 < p` and
`c_p = ∫_0^1 Γ(x)^{-p} dx`, let `u(s)` for `s ∈ [0,1]`, with values in `[0,1]`, solve
`u' = c_p Γ(u)^p` with `u(0) = 0`, and let `H = (1-u)H₀ + uH₁`. Then `H` satisfies the hypotheses
of Theorem 4.2 at width `2`, with
`‖H'(0)‖ + ‖H'(1)‖ = c_p ‖H₁-H₀‖ (Γ(0)^p + Γ(1)^p)`, `‖H'‖∞ ≤ 2^p c_p ‖H₁-H₀‖`, and
`L ≤ p 4^p c_p² ‖H₁-H₀‖²`, so Example 4.5 applies to every bound `‖(1-Q) U(T) P‖ ≤ C/T` for the
spectral projectors `P` and `Q` of `H₀` and `H₁` for their least eigenvalues.

Below, `Γ` is `interpolationGap H₀ H₁` and `c_p` is `gapNormalization H₀ H₁ p`. -/
theorem gap_adapted (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    [NeZero d] {H₀ H₁ : 𝕄} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    (hΓstar : 0 < sInf (interpolationGap H₀ H₁ '' Icc 0 1))
    {p : ℝ} (hp₁ : 1 < p) {u : ℝ → ℝ} (hu0 : u 0 = 0)
    (hu : MapsTo u (Icc 0 1) (Icc 0 1))
    (hu' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt u
      (gapNormalization H₀ H₁ p * interpolationGap H₀ H₁ (u s) ^ p) (Icc 0 1) s) :
    let Γ := interpolationGap H₀ H₁
    let cₚ := gapNormalization H₀ H₁ p
    let H := fun s ↦ (1 - u s) • H₀ + u s • H₁
    let P := leastEigenvalueProjector H₀
    let Q := leastEigenvalueProjector H₁
    IsTimeDepHamiltonian H ∧
      ∃ L, HasLipschitzDerivative H L ∧ HasWidth H 2 ∧
        ‖∂H 0‖ + ‖∂H 1‖ = cₚ * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) ∧
        ‖∂H‖∞ ≤ 2 ^ p * cₚ * ‖H₁ - H₀‖ ∧
        L ≤ p * 4 ^ p * cₚ ^ 2 * ‖H₁ - H₀‖ ^ 2 ∧
        IsOrthogonalProjector P ∧ IsOrthogonalProjector Q ∧ Commute P (H 0) ∧ Commute Q (H 1) ∧
        ∀ (T k : ℕ) (C δ : ℝ), 1 ≤ T → 0 ≤ C → 0 < δ →
          ‖(1 - Q) * evolution H T T * P‖ ≤ C / T →
          2 * (C + ℰ 2 L H) / δ ≤ T →
          √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
          ‖(1 - Q) * stepProduct (truncation k H) T * P‖ ≤ δ := by
  -- The supporting lemmas index the least eigenvalue by `Fin.last n`, so write `d = n + 1`.
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  intro Γ cₚ H P Q
  let D := H₁ - H₀
  -- In the supporting lemmas, `gapInterp H₀ H₁ x` is `(1 - x) • H₀ + x • H₁` by definition.
  -- `Γ ≥ Γ_* > 0` for `x ∈ [0,1]`.
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x := fun x hx ↦
    hΓstar.trans_le (sInf_leastEigenvalueGap_le H₀ H₁ hx)
  -- Weyl: the eigenvalues of `(1-x)H₀ + xH₁` lie in `[-1,1]`, so `Γ ≤ 2`.
  have hbounds : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2 := fun x hx ↦
    ⟨(hpos x hx).le, leastEigenvalueGap_le_two h₀ h₁ hn₀ hn₁ hx (hpos x hx)⟩
  -- Weyl: as the least eigenvalue keeps its multiplicity, `Γ` is Lipschitz with constant
  -- `2‖H₁ - H₀‖`.
  have hΓlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |Γ x - Γ y| ≤ 2 * ‖D‖ * |x - y| := fun x hx y hy ↦
    GapAdaptedSpectralGap.leastEigenvalueGap_lipschitz bhatia_corollary_III_2_6 h₀ h₁
      hΓstar hx hy
  have hΓc : ContinuousOn Γ (Icc (0 : ℝ) 1) :=
    (LipschitzOnWith.of_dist_le_mul
      (K := ⟨2 * ‖D‖, mul_nonneg (by norm_num) (norm_nonneg _)⟩) (by
        intro x hx y hy
        simpa only [Real.dist_eq] using hΓlip x hx y hy)).continuousOn
  -- Every sample has eigenvalue differences of modulus at most `2`.
  have hwidthAll : HasWidth H 2 := by
    intro s hs
    change HasEigenvalueDifferences (gapInterp H₀ H₁ (u s)) 2
    intro x hx y hy
    have hHerm := gapInterp_hermitian h₀ h₁ (u s)
    rw [hHerm.spectrum_real_eq_range_eigenvalues] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact gapInterp_width h₀ h₁ hn₀ hn₁ (hu hs) i j
  -- Integrating `Γ(u)^{-p} u' = c_p` gives `u(1) = 1`, so `H(0) = H₀` and `H(1) = H₁`.
  have hcp : 0 ≤ cₚ := (gap_normalization_pos hΓc hpos p).le
  have hu1 : u 1 = 1 := gap_schedule_endpoint hΓc hpos hu0 hu hu'
  have hH0 : H 0 = H₀ := by simp only [H, hu0, sub_zero, one_smul, zero_smul, add_zero]
  have hH1 : H 1 = H₁ := by simp only [H, hu1, sub_self, zero_smul, one_smul, zero_add]
  have hH : IsTimeDepHamiltonian H := fun s _ ↦ gapInterp_hermitian h₀ h₁ (u s)
  -- `H' = c_p Γ(u)^p (H₁ - H₀)`.
  let Hd := fun s ↦ (cₚ * Γ (u s) ^ p) • D
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ gap_schedule_derivative H₀ H₁ (hu' s hs)
  have hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, ∂H s = Hd s := fun s hs ↦
    (hd s hs).derivWithin ((uniqueDiffOn_Icc (by norm_num)) s hs)
  -- The first displayed line.
  have hends : ‖∂H 0‖ + ‖∂H 1‖ =
      cₚ * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) := by
    rw [hderiv 0 (by norm_num), hderiv 1 (by norm_num)]
    exact gap_derivative_endpoints D hcp (hpos 0 (by norm_num)).le
      (hpos 1 (by norm_num)).le hu0 hu1
  -- The second displayed line, as `Γ ≤ 2`.
  have hsupeq : ‖∂H‖∞ = supNorm Hd := by
    unfold supNorm
    congr 1
    exact Set.image_congr fun s hs ↦ by rw [hderiv s hs]
  have hsup : ‖∂H‖∞ ≤ 2 ^ p * cₚ * ‖H₁ - H₀‖ := by
    rw [hsupeq]
    exact gap_derivative_supNorm_le D (by linarith) hcp hbounds hu
  -- The third displayed line: the product of the Lipschitz constants `p 2^{p-1}` of `y ↦ y^p`,
  -- `2‖H₁ - H₀‖` of `Γ`, and `2^p c_p` of `u`.
  let Lbound := p * 4 ^ p * cₚ ^ 2 * ‖H₁ - H₀‖ ^ 2
  have hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ Lbound * |t - s| := fun s hs t ht ↦
    gap_derivative_lipschitz D hp₁.le hcp hbounds hΓlip hu hu' hs ht
  have hL : HasLipschitzDerivative H Lbound := ⟨hdiff, fun s hs t ht ↦ by
    rw [hderiv s hs, hderiv t ht]
    exact hlip t ht s hs⟩
  -- `P` and `Q` are orthogonal projectors commuting with `H(0) = H₀` and `H(1) = H₁`.
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
  refine ⟨hH, Lbound, hL, hwidthAll, hends, hsup, le_rfl, hPorth, hQorth, hPcomm, hQcomm, ?_⟩
  -- So `H` satisfies the hypotheses of Theorem 4.2 at width `2 < 2π`, and Example 4.5 applies.
  intro T k C δ hT _hC hδ hU hTlarge hsigma
  have hsample : HasSampleWidth H T 2 := by
    intro j hj
    apply hwidthAll
    exact unitInterval.div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast hj)
  exact unit_transfer dieudonne_7_6_1
    dieudonne_10_5_4 dieudonne_10_6_3
    hT hH hL (by linarith [Real.pi_gt_three]) hsample
    hPorth hQorth hPcomm hQcomm hδ hU hTlarge hsigma

/-- **Example 5.2.** Assuming Dieudonné (10.5.4) and (10.6.3) with the remark (10.4.6), let
`ω` and `θ` be real, and let `H(s) = (ω/2) e^{-iθsZ/2} X e^{iθsZ/2}` for `s ∈ [0,1]`,
with the Pauli matrices `X` and `Z`. Let `U` and `V` be the evolutions of `H(t/T)` and
`H(⌊t+1/2⌋/T)`. (i) If `ω` is `π`, then, as `T → ∞` through odd integers `T = 2n + 1`,
`T ‖V(T) - U(T)‖` tends to `c₀ (‖H'(0)‖ + ‖H'(1)‖) (1 + θ²/(4(π-2)²))^{1/2}`, with
`c₀ = 1/(2π) - 1/π²`, the constant of Theorem 4.2 at width `π`. (ii) If `ω` is `2π`, then
`‖V(T) - U(T)‖` tends to `2 |sin(θ/4)|` as `T → ∞`.

The statement holds for every real `ω`; each part fixes its value to `π` or `2π`. -/
theorem precessing_spin (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (ω θ : ℝ) :
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
  -- The `X` and `Z` of the statement are `PrecessingSpin.X` and `PrecessingSpin.Z` by definition.
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
  -- The two opening displays: `U(T) = e^{-iθZ/2} e^{-i(ωTX-θZ)/2}` and `V(T) = e^{-iθZ/2} S^T`
  -- with `S = e^{-iωX/4} e^{iθZ/(2T)} e^{-iωX/4}`.
  have hU (T : ℕ) (hT : 0 < (T : ℝ)) : evolution H T T =
      exp (-(θ / 2 * I) • PrecessingSpin.Z) *
        exp ((-I / 2) • ((ω * T) • PrecessingSpin.X - θ • PrecessingSpin.Z)) :=
    PrecessingSpin.evolution_end_eq dieudonne_10_5_4 dieudonne_10_6_3 ω θ hT
  have hV (T : ℕ) (hT : 1 ≤ T) : roundedEvolution H T T =
      exp (-(θ / 2 * I) • PrecessingSpin.Z) *
        (exp (-(ω / 4 * I) • PrecessingSpin.X) * exp ((θ / (2 * T) * I) • PrecessingSpin.Z) *
          exp (-(ω / 4 * I) • PrecessingSpin.X)) ^ T :=
    PrecessingSpin.roundedEvolution_end_eq dieudonne_10_5_4 ω θ hT
  constructor
  · -- (i): `ω = π` and `T` odd.
    rintro rfl
    refine ⟨c₀_pi, ?_⟩
    -- The paper's `N`, `M`, and `ζ`, as functions of `T`.
    let N := fun T : ℕ ↦ PrecessingSpin.N θ T
    let M := fun T : ℕ ↦ PrecessingSpin.M θ T
    let ζ := fun T : ℕ ↦ PrecessingSpin.ζ θ T
    -- Lines 1, 2, and 3 of the display.
    have hnorm (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
        ‖roundedEvolution H T T - evolution H T T‖ =
          √(‖N T - (Real.cos (ζ T) : ℂ) • M T‖ ^ 2 + Real.sin (ζ T) ^ 2) := by
      calc
        _ = ‖((-I) • N T) ^ T - ((-I) • M T) ^ T *
            exp ((-I * (ζ T : ℂ)) • M T)‖ :=
          PrecessingSpin.norm_difference_eq_norm_powers θ T hT
            (hU T (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT))) (hV T hT)
        _ = ‖N T - (Real.cos (ζ T) : ℂ) • M T + (I * Real.sin (ζ T)) • 1‖ :=
          PrecessingSpin.norm_powers_eq_norm_axes θ T hT hodd
        _ = _ := PrecessingSpin.norm_axes_eq_sqrt θ T
    -- Line 4: `T ‖N - M cos ζ‖ → (π-2)|θ|/(2π)`, and `‖H'‖ = π|θ|/2`.
    have haxis : Tendsto (fun T : ℕ ↦ (T : ℝ) * ‖N T - (Real.cos (ζ T) : ℂ) • M T‖) atTop
        (𝓝 ((π - 2) * |θ| / (2 * π))) := PrecessingSpin.tendsto_axes_distance θ
    have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖∂H s‖ = π * |θ| / 2 :=
      PrecessingSpin.hamiltonian_derivWithin_norm Real.pi_pos.le θ hs
    -- Line 5: `T ζ → θ²/(4π)`, so `T sin ζ → θ²/(4π)`.
    have hphase : Tendsto (fun T : ℕ ↦ (T : ℝ) * ζ T) atTop (𝓝 (θ ^ 2 / (4 * π))) :=
      PrecessingSpin.tendsto_mul_ζ θ
    have hsin : Tendsto (fun T : ℕ ↦ (T : ℝ) * Real.sin (ζ T)) atTop
        (𝓝 (θ ^ 2 / (4 * π))) :=
      PrecessingSpin.scaled_sin_limit (PrecessingSpin.tendsto_ζ θ) hphase
    -- Together: `T ‖V(T) - U(T)‖ = ((T ‖N - M cos ζ‖)² + (T sin ζ)²)^{1/2}` tends to
    -- `(((π-2)|θ|/(2π))² + (θ²/(4π))²)^{1/2}`, which is the stated limit.
    have hlim := ((haxis.pow 2).add (hsin.pow 2)).sqrt
    rw [PrecessingSpin.odd_limit_factored] at hlim
    rw [c₀_pi, hderiv 0 (by simp), hderiv 1 (by simp),
      show π * |θ| / 2 + π * |θ| / 2 = π * |θ| by ring]
    -- `T` runs over the odd numbers `2n + 1`.
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
  · -- (ii): `ω = 2π`. Every factor is `-1`, so `V(T) = (-1)^T e^{-iθZ}`, and
    -- `e^{-i(2πTX-θZ)/2} - (-1)^T → 0`.
    rintro rfl
    exact PrecessingSpin.full_turn_error_limit dieudonne_10_5_4 θ hU

/-- **Example 5.3.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), let `H`, `L`, and `w` satisfy the hypotheses of Theorem 4.2
for every integer `T ≥ 1`, and let `P(s)` for `s ∈ [0,1]` be continuous and, for every `s` other
than one point `s₀`, a spectral projector of `H(s)` for one eigenvalue. If
`‖(1 - P(1)) U(T) P(0)‖ → 0` as `T → ∞`, then `‖(1 - P(1)) W_T P(0)‖ → 0`.

The exceptional point `s₀` may be any real number. -/
theorem crossings (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {L w : ℝ}
    (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : ∀ T : ℕ, 1 ≤ T → HasSampleWidth H T w) {P : ℝ → 𝕄}
    (hPc : IsContinuousFamily P) (s₀ : ℝ)
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, s ≠ s₀ → IsOneEigenvalueProjector (P s) (H s))
    (hlim : Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * evolution H T T * P 0‖) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ ↦ ‖(1 - P 1) * stepProduct H T * P 0‖) atTop (𝓝 0) := by
  -- By continuity, `P(0)` and `P(1)` are orthogonal projectors commuting with `H(0)` and `H(1)`.
  have hcH : ContinuousOn H (Icc (0 : ℝ) 1) := hL.1.continuousOn
  have hprojectors := crossing_projectors_extend H P hH hcH hPc s₀ hP
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hP0 : IsOrthogonalProjector (P 0) := (hprojectors 0 h0).1
  have hP1 : IsOrthogonalProjector (P 1) := (hprojectors 1 h1).1
  have hcomm0 : Commute (P 0) (H 0) := (hprojectors 0 h0).2
  have hcomm1 : Commute (P 1) (H 1) := (hprojectors 1 h1).2
  -- Proposition 2.4 with `A = e^{-iH(1)/2}` and `B = e^{iH(0)/2}`, as in the proof of
  -- Example 4.5.
  let A := exp (-(I / 2) • H 1)
  let B := exp ((I / 2) • H 0)
  have hbound : ∀ᶠ T : ℕ in atTop,
      ‖(1 - P 1) * stepProduct H T * P 0‖ ≤
        ‖(1 - P 1) * evolution H T T * P 0‖ + ℰ w L H / T := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    -- Proposition 2.4 with `P' = P(0)` and `Q' = P(1)`: the projector terms vanish.
    have htransfer := transfer_end_phases (hH h0) (hH h1)
      hP0 hP1 hcomm0 hcomm1 (U := evolution H T T) (W := stepProduct H T)
    -- By (4.6), `‖V(T) - U(T)‖ ≤ ℰ_w(H)/T`, where `V(T) = A W_T B` by (2.5).
    have hclock := rounded_clock_bound dieudonne_7_6_1
      dieudonne_10_5_4 dieudonne_10_6_3
      hT hH hL hw (hwidth T hT)
    rw [roundedEvolution_end dieudonne_10_5_4 hH hT] at hclock
    change ‖A * stepProduct H T * B - evolution H T T‖ ≤ ℰ w L H / T at hclock
    have hdifference := (le_abs_self
      (‖(1 - P 1) * stepProduct H T * P 0‖ -
        ‖(1 - P 1) * evolution H T T * P 0‖)).trans htransfer
    linarith
  -- Both terms of the bound tend to zero.
  have hvanishing : Tendsto (fun T : ℕ ↦ ℰ w L H / T) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (ℰ w L H)
  have hupper : Tendsto
      (fun T : ℕ ↦ ‖(1 - P 1) * evolution H T T * P 0‖ + ℰ w L H / T)
      atTop (nhds 0) := by
    simpa only [zero_add] using hlim.add hvanishing
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hupper

end RoundedClocks
