/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.Appendix.ConstantsArc
public import RoundedClocks.Appendix.ConstantsPi
public import RoundedClocks.Appendix.LogarithmIntegral
public import RoundedClocks.Appendix.LogarithmEstimates
public import RoundedClocks.Appendix.CellFamily
public import RoundedClocks.Appendix.CellCenterBound
public import RoundedClocks.Appendix.CellGrowth
public import RoundedClocks.Appendix.EndValue

/-!
# Appendices A and B: lemmas behind the unit-step comparisons, and constants

Equations (A.1) and (A.2), the correction `Y` of Section 4.1 (Lemma A.1), the Hermitian logarithm
of Section 4.4 (Lemma A.2), the derivative of `𝒩([Ω,·])Ω'` (Lemma A.3), and the constants (Facts
B.1 and B.2).

## Where each step is proved

The supporting lemmas are in `RoundedClocks/Appendix/`.

* Preamble of Appendix A (`PositiveSeries.lean`, `MatrixSeries.lean`, `SeriesDerivative.lean`).
  `‖[Ω,A]‖ ≤ w ‖A‖`: `norm_adL_le_width`. Equation (A.1): `norm_adL_series_le`.
  `([Ω,·]ⁿA)_pq = (λ_p - λ_q)ⁿ A_pq`: `adL_pow_eigenbasis_entry`. Partial fractions of the
  cotangent, `𝒩(x) = ∑ 2/(4π²m² - x²)`: `𝒩_eq_partialFractions`, from `dlmf_4_22_3`. The series
  `𝒩(x) = ∑ νₙ xⁿ` with `νₙ ≥ 0`: `multiplierCoeff_series_eq`, `multiplierCoeff_nonneg`. The two
  meanings of `𝒩([Ω,·])A` agree: `multiplierSeriesOp_eq_𝒩ad`. Equation (A.2):
  `hasDerivWithinAt_adL_series`, `norm_adL_series_deriv_le`.
* Lemma A.1 (`CellMultiplier.lean`, `CellFamily.lean`, `CellCenterBound.lean`, `CellGrowth.lean`).
  The guess `𝒩_τ(x)`: `cellMultiplier`; `Y(τ) = 𝒩_τ([Ω,·])D`: `cellGuess`.
  `∂_τ𝒩_τ + ix𝒩_τ = τ`: `cellMultiplier_derivative`; `Y' + i[Ω,Y] = τD`: `cellGuess_hasDerivAt`.
  `𝒩_{±1/2} = 𝒩`: `cellMultiplier_endpoints`, `cellGuess_endpoints`. Partial fractions of the
  cosecant and nonnegative coefficients: `cellCenter_partialFractions_ne_zero`,
  `cellCenterCoeff_nonneg`. `‖Y(0)‖ ≤ c₀ ‖D‖`: `norm_cellCenter_le`. The conjugate
  `e^{iτΩ} Y e^{-iτΩ}`, its integral, and `‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2`: `norm_le_of_cellEquation`.
* Lemma A.2 (`PointwiseLogarithm.lean`, `LogarithmChord.lean`, `LogarithmResolventCalculus.lean`,
  `LogarithmIntegral.lean`, `LocalLogarithm.lean`, `ResolventBounds.lean`,
  `LogarithmQuadratures.lean`, `LogarithmEstimates.lean`; namespace `WalkLog`).
  `H(s) = ∑ θ_j P_j`: `walk_log_pointwise`; uniqueness: `walk_log_unique`.
  `Log z = ∫₀¹ (z-1)(1+u(z-1))⁻¹ du`: `integral_log_chord`, `walkLogIntegral_eq_cfc`.
  `u(W-1)S_u = 1 - S_u`: `walkLogResolvent_mul_sub`; `∂_s S_u = -u S_u W' S_u`:
  `hasDerivWithinAt_walkLogResolvent`. Equation (A.3) and `C²`: `walk_log_local_derivatives`.
  `1 + u(e^{-iφ}-1) = e^{-iφ/2}(cos(φ/2) - iv sin(φ/2))`, its squared modulus, and
  `‖S_u‖² ≤ 1/r(v)`: `chord_factorization`, `chord_norm_sq`, `chord_radius_lower`,
  `phase_resolvent_bound`. The norm display: `walkLog_integral_norm_bounds`, with
  `square_quadrature`, `cube_weighted_integral`, and `cube_quadrature`.
* Lemma A.3 (`CommutatorSeriesDerivative.lean`, `JacobiTelescope.lean`, `SeriesDerivative.lean`,
  `CommutatorTelescope.lean`, `ExponentialDuhamel.lean`, `EndValueDuhamel.lean`, `EndValue.lean`).
  Part (i): `endValue_part_i`. `(𝒩([Ω,·])Ω')' = 𝒩([Ω,·])Ω'' + 𝓕(Ω')`: `deriv_endValue_eq`.
  Lines 1 and 2 of (A.4): `endValue_F_commutator_series`; lines 3 and 4: `endValue_F_split`, with
  `norm_endValue_F_commutator_le`. The display `[Ω,Λ] = Ω' - X`:
  `EndValue.centeredRemainder_commutator_integral`, `EndValue.centeredRemainder_commutator_deriv`,
  `EndValue.centeredRemainder_commutator_boundary`, `EndValue.centeredDuhamel_decomposition`.
  `‖X‖ = ‖(e^{-iΩ})'‖`: `EndValue.norm_centeredDuhamel`, with Duhamel's formula
  `EndValue.hasDerivWithinAt_evol_curve`. `‖Λ‖ ≤ ‖Ω'‖/4`: `EndValue.norm_centeredRemainder_le`.
  Part (ii): `endValue_part_ii`.
* Fact B.1 (`ConstantsPi.lean`): `c₀_pi`, `multiplier_values_at_pi`,
  `endpoint_derivatives_le_supNorm`, `constants_pi_decimal_bounds`, `ℰ_pi_le`.
* Fact B.2 (`ConstantsArc.lean`): `free_arc_edge_limits`, `tendsto_free_arc_div_cos`,
  `free_arc_coefficient_limits`, `free_arc_equivalents`, `free_arc_isBigO`.

## Names used in the supporting files

* `adL Ω` is `[Ω,·]` and `adL Ω ^ n` is `[Ω,·]ⁿ`; `powDeriv (adL Ω) (adL B) n A` is
  `∑_{k<n} [Ω,·]^k [B, [Ω,·]^{n-1-k} A]` (both are defined in `Definitions.lean`);
  `multiplierCoeff n` is the coefficient `νₙ` of `𝒩(x) = ∑ νₙ xⁿ`; `multiplierSeriesOp Ω E` is
  `∑ νₙ [Ω,·]ⁿ E`.
* `cellMultiplier τ x` is `𝒩_τ(x)`; `cellGuess Ω hΩ D τ` is the guess `Y(τ) = 𝒩_τ([Ω,·])D`;
  `cellCenterCoeff k` is the coefficient of `x^{2k}` in `-𝒩₀(x)`.
* `WalkLog.walkLogResolvent W u` is `S_u = (1 + u(W-1))⁻¹`; `WalkLog.radius w v` is `r(v)`.
* `endValue_F Ω B D` is `𝓕(B)` with `D` in place of `Ω'`; `EndValue.evol Ω σ` is `e^{-iσΩ}`;
  `EndValue.centeredDuhamel` is `X`; `EndValue.centeredRemainder` is `Λ`.
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

/-! ## Appendix A: Lemmas behind the unit-step comparisons -/

/-- **Equation (A.1).** Let `0 ≤ w < 2π`, let `Ω` be a Hermitian matrix with eigenvalue
differences of modulus at most `w`, and let `g(x) = ∑ gₙ xⁿ` be a power series with every `gₙ ≥ 0`
and radius of convergence at least `2π`. Then `g([Ω,·])A = ∑ gₙ [Ω,·]ⁿ A` satisfies
`‖g([Ω,·])A‖ ≤ g(w) ‖A‖` for every matrix `A`. Here `adL Ω` is `[Ω,·]` and `g(w) = ∑ gₙ wⁿ`. -/
theorem series_bound [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : IsHermitian Ω) (hwidth : HasEigenvalueDifferences Ω w) {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hradius : ∀ r : ℝ, 0 ≤ r → r < 2 * π → Summable fun n ↦ g n * r ^ n) (A : 𝕄) :
    ‖∑' n, (g n : ℂ) • (adL Ω ^ n) A‖ ≤ (∑' n, g n * w ^ n) * ‖A‖ :=
  norm_adL_series_le hg (norm_adL_le_width hΩ hw0 hwidth) (hradius w hw0 hw)

/-- **Equation (A.2).** Let `0 ≤ w < 2π`, let `Ω(s)` and `A(s)` be
continuously differentiable for `s ∈ [0,1]`, with every `Ω(s)` Hermitian with eigenvalue
differences of modulus at most `w`, and let `g(x) = ∑ gₙ xⁿ` be a power series with every `gₙ ≥ 0`
and radius of convergence at least `2π`. Then, for every `s ∈ [0,1]`,
`(g([Ω,·])A)' = g([Ω,·])A' + ∑_{n≥1} gₙ ∑_{k=0}^{n-1} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} A]` and
`‖(g([Ω,·])A)'‖ ≤ g(w) ‖A'‖ + 2g'(w) ‖Ω'‖ ‖A‖`. Here `adL Ω` is `[Ω,·]`,
`powDeriv (adL Ω) (adL Ω') n A` is the sum over `k`, `g(w) = ∑ gₙ wⁿ`, and
`g'(w) = ∑ n gₙ w^{n-1}`. -/
theorem series_derivative [NeZero d] {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) {Ω A : ℝ → 𝕄} (hΩC1 : IsC1Family Ω) (hAC1 : IsC1Family A)
    (hΩ : IsTimeDepHamiltonian Ω) (hwidth : HasWidth Ω w) {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (hradius : ∀ r : ℝ, 0 ≤ r → r < 2 * π → Summable fun n ↦ g n * r ^ n) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t ↦ ∑' n, (g n : ℂ) • (adL (Ω t) ^ n) (A t))
        (∑' n, (g n : ℂ) • ((adL (Ω s) ^ n) (∂A s) +
          (powDeriv (adL (Ω s)) (adL (∂Ω s)) n) (A s))) (Icc 0 1) s ∧
      ‖∂(fun t ↦ ∑' n, (g n : ℂ) • (adL (Ω t) ^ n) (A t)) s‖ ≤
        (∑' n, g n * w ^ n) * ‖∂A s‖ + 2 * (∑' n, g n * n * w ^ (n - 1)) * ‖∂Ω s‖ * ‖A s‖ := by
  intro s hs
  have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have ha : ∀ t ∈ Icc (0 : ℝ) 1, ‖adL (Ω t)‖ ≤ w := fun t ht ↦
    norm_adL_le_width (hΩ ht) hw0 (hwidth t ht)
  -- Inside the radius of convergence, the series of `g` and of `g'` converge at `w`.
  have hsum : Summable fun n ↦ g n * w ^ n := hradius w hw0 hw
  have hsum' : Summable fun n ↦ g n * n * w ^ (n - 1) := by
    obtain ⟨R, hwR, hR⟩ := exists_between hw
    exact summable_coeff_deriv hg hw0 hwR (hradius R (hw0.trans hwR.le) hR)
  have hdΩ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt Ω (∂Ω t) (Icc 0 1) t := fun t ht ↦
    (hΩC1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hdA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt A (∂A t) (Icc 0 1) t := fun t ht ↦
    (hAC1.differentiableOn (by norm_num) t ht).hasDerivWithinAt
  have hΩ' : ContinuousOn (∂Ω) (Icc (0 : ℝ) 1) :=
    (hΩC1.derivWithin hu (m := 0) (by norm_num)).continuousOn
  have hA' : ContinuousOn (∂A) (Icc (0 : ℝ) 1) :=
    (hAC1.derivWithin hu (m := 0) (by norm_num)).continuousOn
  -- Termwise differentiation gives the first line.
  have hd := hasDerivWithinAt_adL_series hg hw0 zero_le_one hsum hsum' ha
    hdΩ hdA hΩ' hA' s hs
  have hderiv : ∂(fun t ↦ ∑' n, (g n : ℂ) • (adL (Ω t) ^ n) (A t)) s =
      ∑' n, (g n : ℂ) • ((adL (Ω s) ^ n) (∂A s) +
        (powDeriv (adL (Ω s)) (adL (∂Ω s)) n) (A s)) := hd.derivWithin (hu s hs)
  refine ⟨hd, ?_⟩
  -- The second line: (A.1) for `g([Ω,·])A'`, and each of the `n` terms with coefficient `gₙ` has
  -- norm at most `2gₙ w^{n-1} ‖Ω'‖ ‖A‖`.
  rw [hderiv]
  exact norm_adL_series_deriv_le hg hw0 (ha s hs) hsum hsum'

/-- **Lemma A.1.** Let `0 ≤ w < 2π`, let `Ω` be a Hermitian matrix with
eigenvalue differences of modulus at most `w`, and let `D` be a matrix. There is a continuously
differentiable matrix-valued `Y(τ)` for `|τ| ≤ 1/2` such that the following hold.
(i) `Y` solves `Y' + i[Ω,Y] = τD`, with end values `Y(-1/2) = Y(1/2) = 𝒩([Ω,·])D`.
(ii) `‖Y(0)‖ ≤ c₀ ‖D‖` for the `c₀` of Appendix B, and `‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2` for
`|τ| ≤ 1/2`. -/
theorem cell {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) (hwidth : HasEigenvalueDifferences Ω w) (D : 𝕄) :
    ∃ Y : ℝ → 𝕄, IsC1FamilyOn Y (-1 / 2) (1 / 2) ∧
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
          (Icc (-1 / 2) (1 / 2)) τ) ∧
      Y (-1 / 2) = 𝒩ad Ω D ∧ Y (1 / 2) = 𝒩ad Ω D ∧ ‖Y 0‖ ≤ c₀ w * ‖D‖ ∧
      ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 := by
  -- The guess `Y(τ) = 𝒩_τ([Ω,·])D`.
  let Y : ℝ → 𝕄 := cellGuess Ω hΩ D
  -- The guess is continuously differentiable for `|τ| ≤ 1/2`.
  have hC1 : IsC1FamilyOn Y (-1 / 2) (1 / 2) :=
    (cellGuess_contDiff Ω hΩ D).contDiffOn
  -- Differentiating gives `∂_τ𝒩_τ(x) + ix𝒩_τ(x) = τ`, so `Y' + i[Ω,Y] = τD`.
  have hODE : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
        (Icc (-1 / 2) (1 / 2)) τ := by
    intro τ hτ
    exact (cellGuess_hasDerivAt Ω hΩ D τ).hasDerivWithinAt
  -- `𝒩_{±1/2}(x) = 𝒩(x)`, so `Y(±1/2) = 𝒩([Ω,·])D`.
  have hends : Y (-1 / 2) = 𝒩ad Ω D ∧ Y (1 / 2) = 𝒩ad Ω D :=
    cellGuess_endpoints hΩ D hw hwidth
  -- The partial fractions of the cosecant and (A.1): `‖Y(0)‖ ≤ -𝒩₀(w) ‖D‖ = c₀ ‖D‖`.
  have hcenter : ‖Y 0‖ ≤ c₀ w * ‖D‖ :=
    norm_cellCenter_le hw0 hw hΩ hwidth D
  -- Integrating the derivative of `e^{iτΩ} Y e^{-iτΩ}`: `‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2`.
  have hgrowth : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 :=
    norm_le_of_cellEquation hΩ D hODE
  exact ⟨Y, hC1, hODE, hends.1, hends.2, hcenter, hgrowth⟩

/-- **Lemma A.2.** Let `0 ≤ w < 2π`, let `a : [0,1] → ℝ` be continuous, and let `W(s)` for
`s ∈ [0,1]` be a twice continuously differentiable unitary family with spectrum in
`{e^{-iθ} : θ ∈ [a(s), a(s) + w]}`. Then `W = e^{-iH}` for exactly one Hermitian `H(s)` with
spectrum in `[a(s), a(s) + w]`, `H` is twice continuously differentiable in `s ∈ [0,1]`, and, with
the `κ` of Appendix B, for every `s ∈ [0,1]`,
(i) `‖H'(s)‖ ≤ κ ‖W'(s)‖`, and
(ii) `‖H''(s)‖ ≤ κ ‖W''(s)‖ + ‖W'(s)‖²/cos²(w/4)`. -/
theorem walk_log [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {a : ℝ → ℝ}
    (ha : IsContinuousFamily a) {W : ℝ → 𝕄} (hW : IsUnitaryFamily W 0 1)
    (harc : HasSpectrumInPhaseInterval W a w)
    (hC2 : IsC2Family W) :
    ∃ H : ℝ → 𝕄, IsTimeDepHamiltonian H ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        exp (-I • H s) = W s ∧ HasRealSpectrumIn (H s) (Icc (a s) (a s + w))) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ B : 𝕄, IsHermitian B →
        HasRealSpectrumIn B (Icc (a s) (a s + w)) →
        exp (-I • B) = W s → B = H s) ∧
      IsC2Family H ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ‖∂H s‖ ≤ κ w * ‖∂W s‖ ∧
        ‖∂∂H s‖ ≤ κ w * ‖∂∂W s‖ + ‖∂W s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  classical
  -- The spectral theorem: for each `s`, a Hermitian `H(s)` with spectrum in `[a(s), a(s)+w]`
  -- and `e^{-iH(s)} = W(s)`.
  have hex (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :=
    WalkLog.walk_log_pointwise (a s) w (W s) (hW hs) (harc s hs)
  let H : ℝ → 𝕄 := fun s ↦ if hs : s ∈ Icc (0 : ℝ) 1 then
    (hex s hs).choose else 0
  have hchosen (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (H s).IsHermitian ∧ HasRealSpectrumIn (H s) (Icc (a s) (a s + w)) ∧
        exp (-I • H s) = W s := by
    obtain ⟨hherm, hspec, hexp⟩ := (hex s hs).choose_spec
    exact ⟨by simpa only [H, dif_pos hs] using hherm,
      by simpa only [H, dif_pos hs] using hspec,
      by simpa only [H, dif_pos hs] using hexp⟩
  have hH : IsTimeDepHamiltonian H := fun s hs ↦ (hchosen s hs).1
  have he : ∀ s ∈ Icc (0 : ℝ) 1, exp (-I • H s) = W s := fun s hs ↦ (hchosen s hs).2.2
  have hwindow : ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Icc (a s) (a s + w)) :=
    fun s hs ↦ (hchosen s hs).2.1
  -- `θ ↦ e^{-iθ}` is injective for `θ ∈ [a(s), a(s)+w]`, so `H(s)` is unique.
  have hunique : ∀ s ∈ Icc (0 : ℝ) 1, ∀ B : 𝕄, IsHermitian B →
      HasRealSpectrumIn B (Icc (a s) (a s + w)) →
      exp (-I • B) = W s → B = H s := by
    intro s hs B hB hBw hBe
    exact WalkLog.walk_log_unique hw hB hBw (hH hs) (hwindow s hs)
      (hBe.trans (he s hs).symm)
  -- Fix `s₀`. The paper's "we may take `a(s₀) = -w/2`" is the constant phase
  -- `c = e^{i(a(s₀)+w/2)}`: near `s₀`, `H = a(s₀) + w/2 + i Log(cW)`, so `H` is `C²`, and (A.3)
  -- gives `H' = i∫₀¹ S_u (cW') S_u du` and
  -- `H'' = i∫₀¹ (S_u (cW'') S_u - 2u S_u (cW') S_u (cW') S_u) du`.
  obtain ⟨hcH, hderiv⟩ :=
    WalkLog.walk_log_local_derivatives hw ha hC2 hW harc (fun s hs ↦ hH hs) he hwindow
  refine ⟨H, hH, (fun s hs ↦ ⟨he s hs, hwindow s hs⟩), hunique, hcH, ?_⟩
  intro s₀ hs₀
  let μ := a s₀ + w / 2
  let c := Complex.exp (I * (μ : ℂ))
  -- The spectrum of `H(s₀)` lies within `w/2` of `μ = a(s₀) + w/2`:
  -- `[μ - w/2, μ + w/2] = [a(s₀), a(s₀) + w]`.
  have hcenter : HasRealSpectrumIn (H s₀) (Icc (μ - w / 2) (μ + w / 2)) := by
    convert hwindow s₀ hs₀ using 1
    all_goals
      dsimp [μ]
      congr 1
      all_goals ring
  -- The constant phase changes none of the norms: `‖cA‖ = ‖A‖`.
  have hphase : ‖c‖ = 1 := by
    dsimp [c]
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hnorm (A : 𝕄) : ‖c • A‖ = ‖A‖ := by rw [norm_smul, hphase, one_mul]
  -- `‖S_u‖² ≤ 1/r(v)` at `s₀` and the two quadratures: the norm display, for `cW'` and `cW''`.
  have hbounds := WalkLog.walkLog_integral_norm_bounds (hH hs₀) hw0 hw hcenter
    (c • ∂W s₀) (c • ∂∂W s₀)
  -- Write `e^{iμ} e^{-iH(s₀)}` as `c W(s₀)`.
  dsimp only at hbounds
  rw [he s₀ hs₀] at hbounds
  change ‖WalkLog.walkLogFirstIntegral (c • W s₀) (c • ∂W s₀)‖ ≤ _ ∧
    ‖WalkLog.walkLogSecondIntegral (c • W s₀) (c • ∂W s₀)
      (c • ∂∂W s₀)‖ ≤ _ at hbounds
  obtain ⟨hfirst, hsecond⟩ := hderiv s₀ hs₀
  constructor
  · rw [hfirst, norm_smul, Complex.norm_I, one_mul]
    simpa only [hnorm] using hbounds.1
  · rw [hsecond, norm_smul, Complex.norm_I, one_mul]
    simpa only [hnorm] using hbounds.2

/-- **Lemma A.3.** Let `0 ≤ w < 2π`, and let `Ω(s)` be twice
continuously differentiable for `s ∈ [0,1]`, with every `Ω(s)` Hermitian with eigenvalue
differences of modulus at most `w`. Then `𝒩([Ω,·])Ω'` is continuously differentiable in
`s ∈ [0,1]`, and for every `s ∈ [0,1]` the following hold.
(i) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖Ω'‖²`.
(ii) `‖(𝒩([Ω,·])Ω')'‖ ≤ 𝒩(w) ‖Ω''‖ + 2𝒩'(w) ‖(e^{-iΩ})'‖ ‖Ω'‖ + (𝒩(w) - 𝒩(0)) ‖Ω'‖²`.
Below, `endValue Ω` is `𝒩([Ω,·])Ω'`. -/
theorem end_value
    [NeZero d] {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : ℝ → 𝕄}
    (hC2 : IsC2Family Ω) (hΩ : IsTimeDepHamiltonian Ω) (hwidth : HasWidth Ω w) :
    IsC1Family (endValue Ω) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖∂(endValue Ω) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ + 2 * 𝒩' w * ‖∂Ω s‖ ^ 2 ∧
        ‖∂(endValue Ω) s‖ ≤ 𝒩 w * ‖∂∂Ω s‖ +
          2 * 𝒩' w * ‖∂(fun t ↦ exp (-I • Ω t)) s‖ * ‖∂Ω s‖ + (𝒩 w - 𝒩 0) * ‖∂Ω s‖ ^ 2 := by
  -- With `g = 𝒩` and `A = Ω'`, (A.2) gives the continuous differentiability and (i).
  have hfirst := endValue_part_i hw0 hw hΩ hwidth hC2
  -- The decomposition `Ω' = X + [Ω,Λ]` in (A.4) gives (ii).
  exact ⟨hfirst.1, fun s hs ↦
    ⟨hfirst.2 s hs, endValue_part_ii hw0 hw hΩ hwidth hC2 s hs⟩⟩

/-! ## Appendix B: Constants -/

/-- **Fact B.1.** At width `π`, `c₀ = 1/(2π) - 1/π²`, `𝒩(π) = 1/π²`, `𝒩'(π) = 1/(4π) - 2/π³`, and
`ℰ_π(H) ≤ 0.116 ‖H'‖∞ + 0.143 L + 0.061 ‖H'‖∞²`. -/
theorem constants_at_pi [NeZero d] :
    c₀ π = 1 / (2 * π) - 1 / π ^ 2 ∧ 𝒩 π = 1 / π ^ 2 ∧ 𝒩' π = 1 / (4 * π) - 2 / π ^ 3 ∧
      ∀ (H : ℝ → 𝕄) (L : ℝ), HasLipschitzDerivative H L →
        ℰ π L H ≤ 0.116 * ‖∂H‖∞ + 0.143 * L + 0.061 * ‖∂H‖∞ ^ 2 := by
  exact ⟨c₀_pi, multiplier_values_at_pi.1, multiplier_values_at_pi.2, ℰ_pi_le⟩

/-- **Fact B.2.** As `w → 2π`, with `ϑ = 2π - w`, `c₀ κ ∼ (1/24 + 𝒩(w)) κ ∼ ϑ⁻²` and
`c₂ ∼ (8/π + 5π/2 + 2) ϑ⁻³`, so every coefficient of `ℰ̃_w(W)` is `O(ϑ⁻³)`. -/
theorem constants_near_two_pi :
    (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 2) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) ~[𝓝[>] 0] (fun ϑ ↦ (8 / π + 5 * π / 2 + 2) / ϑ ^ 3) ∧
      (fun ϑ ↦ c₀ (2 * π - ϑ) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ (1 / 24 + 𝒩 (2 * π - ϑ)) * κ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) ∧
      (fun ϑ ↦ c₂ (2 * π - ϑ)) =O[𝓝[>] 0] (fun ϑ ↦ 1 / ϑ ^ 3) := by
  exact ⟨free_arc_equivalents.1, free_arc_equivalents.2.1,
    free_arc_equivalents.2.2, free_arc_isBigO.1,
    free_arc_isBigO.2.1, free_arc_isBigO.2.2⟩

end RoundedClocks
