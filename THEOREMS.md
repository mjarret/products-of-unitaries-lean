# Statement index

The statements of Michael Jarret, *Rounded clocks and finite precision: a transfer principle between
continuous and discrete quantum dynamics* (arXiv:2610.06541), each with the Lean declaration that
states it. The first table gives the Lean name of each symbol of the paper. The second lists the
statements, with the results from the literature that each one assumes.

## Symbols

Each term is defined, in the paper's words, in
[RoundedClocks/Definitions.lean](RoundedClocks/Definitions.lean), under the declaration named in
the last column. Matrix products are written with `*`, and `exp` is the matrix exponential.

| Paper | Lean | Declaration |
| --- | --- | --- |
| `A†`, the conjugate transpose | `A†` | notation for `star` |
| `H'`, `H''`, derivatives in `[0,1]`, one-sided at the ends | `∂H`, `∂∂H` | `deriv01` |
| `‖H'‖∞ = sup_{s∈[0,1]} ‖H'(s)‖` | `‖∂H‖∞` | `supNorm` |
| `A` is Hermitian, `A` is unitary, `P` is an orthogonal projector | `IsHermitian A`, `IsUnitary A`, `IsOrthogonalProjector P` | `IsHermitian`, `IsUnitary`, `IsOrthogonalProjector` |
| `H(t)` with `t ∈ [a,b]` is regulated, piecewise constant, Hermitian | `IsRegulated H a b`, `IsPiecewiseConstant H a b`, `IsHermitianFamily H a b` | `IsRegulated`, `IsPiecewiseConstant`, `IsHermitianFamily` |
| continuously differentiable for `t ∈ [a,b]` | `IsC1FamilyOn A a b` | `IsC1FamilyOn` |
| unitary family | `IsUnitaryFamily A a b` | `IsUnitaryFamily` |
| `A(s)` for `s ∈ [0,1]` is continuous, continuously differentiable, twice continuously differentiable | `IsContinuousFamily A`, `IsC1Family A`, `IsC2Family A` | `IsContinuousFamily`, `IsC1Family`, `IsC2Family` |
| `H` is a time-dependent Hamiltonian | `IsTimeDepHamiltonian H` | `IsTimeDepHamiltonian` |
| `H` is a regulated time-dependent Hamiltonian | `IsRegulatedTimeDepHamiltonian H` | `IsRegulatedTimeDepHamiltonian` |
| `G` generates the evolution `V` for `t ∈ [a,b]`, equation (2.1) | `Generates G V a b` | `Generates` |
| `U(T)`, where `U` is the evolution of `H` over time `T` | `evolution H T T` | `evolution` |
| `V(T)`, where `V` is the evolution of `H(⌊t+1/2⌋/T)` | `roundedEvolution H T T` | `roundedEvolution` |
| `W_T`, the `T`-step product of `H` | `stepProduct H T` | `stepProduct` |
| `W((T-1)/T) ⋯ W(0)` for a family `W` | `sampleProduct W T` | `sampleProduct` |
| `A(n-1) ⋯ A(1) A(0)` | `orderedProduct n A` | `orderedProduct` |
| leakage `‖(1 - Q) W P‖` | `‖(1 - Q) * W * P‖` |  |
| `P̃`, `Q̃` | `P'`, `Q'` |  |
| a band `{λ : a < λ < b}` of a Hermitian `A`, its spectral gap, its spectral projector | `IsBand A a b`, `spectralGap A a b`, `bandProjector A a b` | `IsBand`, `spectralGap`, `bandProjector` |
| a band `{e^{-iθ} : a < θ < b}` of a unitary `A`, its eigenphase gap, its spectral projector | `IsArcBand A a b`, `eigenphaseGap A a b`, `arcBandProjector A a b` | `IsArcBand`, `eigenphaseGap`, `arcBandProjector` |
| `{λ : a < λ < b}`, `{e^{-iθ} : a < θ < b}` | `interval a b`, `arc a b` | `interval`, `arc` |
| spectrum in `S` | `HasRealSpectrumIn A S` | `HasRealSpectrumIn` |
| a band of a unitary family with endpoints `a(s)`, `b(s)` | `IsArcBandFamily A a b` | `IsArcBandFamily` |
| the spectral projector of `A` for its eigenvalues in a set `S` | `spectralProjector A S` | `spectralProjector` |
| the number of eigenvalues of `A` in `S`, with multiplicity | `eigenvalueCount A S` | `eigenvalueCount` |
| `A^{(F)}`, and `H^{(F)}` for a function `H` | `entrywise F A`, `entrywiseFamily F H` | `entrywise`, `entrywiseFamily` |
| bit truncation `[x]_k` | `bitTruncation k x` | `bitTruncation` |
| the truncation `H^{(k)}` | `truncation k H` | `truncation` |
| `σ_k` | `sparsity k H` | `sparsity` |
| `√2 σ_k 2^{-k}` | `√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹` |  |
| checkpoints `0 = s₀ ≤ ⋯ ≤ s_N = 1`, strict when `<` | `IsCheckpoints N s`, `IsStrictCheckpoints N s` | `IsCheckpoints`, `IsStrictCheckpoints` |
| midpoint error at most `ε` for `H` | `HasMidpointError H N s ε` | `HasMidpointError` |
| the midpoint product of `A` over time `T` on `s₀, …, s_N` | `midpointProduct A T N s` | `midpointProduct` |
| `max_j sup_{s_j<s<s_{j+1}} ‖H(s) - H^{(F)}(s_{j+1/2})‖` of Theorem 3.6 | `midpointApproximationError F H N s` | `midpointApproximationError` |
| `I_s = [min S_s, max S_s]` of Remark 3.8 | `bandHull A a b` | `bandHull` |
| bands at `s ∈ {0,1}`, eigenvalues within `ε` of `I_s` | `HasEndpointBands A a b`, `nearBand A a b ε` | `HasEndpointBands`, `nearBand` |
| equal rank | `HasEqualRank A B` | `HasEqualRank` |
| `H` is differentiable and `H'` has Lipschitz constant `L` | `HasLipschitzDerivative H L` | `HasLipschitzDerivative` |
| eigenvalue differences of modulus at most `w`: one matrix, the samples `H(j/T)`, every `H(s)` | `HasEigenvalueDifferences A w`, `HasSampleWidth H T w`, `HasWidth H w` | `HasEigenvalueDifferences`, `HasSampleWidth`, `HasWidth` |
| `𝒩(x)`, `𝒩'(x)` | `𝒩 x`, `𝒩' x` | `𝒩`, `𝒩'` |
| `𝒩([Ω,·])E` | `𝒩ad Ω E` | `𝒩ad` |
| `𝒩([Ω(s),·])Ω'(s)` of Lemma A.3 | `endValue Ω s` | `endValue` |
| the jump `Δ_j` of Theorem 4.2 | `Δ H T j` | `Δ` |
| `c₀`, `c₁`, `c₂`, `κ` at width `w` | `c₀ w`, `c₁ w`, `c₂ w`, `κ w` | `c₀`, `c₁`, `c₂`, `κ` |
| `ℰ_w(H)`, with `L` as in Theorem 4.2 | `ℰ w L H` | `ℰ` |
| `ℰ̃_w(W)` | `ℰtilde w W` | `ℰtilde` |
| the Hermitian `H(s)` with `e^{-iH(s)} = W(s)` and spectrum in `(α(s), α(s) + 2π)` | `IsLogarithm W α H` | `IsLogarithm` |
| `spec W(s) ⊂ {e^{-iθ} : a(s) ≤ θ ≤ a(s) + w}`, equation (4.7) | `HasSpectrumInPhaseInterval W a w` | `HasSpectrumInPhaseInterval` |
| `Γ(x)` and `c_p` of Example 5.1 | `interpolationGap H₀ H₁ x`, `gapNormalization H₀ H₁ p` | `interpolationGap`, `gapNormalization` |
| the spectral projector of `A` for its least eigenvalue (Example 5.1) | `leastEigenvalueProjector A` | `leastEigenvalueProjector` |
| a spectral projector of `A` for one eigenvalue (Example 5.3) | `IsOneEigenvalueProjector P A` | `IsOneEigenvalueProjector` |
| `[Ω,·]`, and the `n`-fold commutator `[Ω,·]ⁿ` | `adL Ω`, `adL Ω ^ n` | `adL` |
| `∑_k [Ω,·]^k[Ω′,[Ω,·]^{n−1−k}A]` | `powDeriv (adL Ω) (adL Ω') n A` | `powDeriv` |
| `g([Ω,·])A = ∑ gₙ [Ω,·]ⁿ A` | `∑' n, (g n : ℂ) • (adL Ω ^ n) A` |  |

## Statements

Each row gives a statement of the paper and the declaration that states it. The first column is
the paper's number of a numbered statement or of Theorem A or B, and `unnumbered` for a displayed
equation or a claim of the running text. The second column is the label of the statement or
equation in the paper's source. The column *Assumes* lists the results from the literature that
the declaration takes as hypotheses. They are stated in
[RoundedClocks/Citations.lean](RoundedClocks/Citations.lean), where Dieudonné is *Foundations of
Modern Analysis* and Bhatia is *Matrix Analysis*. The partial fractions DLMF 4.22.3 and 4.22.5 of
the NIST Digital Library of Mathematical Functions are proved from Mathlib in
[RoundedClocks/Appendix/PositiveSeries.lean](RoundedClocks/Appendix/PositiveSeries.lean).

| Number | Label | Declaration | File:line | Statement | Assumes |
| --- | --- | --- | --- | --- | --- |
| A | `introthm:unit` | `RoundedClocks.theorem_A` | [RoundedClocks/Introduction.lean:42](RoundedClocks/Introduction.lean#L42) | Theorem A (unit steps at width π) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| B | `introthm:fine-count` | `RoundedClocks.theorem_B` | [RoundedClocks/Introduction.lean:65](RoundedClocks/Introduction.lean#L65) | Theorem B (fine steps with truncated entries) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 2.1 | `def:regulated` | `RoundedClocks.IsRegulated` | [RoundedClocks/Definitions.lean:106](RoundedClocks/Definitions.lean#L106) | Definition 2.1 (regulated functions) | none |
| unnumbered | `eq:evolution` | `RoundedClocks.generates_exists` | [RoundedClocks/Preliminaries.lean:69](RoundedClocks/Preliminaries.lean#L69) | Section 2, after equation (2.1): a regulated Hermitian family generates an evolution | Dieudonné (10.5.4), (10.6.3) |
| unnumbered | `eq:evolution` | `RoundedClocks.generates_evolutionOf` | [RoundedClocks/Preliminaries.lean:91](RoundedClocks/Preliminaries.lean#L91) | Section 2, after equation (2.1): it generates `evolutionOf G T` | Dieudonné (10.5.4), (10.6.3) |
| unnumbered | `eq:evolution` | `RoundedClocks.generates_unique` | [RoundedClocks/Preliminaries.lean:100](RoundedClocks/Preliminaries.lean#L100) | Section 2, after equation (2.1): it generates at most one evolution | Dieudonné (10.5.4) |
| 2.2 | `thm:comparison` | `RoundedClocks.comparison` | [RoundedClocks/Preliminaries.lean:133](RoundedClocks/Preliminaries.lean#L133) | Theorem 2.2 (Comparison of evolutions) | Dieudonné (7.6.1) |
| unnumbered | `eq:duhamel` | `RoundedClocks.duhamel` | [RoundedClocks/Preliminaries.lean:251](RoundedClocks/Preliminaries.lean#L251) | Equation (2.3) (Duhamel's bound) | Dieudonné (7.6.1) |
| unnumbered | `eq:piecewise-product` | `RoundedClocks.piecewise_product` | [RoundedClocks/Preliminaries.lean:306](RoundedClocks/Preliminaries.lean#L306) | Equation (2.4) (evolution of a piecewise-constant family) | none |
| 2.3 | `def:unit-product` | `RoundedClocks.stepProduct` | [RoundedClocks/Definitions.lean:174](RoundedClocks/Definitions.lean#L174) | Definition 2.3 (`T`-step product) | none |
| unnumbered | `eq:rounded` | `RoundedClocks.roundedEvolution_end` | [RoundedClocks/Preliminaries.lean:320](RoundedClocks/Preliminaries.lean#L320) | Equation (2.5) (rounded-clock identity) | Dieudonné (10.5.4) |
| 2.4 | `prop:transfer` | `RoundedClocks.transfer` | [RoundedClocks/Preliminaries.lean:433](RoundedClocks/Preliminaries.lean#L433) | Proposition 2.4 (Transfer of leakage bounds) | none |
| 2.5 | `def:spectral-window` | `RoundedClocks.IsBand` | [RoundedClocks/Definitions.lean:191](RoundedClocks/Definitions.lean#L191) | Definition 2.5 (bands, gaps, spectral projectors); its other parts are `spectralGap`, `IsArcBand`, `eigenphaseGap`, `spectralProjector`, `IsArcBandFamily`, and `eigenvalueCount` | none |
| 3.1 | `def:level-function` | `RoundedClocks.entrywise` | [RoundedClocks/Definitions.lean:277](RoundedClocks/Definitions.lean#L277) | Definition 3.1 (`A^{(F)}`); for functions, `entrywiseFamily` | none |
| 3.2 | `ex:truncation-bits` | `RoundedClocks.truncation_bits` | [RoundedClocks/FineSteps.lean:65](RoundedClocks/FineSteps.lean#L65) | Example 3.2 (Bits) | none |
| 3.3 | `def:oscillation-checkpoints` | `RoundedClocks.HasMidpointError` | [RoundedClocks/Definitions.lean:310](RoundedClocks/Definitions.lean#L310) | Definition 3.3 (midpoint error) | none |
| 3.4 | `lem:oscillation-partition` | `RoundedClocks.exists_checkpoints` | [RoundedClocks/FineSteps.lean:95](RoundedClocks/FineSteps.lean#L95) | Lemma 3.4 (checkpoints exist) | Dieudonné (7.6.1) |
| 3.5 | `def:midpoint-product` | `RoundedClocks.midpointProduct` | [RoundedClocks/Definitions.lean:325](RoundedClocks/Definitions.lean#L325) | Definition 3.5 (midpoint product) | none |
| 3.6 | `thm:fine-steps` | `RoundedClocks.fine_steps` | [RoundedClocks/FineSteps.lean:138](RoundedClocks/FineSteps.lean#L138) | Theorem 3.6 (fine steps) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| unnumbered | `eq:fine-bits` | `RoundedClocks.fine_steps_bits` | [RoundedClocks/FineSteps.lean:214](RoundedClocks/FineSteps.lean#L214) | Equation (3.1) (fine steps with bit truncation) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| unnumbered | `eq:fine-bits` | `RoundedClocks.exists_bits` | [RoundedClocks/FineSteps.lean:242](RoundedClocks/FineSteps.lean#L242) | Section 3.2, after equation (3.1): the truncation error is arbitrarily small | none |
| 3.7 | `cor:jrs` | `RoundedClocks.jrs_leakage` | [RoundedClocks/FineSteps.lean:275](RoundedClocks/FineSteps.lean#L275) | Example 3.7 (Bits) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 3.8 | `rem:truncated-endpoints` | `RoundedClocks.truncated_endpoints` | [RoundedClocks/FineSteps.lean:320](RoundedClocks/FineSteps.lean#L320) | Remark 3.8 (truncated endpoint projectors) | Bhatia III.2.6, Exercise VII.1.11, VII.3.1 |
| 4.1 | `def:unit-objects` | `RoundedClocks.𝒩` | [RoundedClocks/Definitions.lean:385](RoundedClocks/Definitions.lean#L385) | Definition 4.1 (the multiplier `𝒩`); `𝒩([Ω,·])E` is `𝒩ad` | none |
| 4.2 | `thm:clocks` | `RoundedClocks.rounded_clock_comparison` | [RoundedClocks/UnitSteps.lean:80](RoundedClocks/UnitSteps.lean#L80) | Theorem 4.2 (comparison up to the jumps) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 4.3 | `ex:unit-sharp` | `RoundedClocks.unit_sharp` | [RoundedClocks/UnitSteps.lean:286](RoundedClocks/UnitSteps.lean#L286) | Example 4.3 (the order `1/T` is attained) | Dieudonné (10.5.4), (10.6.3) |
| 4.4 | `thm:jumps` | `RoundedClocks.rounded_clock_bound` | [RoundedClocks/UnitSteps.lean:373](RoundedClocks/UnitSteps.lean#L373) | Theorem 4.4, equation (4.6) (the comparison) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 4.5 | `ex:unit-transfer` | `RoundedClocks.unit_transfer` | [RoundedClocks/UnitSteps.lean:406](RoundedClocks/UnitSteps.lean#L406) | Example 4.5 (Bits) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 4.6 | `cor:walks` | `RoundedClocks.unitary_products` | [RoundedClocks/UnitSteps.lean:505](RoundedClocks/UnitSteps.lean#L505) | Theorem 4.6, equation (4.8) (products of given unitaries) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 4.7 | `cor:walk-leakage` | `RoundedClocks.walk_leakage` | [RoundedClocks/UnitSteps.lean:598](RoundedClocks/UnitSteps.lean#L598) | Theorem 4.7 (leakage of a product of given unitaries) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| 5.1 | `ex:gap-adapted` | `RoundedClocks.gap_adapted` | [RoundedClocks/Examples.lean:75](RoundedClocks/Examples.lean#L75) | Example 5.1 (Gap-adapted schedules) | Dieudonné (7.6.1), (10.5.4), (10.6.3); Bhatia III.2.6 |
| 5.2 | `ex:precessing-spin` | `RoundedClocks.precessing_spin` | [RoundedClocks/Examples.lean:204](RoundedClocks/Examples.lean#L204) | Example 5.2 (A precessing spin) | Dieudonné (10.5.4), (10.6.3) |
| 5.3 | `ex:crossings` | `RoundedClocks.crossings` | [RoundedClocks/Examples.lean:306](RoundedClocks/Examples.lean#L306) | Example 5.3 (Eigenvalue crossings) | Dieudonné (7.6.1), (10.5.4), (10.6.3) |
| unnumbered | `eq:series-bound` | `RoundedClocks.series_bound` | [RoundedClocks/Appendix.lean:104](RoundedClocks/Appendix.lean#L104) | Equation (A.1) (series in the commutator) | none |
| unnumbered | `eq:series-derivative` | `RoundedClocks.series_derivative` | [RoundedClocks/Appendix.lean:118](RoundedClocks/Appendix.lean#L118) | Equation (A.2) (derivative of a series in the commutator) | none |
| A.1 | `lem:cell` | `RoundedClocks.cell` | [RoundedClocks/Appendix.lean:163](RoundedClocks/Appendix.lean#L163) | Lemma A.1 (the correction) | none |
| A.2 | `lem:walk-log` | `RoundedClocks.walk_log` | [RoundedClocks/Appendix.lean:201](RoundedClocks/Appendix.lean#L201) | Lemma A.2 (the Hermitian logarithm) | none |
| A.3 | `lem:end-value` | `RoundedClocks.end_value` | [RoundedClocks/Appendix.lean:285](RoundedClocks/Appendix.lean#L285) | Lemma A.3 (derivative of `𝒩([Ω,·])Ω'`) | none |
| B.1 | `fact:pi` | `RoundedClocks.constants_at_pi` | [RoundedClocks/Appendix.lean:303](RoundedClocks/Appendix.lean#L303) | Fact B.1 (constants at width π) | none |
| B.2 | `fact:arc` | `RoundedClocks.constants_near_two_pi` | [RoundedClocks/Appendix.lean:311](RoundedClocks/Appendix.lean#L311) | Fact B.2 (constants as the width tends to 2π) | none |
