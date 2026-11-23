# Rounded clocks

Lean 4 proofs of the results of Michael Jarret's *Rounded clocks and finite precision: a transfer
principle between continuous and discrete quantum dynamics*
([arXiv:2610.06541](https://arxiv.org/abs/2610.06541)): every numbered theorem, lemma,
proposition, example, remark, and fact, the displayed equations (2.3)–(2.5), (3.1), (A.1), and
(A.2), and Theorems A and B of the introduction. The statement numbers are those of the paper's
statement headers, each of which links to its Lean declaration here.

The paper compares finite products of unitary matrices with continuous Schrödinger evolutions. It
proves fine-step error bounds for midpoint products with truncated entries, a unit-step comparison
for Hamiltonians with Lipschitz derivative, the corresponding comparison for products of given
unitaries through a Hermitian logarithm, and transfer bounds for leakage between spectral
subspaces. All matrix norms are operator norms.

## Where to start

The [statement index](THEOREMS.md) gives the Lean name of each symbol of the paper, and lists each
statement of the paper with the declaration that states it and the results from the literature
that it assumes. Each statement's docstring gives the paper's statement in words. The proofs take
the paper's steps in the paper's order.

## Layout

The library follows the paper. Each part of the paper has one file holding its statements and
proofs, and a folder of the same name holding the supporting lemmas of those proofs.

| File | Paper |
| --- | --- |
| [RoundedClocks/Definitions.lean](RoundedClocks/Definitions.lean) | the terms and notation of the statements |
| [RoundedClocks/Citations.lean](RoundedClocks/Citations.lean) | the results the paper cites from the literature |
| [RoundedClocks/Introduction.lean](RoundedClocks/Introduction.lean) | Section 1, Discretizing unitary evolution: Theorems A and B |
| [RoundedClocks/Preliminaries.lean](RoundedClocks/Preliminaries.lean) | Section 2, Preliminaries |
| [RoundedClocks/FineSteps.lean](RoundedClocks/FineSteps.lean) | Section 3, Evolutions as products |
| [RoundedClocks/UnitSteps.lean](RoundedClocks/UnitSteps.lean) | Section 4, Products as evolutions |
| [RoundedClocks/Examples.lean](RoundedClocks/Examples.lean) | Section 5, Examples |
| [RoundedClocks/Appendix.lean](RoundedClocks/Appendix.lean) | Appendix A, Lemmas behind the unit-step comparisons, and Appendix B, Constants |

## Cited results

The paper cites Dieudonné's *Foundations of Modern Analysis*, Bhatia's *Matrix Analysis*, and the
NIST Digital Library of Mathematical Functions (DLMF). Each result used as an external input is a
proposition in [RoundedClocks/Citations.lean](RoundedClocks/Citations.lean), with the source's
statement quoted in its docstring and specialized to finite-dimensional complex matrices where
that is all the paper uses. A statement whose proof uses a cited result takes that proposition as
an explicit hypothesis, and its docstring says "Assuming …". No cited result is an axiom. The
statement index lists the propositions that each statement assumes.

| Proposition | Source | Content | Used for |
| --- | --- | --- | --- |
| `Dieudonne_7_6_1` | Dieudonné (7.6.1) | a regulated function is a uniform limit of step functions | regulated functions are bounded and integrable (Section 2); Lemma 3.4 |
| `Dieudonne_10_5_4` | Dieudonné (10.5.4) | a linear differential equation with regulated coefficients has at most one solution | an evolution is unique and unitary (Section 2); equation (2.5) |
| `Dieudonne_10_6_3` | Dieudonné (10.6.3), with the remark (10.4.6) | such an equation has a solution | an evolution exists (Section 2) |
| `Bhatia_Corollary_III_2_6` | Bhatia, Corollary III.2.6 | Weyl's perturbation theorem | Remark 3.8 and Example 5.1 |
| `Bhatia_Exercise_VII_1_11` | Bhatia, Exercise VII.1.11 | `‖P - Q‖ = ‖(1 - Q) P‖` for orthogonal projectors of equal rank | Remark 3.8 |
| `Bhatia_Theorem_VII_3_1` | Bhatia, Theorem VII.3.1 | the Davis–Kahan `sin Θ` theorem | Remark 3.8 |

Six results are explicit hypotheses. DLMF 4.22.3 and 4.22.5, the partial fractions of the
cotangent and cosecant, are proved from Mathlib's cotangent series in
[RoundedClocks/Appendix/PositiveSeries.lean](RoundedClocks/Appendix/PositiveSeries.lean).
The termwise differentiation used from Dieudonné (8.6.4) is proved from Mathlib in
[RoundedClocks/Appendix/SeriesDerivative.lean](RoundedClocks/Appendix/SeriesDerivative.lean).
The fundamental theorem used from Dieudonné, Section 8.7 is proved from Mathlib's theorem for
derivatives off a countable set in
[RoundedClocks/Preliminaries/EvolutionComparisonCalculus.lean](RoundedClocks/Preliminaries/EvolutionComparisonCalculus.lean);
regulated integrability uses Dieudonné (7.6.1). The least-eigenvalue perturbation bound used
in Theorems 4.6 and 4.7 follows from Mathlib's order and spectrum lemmas; the general ordered
eigenvalue bound is a hypothesis where used.

## What is not formalized

Continuous adiabatic theorems are not formalized. Where the paper assumes a continuous leakage
bound such as `‖(1 - Q) U(T) P‖ ≤ C / T`, the Lean statement takes it as a hypothesis.

Claims of the running text are formalized only where a listed statement needs them. In particular,
the following are not formalized:

* the optimality of `c₀` at every width in `(0, 2π)`, argued after Example 5.2 (Example 5.2(i)
  gives the limit at width `π`);
* the Jansen–Ruskai–Seiler coefficient (3.2), and the adiabatic theorems of Guo and An and of Avron
  and Elgart that Section 5 transfers;
* the necessity of oddness for `d ≥ 2` in Section 3.1;
* the quadrature reading of the comparison for commuting values in Section 4.1.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib are pinned to version 4.28.0; the manifest records the exact commits.

## Checking the build

After `lake build`, these scripts print what the build establishes:

```sh
lake env lean scripts/Axioms.lean       # the axioms that the library depends on
lake env lean scripts/Statements.lean   # every statement of the index, as Lean prints it
lake env lean scripts/DeadCode.lean     # reachability from indexed statements and definitions
```

Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. This script
checks docstrings for 40 primary declarations and the eight companion definitions named in the
index rows. The dependency check keeps the three explicit computation helpers
`matrixEntryCLM_apply`, `walk_evalCLM_apply`, and `summable_norm_powDeriv`.

## License and citation

The code is released under the [Apache License 2.0](LICENSE). Citation metadata is in
[CITATION.cff](CITATION.cff).
