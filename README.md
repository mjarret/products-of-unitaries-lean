# Rounded clocks

Lean 4 proofs of the results of Michael Jarret's *Rounded clocks and finite precision: a transfer
principle between continuous and discrete quantum dynamics*: every numbered theorem, lemma,
proposition, example, remark, and fact, the displayed equations (2.3)–(2.5), and Theorems A and B
of the introduction.

The paper compares finite products of unitary matrices with continuous Schrödinger evolutions. It
proves fine-step error bounds for midpoint products with truncated entries, a unit-step comparison
for Hamiltonians with Lipschitz derivative, the corresponding comparison for products of given
unitaries through a Hermitian logarithm, and transfer bounds for leakage between spectral
subspaces. All matrix norms are operator norms.

## Layout

The library follows the paper. Each part of the paper has one file holding its statements and
proofs, and a folder of the same name holding the supporting lemmas of those proofs.

| File | Paper |
| --- | --- |
| [RoundedClocks/Definitions.lean](RoundedClocks/Definitions.lean) | the objects and notation the statements use |
| [RoundedClocks/Citations.lean](RoundedClocks/Citations.lean) | the results the paper cites from the literature |
| [RoundedClocks/Introduction.lean](RoundedClocks/Introduction.lean) | Theorems A and B |
| [RoundedClocks/Preliminaries.lean](RoundedClocks/Preliminaries.lean) | Section 2 |
| [RoundedClocks/FineSteps.lean](RoundedClocks/FineSteps.lean) | Section 3 |
| [RoundedClocks/UnitSteps.lean](RoundedClocks/UnitSteps.lean) | Section 4 |
| [RoundedClocks/Examples.lean](RoundedClocks/Examples.lean) | Section 5 |
| [RoundedClocks/Appendix.lean](RoundedClocks/Appendix.lean) | Appendices A and B |

The [statement index](THEOREMS.md) lists each result of the paper with the declaration that states
it. Each statement's docstring gives the paper's statement in words. The proofs take the paper's
steps in the paper's order.

## Cited results

The paper cites Dieudonné's *Foundations of Modern Analysis*, Bhatia's *Matrix Analysis*, and the
NIST Digital Library of Mathematical Functions. Each cited result is a proposition in
[RoundedClocks/Citations.lean](RoundedClocks/Citations.lean), with the source's statement quoted
verbatim in its docstring and specialized to finite-dimensional complex matrices where that is all
the paper uses. A statement whose proof uses a cited result takes that proposition as an explicit
hypothesis, and its docstring begins "Assuming …". No cited result is an axiom.

Continuous adiabatic theorems are not formalized. Where the paper assumes a continuous leakage bound
such as `‖(1 - Q) U(T) P‖ ≤ C / T`, the Lean statement takes it as a hypothesis.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib are pinned to version 4.28.0; the manifest records exact revisions.

## Checking the build

After `lake build`, two scripts print what the build establishes:

```sh
lake env lean scripts/Audit.lean       # the axioms of every declaration
lake env lean scripts/HeadTypes.lean   # the full statement of every indexed declaration
```

Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## License and citation

The code is released under the [Apache License 2.0](LICENSE). Citation metadata is in
[CITATION.cff](CITATION.cff).
