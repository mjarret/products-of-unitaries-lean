# Rounded clocks

Lean proofs of every numbered statement of Michael Jarret's *Rounded clocks and finite precision: a
transfer principle between continuous and discrete quantum dynamics*, and of its Theorems A and B.

The paper compares finite products of unitary matrices with continuous Schrödinger evolutions. It
proves fine-step error bounds for midpoint products with truncated entries, a unit-step comparison
for Hamiltonians with Lipschitz derivative, the corresponding comparison for products of given
unitaries through a Hermitian logarithm, and transfer bounds for leakage between spectral
subspaces. All matrix norms are operator norms.

Continuous adiabatic theorems are not formalized. Where the paper assumes a continuous leakage
bound such as `‖(1 - Q) U(T) P‖ ≤ C / T`, the Lean statement takes it as a hypothesis.

## Reading the statements

Start with the [statement index](THEOREMS.md). It lists each numbered statement of the paper, and
Theorems A and B, with the Lean declaration that states it.

The statements are in `RoundedClocks/`, one file per part of the paper, and use only the terms
defined in [RoundedClocks/Definitions.lean](RoundedClocks/Definitions.lean). Those definitions
follow the paper's wording and notation: `H` is a time-dependent Hamiltonian, `evolution H T` is its
evolution over time `T`, `roundedEvolution H T` is the evolution of `H(⌊t+1/2⌋/T)`, `stepProduct H T`
is the `T`-step product, `∂H` is the derivative of `H` on `[0,1]`, `‖f‖∞` is the supremum of `‖f‖`
on `[0,1]`, `A†` is the conjugate transpose, and `𝒩`, `c₀`, `c₁`, `c₂`, `κ`, `ℰ`, and `ℰtilde` are
the multiplier and constants of the paper. Each statement's docstring gives the paper's statement in
words.

The proofs are in `UnitaryProducts/`. The file
[RoundedClocks/Bridge.lean](RoundedClocks/Bridge.lean) identifies each definition of the paper with
the form the proofs use.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib dependency are pinned to version 4.28.0. The dependency manifest records
exact revisions. The build enables Mathlib's standard linter set.

## Checking the build

After `lake build`, three scripts print what the build establishes:

```sh
lake env lean scripts/Audit.lean       # the axioms of every declaration
lake env lean scripts/Lint.lean        # the Batteries and Mathlib environment linters
lake env lean scripts/HeadTypes.lean   # the full statement of every indexed declaration
```

Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## License and citation

The code is released under the [Apache License 2.0](LICENSE).
Citation metadata is provided in [CITATION.cff](CITATION.cff).
