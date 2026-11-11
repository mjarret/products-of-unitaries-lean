# Products of unitaries

Lean proofs accompanying Michael Jarret's *Products of unitaries as continuous evolutions at finite precision*.

The library compares finite products of unitary matrices with continuous Schrödinger evolutions.
It proves fine-step error bounds for truncated midpoint samples, a unit-step comparison for
Hamiltonians with Lipschitz derivative, the corresponding walk comparison through a logarithm,
and transfer bounds for leakage between spectral subspaces. The examples cover gap-adapted
schedules, a precessing spin (including endpoint-coefficient optimality), and eigenvalue
crossings. All matrix norms are operator norms.

The Jansen–Ruskai–Seiler continuous adiabatic bound is an input hypothesis. Its continuous theorem
is not formalized here. The formalized results transfer that bound to the products under the
hypotheses stated in Lean.

## Build

Install Lean through [elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib dependency are pinned to version 4.28.0. The dependency manifest records
exact revisions. The build enables Mathlib's standard linter set.

## Reading the proofs

Start with the [statement index](THEOREMS.md), which gives each paper number, label,
declaration, and source location. [PAPER_MAP.tsv](PAPER_MAP.tsv) contains the same mapping
in tab-separated form. [CLAIMS.md](CLAIMS.md) maps the paper's unnumbered mathematical
claims to their supporting declarations or external references.

The numbered proof heads are under `PaperProof`, with definitions under `Paper` and
unnumbered steps under `Prose`. Supporting mathematics is organized under `Matrix`,
`Evolution`, `Spectral`, `Approximation`, `Corrector`, `Comparison`, and `Walks`.
Follow each index link for the full hypotheses, statement, and proof.

## Checking the build

After `lake exe cache get && lake build`, three scripts print what the build establishes:

```sh
lake env lean scripts/Audit.lean       # the axioms of every indexed statement
lake env lean scripts/Lint.lean        # the Batteries and Mathlib environment linters
lake env lean scripts/HeadTypes.lean   # the full statement of every indexed declaration
```

Every indexed statement depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Conventions

- **Statements.** Every numbered statement of the paper, Theorems A and B, and each unnumbered claim
  the paper relies on has a row in [THEOREMS.md](THEOREMS.md). Each numbered head's docstring
  gives the paper's number and explains the correspondence between the Lean statement and
  the paper's formulation. Supporting docstrings describe the corresponding calculation.
- **Hypotheses.** Where a proof does not use one of the paper's standing hypotheses (for example
  `d ≥ 1`), the Lean statement omits it and the docstring says so.
- **Inputs.** Continuous adiabatic theorems are not formalized. The two Jansen–Ruskai–Seiler
  examples take the bound `‖(1 - Q) U(T) P‖ ≤ C / T` as a hypothesis, and the other transfer
  statements bound the product's leakage by the continuous leakage plus the comparison error.
- **Norms.** Matrices carry the ℓ² operator norm (`Matrix.Norms.L2Operator`); the local
  instance `matrixCStarAlgebra` (a C⋆-algebra structure for `cfc`) is built from it.

## License and citation

The code is released under the [Apache License 2.0](LICENSE).
Citation metadata is provided in [CITATION.cff](CITATION.cff).
