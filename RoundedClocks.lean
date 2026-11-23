/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Citations
public import RoundedClocks.Introduction
public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps
public import RoundedClocks.UnitSteps
public import RoundedClocks.Examples
public import RoundedClocks.Appendix

/-!
# Rounded clocks

Lean proofs of the numbered statements of Michael Jarret, *Rounded clocks and finite precision: a
transfer principle between continuous and discrete quantum dynamics*.

* `THEOREMS.md` lists each statement of the paper with the declaration that states it, and gives
  the Lean name of each symbol of the paper.
* `RoundedClocks/Definitions.lean` defines the paper's terms.
* `RoundedClocks/Citations.lean` states the results that the paper cites from the literature. The
  theorems take them as hypotheses.
* The other files follow the paper: `Introduction` (Theorems A and B), `Preliminaries`
  (Section 2), `FineSteps` (Section 3, Evolutions as products), `UnitSteps` (Section 4, Products as
  evolutions), `Examples` (Section 5), and `Appendix` (Appendices A and B). Each has a folder of
  the same name with the supporting lemmas of its proofs.
-/
