/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/

import RoundedClocks
import Lean.Util.CollectAxioms

/-!
# Axiom check

## Main results

Check that every statement of the index `THEOREMS.md` has a docstring, and that every declaration
of the library, including private and generated declarations, depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## References

Michael Jarret, *Rounded clocks and finite precision: a transfer principle between continuous and
discrete quantum dynamics*.
-/

-- Traverse the entire library, including private and generated declarations.
set_option maxHeartbeats 16000000 in
-- Inspect the transitive axiom dependencies of every declaration in the library.
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let statements : List Name := [
    `RoundedClocks.theorem_A,
    `RoundedClocks.theorem_B,
    `RoundedClocks.IsRegulated,
    `RoundedClocks.generates_exists, `RoundedClocks.generates_evolutionOf,
    `RoundedClocks.generates_unique,
    `RoundedClocks.comparison,
    `RoundedClocks.duhamel,
    `RoundedClocks.piecewise_product,
    `RoundedClocks.roundedEvolution_end,
    `RoundedClocks.stepProduct,
    `RoundedClocks.transfer,
    `RoundedClocks.IsBand,
    `RoundedClocks.entrywise,
    `RoundedClocks.truncation_bits,
    `RoundedClocks.HasMidpointError,
    `RoundedClocks.exists_checkpoints,
    `RoundedClocks.midpointProduct,
    `RoundedClocks.fine_steps,
    `RoundedClocks.fine_steps_bits,
    `RoundedClocks.exists_bits,
    `RoundedClocks.jrs_leakage,
    `RoundedClocks.truncated_endpoints,
    `RoundedClocks.𝒩,
    `RoundedClocks.rounded_clock_comparison,
    `RoundedClocks.unit_sharp,
    `RoundedClocks.rounded_clock_bound,
    `RoundedClocks.unit_transfer,
    `RoundedClocks.unitary_products,
    `RoundedClocks.walk_leakage,
    `RoundedClocks.gap_adapted,
    `RoundedClocks.precessing_spin,
    `RoundedClocks.crossings,
    `RoundedClocks.series_bound,
    `RoundedClocks.series_derivative,
    `RoundedClocks.cell,
    `RoundedClocks.walk_log,
    `RoundedClocks.end_value,
    `RoundedClocks.constants_at_pi,
    `RoundedClocks.constants_near_two_pi,
    `RoundedClocks.spectralGap,
    `RoundedClocks.IsArcBand,
    `RoundedClocks.eigenphaseGap,
    `RoundedClocks.spectralProjector,
    `RoundedClocks.IsArcBandFamily,
    `RoundedClocks.eigenvalueCount,
    `RoundedClocks.entrywiseFamily,
    `RoundedClocks.𝒩ad
  ]
  unless statements.length == 48 do
    throwError "INDEX_COUNT_MISMATCH: expected 40 row declarations and eight companion definitions"
  let citations : List Name := [
    `RoundedClocks.Dieudonne_7_6_1, `RoundedClocks.Dieudonne_10_5_4,
    `RoundedClocks.Dieudonne_10_6_3, `RoundedClocks.Bhatia_Corollary_III_2_6,
    `RoundedClocks.Bhatia_Exercise_VII_1_11, `RoundedClocks.Bhatia_Theorem_VII_3_1]
  for name in citations do
    unless (env.find? name).isSome do
      throwError "MISSING_CITATION: {name}"
  for name in [`RoundedClocks.Dieudonne_8_6_4, `RoundedClocks.Dieudonne_Section_8_7,
      `RoundedClocks.DLMF_4_22_5] do
    if (env.find? name).isSome then
      throwError "UNEXPECTED_CITATION: {name}"
  IO.println s!"CITATIONS_OK {citations.length} hypotheses"
  let mut missingDocs : List Name := []
  for name in statements do
    unless (env.find? name).isSome do
      throwError "MISSING_STATEMENT: {name}"
    unless (← findDocString? env name).isSome do
      missingDocs := name :: missingDocs
  unless missingDocs.isEmpty do
    throwError "MISSING_DOCSTRINGS: {missingDocs}"
  let mut state : CollectAxioms.State := {}
  let mut count := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let m := env.header.moduleNames[idx.toNat]!
      if (`RoundedClocks).isPrefixOf m then
        let (_, next) := ((CollectAxioms.collect name).run env).run state
        state := next
        count := count + 1
  for ax in state.axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "UNEXPECTED_AXIOM: {ax}"
    IO.println s!"LIBRARY_AXIOM {ax}"
  IO.println s!"INDEX_DOCSTRINGS_OK {statements.length} statements"
  IO.println s!"LIBRARY_STANDARD_AXIOMS_OK {count} declarations"
