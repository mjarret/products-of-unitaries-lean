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

Check that every statement of the index has a docstring, and that every declaration of the library,
including private and generated declarations, depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

## References

Michael Jarret, *Rounded clocks and finite precision: a transfer principle between continuous and
discrete quantum dynamics*.
-/

-- Traverse the entire library, including private and generated declarations.
set_option maxHeartbeats 16000000 in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let heads : List Name := [
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
    `RoundedClocks.exists_bits,
    `RoundedClocks.exists_checkpoints,
    `RoundedClocks.midpointProduct,
    `RoundedClocks.fine_steps,
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
    `RoundedClocks.cell,
    `RoundedClocks.walk_log,
    `RoundedClocks.end_value,
    `RoundedClocks.constants_at_pi,
    `RoundedClocks.constants_near_two_pi
  ]
  let mut missingDocs : List Name := []
  for name in heads do
    unless (env.find? name).isSome do
      throwError "MISSING_HEAD: {name}"
    unless (← findDocString? env name).isSome do
      missingDocs := name :: missingDocs
  unless missingDocs.isEmpty do
    throwError "MISSING_HEAD_DOCSTRINGS: {missingDocs}"
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
  IO.println s!"HEAD_DOCSTRINGS_OK {heads.length} heads"
  IO.println s!"LIBRARY_STANDARD_AXIOMS_OK {count} declarations"
