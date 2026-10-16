/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/

import UnitaryProducts
import Mathlib.Tactic.Linter.Lint

/-!
# Environment linter check

## Main results

Run every enabled Batteries and Mathlib environment linter on this library.

## References

Michael Jarret, *Products of unitaries as continuous evolutions at finite precision*.
-/

-- Checking the entire declaration set requires more heartbeats than a single theorem.
set_option maxHeartbeats 16000000 in
open Lean Meta Batteries.Tactic.Lint in
#eval show MetaM Unit from do
  let env ← getEnv
  let decls := env.constants.toList.filterMap fun (name, _) ↦ do
    let idx ← env.getModuleIdxFor? name
    let mod := env.header.moduleNames[idx.toNat]!
    if (`UnitaryProducts).isPrefixOf mod then some name else none
  let linters ← getChecks true none none
  let results ← lintCore decls.toArray linters (inIO := true)
  let mut failures := 0
  for (linter, messages) in results do
    IO.println s!"LINTER|{linter.name}|failures={messages.size}"
    for (name, msg) in messages.toList do
      IO.println s!"LINT_FAILURE|{linter.name}|{name}|{← msg.toString}"
      failures := failures + 1
  IO.println s!"LINTER_DECLARATIONS={decls.length}"
  IO.println s!"LINTER_FAILURES={failures}"
  unless failures == 0 do throwError "Environment lint failed"
  IO.println "ENVIRONMENT_LINTERS_OK"
