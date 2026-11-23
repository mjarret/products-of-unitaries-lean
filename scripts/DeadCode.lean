import RoundedClocks
open Lean Elab Command

/-- Print source declarations not reachable from the index and its companion definitions. -/
elab "#dead_code" : command => do
  let env ← getEnv
  let roots : List Name := [
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
  let ours (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!).getRoot == `RoundedClocks
    | none => false
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet.toList do
        if ours m && !seen.contains m then todo := m :: todo
  let kept : List Name := [`RoundedClocks.matrixEntryCLM_apply,
    `RoundedClocks.walk_evalCLM_apply, `RoundedClocks.summable_norm_powDeriv]
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    let aux := n.components.any fun c => match c with
      | .str _ s => s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" ||
          s == "eq_def" || s == "congr_simp" || s.startsWith "term" ||
          s.startsWith "_" && s != "_private"
      | _ => false
    if ours n && !seen.contains n && !aux && !kept.contains n &&
        !(isPrivateName n && (privateToUserName n).isInternal) then
      let some i := env.getModuleIdxFor? n | continue
      out := out.push s!"DEAD {env.header.moduleNames[i.toNat]!} {privateToUserName n}"
  logInfo (String.intercalate "\n" out.qsort.toList)
  logInfo s!"DEAD_CODE_COUNT {out.size}"
  unless out.isEmpty do
    throwError "UNREACHABLE_SOURCE_DECLARATIONS: {out.size}"
  logInfo "DEAD_CODE_OK: only generated syntax and the three kept helpers are excluded"

#dead_code
