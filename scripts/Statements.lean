/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/

import RoundedClocks

/-!
# Statements of the index

## Main results

Print the 40 row declarations and eight companion definitions of `THEOREMS.md`: the complete type
of each theorem, and the definition of each indexed term. The namespaces below are open so that
the statements print with
the notation of `RoundedClocks/Definitions.lean`.

## References

Michael Jarret, *Rounded clocks and finite precision: a transfer principle between continuous and
discrete quantum dynamics*.
-/

open RoundedClocks Set Filter
open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Complex (I)
open NormedSpace (exp)

set_option format.width 100

#check @RoundedClocks.theorem_A
#check @RoundedClocks.theorem_B
#print RoundedClocks.IsRegulated
#check @RoundedClocks.generates_exists
#check @RoundedClocks.generates_evolutionOf
#check @RoundedClocks.generates_unique
#check @RoundedClocks.comparison
#check @RoundedClocks.duhamel
#check @RoundedClocks.piecewise_product
#check @RoundedClocks.roundedEvolution_end
#print RoundedClocks.stepProduct
#check @RoundedClocks.transfer
#print RoundedClocks.IsBand
#print RoundedClocks.entrywise
#check @RoundedClocks.truncation_bits
#print RoundedClocks.HasMidpointError
#check @RoundedClocks.exists_checkpoints
#print RoundedClocks.midpointProduct
#check @RoundedClocks.fine_steps
#check @RoundedClocks.fine_steps_bits
#check @RoundedClocks.exists_bits
#check @RoundedClocks.jrs_leakage
#check @RoundedClocks.truncated_endpoints
#print RoundedClocks.𝒩
#check @RoundedClocks.rounded_clock_comparison
#check @RoundedClocks.unit_sharp
#check @RoundedClocks.rounded_clock_bound
#check @RoundedClocks.unit_transfer
#check @RoundedClocks.unitary_products
#check @RoundedClocks.walk_leakage
#check @RoundedClocks.gap_adapted
#check @RoundedClocks.precessing_spin
#check @RoundedClocks.crossings
#check @RoundedClocks.series_bound
#check @RoundedClocks.series_derivative
#check @RoundedClocks.cell
#check @RoundedClocks.walk_log
#check @RoundedClocks.end_value
#check @RoundedClocks.constants_at_pi
#check @RoundedClocks.constants_near_two_pi

-- The two partial-fraction identities are theorems, not cited hypotheses.
#check @RoundedClocks.dlmf_4_22_3
#check @RoundedClocks.dlmf_4_22_5

-- Companion definitions named in the indexed rows.
#print RoundedClocks.spectralGap
#print RoundedClocks.IsArcBand
#print RoundedClocks.eigenphaseGap
#print RoundedClocks.spectralProjector
#print RoundedClocks.IsArcBandFamily
#print RoundedClocks.eigenvalueCount
#print RoundedClocks.entrywiseFamily
#print RoundedClocks.𝒩ad
