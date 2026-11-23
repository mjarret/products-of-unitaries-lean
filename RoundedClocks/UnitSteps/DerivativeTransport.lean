/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Transport of derivatives along equal paths

Theorem 4.6 transports first and second derivatives between Hermitian paths that agree on the unit
interval.
-/

@[expose] public section

open Set
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RoundedClocks.WalkLeakageTransport

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Agreement on the unit interval identifies the first within derivatives. -/
theorem deriv01_eqOn {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    EqOn (∂F) (∂G) (Icc 0 1) := by
  intro s hs
  exact derivWithin_congr h (h hs)

/-- Agreement on the unit interval identifies both within derivatives. -/
theorem second_deriv01_eqOn {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    EqOn (∂∂F) (∂∂G) (Icc 0 1) :=
  deriv01_eqOn (deriv01_eqOn h)

/-- The interval supremum norm depends only on values on the interval. -/
theorem supNorm_eq {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    supNorm F = supNorm G := by
  unfold supNorm
  congr 1
  exact Set.image_congr (fun s hs ↦ congrArg norm (h hs))

/-- The walk comparison energy depends only on the family on the unit interval. -/
theorem energy_eq {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) (w : ℝ) :
    ℰtilde w F = ℰtilde w G := by
  have hfirst := deriv01_eqOn h
  have hsecond := second_deriv01_eqOn h
  simp only [ℰtilde, hfirst (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
    hfirst (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
    supNorm_eq hfirst, supNorm_eq hsecond]

/-- Every sampled factor lies in the interval on which the families agree. -/
theorem sampleProduct_eq {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1))
    {T : ℕ} (hT : 1 ≤ T) : sampleProduct F T = sampleProduct G T := by
  unfold sampleProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j < T := List.mem_range.mp (List.mem_reverse.mp hj)
  apply h
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · positivity
  · apply (div_le_one hTpos).mpr
    exact_mod_cast hjT.le

end RoundedClocks.WalkLeakageTransport
