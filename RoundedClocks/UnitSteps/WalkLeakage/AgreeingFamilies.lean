/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Families that agree for `s ∈ [0,1]`

Proof of Theorem 4.7: "So Theorem 4.6 applies." Theorem 4.6 is stated for `e^{-iH}`, which agrees
with `W` for `s ∈ [0,1]`. Families that agree there have the same samples, the same derivatives
`∂` and `∂∂`, and the same `‖·‖∞`, hence the same product (`sampleProduct_eq`) and the same
`ℰ̃_w` (`ℰtilde_congr`).
-/

@[expose] public section

open Set
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RoundedClocks.WalkLeakage

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Families that agree for `s ∈ [0,1]` have the same derivative `∂` there. -/
theorem deriv01_eqOn {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    EqOn (∂F) (∂G) (Icc 0 1) := by
  intro s hs
  exact derivWithin_congr h (h hs)

/-- Families that agree for `s ∈ [0,1]` have the same second derivative `∂∂` there. -/
theorem second_deriv01_eqOn {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    EqOn (∂∂F) (∂∂G) (Icc 0 1) :=
  deriv01_eqOn (deriv01_eqOn h)

/-- Families that agree for `s ∈ [0,1]` have the same `‖·‖∞`. -/
theorem supNorm_eq {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) :
    supNorm F = supNorm G := by
  unfold supNorm
  congr 1
  exact Set.image_congr (fun s hs ↦ congrArg norm (h hs))

/-- `ℰ̃_w(F) = ℰ̃_w(G)` for families `F` and `G` that agree for `s ∈ [0,1]`. -/
theorem ℰtilde_congr {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1)) (w : ℝ) :
    ℰtilde w F = ℰtilde w G := by
  have hfirst := deriv01_eqOn h
  have hsecond := second_deriv01_eqOn h
  simp only [ℰtilde, hfirst (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
    hfirst (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
    supNorm_eq hfirst, supNorm_eq hsecond]

/-- Families that agree for `s ∈ [0,1]` have the same product of `T` samples, as every sample
`j/T` with `j < T` lies in `[0,1]`. -/
theorem sampleProduct_eq {F G : ℝ → 𝕄} (h : EqOn F G (Icc 0 1))
    {T : ℕ} : sampleProduct F T = sampleProduct G T := by
  unfold sampleProduct orderedProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j < T := List.mem_range.mp (List.mem_reverse.mp hj)
  apply h
  exact unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T) (by exact_mod_cast hjT.le)

end RoundedClocks.WalkLeakage
