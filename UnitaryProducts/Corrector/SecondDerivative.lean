/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.CommutatorRegularity

/-!
# Chain and product rules through $\mathbb C$-linear maps

## Declarations

- `hasDerivAt_clmC_apply`
- `hasDerivAt_clmC_comp`
-/

@[expose] public section

namespace UnitaryProducts.Corrector

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The chain rule through a `ℂ`-linear map, for a real-variable path. -/
theorem hasDerivAt_clmC_comp (Ψ : V →L[ℂ] W) {f : ℝ → V} {f' : V} {x : ℝ}
    (hf : HasDerivAt f f' x) : HasDerivAt (fun v ↦ Ψ (f v)) (Ψ f') x :=
  (Ψ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hf

/-- The product rule for the application of a `ℂ`-linear-map-valued path to a vector path. -/
theorem hasDerivAt_clmC_apply {c : ℝ → (V →L[ℂ] W)} {c' : V →L[ℂ] W} {u : ℝ → V} {u' : V} {x : ℝ}
    (hc : HasDerivAt c c' x) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun y ↦ (c y) (u y)) (c' (u x) + c x u') x :=
  ((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).hasFDerivAt.comp_hasDerivAt x hc).clm_apply hu

end UnitaryProducts.Corrector

