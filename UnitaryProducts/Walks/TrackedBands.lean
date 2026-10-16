/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Spectral.TrackedCircularBand

/-!
# Bands of walks on moving arcs

## Declarations

- `trackedCircularBand`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A band of a walk on moving arcs (§4.3, the walk paragraph): `α`, `β`, `g`
are
continuous on $[0,1]$, and for each $s$: $g(s) > 0$; $\alpha(s) < \beta(s) < \alpha(s) + 2\pi$;
$e^{-i\alpha(s)}$ and $e^{-i\beta(s)}$ are not eigenvalues of $W(s)$; some eigenvalue has phase in
$(\alpha, \beta)$ (the band) and some in $(\beta, \alpha + 2\pi)$ (the rest); and every band phase
$x$ and other phase $y$ satisfy $g(s) \le \min(y - x, 2\pi - (y - x))$, the circular distance, so
$g$ is a continuous positive lower bound for the band's spectral gap. Phases are represented in
the one turn starting at $\alpha(s)$. -/
def trackedCircularBand (W : ℝ → 𝕄) (α β g : ℝ → ℝ) : Prop :=
  ContinuousOn α (Icc (0:ℝ) 1) ∧ ContinuousOn β (Icc (0:ℝ) 1) ∧
  ContinuousOn g (Icc (0:ℝ) 1) ∧
  ∀ s ∈ Icc (0:ℝ) 1,
    0<g s ∧ α s<β s ∧ β s<α s+2*π ∧
    Complex.exp (-I*(α s:ℂ)) ∉ spectrum ℂ (W s) ∧
    Complex.exp (-I*(β s:ℂ)) ∉ spectrum ℂ (W s) ∧
    (∃ θ ∈ Ioo (α s) (β s), Complex.exp (-I*(θ:ℂ)) ∈ spectrum ℂ (W s)) ∧
    (∃ θ ∈ Ioo (β s) (α s+2*π), Complex.exp (-I*(θ:ℂ)) ∈ spectrum ℂ (W s)) ∧
    ∀ x y, x ∈ Ioo (α s) (β s) → y ∈ Ioo (β s) (α s+2*π) →
      Complex.exp (-I*(x:ℂ)) ∈ spectrum ℂ (W s) →
      Complex.exp (-I*(y:ℂ)) ∈ spectrum ℂ (W s) →
      g s ≤ min (y-x) (2*π-(y-x))

end UnitaryProducts.Paper
