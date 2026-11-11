/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.ExactGap
public import UnitaryProducts.Walks.LogarithmBranch

/-!
# Band eigenphase gaps of sampled exponentials

## Declarations

- `finiteEigenphaseGap`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Real Set
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}

/-- The circle distance between phases, minimized over a band and its complement.
The quotient norm is angular distance in radians, not chord distance: for phases $\theta_i$,
$\theta_j$ it is $\min_k |\theta_i - \theta_j + 2\pi k|$, as in the paragraph after
Definition 2.5. For a Hermitian sample $h$ with eigenvalues `θ`, these are the eigenphases of
$e^{-ih}$. The nonemptiness of the band `S` and of its complement are arguments, so there is no
junk value. -/
def finiteEigenphaseGap (θ : Fin d → ℝ) (S : Finset (Fin d))
    (hS : S.Nonempty) (hR : Sᶜ.Nonempty) : ℝ :=
  S.inf' hS (fun i ↦ Sᶜ.inf' hR
    (fun j ↦ ‖((θ i - θ j : ℝ) : AddCircle (2 * π))‖))

end UnitaryProducts.Paper
