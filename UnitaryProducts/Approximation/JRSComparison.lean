/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-!
# The Jansen–Ruskai–Seiler coefficient

## Declarations

- `jrsFunctional`
-/

@[expose] public section

open MeasureTheory Set
namespace UnitaryProducts

/-- The scalar functional of Jansen–Ruskai–Seiler's Theorem 3, eq. (3.2):
$\frac{m\,u(0)}{g(0)^2}+\frac{m\,u(1)}{g(1)^2}+\int_0^1\Bigl(\frac{m\,v(s)}{g(s)^2}
+7m\sqrt m\,\frac{u(s)^2}{g(s)^3}\Bigr)\,ds$. With $u=\|\tilde H'\|$, $v=\|\tilde H''\|$ and
$g=\Gamma(\tilde H)$ it is $J_m(\tilde H)$.

Junk values: a quotient with $g(s)=0$ is `0`, and the interval integral is `0` if the integrand
is not integrable. Every use (`jrsCoefficient`) assumes `g` continuous and positive on $[0,1]$.
The continuous adiabatic theorem is a cited input, not part of this definition. -/
noncomputable def jrsFunctional (m : ℝ) (u v g : ℝ → ℝ) : ℝ :=
  m * u 0 / g 0 ^ 2 + m * u 1 / g 1 ^ 2 +
    ∫ s in (0 : ℝ)..1, m * v s / g s ^ 2 + 7 * m * Real.sqrt m * u s ^ 2 / g s ^ 3

end UnitaryProducts
