/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.MidpointError
public import UnitaryProducts.Evolution.RoundedClockEvolution

/-!
# Existence of evolutions and the fine-step theorems

## Declarations

- `exists_unique_evolution`
- `midpoint_product_error_and_infimum`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator ENNReal
open Complex Set MeasureTheory
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Existence and uniqueness of evolutions** (§2.1, unnumbered). Every regulated Hermitian family
$H$ on $[0,T]$ generates exactly one $U$.

Reading the statement against the paper:
* "Exactly one" is existence together with `EqOn V U (Icc 0 T)` for every `V` that $H$
  generates: the evolution is unique on $[0,T]$, and its values outside $[0,T]$ are irrelevant.
* `hH` is the paper's standing assumption that families are Hermitian.

The proof projects existence and uniqueness out of `regulated_evolution_rounded`, that is, out of
`regulated_evolution`. The route differs from the paper's, which cites Dieudonné: existence is
built by hand as a uniform limit of evolutions of step approximations of $H$, with dominated
convergence for the integral equation; unitarity comes from $(U^\dagger U)'=0$ off a countable
set, as in the paper; and uniqueness comes from the Duhamel bound `duhamel`. -/
theorem exists_unique_evolution (H : ℝ → 𝕄) (T : ℝ) (hT : 0 < T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) (hreg : IsRegulated H 0 T) :
    ∃ U : ℝ → 𝕄, IsEvolution H U 0 T ∧
      ∀ V : ℝ → 𝕄, IsEvolution H V 0 T → EqOn V U (Icc 0 T) :=
  ((regulated_evolution_rounded (d := d)).1 H T hT hH hreg).imp fun _ h ↦ ⟨h.1, h.2.1⟩

/-- **Auxiliary integrated midpoint estimate on $[0,T]$** (midpoint products for a family on
$[0,T]$). This is the form of
the auxiliary integrated midpoint estimate for a family on $[0,T]$; the normalized auxiliary form
is `path_midpoint_product_error_and_infimum`,
which is equivalent under $t=Ts$ (`midpoint_product_error_and_infimum_of_path`). Let $F$ be an
odd function and $H$ a regulated Hermitian family on $[0,T]$ generating $U$. (i) The
midpoint product $W$ of $H^{(F)}$ on checkpoints
$t_0,\dots,t_n$ satisfies $\|W-U(T)\|\le\sum_j\int_{t_j}^{t_{j+1}}\|H(t)-H(t_{j+1/2})\|\,dt
+T\max_j\|H(t_{j+1/2})-H^{(F)}(t_{j+1/2})\|$. (ii) For every $\varepsilon>0$, some checkpoints make
the first term less than $\varepsilon$.

Reading the statement against the paper:
* `osc n t` is the first term, $\sum_j\int_{t_j}^{t_{j+1}}\|H(x)-H(t_{j+1/2})\|\,dx$.
* "Odd function" is `∀ x, F (-x) = -F x`. $H^{(F)}$ is
  `(levelFunctionData F).2 H`, and at a sample it is `(levelFunctionData F).1`.
* The checkpoints $t_0,\dots,t_n$ are `(variationCheckpoints H T n).2.1 t`: `t` nondecreasing with
  $t_0=0$ and $t_n=T$.
* The maximum is `⨆ j : Fin n`. At $n=0$ this would be the junk value $0$, but $t_0=0<T=t_n$
  forces $n\ge1$, so it is a maximum over a nonempty finite set.
* (ii) is `sInf {…} = 0` over all $n$ and all checkpoints. The set is nonempty and bounded below by
  $0$, so this is the genuine infimum, and it says exactly that every $\varepsilon>0$ exceeds
  `osc n t` for some checkpoints (`exists_lt_of_csInf_lt`).
* The proof of (i) uses only that $F$ is odd.
* Stronger than the paper's setting: no $d\ge1$.

The proof projects (i) and (ii) out of `fine_steps_split`. (ii) follows the paper: the nodes of a
step function uniformly close to $H$ (Dieudonné (7.6.1), `exists_pieces_of_regulated`) are
checkpoints with small oscillation. (i) differs in form: instead of applying the Duhamel bound once
to the evolution of the piecewise-constant family $G$, the proof compares $U$ with the frozen
exponential on each interval and telescopes (`piecewise_product_error_le_integral`), then splits
each integrand at the midpoint sample; the two bookkeepings agree, and the evolution of $G$ is never
built. -/
theorem midpoint_product_error_and_infimum {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hU : IsEvolution H U 0 T) :
    let osc := fun (n : ℕ) (t : ℕ → ℝ) ↦
      ∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-H ((t j+t (j+1))/2)‖
    (∀ F : ℝ → ℝ, (∀ x, F (-x) = -F x) →
      ∀ (n : ℕ) (t : ℕ → ℝ), (variationCheckpoints H T n).2.1 t →
      ‖midpointProduct ((levelFunctionData F).2 H) n t-U T‖ ≤
        osc n t+T*⨆ j : Fin n, ‖H ((t j+t (j+1))/2)-
          (levelFunctionData F).1 (H ((t j+t (j+1))/2))‖) ∧
    sInf {x : ℝ | ∃ (n : ℕ) (t : ℕ → ℝ), (variationCheckpoints H T n).2.1 t ∧
      x = osc n t} = 0 :=
  (fine_steps_split hT hreg hH hU).imp_right And.left

end UnitaryProducts.Paper
