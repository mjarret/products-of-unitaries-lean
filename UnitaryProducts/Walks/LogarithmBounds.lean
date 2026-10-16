/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.TransferBounds

/-!
# Lemma A.2: the logarithm of a walk

## Declarations

- `exists_logarithm_with_derivative_bounds`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Lemma A.2** (logarithm of a walk). A $C^2$ walk $W$ whose spectrum lies on the moving arc
$\{e^{-i\theta} : a(s) \le \theta \le a(s) + w\}$, $w = 2\pi - \vartheta < 2\pi$, has exactly one
Hermitian logarithm $\Lambda$ with spectrum in $[a(s), a(s) + w]$; it is $C^2$, and on $[0,1]$
$\|\Lambda'\| \le S\|W'\|$ and $\|\Lambda''\| \le S\|W''\| + \|W'\|^2/\cos^2(w/4)$, with
$S = (w/2)/\sin(w/2)$.

Reading the statement against the paper:
* The closed spectral arc has length $w = 2\pi - \vartheta$: `0 ≤ w` and `w < 2 * π` are
  $0 < \vartheta \le 2\pi$.
* `(walk W 1).1` says that each $W(s)$, $s \in [0,1]$, is unitary.
* `let S` is $(w/2)/\sin(w/2)$; the `if` gives the paper's value $1$ at $w = 0$.
* Part (i) is two conjuncts: existence (the eigenvalue window and `evol (Λ s) 1 = W s`, that is
  $e^{-i\Lambda(s)} = W(s)$) and, for each $s$, uniqueness among Hermitian `B` with the same window
  and exponential.
* `derivWithin … (Icc 0 1)` is the derivative on $[0,1]$, one-sided at $0$ and $1$.

The proof identifies the constants and calls `exists_logarithm_of_free_arc`, which reaches
`walk_log`: (1) the Hermitian logarithm in the window is continuous (`walk_log_moving`) and unique,
as $\theta \mapsto e^{-i\theta}$ is one-to-one on a window of width below $2\pi$ (`eq_of_evol_eq`);
(2) it is $C^2$ by the inverse function theorem for $X \mapsto e^{-iX}$
(`contDiffOn_log_of_continuous`); (3) $\Lambda' = \Phi_\Lambda^{-1}(iW^\dagger W')$, where the
Bernoulli series $\Phi_\Lambda^{-1}$ of $i\,\mathrm{ad}_\Lambda$ has norm at most $S$
(`norm_walkLogSlope_on_Icc_le`); (4) the paper's $Z_u$ integral and its two quadratures
$\int_0^1 du/r_u^2 = S$ (`walk_slope_quadrature`) and $\int_0^1 2u\,du/r_u^3 = 1/\cos^2(w/4)$
(`walk_hessian_quadrature_re`, whose $2/(1+c)$ at $c = \cos(w/2)$ is $1/\cos^2(w/4)$) give
$\|\Lambda''\| \le S\|W''\| + \|W'\|^2/\cos^2(w/4)$
(`norm_walkLogHessian_on_Icc_le`). Steps (2) and (3) differ from the paper's proof, which uses the
local principal logarithm and $\int_0^1\|Z_u\|^2\,du$; the constant is the same. -/
theorem exists_logarithm_with_derivative_bounds [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s+w)) ∧ evol (Λ s) 1=W s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (B : 𝕄) (hB : B.IsHermitian),
        (∀ i, hB.eigenvalues i ∈ Icc (a s) (a s+w)) → evol B 1=W s → B=Λ s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖derivWithin Λ (Icc (0 : ℝ) 1) s‖ ≤ S w*‖derivWithin W (Icc (0 : ℝ) 1) s‖ ∧
        ‖derivWithin (derivWithin Λ (Icc (0 : ℝ) 1)) (Icc 0 1) s‖ ≤
          S w*‖derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1) s‖+
            ‖derivWithin W (Icc (0 : ℝ) 1) s‖^2/Real.cos (w/4)^2 := by
  simpa only [show Real.sin ((2 * π - w) / 4) = Real.cos (w / 4) by
    rw [show (2 * π - w) / 4 = π / 2 - w / 4 by ring, Real.sin_pi_div_two_sub],
    inv_pow, inv_mul_eq_div] using exists_logarithm_of_free_arc a w hw W ha hunit harc hc

end UnitaryProducts.Paper
