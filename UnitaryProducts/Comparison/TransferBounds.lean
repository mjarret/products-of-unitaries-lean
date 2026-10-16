/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Walks.FrameDerivativeBounds
public import UnitaryProducts.Walks.LogarithmDerivativeBounds
public import UnitaryProducts.Walks.LogarithmUniqueness

/-!
# Transfer of continuous bounds to unit steps

## Declarations

- `exists_logarithm_of_free_arc`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Lemma A.2 for a $C^2$ walk whose spectrum lies on the arcs
$\{e^{-i\theta}:a(s)\le\theta\le a(s)+w\}$, $w<2\pi$: a Hermitian logarithm $\Lambda$ with
eigenvalues in $[a(s),a(s)+w]$, unique among such logarithms at each $s$, $C^2$, with
$\|\Lambda'\|\le S\|W'\|$ and $\|\Lambda''\|\le S\|W''\|+\|W'\|^2/\cos^2(w/4)$, where
$S=g(w)$ with $g(x)=(x/2)/\sin(x/2)$ for $x\ne0$ and $g(0)=1$. The paper's (iv) then uses
$1/\cos(w/4)\le S$. -/
theorem exists_logarithm_of_free_arc [NeZero d] (a : ℝ → ℝ) (w : ℝ)
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
            (Real.sin ((2*π-w)/4))⁻¹^2*‖derivWithin W (Icc (0 : ℝ) 1) s‖^2 := by
  intro S
  rw [show Real.sin ((2*π-w)/4) = Real.cos (w/4) by
    rw [show (2*π-w)/4 = π/2-w/4 by ring, Real.sin_pi_div_two_sub]]
  exact walk_log_unique a w hw W ha hunit harc hc


end UnitaryProducts.Paper
