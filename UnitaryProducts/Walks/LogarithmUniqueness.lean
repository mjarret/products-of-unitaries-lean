/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.FrameDerivativeBounds

/-!
# Uniqueness of the walk logarithm

## Declarations

- `walk_log_unique`
-/

@[expose] public section

open Real Set Complex UnitaryProducts.Corrector UnitaryProducts Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2 with the Hessian coefficient $\cos^{-2}(w/4)$ in place of $S^2$: `walk_log` plus the
uniqueness clause of (i), proved by `eq_of_evol_eq` on the window $[a(s), a(s) + w]$, centred at
$a(s) + w/2$ with half-width $w/2 < \pi$. Used by `exists_logarithm_of_free_arc`. -/
theorem walk_log_unique [NeZero d] (a : ℝ → ℝ) (w : ℝ)
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
            (Real.cos (w/4))⁻¹^2*‖derivWithin W (Icc (0 : ℝ) 1) s‖^2 := by
  intro S
  obtain ⟨Λ,hΛ,hlog,hc2,hbd⟩ := walk_log a w hw W ha hunit harc hc
  refine ⟨Λ,hΛ,hlog,?_,hc2,hbd⟩
  intro s hs B hB hBe hBW
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by have h := hBe 0; linarith [h.1, h.2]
  apply eq_of_evol_eq (α := -(a s+w/2)) (r := w/2) (by linarith) hB
    (by simpa only [neg_neg] using norm_sub_smul_one_le_of_eigenvalues hB hw0 hBe) (hΛ s hs)
    (by simpa only [neg_neg] using norm_sub_smul_one_le_of_eigenvalues (hΛ s hs) hw0 (hlog s hs).1)
  rw [hBW,(hlog s hs).2]

end UnitaryProducts.Paper
