/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.FrameCubic
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Walks.MeshComparison

/-!
# The walk logarithm, and a larger walk coefficient

## Declarations

- `walk_log`
-/

@[expose] public section

open Real Set Complex UnitaryProducts.Corrector UnitaryProducts Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2 without the uniqueness clause, and with the Hessian coefficient $\cos^{-2}(w/4)$ in
place of $S^2$: the continuous logarithm of `walk_log_moving` with spectrum in
$[a(s), a(s) + w]$ (i), $C^2$ by `contDiffOn_log_of_continuous` (ii), with the bounds of
`norm_walkLogSlope_on_Icc_le` (iii) and `norm_walkLogHessian_on_Icc_le` (iv). -/
theorem walk_log [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1=W s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖derivWithin Λ (Icc (0 : ℝ) 1) s‖ ≤ S w*‖derivWithin W (Icc (0 : ℝ) 1) s‖ ∧
        ‖derivWithin (derivWithin Λ (Icc (0 : ℝ) 1)) (Icc 0 1) s‖ ≤
          S w*‖derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1) s‖+
            (Real.cos (w/4))⁻¹^2*‖derivWithin W (Icc (0 : ℝ) 1) s‖^2 := by
  intro S
  obtain ⟨Λ,hΛ,hcont,he⟩ := walk_log_moving a w hw W ha hc.continuousOn hunit harc
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by have h := (he 0 ⟨le_rfl, zero_le_one⟩).1 0; linarith [h.1, h.2]
  have hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖Λ s-(c:ℂ) • 1‖≤w/2 := fun s hs ↦
    ⟨a s+w/2,norm_sub_smul_one_le_of_eigenvalues (hΛ s hs) hw0 (he s hs).1⟩
  have hev : ∀ s ∈ Icc (0 : ℝ) 1, evol (Λ s) 1 = W s := fun s hs ↦ (he s hs).2
  have hΛc : ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) := by
    refine contDiffOn_log_of_continuous hcont hΛ (fun s hs ↦ ?_) hev hc
    obtain ⟨c,hc⟩ := hcenter s hs
    exact ((norm_I_smul_adL_le (Λ s) (c:ℂ)).trans (by linarith)).trans_lt hw
  rw [show S w = walkLogSlope w from walkLogSlope_closed hw0 hw]
  exact ⟨Λ,hΛ,he,hΛc,fun s hs ↦ ⟨norm_walkLogSlope_on_Icc_le hw hΛ hcont hc hcenter hev s hs,
    norm_walkLogHessian_on_Icc_le hw hΛ hΛc hc hcenter hev s hs⟩⟩

end UnitaryProducts.Paper
