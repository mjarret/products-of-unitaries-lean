/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Spectral.TrackedBandGap

/-! # The principal logarithm on a centered spectral window

Centering an open turn places the unitary spectrum in the slit plane and
identifies the Hermitian logarithm by continuous functional calculus.
-/

@[expose] public section
open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
noncomputable section
namespace UnitaryProducts.PaperProof
-- This C*-algebra structure uses the same L2 operator norm as the paper.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

set_option maxHeartbeats 800000 in
-- Functional-calculus elaboration expands the finite-dimensional matrix instances.
/-- Centering an open spectral turn places the unitary spectrum in the slit
plane and recovers its Hermitian logarithm by continuous functional calculus. -/
theorem cut_log_eq_principal {G W : 𝕄} {α : ℝ} (hG : G.IsHermitian)
    (he : evol G 1 = W)
    (hopen : ∀ x ∈ spectrum ℝ G, x ∈ Ioo α (α + 2 * π)) :
    spectrum ℂ (Complex.exp (I * ((α + π : ℝ) : ℂ)) • W) ⊆ Complex.slitPlane ∧
      G = ((α + π : ℝ) : ℂ) • 1 +
        I • cfc Complex.log (Complex.exp (I * ((α + π : ℝ) : ℂ)) • W) := by
  let μ := α + π
  have hn := norm_center_lt_pi_of_open_turn hG (by
    intro i
    exact hopen _ (hG.eigenvalues_mem_spectrum_real i))
  have hcenter : (G - (μ : ℂ) • 1).IsHermitian := by
    apply hG.sub
    change star ((μ : ℂ) • (1 : 𝕄)) = (μ : ℂ) • 1
    simp only [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
  have hev : evol (G - (μ : ℂ) • 1) 1 = Complex.exp (I * (μ : ℂ)) • W := by
    rw [evol_sub_scalar_one, he]
  have hcut := spectrum_evol_one_subset_slitPlane hcenter hn
  letI := isStarNormal_evol_one hcenter
  have hlog := walkLogIntegral_evol hcenter hn
  rw [walkLogIntegral_eq_cfc _ hcut] at hlog
  constructor
  · simpa only [hev, μ] using hcut
  · rw [← hev, hlog, smul_smul, show I * (-I) = (1 : ℂ) by simp, one_smul]
    dsimp only [μ]
    abel

end UnitaryProducts.PaperProof
