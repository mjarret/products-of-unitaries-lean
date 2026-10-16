/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.PaperProof.PropTransfer
public import UnitaryProducts.PaperProof.UnifiedProducts
public import UnitaryProducts.PaperProof.CanonicalCell
public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.PaperProof.WalkCutFormula
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.WalkScalarCut
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.Units
public import UnitaryProducts.Prose.WalkComparisonJRS
public import UnitaryProducts.Prose.SyncSteps
public import UnitaryProducts.PaperProof.ExTruncationBits
public import UnitaryProducts.PaperProof.ThmTransfer
public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.UniformConstants
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.PaperProof.ClosedCellCorrector

/-!
# Leakage transfer for unitary products

-/

@[expose] public section

open Real Complex Set Filter MeasureTheory UnitaryProducts.Paper UnitaryProducts.Corrector
open UnitaryProducts.Paper.UnitStepsProse
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.Prose

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4.3: the endpoint-sensitive walk comparison transfers leakage in
both directions when the endpoint projectors commute with the logarithms. -/
theorem walk_uniform_leakage_transfer_bounds [NeZero d] (a : ℝ → ℝ) (θ : ℝ)
    (hθ : 0 < θ) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ α ∈ Icc (a s) (a s + (2 * π - θ)), z = Complex.exp (-I * (α : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (H : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hlog : ∀ s ∈ Icc (0 : ℝ) 1, evol (H s) 1 = W s)
    (hwindow : ∀ s (hs : s ∈ Icc (0 : ℝ) 1),
      ∀ i, (hH s hs).eigenvalues i ∈ Icc (a s) (a s + (2 * π - θ))) :
    let w := 2 * π - θ
    let Wd := derivWithin W (Icc (0 : ℝ) 1)
    let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
    let c₀ := frameBound w - frameBound (w / 2) / 2
    ∀ T : ℕ, 1 ≤ T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ H (t / T)) U 0 T →
      ∀ P Q : 𝕄, IsStarProjection P → IsStarProjection Q →
        Commute P (H 0) → Commute Q (H 1) →
        |‖(1 - Q) * (walk W T).2 * P‖ - ‖(1 - Q) * U T * P‖| ≤
          (1 / T) * (c₀ * walkLogSlope w * (‖Wd 0‖ + ‖Wd 1‖) +
            (1 / 24 + frameBound w) * walkLogSlope w * unitSupNorm Wdd +
            PaperProof.walk_square w * unitSupNorm Wd ^ 2) := by
  intro w Wd Wdd c₀ T hT U hU P Q hP hQ hPc hQc
  have hw : 2 * π - θ < 2 * π := by linarith
  have hb := PaperProof.unified_products_walk (by omega : 0 < T) a hw W ha hunit harc hc
    H hH hlog hwindow U hU
  have hl := PaperProof.prop_transfer (U := U T) (W := (walk W T).2)
    hP hQ hP hQ
    (evol_mem_unitary (hH 1 ⟨zero_le_one, le_rfl⟩) (1 / 2))
    (evol_mem_unitary (hH 0 ⟨le_rfl, zero_le_one⟩) (-(1 / 2)))
    (commute_evol_right hQc (1 / 2)).symm
    (commute_evol_right hPc (-(1 / 2))).symm
  simp only [sub_self, norm_zero, add_zero, mul_zero] at hl
  exact hl.trans (by
    simpa only [w, Wd, Wdd, c₀, PaperProof.walk_square, PaperProof.uniform_c0,
      PaperProof.uniform_c1] using hb)

/-- Section 4.3: selecting the logarithm eigenvectors by membership of their
phases in the walk's band gives exactly its interval spectral projector. The
selection equivalence is the last conclusion of `walk_band_log`. This projector
is orthogonal and commutes with the logarithm, hence with its half-step phases. -/
theorem log_band_projector {A : 𝕄} (hA : A.IsHermitian) (α β : ℝ)
    (hselect : ∀ i, hA.eigenvalues i ∈ Icc α β ↔
      ∃ θ ∈ Ioo α β, Complex.exp (-I * (θ : ℂ)) =
        Complex.exp (-I * (hA.eigenvalues i : ℂ))) :
    let B := {x : ℝ | ∃ θ ∈ Ioo α β,
      Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ))}
    specProj hA B = specProj hA (Icc α β) ∧
      IsStarProjection (specProj hA B) ∧ Commute (specProj hA B) A ∧
      ∀ t : ℝ, Commute (specProj hA B) (evol A t) := by
  intro B
  have hidx : idx hA.eigenvalues B = idx hA.eigenvalues (Icc α β) := by
    ext i
    simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hselect i).symm
  refine ⟨?_, isStarProjection_specProj hA B, commute_specProj hA B,
    fun t ↦ commute_evol_right (commute_specProj hA B) t⟩
  simp only [specProj, proj, hidx]


end UnitaryProducts.Prose
