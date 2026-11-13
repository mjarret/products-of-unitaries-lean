/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.CommutatorTelescope

/-! # The general derivative-series estimate specialized to the cotangent multiplier -/
@[expose] public section
noncomputable section
open Complex Real Set Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.3(i) is exactly the general derivative bound with `g=N`.
The independent-input form is also used before setting the input to `Ω'`. -/
theorem frame_series_derivative_bound [NeZero d]
    {Ω D : ℝ → 𝕄} {Ωd Dd : 𝕄} {S : Set ℝ} {s : ℝ}
    (hΩd : HasDerivWithinAt Ω Ωd S s) (hDd : HasDerivWithinAt D Dd S s)
    (hu : UniqueDiffWithinAt ℝ S s) (hΩ : (Ω s).IsHermitian)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) :
    ‖derivWithin (fun t ↦ frameOp (Ω t) (D t)) S s‖ ≤
      frameBound w * ‖Dd‖ + 2 * frameLip w * ‖Ωd‖ * ‖D s‖ := by
  have hb := general_series_derivative_bound frame_nonnegativeSeries
    hΩd hDd hu hΩ hw0 hw hwidth
  rw [(frame_nonnegativeSeries.hasDerivAt_scalar hw0 hw).deriv] at hb
  exact hb

/-- The `C¹` conclusion of Lemma A.3 follows from the general series theorem
with the `C¹` paths `Ω` and `Ω'`. -/
theorem self_frame_series_contDiffOn [NeZero d] {Ω : ℝ → 𝕄} {w : ℝ}
    (hw : w < 2 * π)
    (hΩ : IsTimeDepHamiltonian Ω)
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 2 Ω (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (derivWithin Ω (Icc (0 : ℝ) 1) s))
      (Icc (0 : ℝ) 1) := by
  have hcD : ContDiffOn ℝ 1 (derivWithin Ω (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    hcΩ.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  exact general_series_contDiffOn frame_nonnegativeSeries hw hΩ hwidth
    (hcΩ.of_le (by norm_num)) hcD

end UnitaryProducts.PaperProof
