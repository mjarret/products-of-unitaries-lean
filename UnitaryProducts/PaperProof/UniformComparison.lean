/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.UniformCells
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.PaperProof.UniformTruncation

/-!
# UniformComparison

## Declarations

-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The boundary estimate retaining the actual derivatives at the two endpoints. -/
theorem uniform_boundary_endpoints [NeZero d] {T : ℝ} (hT : 0 < T) {N : ℕ}
    (hN : 0 < N) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let Yr := allSampleCorrectorFamily T N H Hd hH
    let Δ := fun j : ℕ ↦ Yr j (-(1 / 2)) - Yr (j - 1) (1 / 2)
    let Yb := fun s ↦ frameOp ((T / N) • H s) (Hd s)
    let sigma := ∑ j ∈ Finset.Icc 1 N, ‖Yb ((j : ℝ) / N) - Yb (((j : ℝ) - 1) / N)‖
    let c₀ := frameBound w - frameBound (w / 2) / 2
    ‖Yr 0 0‖ + ‖Yr N 0‖ + ∑ j ∈ Finset.Icc 1 N, ‖Δ j‖ ≤
      T / (N : ℝ) ^ 2 * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + sigma) := by
  intro Yr Δ Yb sigma c₀
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw₀ : 0 ≤ w := by simpa using hwidth 0 (by omega) 0 0
  have hc₀ : 0 ≤ c₀ := center_bound_nonneg hw₀ hw
  -- the proof of Lemma A.1 at the cell centers bounds the two outer endpoint values.
  have hends : ‖Yr 0 0‖ + ‖Yr N 0‖ ≤
      c₀ * T / (N : ℝ) ^ 2 * (‖Hd 0‖ + ‖Hd 1‖) := by
    simpa only [Int.cast_zero, zero_div, Int.cast_natCast, div_self hn.ne', mul_add] using
      add_le_add (allSampleCorrectorFamily_center_norm_le hT.le N H Hd hH hw hwidth
        (r := 0) (by omega)) (allSampleCorrectorFamily_center_norm_le hT.le N H Hd hH hw hwidth
        (r := N) (by omega))
  -- Linearity identifies each jump with T/N² times the adjacent frame-value change.
  have hjump : (∑ j ∈ Finset.Icc 1 N, ‖Δ j‖) = T / (N : ℝ) ^ 2 * sigma := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show Δ j = _ from uniformCorrectionPiece_jump_frame T N H Hd hH hw hwidth
      (j := (j : ℤ)) (by exact_mod_cast (Finset.mem_Icc.mp hj).1)
      (by exact_mod_cast (Finset.mem_Icc.mp hj).2)]
    simp only [norm_smul_of_nonneg (by positivity : 0 ≤ T / (N : ℝ)^2), Yb, Int.cast_natCast]
  rw [hjump]
  exact (add_le_add_left hends (T / (N : ℝ) ^ 2 * sigma)).trans_eq (by ring)

end UnitaryProducts.PaperProof
