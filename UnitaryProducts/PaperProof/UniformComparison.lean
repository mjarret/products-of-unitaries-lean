/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.UniformCells
public import UnitaryProducts.PaperProof.ThmUnitStepsMax
public import UnitaryProducts.PaperProof.UniformTruncation

/-!
# UniformComparison

## Declarations

- `lem_boundary_uniform`
- `uniform_step_sigma_LM`
- `uniform_steps_sigma_LM`
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

/-- Lemma A.3 bounds each of the N adjacent sample increments. -/
theorem uniform_step_sigma_LM [NeZero d] {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
    let Yb := fun s ↦ frameOp ((T / N) • H s) (Hd s)
    ‖Yb ((j : ℝ) / N) - Yb (((j : ℝ) - 1) / N)‖ ≤
      (frameBound w * M + 2 * frameLip w * (T / N) * L ^ 2) / N := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw₀ : 0 ≤ w := by simpa using hwidth 0 (by omega) 0 0
  intro Yb
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hL : 0 ≤ L := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, zero_le_one⟩)
  have hB := frameBound_nonneg hw₀
  have hD := frameLip_nonneg hw₀
  have hr₁ : 0 ≤ (j : ℤ) - 1 ∧ (j : ℤ) - 1 ≤ N := by omega
  have hr₂ : 0 ≤ (j : ℤ) ∧ (j : ℤ) ≤ N := by omega
  let a : ℝ := (((j : ℤ) - 1 : ℤ) : ℝ) / N
  let b : ℝ := ((j : ℤ) : ℝ) / N
  have ha : a ∈ Icc (0 : ℝ) 1 := all_grid_mem hr₁
  have hb : b ∈ Icc (0 : ℝ) 1 := all_grid_mem hr₂
  let hΩa := Separation.isHermitian_real_smul (hH a ha) (T / N)
  let hΩb := Separation.isHermitian_real_smul (hH b hb) (T / N)
  have hca := norm_sub_smul_one_le_of_eigenvalues hΩa hw₀ (eigen_interval hΩa (hwidth _ hr₁))
  have hcb := norm_sub_smul_one_le_of_eigenvalues hΩb hw₀ (eigen_interval hΩb (hwidth _ hr₂))
  have hf := (Prose.frameOp_change_split ((T / N) • H a) ((T / N) • H b) (Hd a) (Hd b)).trans
    (Prose.frameOp_split_norm_bound hw hca hcb)
  have hstep : |b - a| = 1 / N := by
    simp [a, b, ← sub_div, abs_of_pos hn]
  have hΩdiff := (uniform_local_bounds (N := N) hT H Hd hd hbd hl ha hb).2.1
  simp only [abs_mul, abs_of_pos hn, hstep, mul_one_div_cancel hn.ne', mul_one] at hΩdiff
  have hDdiff : ‖Hd b - Hd a‖ ≤ M / N := by
    simpa only [hstep, mul_one_div] using hl a ha b hb
  -- The auxiliary two-point series estimate separates the two input changes.
  have hbound : ‖Yb b - Yb a‖ ≤
      frameBound w * (M / N) +
        2 * frameLip w * (T / (N : ℝ) ^ 2 * L) * L := by
    apply hf.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hDdiff hB)
      (mul_le_mul (mul_le_mul_of_nonneg_left hΩdiff (by positivity)) (hbd a ha)
        (norm_nonneg _) (by positivity))
  -- Normalize the indexed endpoints, then collect the common factor 1/N.
  simp only [a, b, Int.cast_sub, Int.cast_natCast, Int.cast_one] at hbound
  exact hbound.trans_eq (by ring)

/-- Sum the auxiliary two-point estimate over all N adjacent sample pairs. -/
theorem uniform_steps_sigma_LM [NeZero d] {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let Yb := fun s ↦ frameOp ((T / N) • H s) (Hd s)
    (∑ j ∈ Finset.Icc 1 N, ‖Yb ((j : ℝ) / N) - Yb (((j : ℝ) - 1) / N)‖) ≤
      frameBound w * M + 2 * frameLip w * (T / N) * L ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using mul_nonneg (frameBound_nonneg (by simpa using hwidth 0 (by simp) 0 0))
      (unit_lipschitz_constant_nonneg hl)
  intro Yb
  let C := frameBound w * M + 2 * frameLip w * (T / N) * L ^ 2
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      ‖Yb ((j : ℝ) / N) - Yb (((j : ℝ) - 1) / N)‖ ≤ C / N :=
    uniform_step_sigma_LM hT H Hd hH hd hbd hl hw hwidth j
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  -- There are N jumps, each bounded by C/N, including the two endpoint pairs.
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 N, C / N := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (C / N) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = C := mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')

/-- General-step endpoint values and jumps of the periodic
pieces, and the variation of their end-value multiplier, for any supplied derivative
bound `L` and Lipschitz bound `M`. `lem_boundary` specializes them to the attained
maximum and least Lipschitz constant of Theorem 4.2.
The continuous within derivative Hd represents the C¹ path on the closed interval. -/
theorem lem_boundary_uniform [NeZero d] {T : ℝ} (hT : 0 < T) {N : ℕ}
    (hN : 0 < N) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let Yr := allSampleCorrectorFamily T N H Hd hH
    let Δ := fun j : ℕ ↦ Yr j (-(1 / 2)) - Yr (j - 1) (1 / 2)
    let Yb := fun s ↦ frameOp ((T / N) • H s) (Hd s)
    let sigma := ∑ j ∈ Finset.Icc 1 N, ‖Yb ((j : ℝ) / N) - Yb (((j : ℝ) - 1) / N)‖
    let c₀ := frameBound w - frameBound (w / 2) / 2
    (‖Yr 0 0‖ + ‖Yr N 0‖ + ∑ j ∈ Finset.Icc 1 N, ‖Δ j‖ ≤
      T / (N : ℝ) ^ 2 * (2 * c₀ * L + sigma)) ∧
    sigma ≤ frameBound w * M + 2 * frameLip w * (T / N) * L ^ 2 := by
  intro Yr Δ Yb sigma c₀
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw₀ : 0 ≤ w := by simpa using hwidth 0 (by omega) 0 0
  have hc₀ : 0 ≤ c₀ := center_bound_nonneg hw₀ hw
  -- Linearity identifies each jump with T/N² times the adjacent frame-value change.
  have hjump : (∑ j ∈ Finset.Icc 1 N, ‖Δ j‖) = T / (N : ℝ) ^ 2 * sigma := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show Δ j = _ from uniformCorrectionPiece_jump_frame T N H Hd hH hw hwidth
      (j := (j : ℤ)) (by exact_mod_cast (Finset.mem_Icc.mp hj).1)
      (by exact_mod_cast (Finset.mem_Icc.mp hj).2)]
    simp only [norm_smul_of_nonneg (by positivity : 0 ≤ T / (N : ℝ)^2), Yb, Int.cast_natCast]
  -- Lemma A.3 bounds the sum of adjacent frame-value changes.
  refine ⟨?_, uniform_steps_sigma_LM hT.le H Hd hH hd hbd hlip hw hwidth⟩
  -- the proof of Lemma A.1 at the cell centers bounds the two outer endpoint values.
  have hends : ‖Yr 0 0‖ + ‖Yr N 0‖ ≤
      c₀ * T / (N : ℝ) ^ 2 * (‖Hd 0‖ + ‖Hd 1‖) := by
    simpa only [Int.cast_zero, zero_div, Int.cast_natCast, div_self hn.ne', mul_add] using
      add_le_add (allSampleCorrectorFamily_center_norm_le hT.le N H Hd hH hw hwidth
        (r := 0) (by omega)) (allSampleCorrectorFamily_center_norm_le hT.le N H Hd hH hw hwidth
        (r := N) (by omega))
  rw [hjump]
  have hendsLM := mul_le_mul_of_nonneg_left
    (add_le_add (hbd 0 (by norm_num)) (hbd 1 (by norm_num)))
    (show 0 ≤ c₀ * T / (N : ℝ) ^ 2 by positivity)
  exact (add_le_add_left (hends.trans hendsLM) (T / (N : ℝ) ^ 2 * sigma)).trans_eq (by ring)


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
