/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Prose.Introduction

/-!
# The unit-step comparison with a maximum and a Lipschitz supremum

## Declarations

- `exists_norm_eq_unitSupNorm`
- `unitLip`
- `unitLip_spec`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A continuous norm on `[0, 1]` attains the supremum used in the paper. -/
theorem exists_norm_eq_unitSupNorm {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → E} (hc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    ∃ s ∈ Icc (0 : ℝ) 1, ‖F s‖ = unitSupNorm F := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, zero_le_one⟩) hc.norm
  refine ⟨s, hs, le_antisymm (norm_le_unitSupNorm hc hs) ?_⟩
  exact csSup_le ⟨‖F s‖, s, hs, rfl⟩ (by
    rintro _ ⟨t, ht, rfl⟩
    exact hmax ht)

/-- The Lipschitz constant on `[0,1]`, defined by the distinct-point
difference quotients. No attainment is asserted for this supremum. -/
def unitLip {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) : ℝ :=
  sSup {r : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
    s ≠ t ∧ r = ‖F t - F s‖ / |t - s|}

/-- A global Lipschitz bound makes the quotient supremum finite, nonnegative,
and itself a Lipschitz bound. -/
theorem unitLip_spec {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    {M : ℝ} (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F t - F s‖ ≤ M * |t - s|) :
    0 ≤ unitLip F ∧ unitLip F ≤ M ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖F t - F s‖ ≤ unitLip F * |t - s| := by
  let S := {r : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
    s ≠ t ∧ r = ‖F t - F s‖ / |t - s|}
  have hne : S.Nonempty :=
    ⟨_, 0, ⟨le_rfl, zero_le_one⟩, 1, ⟨zero_le_one, le_rfl⟩, by norm_num, rfl⟩
  have hb : ∀ r ∈ S, r ≤ M := by
    rintro _ ⟨s, hs, t, ht, hst, rfl⟩
    exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hst.symm))).mpr (hl s hs t ht)
  have hB : BddAbove S := ⟨M, hb⟩
  refine ⟨?_, csSup_le hne hb, ?_⟩
  · apply Real.sSup_nonneg
    rintro _ ⟨s, hs, t, ht, hst, rfl⟩
    exact div_nonneg (norm_nonneg _) (abs_nonneg _)
  · intro s hs t ht
    by_cases he : s = t
    · subst t; simp
    · exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm he)))).mp
        (le_csSup hB ⟨s, hs, t, ht, he, rfl⟩)


end UnitaryProducts.PaperProof
