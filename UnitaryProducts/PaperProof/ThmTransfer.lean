/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.FineSteps
public import UnitaryProducts.Prose.LocalSteps

/-!
# Supporting endpoint transfer estimates

## Declarations

- `transfer_hull`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The convex hull used in the unnumbered endpoint-transfer estimate has attained ends and selects
precisely the band. -/
theorem transfer_hull (ev : Fin d → ℝ) {S : Finset (Fin d)} (hS : S.Nonempty)
    {m r : ℝ} (hmem : ∀ i, i ∈ S ↔ |ev i - m| ≤ r) :
    let a := S.inf' hS ev
    let b := S.sup' hS ev
    0 ≤ (b - a) / 2 ∧
      (∀ i, i ∈ S ↔ |ev i - (a + b) / 2| ≤ (b - a) / 2) ∧
      (∃ i ∈ S, ev i = (a + b) / 2 - (b - a) / 2) ∧
      (∃ i ∈ S, ev i = (a + b) / 2 + (b - a) / 2) := by
  dsimp only
  obtain ⟨ia, ha, hea⟩ := S.exists_mem_eq_inf' hS ev
  obtain ⟨ib, hb, heb⟩ := S.exists_mem_eq_sup' hS ev
  have hab : S.inf' hS ev ≤ S.sup' hS ev := (S.inf'_le ev ha).trans (S.le_sup' ev ha)
  refine ⟨div_nonneg (sub_nonneg.mpr hab) zero_le_two, fun i ↦ ?_,
    ⟨ia, ha, by rw [← hea]; ring⟩, ⟨ib, hb, by rw [← heb]; ring⟩⟩
  rw [abs_le]
  constructor
  · intro hi
    have h₁ := S.inf'_le ev hi
    have h₂ := S.le_sup' ev hi
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have hA := (hmem ia).mp ha
    have hB := (hmem ib).mp hb
    rw [abs_le] at hA hB
    rw [hmem i, abs_le]
    constructor <;> linarith




end UnitaryProducts.PaperProof
