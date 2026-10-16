/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.UniformConstants
public import UnitaryProducts.Evolution.RoundedClockEvolution

/-! # Unitary factors and the cost of substituting logarithm bounds

These declarations back the unnumbered assertions after Definition 2.3 and
at the start of Section 4.2. No regularity is required to represent finitely
many factors. The coefficient limits use the paper's series and sine quotient.
-/

@[expose] public section
noncomputable section
open Real Set Filter
open UnitaryProducts.Paper UnitaryProducts.PaperProof
open scoped Topology Matrix.Norms.L2Operator
namespace UnitaryProducts.Prose

/-- Every finite product of unitaries is the T-step product of a Hermitian
family: choose logarithms of the factors and extend their sample values. -/
theorem exists_unitProduct_of_unitaries {d T : ℕ} (hT : 0 < T)
    (U : ℕ → Matrix (Fin d) (Fin d) ℂ) (hU : ∀ j < T, star (U j) * U j = 1) :
    ∃ H : ℝ → Matrix (Fin d) (Fin d) ℂ,
      (∀ s, (H s).IsHermitian) ∧
      (∀ j < T, evol (H (j / T)) 1 = U j) ∧
      (unitProduct H T).1 = ((List.range T).map U).reverse.prod := by
  obtain ⟨A, hA, hAU, hprod⟩ := unitary_product_evolution T U hU
  let H := fun s : ℝ ↦ A ⌊s * T⌋₊
  have hT0 : (T : ℝ) ≠ 0 := (Nat.cast_pos.mpr hT).ne'
  have hs (j : ℕ) : H (j / T) = A j := by
    dsimp only [H]
    rw [div_mul_cancel₀ _ hT0, Nat.floor_natCast]
  refine ⟨H, fun s ↦ hA _, fun j hj ↦ ?_, ?_⟩
  · rw [hs]
    exact hAU j hj
  · simpa only [unitProduct, hs] using hprod


end UnitaryProducts.Prose
