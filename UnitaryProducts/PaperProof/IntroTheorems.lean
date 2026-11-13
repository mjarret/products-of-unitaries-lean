/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.ExamplesPi
public import UnitaryProducts.PaperProof.WalkCoefficients

/-!
# The introductory comparisons

## Declarations

- `introthm_unit`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Set MeasureTheory Real
open UnitaryProducts.Paper UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Theorem A** (`introthm:unit`): for every integer `T ≥ 1`, the
width-pi comparison with the derivative supremum and its Lipschitz constant `L`.
The proof specializes (4.6), bounds both endpoint derivatives by their supremum,
and inserts the three decimal upper bounds. Dimension zero is included. -/
theorem introthm_unit
    (H : ℝ → 𝕄) (T : ℕ) (hT : 1 ≤ T) (hH : IsTimeDepHamiltonian H)
    (L : ℝ) (hder : HasLipschitzDerivative H (derivWithin H (Icc (0 : ℝ) 1)) L)
    (hwidth : HasSampleWidth H T π) :
    let D := unitSupNorm (derivWithin H (Icc (0 : ℝ) 1))
    ‖UnitaryProducts.evol (H 1) (1 / 2) * (unitProduct H T).1 *
      UnitaryProducts.evol (H 0) (-(1 / 2)) - evolution H T T‖ ≤
      ((116 / 1000 : ℝ) * D + (143 / 1000 : ℝ) * L + (61 / 1000 : ℝ) * D ^ 2) / T := by
  let U := evolution H T
  have hU := evolution_spec (Nat.cast_pos.mpr (show 0 < T by omega)) hH
    (UnitaryProducts.Prose.regulated_of_continuousOn hder.continuousOn)
  obtain ⟨hd, hlip⟩ := hder
  have hdiff : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).differentiableWithinAt
  have hwidth := (hasSampleWidth_iff hH).1 hwidth
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  have hL : 0 ≤ L := by
    have h := hlip 0 (by norm_num) 1 (by norm_num)
    simp only [sub_zero, abs_one, mul_one] at h
    exact (norm_nonneg _).trans h
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero]
    have hsup : unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) = 0 := by
      simp [unitSupNorm, hz]
    rw [hsup]
    positivity
  letI : NeZero d := ⟨hdpos.ne'⟩
  have hb := products_pi (by omega) H Hd U hH
    (fun s hs ↦ (hdiff s hs).hasDerivWithinAt) hlip hwidth hU
  have hcoeff := hamiltonianEnergy_pi_le H Hd
    ⟨fun s hs ↦ (hdiff s hs).hasDerivWithinAt, hlip⟩
  exact hb.trans (div_le_div_of_nonneg_right hcoeff.2.2.2 (by positivity))

end UnitaryProducts.PaperProof
