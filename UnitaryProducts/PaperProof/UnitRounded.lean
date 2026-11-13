/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.Evolution.RoundedClockEvolution

/-!
# The rounded-clock identity at unit steps

## Declarations

- `unit_rounded_clock_endpoint`
-/

@[expose] public section
open scoped Matrix.Norms.L2Operator
open Set
noncomputable section
namespace UnitaryProducts.PaperProof

/-- Equation (2.5), `eq:rounded`, at the paper's unit steps on `[0,T]`.
The general-duration identity is an internal ingredient of this specialization. -/
theorem unit_rounded_clock_endpoint {d : ℕ} (H : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (hH : UnitaryProducts.Paper.IsTimeDepHamiltonian H)
    (T : ℕ) (hT : 1 ≤ T) (V : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (hV : UnitaryProducts.Paper.IsEvolution
      (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) V 0 T) :
    V T = UnitaryProducts.evol (H 1) (1 / 2) *
      (UnitaryProducts.Paper.unitProduct H T).1 *
        UnitaryProducts.evol (H 0) (-(1 / 2)) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hn : (T : ℝ) ≠ 0 := ne_of_gt hTr
  have hclock : (fun t : ℝ ↦ H ((⌊(T : ℝ) * t / T + 1 / 2⌋ : ℝ) / T)) =
      (fun t : ℝ ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) := by
    funext t
    have h : (T : ℝ) * t / T = t := by field_simp
    rw [h]
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  have h := (UnitaryProducts.Paper.regulated_evolution_rounded (d := d)).2 H hH T T hTr hT V
    (by rw [hclock]; exact hV)
  simpa only [hhalf, div_self hn, one_smul] using h

end UnitaryProducts.PaperProof
