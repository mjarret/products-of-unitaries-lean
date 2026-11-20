/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Algebra.Order.Round
public import UnitaryProducts.Comparison.OneSize
public import UnitaryProducts.Spectral.CircularBands
public import UnitaryProducts.Corrector.ScalarEntrySolutions
public import UnitaryProducts.Evolution.RegulatedComparison
public import UnitaryProducts.Paper.OneVariable
public import UnitaryProducts.Spectral.ExactGap
public import UnitaryProducts.Walks.LogarithmBranch
public import UnitaryProducts.Spectral.BandTransfer

/-!
# Mathematical claims in the abstract and introduction

## Declarations

- `periodic_corrector_zero_limit`
- `rounded_hamiltonian_regulated`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Real Set Filter MeasureTheory Matrix
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed

noncomputable section
namespace UnitaryProducts.Paper

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1, the rounded-clock Hamiltonian is regulated regardless of the path's regularity. -/
theorem rounded_hamiltonian_regulated (H : ℝ → 𝕄) (N : ℕ) :
    IsRegulated (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / N)) 0 N := by
  let a : ℕ → ℝ := fun j ↦ if j = 0 then 0 else min N ((j : ℝ) - 1 / 2)
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a (N + 1) = N := by
    simp only [a, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
    exact min_eq_left (by linarith)
  rw [← ha0, ← haN]
  apply piecewise_regulated _ a (fun j ↦ H ((j : ℝ) / N)) (N + 1)
  intro j hj t ht
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (show j ≤ N by omega)
  have hlo : (j : ℝ) ≤ t + 1 / 2 := by
    by_cases hz : j = 0
    · subst j; simp only [ha0] at ht; push_cast; linarith [ht.1]
    · have he : a j = (j : ℝ) - 1 / 2 := by
        simp only [a, if_neg hz]; exact min_eq_right (by linarith)
      rw [he] at ht; linarith [ht.1]
  have hhi : t + 1 / 2 < (j : ℝ) + 1 := by
    have he : a (j + 1) ≤ (j : ℝ) + 1 / 2 := by
      simp only [a, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
      linarith [min_le_right (N : ℝ) ((j : ℝ) + 1 - 1 / 2)]
    linarith [ht.2]
  have hfloor : ⌊t + 1 / 2⌋ = (j : ℤ) := Int.floor_eq_iff.mpr
    ⟨by simpa only [Int.cast_natCast] using hlo,
      by simpa only [Int.cast_natCast] using hhi⟩
  simp only [hfloor, Int.cast_natCast, haN]

/-- Section 1, the zero-frequency selection is the limit of the endpoint multiplier. The
corresponding
normalized solution is (tau^2/2 - 1/24)a and its common endpoint value is a/12. -/
theorem periodic_corrector_zero_limit (a : ℂ) :
    Tendsto (fun x : ℝ ↦ (UnitaryProducts.Corrector.frameMult x : ℂ) * a)
      (𝓝[≠] 0) (𝓝 (a / 12)) ∧
    (∀ τ : ℝ, HasDerivAt (fun t : ℝ ↦ ((t : ℂ) ^ 2 / 2 - 1 / 24) * a)
      ((τ : ℂ) * a) τ) ∧
    ((1 / 2 : ℂ) ^ 2 / 2 - 1 / 24) * a = a / 12 ∧
    ((-1 / 2 : ℂ) ^ 2 / 2 - 1 / 24) * a = a / 12 := by
  refine ⟨?_, fun τ ↦ ?_, by ring, by ring⟩
  · have hc := (Complex.continuous_ofReal.continuousAt.comp
      UnitaryProducts.Separation.analyticAt_frameMult_zero.continuousAt).mul_const a
    have he : ((UnitaryProducts.Corrector.frameMult 0 : ℝ) : ℂ) * a = a / 12 := by
      simp only [UnitaryProducts.Corrector.frameMult]; push_cast; ring
    simpa only [Function.comp_def, he] using hc.mono_left nhdsWithin_le_nhds
  · have ht : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 τ := by simpa using (hasDerivAt_id' τ).ofReal_comp
    convert (((ht.pow 2).div_const 2).sub_const (1 / 24)).mul_const a using 1
    ring

end UnitaryProducts.Paper
