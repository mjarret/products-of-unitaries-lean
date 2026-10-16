/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ClosedCellConstruction
public import UnitaryProducts.Prose.ChainSteps
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.WalkScalarCut
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-! # Literal intermediate steps in Appendix A.1–A.2 -/
@[expose] public section
open Real Complex Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Prose
noncomputable section
namespace UnitaryProducts.PaperProof

/-- The local phase bound in Lemma A.2: shift the moving spectral window
by the fixed midpoint at the base point. -/
theorem moving_window_center_bound {θ a a₀ w : ℝ}
    (hθ : θ ∈ Icc a (a + w)) :
    |θ - (a₀ + w / 2)| ≤ |a - a₀| + w / 2 := by
  have hcenter : |θ - (a + w / 2)| ≤ w / 2 :=
    abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  calc
    _ = |(θ - (a + w / 2)) + (a - a₀)| := by congr 1; ring
    _ ≤ |θ - (a + w / 2)| + |a - a₀| := abs_add_le _ _
    _ ≤ |a - a₀| + w / 2 := by linarith


/-- The explicit even coefficients in the appendix follow from Mathlib's
Euler evaluation of the positive even zeta values. The index `m+1` means `m≥1`. -/
theorem frame_coefficient_even_partial_fractions (k : ℕ) :
    |((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (Nat.factorial (2 * k + 2) : ℝ) =
      ∑' m : ℕ, 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) := by
  have hz := hasSum_zeta_nat (k := k + 1) (by omega)
  have hsign := neg_one_pow_mul_bernoulli_two_mul_add_two k
  have heven : 2 * (k + 1) = 2 * k + 2 := by omega
  have hsignpow : (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ k := by
    rw [show k + 1 + 1 = k + 2 by omega, pow_add]
    norm_num
  rw [heven, hsignpow] at hz
  have h := hz.mul_left (2 / (2 * π) ^ (2 * k + 2))
  have hterms : (fun m : ℕ ↦ (2 / (2 * π) ^ (2 * k + 2)) *
      (1 / (m : ℝ) ^ (2 * k + 2))) =
      (fun m : ℕ ↦ 2 / (2 * π * (m : ℝ)) ^ (2 * k + 2)) := by
    funext m
    rw [mul_pow]
    ring
  rw [hterms] at h
  have hvalue : (2 / (2 * π) ^ (2 * k + 2)) *
      ((-1 : ℝ) ^ k * 2 ^ (2 * k + 2 - 1) * π ^ (2 * k + 2) *
        ((bernoulli (2 * k + 2) : ℚ) : ℝ) / (Nat.factorial (2 * k + 2) : ℝ)) =
      |((bernoulli (2 * k + 2) : ℚ) : ℝ)| / (Nat.factorial (2 * k + 2) : ℝ) := by
    rw [← hsign, mul_pow, show 2 * k + 2 - 1 = 2 * k + 1 by omega,
      show (2 : ℝ) ^ (2 * k + 2) = 2 ^ (2 * k + 1) * 2 by rw [← pow_succ]]
    field_simp
  rw [hvalue] at h
  have hshift := (hasSum_nat_add_iff (f := fun m : ℕ ↦
    2 / (2 * π * (m : ℝ)) ^ (2 * k + 2)) 1).mpr (by simpa using h)
  simpa only [Nat.cast_add, Nat.cast_one] using hshift.tsum_eq.symm

/-- Odd coefficients vanish, exactly as stated after equation `eq:N-series`. -/
theorem frame_coefficient_odd_zero (k : ℕ) :
    |((bernoulli ((2 * k + 1) + 2) : ℚ) : ℝ)| /
      (Nat.factorial ((2 * k + 1) + 2) : ℝ) = 0 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by omega),
    bernoulli'_eq_zero_of_odd ⟨k + 1, by omega⟩ (by omega)]
  simp


end UnitaryProducts.PaperProof
