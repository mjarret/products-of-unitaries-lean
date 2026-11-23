/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueSeriesIdentities
public import RoundedClocks.Appendix.CommutatorTelescope

/-! # Series bounds for the end value

Lemma A.3 bounds the multiplier tail by its positive series and the Jacobi identity for the
remaining scalar sum.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real

noncomputable section

namespace RoundedClocks.EndValueCitedBounds

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The constant term in (F-split) is the multiplier's defining value at zero. -/
theorem multiplier_zero : 𝒩 0 = multiplierCoeff 0 := by
  rw [𝒩, if_pos rfl, multiplierCoeff_zero]

/-- Removing degree zero from the DLMF series gives the scalar tail in (F-split). -/
theorem positive_tail {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∑' n : ℕ, multiplierCoeff (n + 1) * w ^ (n + 1)) = 𝒩 w - 𝒩 0 := by
  have hs := (summable_multiplierCoeff_power
    (by rwa [abs_of_nonneg hw0])).tsum_eq_zero_add
  rw [endValue_coeffSeries_cited w (by rwa [abs_of_nonneg hw0])] at hs
  rw [multiplier_zero]
  simpa only [pow_zero, mul_one, eq_sub_iff_add_eq, add_comm] using hs.symm

/-- Equation (series-bound) follows by summing the width bounds and citing DLMF. -/
theorem norm_series_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    ‖multiplierSeriesOp Ω E‖ ≤ 𝒩 w * ‖E‖ := by
  have hs := summable_norm_multiplierSeriesOp hΩ hw0 hw hwidth (E := E)
  have hb (n : ℕ) : ‖(multiplierCoeff n : ℂ) • (adL Ω ^ n) E‖ ≤
      multiplierCoeff n * w ^ n * ‖E‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (multiplierCoeff_nonneg n)]
    calc
      multiplierCoeff n * ‖(adL Ω ^ n) E‖ ≤
          multiplierCoeff n * (w ^ n * ‖E‖) :=
        mul_le_mul_of_nonneg_left (norm_adL_pow_apply_le hΩ hw0 hwidth n)
          (multiplierCoeff_nonneg n)
      _ = multiplierCoeff n * w ^ n * ‖E‖ := by ring
  have hscalar : Summable (fun n : ℕ ↦ multiplierCoeff n * w ^ n * ‖E‖) :=
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0])).mul_right ‖E‖
  calc
    ‖multiplierSeriesOp Ω E‖ ≤
        ∑' n : ℕ, ‖(multiplierCoeff n : ℂ) • (adL Ω ^ n) E‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, multiplierCoeff n * w ^ n * ‖E‖ :=
      hs.tsum_le_tsum hb hscalar
    _ = (∑' n : ℕ, multiplierCoeff n * w ^ n) * ‖E‖ := tsum_mul_right
    _ = 𝒩 w * ‖E‖ := by
      rw [endValue_coeffSeries_cited w (by rwa [abs_of_nonneg hw0])]

/-- The two Jacobi boundary terms give the positive-degree bound in (F-split). -/
theorem norm_F_commutator_le [NeZero d] {Ω : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (Λ D : 𝕄) :
    ‖endValue_F Ω (adL Ω Λ) D‖ ≤ 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by
  have ha := (norm_adL_le_width hΩ hw0 hwidth).trans_lt hw
  have hc (E : 𝕄) : ‖adL Λ E‖ ≤ 2 * ‖Λ‖ * ‖E‖ := by
    simpa only [zero_smul, sub_zero] using norm_adL_apply_le Λ E 0
  have hb (n : ℕ) :
      ‖(multiplierCoeff (n + 1) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL Λ D) - adL Λ ((adL Ω ^ (n + 1)) D))‖ ≤
      4 * (multiplierCoeff (n + 1) * w ^ (n + 1)) * ‖Λ‖ * ‖D‖ := by
    have hleft : ‖(adL Ω ^ (n + 1)) (adL Λ D)‖ ≤
        w ^ (n + 1) * (2 * ‖Λ‖ * ‖D‖) :=
      (norm_adL_pow_apply_le hΩ hw0 hwidth (n + 1)).trans
        (mul_le_mul_of_nonneg_left (hc D) (pow_nonneg hw0 _))
    have hright : ‖adL Λ ((adL Ω ^ (n + 1)) D)‖ ≤
        2 * ‖Λ‖ * (w ^ (n + 1) * ‖D‖) :=
      (hc _).trans (mul_le_mul_of_nonneg_left
        (norm_adL_pow_apply_le hΩ hw0 hwidth (n + 1)) (by positivity))
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (multiplierCoeff_nonneg _)]
    calc
      _ ≤ multiplierCoeff (n + 1) *
          (‖(adL Ω ^ (n + 1)) (adL Λ D)‖ +
            ‖adL Λ ((adL Ω ^ (n + 1)) D)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (multiplierCoeff_nonneg _)
      _ ≤ multiplierCoeff (n + 1) *
          (w ^ (n + 1) * (2 * ‖Λ‖ * ‖D‖) +
            2 * ‖Λ‖ * (w ^ (n + 1) * ‖D‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hleft hright) (multiplierCoeff_nonneg _)
      _ = _ := by ring
  have ht := (((summable_nat_add_iff 1).mpr
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))).mul_left 4).mul_right
      ‖Λ‖ |>.mul_right ‖D‖
  have hs := Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hb ht
  rw [endValue_F_commutator_series Ω Λ D ha]
  calc
    _ ≤ ∑' n : ℕ, ‖(multiplierCoeff (n + 1) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL Λ D) - adL Λ ((adL Ω ^ (n + 1)) D))‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, 4 * (multiplierCoeff (n + 1) * w ^ (n + 1)) * ‖Λ‖ * ‖D‖ :=
      hs.tsum_le_tsum hb ht
    _ = 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by
      rw [tsum_mul_right, tsum_mul_right, tsum_mul_left, positive_tail hw0 hw]

end RoundedClocks.EndValueCitedBounds
