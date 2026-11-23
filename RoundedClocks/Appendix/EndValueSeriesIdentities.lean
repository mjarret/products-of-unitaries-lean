/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.MatrixSeries
public import RoundedClocks.Citations

/-! # Cotangent expansion of the endpoint multiplier

Lemma A.3 expresses the endpoint multiplier through the cotangent partial fractions and derives
the scalar coefficient identities used by its derivative estimate.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real
open Real

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- DLMF 4.22.3 (Mathlib's `cot_series_rep`) gives the endpoint multiplier's pole sum. -/
theorem endValue_partialFractions_cited {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    𝒩 x = ∑' m : ℕ, 2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2) := by
  have hn (n : ℤ) : x / 2 ≠ n * π := by
    intro he
    have he' : x = 2 * π * n := by linarith
    by_cases hz : n = 0
    · simp only [hz, Int.cast_zero, mul_zero] at he'
      exact hx0 he'
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hz
      rw [he', abs_mul, abs_of_pos Real.two_pi_pos] at hx
      exact hx.not_ge (le_mul_of_one_le_right Real.two_pi_pos.le h1)
  have hnc (n : ℤ) : (x : ℂ) / 2 ≠ n * (π : ℂ) := by
    exact_mod_cast hn n
  have hc := dlmf_4_22_3 ((x : ℂ) / 2) hnc
  have ht (m : ℕ) :
      2 / ((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2) =
      -(1 / (((x : ℂ) / 2) ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) / 2 := by
    push_cast
    have he : ((x : ℂ) / 2) ^ 2 - (m + 1 : ℂ) ^ 2 * (π : ℂ) ^ 2 =
        -((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2) / 4 := by ring
    rw [he]
    field_simp
    all_goals ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [tsum_congr ht, tsum_div_const, tsum_neg]
  generalize hs : (∑' n : ℕ, 1 /
    (((x : ℂ) / 2) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) = s at hc ⊢
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  simp only [𝒩, if_neg hx0]
  push_cast
  rw [hc]
  field_simp [hxC]
  all_goals ring

/-- The multiplier's coefficient series agrees with the cotangent formula. -/
theorem endValue_coeffSeries_cited (x : ℝ) (hx : |x| < 2 * π) :
    (∑' n : ℕ, multiplierCoeff n * x ^ n) = 𝒩 x := by
  by_cases hx0 : x = 0
  · subst x
    rw [tsum_eq_single 0]
    · simp [𝒩, multiplierCoeff_zero]
    · intro n hn
      simp [zero_pow hn]
  · rw [multiplierCoeff_power_eq_partialFractions hx]
    exact (endValue_partialFractions_cited hx0 hx).symm

/-- The commutator series has the scalar multiplier on every eigenbasis entry. -/
theorem endValue_eigenbasisEntry_cited [NeZero d] {Ω E : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (U† * multiplierSeriesOp Ω E * U) p q =
      (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) *
        (U† * E * U) p q := by
  dsimp only
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hs := (summable_norm_multiplierSeriesOp hΩ hw0 hw hwidth (E := E)).of_norm
  have hmap := ((matrixEntryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (U†) U)).map_tsum hs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    matrixEntryCLM_apply] at hmap
  have hdiff : |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
    (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
      (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw
  have hscalar : (∑' n : ℕ, (multiplierCoeff n : ℂ) *
      ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ n) =
      (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) := by
    simpa only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) (endValue_coeffSeries_cited _ hdiff)
  have hdiag : (hΩ.eigenvectorUnitary : 𝕄)† * Ω *
      (hΩ.eigenvectorUnitary : 𝕄) =
      Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_apply] using hΩ.conjStarAlgAut_star_eigenvectorUnitary
  change (U† * multiplierSeriesOp Ω E * U) p q = _
  rw [multiplierSeriesOp]
  calc
    (U† * (∑' n : ℕ, (multiplierCoeff n : ℂ) • (adL Ω ^ n) E) * U) p q =
        ∑' n : ℕ, (U† * ((multiplierCoeff n : ℂ) •
          (adL Ω ^ n) E) * U) p q := hmap
    _ = (∑' n : ℕ, (multiplierCoeff n : ℂ) *
        ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ n) *
          (U† * E * U) p q := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      rw [adL_pow_eigenbasis_entry Ω E hΩ.eigenvectorUnitary hΩ.eigenvalues
        hdiag n p q]
      ring
    _ = _ := by rw [hscalar]

/-- Under the width hypothesis, the series interpretation agrees with Definition 4.1. -/
theorem endValue_matrixSeries_cited [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) : multiplierSeriesOp Ω E = 𝒩ad Ω E := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hstrict (p q : Fin d) :
      |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
    (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
      (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw
  let F : 𝕄 := Matrix.of fun p q ↦
    (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) * (U† * E * U) p q
  have hkey : U† * multiplierSeriesOp Ω E * U = F := by
    ext p q
    exact endValue_eigenbasisEntry_cited hΩ hw0 hw hwidth p q
  have hU : U† * U = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp hΩ.eigenvectorUnitary.property
  have hU' : U * U† = 1 := mul_eq_one_comm.mp hU
  rw [𝒩ad, dif_pos hΩ, if_pos hstrict]
  change multiplierSeriesOp Ω E = U * F * U†
  calc
    multiplierSeriesOp Ω E =
        U * (U† * multiplierSeriesOp Ω E * U) * U† := by
      rw [show U * (U† * multiplierSeriesOp Ω E * U) * U† =
        (U * U†) * multiplierSeriesOp Ω E * (U * U†) by noncomm_ring,
        hU', one_mul, mul_one]
    _ = U * F * U† := by rw [hkey]


end RoundedClocks
