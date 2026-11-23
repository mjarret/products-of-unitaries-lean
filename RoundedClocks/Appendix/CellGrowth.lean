/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.MatrixSeries

/-! # Lemma A.1(ii): the bound `‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2`

As `Y' + i[Ω,Y] = τD`, the conjugate `e^{iτΩ} Y e^{-iτΩ}` has derivative `τ e^{iτΩ} D e^{-iτΩ}`.
Integrating from `0` to `τ` gives
`Y(τ) = e^{-iτΩ} (Y(0) + ∫₀^τ σ e^{iσΩ} D e^{-iσΩ} dσ) e^{iτΩ}`, and conjugation by a unitary
preserves the norm. Here `cellPhase Ω τ` is `e^{iτΩ}`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `cellPhase Ω τ` is `e^{iτΩ}`. -/
private def cellPhase (Ω : 𝕄) (τ : ℝ) : 𝕄 := exp (τ • (I • Ω))

/-- `(e^{iτΩ})' = e^{iτΩ} iΩ`. -/
private lemma cellPhase_deriv (Ω : 𝕄) (τ : ℝ) :
    HasDerivAt (cellPhase Ω) (cellPhase Ω τ * (I • Ω)) τ :=
  hasDerivAt_exp_smul_const (I • Ω) τ

/-- `(e^{-iτΩ})' = -iΩ e^{-iτΩ}`. -/
private lemma cellPhase_neg_deriv (Ω : 𝕄) (τ : ℝ) :
    HasDerivAt (fun σ ↦ cellPhase Ω (-σ)) ((-I • Ω) * cellPhase Ω (-τ)) τ := by
  simpa only [cellPhase, Function.comp_def, neg_smul, neg_mul, smul_neg, one_smul] using
    (hasDerivAt_exp_smul_const' (I • Ω) (-τ)).scomp τ (hasDerivAt_neg τ)

/-- `τ ↦ e^{iτΩ}` is continuous. -/
private lemma cellPhase_continuous (Ω : 𝕄) : Continuous (cellPhase Ω) :=
  continuous_iff_continuousAt.mpr fun τ ↦ (cellPhase_deriv Ω τ).continuousAt

/-- `(e^{iτΩ})† = e^{-iτΩ}` for Hermitian `Ω`. -/
private lemma cellPhase_star {Ω : 𝕄} (hΩ : IsHermitian Ω) (τ : ℝ) :
    star (cellPhase Ω τ) = cellPhase Ω (-τ) := by
  simp [cellPhase, NormedSpace.star_exp, star_smul, hΩ.isSelfAdjoint.star_eq,
    neg_smul, smul_neg]

/-- If `Y' + i[Ω,Y] = σD`, then `e^{iσΩ} Y e^{-iσΩ}` has derivative `σ e^{iσΩ} D e^{-iσΩ}`. -/
private lemma cell_conjugate_deriv (Ω D : 𝕄) {Y : ℝ → 𝕄} {σ : ℝ}
    (hY : HasDerivWithinAt Y (σ • D - I • (Ω * Y σ - Y σ * Ω))
      (Icc (-1 / 2 : ℝ) (1 / 2)) σ) :
    HasDerivWithinAt (fun s ↦ cellPhase Ω s * Y s * cellPhase Ω (-s))
      (σ • (cellPhase Ω σ * D * cellPhase Ω (-σ)))
      (Icc (-1 / 2 : ℝ) (1 / 2)) σ := by
  convert ((cellPhase_deriv Ω σ).hasDerivWithinAt.mul hY).mul
    (cellPhase_neg_deriv Ω σ).hasDerivWithinAt using 1
  simp only [Pi.mul_apply, add_mul, mul_sub, sub_mul, smul_sub, mul_smul_comm,
    smul_mul_assoc, neg_smul, neg_mul, mul_neg, mul_assoc]
  abel

/-- `|∫₀^τ |σ| dσ| = τ²/2`, for `τ` of either sign. -/
private lemma cell_abs_integral (τ : ℝ) :
    |(∫ σ in (0 : ℝ)..τ, |σ|)| = τ ^ 2 / 2 := by
  rcases le_total 0 τ with ht | ht
  · have he : (∫ σ in (0 : ℝ)..τ, |σ|) = ∫ σ in (0 : ℝ)..τ, σ :=
      intervalIntegral.integral_congr fun σ hs ↦
        abs_of_nonneg (by simpa [min_eq_left ht] using hs.1)
    rw [he, integral_id, zero_pow, sub_zero, abs_of_nonneg (by positivity)]
    norm_num
  · have he : (∫ σ in (0 : ℝ)..τ, |σ|) = ∫ σ in (0 : ℝ)..τ, -σ :=
      intervalIntegral.integral_congr fun σ hs ↦
        abs_of_nonpos (by simpa [max_eq_left ht] using hs.2)
    rw [he, intervalIntegral.integral_neg, integral_id, zero_pow, sub_zero,
      abs_neg, abs_of_nonneg (by positivity)]
    norm_num

/-- Integrating from `0` to `τ`: `Y(τ) = e^{-iτΩ} (Y(0) + ∫₀^τ σ e^{iσΩ} D e^{-iσΩ} dσ) e^{iτΩ}`. -/
private lemma cell_integral_formula {Ω : 𝕄} (hΩ : IsHermitian Ω) (D : 𝕄)
    {Y : ℝ → 𝕄} (hY : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
        (Icc (-1 / 2) (1 / 2)) τ) {τ : ℝ}
    (hτ : τ ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    Y τ = cellPhase Ω (-τ) * (Y 0 + ∫ σ in (0 : ℝ)..τ,
      σ • (cellPhase Ω σ * D * cellPhase Ω (-σ))) * cellPhase Ω τ := by
  let Z := fun σ ↦ cellPhase Ω σ * Y σ * cellPhase Ω (-σ)
  let F := fun σ ↦ σ • (cellPhase Ω σ * D * cellPhase Ω (-σ))
  -- `Z(σ) = e^{iσΩ} Y(σ) e^{-iσΩ}` has derivative `F(σ) = σ e^{iσΩ} D e^{-iσΩ}`.
  have hZ (σ : ℝ) (hσ : σ ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivWithinAt Z (F σ) (Icc (-1 / 2 : ℝ) (1 / 2)) σ :=
    cell_conjugate_deriv Ω D (hY σ hσ)
  have hsub : uIcc 0 τ ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro σ hσ
    exact ⟨(le_min (by norm_num) hτ.1).trans hσ.1,
      hσ.2.trans (max_le (by norm_num) hτ.2)⟩
  have hF : Continuous F :=
    continuous_id.smul (((cellPhase_continuous Ω).mul continuous_const).mul
      ((cellPhase_continuous Ω).comp continuous_neg))
  -- Integrating from `0` to `τ`: `∫₀^τ F = Z(τ) - Z(0)`.
  have hint : (∫ σ in (0 : ℝ)..τ, F σ) = Z τ - Z 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
      ((show ContinuousOn Z (Icc (-1 / 2 : ℝ) (1 / 2)) from
        fun σ hσ ↦ (hZ σ hσ).continuousWithinAt).mono hsub)
    · intro σ hσ
      have hσ' : σ ∈ Ioo (-1 / 2 : ℝ) (1 / 2) :=
        ⟨lt_of_le_of_lt (le_min (by norm_num) hτ.1) hσ.1,
          lt_of_lt_of_le hσ.2 (max_le (by norm_num) hτ.2)⟩
      exact ((hZ σ ⟨hσ'.1.le, hσ'.2.le⟩).hasDerivAt
        (Icc_mem_nhds hσ'.1 hσ'.2)).hasDerivWithinAt
    · exact hF.intervalIntegrable _ _
  have hzero : Z 0 = Y 0 := by simp [Z, cellPhase]
  have hsum : Y 0 + ∫ σ in (0 : ℝ)..τ, F σ = Z τ := by rw [hint, hzero]; abel
  -- `Z(0) = Y(0)`, and conjugating back gives `Y(τ)`.
  change Y τ = cellPhase Ω (-τ) *
    (Y 0 + ∫ σ in (0 : ℝ)..τ, F σ) * cellPhase Ω τ
  rw [hsum]
  have hi : cellPhase Ω (-τ) * cellPhase Ω τ = 1 := by
    rw [← cellPhase_star hΩ]
    simpa only [cellPhase, Complex.ofReal_neg, neg_smul, smul_neg, neg_neg] using
      Unitary.star_mul_self_of_mem (exp_neg_I_smul_isUnitary hΩ (-τ))
  simp only [Z, ← mul_assoc, hi, one_mul]
  rw [mul_assoc, hi, mul_one]


/-- If `‖F(σ)‖ ≤ |σ| C` for every `σ`, then `‖∫₀^τ F‖ ≤ (τ²/2) C`. -/
private lemma cell_integral_bound (F : ℝ → 𝕄) (C τ : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ σ : ℝ, ‖F σ‖ ≤ |σ| * C) :
    ‖∫ σ in (0 : ℝ)..τ, F σ‖ ≤ τ ^ 2 / 2 * C := by
  have hcont : Continuous (fun σ : ℝ ↦ |σ| * C) :=
    continuous_abs.mul continuous_const
  have hint : IntervalIntegrable (fun σ : ℝ ↦ |σ| * C)
      MeasureTheory.volume 0 τ := hcont.intervalIntegrable 0 τ
  have hbound : ‖∫ σ in (0 : ℝ)..τ, F σ‖ ≤
      |∫ σ in (0 : ℝ)..τ, |σ| * C| :=
    intervalIntegral.norm_integral_le_abs_of_norm_le
      (MeasureTheory.ae_of_all _ hpoint) hint
  have hscalar : |∫ σ in (0 : ℝ)..τ, |σ| * C| = τ ^ 2 / 2 * C := by
    rw [intervalIntegral.integral_mul_const, abs_mul,
      abs_of_nonneg hC, cell_abs_integral]
  exact hbound.trans_eq hscalar

/-- `‖σ e^{iσΩ} D e^{-iσΩ}‖ = |σ| ‖D‖`. -/
private lemma cell_integrand_norm [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω)
    (D : 𝕄) (σ : ℝ) :
    ‖σ • (cellPhase Ω σ * D * cellPhase Ω (-σ))‖ = |σ| * ‖D‖ := by
  rw [norm_smul, Real.norm_eq_abs, ← cellPhase_star hΩ,
    norm_unitary_conj_eq D (by
      simpa only [cellPhase, Complex.ofReal_neg, neg_smul, smul_neg, neg_neg] using
        exp_neg_I_smul_isUnitary hΩ (-σ))]

/-- `‖∫₀^τ σ e^{iσΩ} D e^{-iσΩ} dσ‖ ≤ (τ²/2) ‖D‖`. -/
private lemma cell_integral_norm [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω)
    (D : 𝕄) (τ : ℝ) :
    ‖∫ σ in (0 : ℝ)..τ, σ • (cellPhase Ω σ * D * cellPhase Ω (-σ))‖ ≤
      τ ^ 2 / 2 * ‖D‖ :=
  cell_integral_bound _ ‖D‖ τ (norm_nonneg D) fun σ ↦ (cell_integrand_norm hΩ D σ).le

/-- Lemma A.1(ii), second bound: a solution of `Y' + i[Ω,Y] = τD` for `|τ| ≤ 1/2` satisfies
`‖Y(τ)‖ ≤ ‖Y(0)‖ + τ² ‖D‖/2`. -/
theorem norm_le_of_cellEquation [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) (D : 𝕄)
    {Y : ℝ → 𝕄} (hY : ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
      HasDerivWithinAt Y (τ • D - I • (Ω * Y τ - Y τ * Ω))
        (Icc (-1 / 2) (1 / 2)) τ) :
    ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Y τ‖ ≤ ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 := by
  intro τ hτ
  have hformula := cell_integral_formula hΩ D hY hτ
  have hbound := cell_integral_norm hΩ D τ
  generalize (∫ σ in (0 : ℝ)..τ, σ • (cellPhase Ω σ * D * cellPhase Ω (-σ))) = J
    at hformula hbound
  have hn : ‖cellPhase Ω (-τ) * (Y 0 + J) * star (cellPhase Ω (-τ))‖ = ‖Y 0 + J‖ :=
    norm_unitary_conj_eq (Y 0 + J) (by
      simpa only [cellPhase, Complex.ofReal_neg, neg_smul, smul_neg, neg_neg] using
        exp_neg_I_smul_isUnitary hΩ τ)
  rw [cellPhase_star hΩ, neg_neg] at hn
  calc
    ‖Y τ‖ = ‖cellPhase Ω (-τ) * (Y 0 + J) * cellPhase Ω τ‖ := by rw [hformula]
    _ = ‖Y 0 + J‖ := hn
    _ ≤ ‖Y 0‖ + ‖J‖ := norm_add_le _ _
    _ ≤ ‖Y 0‖ + τ ^ 2 / 2 * ‖D‖ := by gcongr
    _ = ‖Y 0‖ + τ ^ 2 * ‖D‖ / 2 := by ring

end RoundedClocks
