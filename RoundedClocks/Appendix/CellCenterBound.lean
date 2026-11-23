/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CellFamily
public import RoundedClocks.Citations

/-! # Lemma A.1: the bound `‖Y(0)‖ ≤ c₀ ‖D‖`

By the partial fractions of the cosecant (DLMF 4.22.5),
`-𝒩₀(x) = ∑_{m ≥ 1} (-1)^{m+1} 2/(4π²m² - x²)`, whose coefficient of each `x^{2k}` is an alternating
sum with decreasing terms and so nonnegative. Equation (A.1) then gives
`‖Y(0)‖ = ‖𝒩₀([Ω,·])D‖ ≤ -𝒩₀(w) ‖D‖ = c₀ ‖D‖`. Here `cellCenterCoeff k` is the coefficient of
`x^{2k}` in `-𝒩₀`.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real
open Real

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Substituting `z = x/2` in DLMF 4.22.5 gives
`-𝒩₀(x) = ∑_{m ≥ 1} (-1)^{m+1} 2/(4π²m² - x²)` for `x ≠ 0`. -/
theorem cellCenter_partialFractions_ne_zero
    {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    -cellMultiplier 0 x = ((∑' m : ℕ,
      (-1 : ℝ) ^ m * (2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2))) : ℝ) := by
  have hc := dlmf_4_22_5 ((x : ℂ) / 2) (div_two_ne_int_mul_pi hx0 hx)
  have ht (m : ℕ) :
      (-1 : ℂ) ^ m * (2 / ((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2)) =
      ((-1 : ℂ) ^ (m + 1) /
        (((x : ℂ) / 2) ^ 2 - ((m + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) / 2 := by
    push_cast
    rw [pow_succ]
    have he : ((x : ℂ) / 2) ^ 2 - (m + 1 : ℂ) ^ 2 * (π : ℂ) ^ 2 =
        -((2 * (π : ℂ) * (m + 1 : ℂ)) ^ 2 - (x : ℂ) ^ 2) / 4 := by ring
    rw [he]
    field_simp
    ring
  simp only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast]
  rw [tsum_congr ht, tsum_div_const]
  generalize hs : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) /
    (((x : ℂ) / 2) ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)) = s at hc ⊢
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
  simp only [cellMultiplier, if_neg hx0, Complex.ofReal_zero, mul_zero, sub_zero,
    neg_mul, Complex.exp_zero]
  rw [show (Real.sin (x / 2) : ℂ) = Complex.sin ((x : ℂ) / 2) by push_cast; rfl]
  simp only [one_div, mul_inv]
  rw [hc]
  field_simp [hxC]
  ring

/-- The coefficient of `x^{2k}` in `-𝒩₀(x)`: the alternating sum
`∑_{m ≥ 1} (-1)^{m+1} 2/(2πm)^{2k+2}`. -/
def cellCenterCoeff (k : ℕ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))

/-- Each alternating coefficient is absolutely summable. -/
theorem summable_cellCenterCoeff (k : ℕ) :
    Summable (fun m : ℕ ↦
      (-1 : ℝ) ^ m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))) := by
  apply (summable_multiplierEvenCoeff k).of_norm_bounded
  intro m
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))]
  exact le_rfl

/-- Each coefficient is an alternating sum with decreasing terms and so nonnegative. -/
theorem cellCenterCoeff_nonneg (k : ℕ) : 0 ≤ cellCenterCoeff k := by
  have ha : Antitone (fun m : ℕ ↦ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2)) := by
    intro i j hij
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have ht := (summable_multiplierEvenCoeff k).tendsto_alternating_series_tsum
  simpa [cellCenterCoeff] using ha.alternating_series_le_tendsto ht 0

/-- The absolute value of a cosecant coefficient is bounded by the unsigned pole sum. -/
theorem abs_cellCenterCoeff_le (k : ℕ) :
    |cellCenterCoeff k| ≤ multiplierEvenCoeff k := by
  have hs := (summable_cellCenterCoeff k).norm
  calc
    |cellCenterCoeff k| ≤ ∑' m : ℕ,
        ‖(-1 : ℝ) ^ m * (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))‖ :=
      norm_tsum_le_tsum_norm hs
    _ = multiplierEvenCoeff k := by
      apply tsum_congr
      intro m
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ 2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2))]

/-- The cosecant Taylor series converges inside the first pair of poles. -/
theorem summable_cellCenterCoeff_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun k : ℕ ↦ cellCenterCoeff k * x ^ (2 * k)) := by
  apply (summable_multiplierEvenCoeff_power hx).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_pow, (even_two_mul k).pow_abs]
  exact mul_le_mul_of_nonneg_right (abs_cellCenterCoeff_le k)
    ((even_two_mul k).pow_nonneg x)

/-- Absolute convergence permits swapping the cosecant pole and Taylor sums. -/
theorem summable_cellCenter_partialFraction_power {x : ℝ} (hx : |x| < 2 * π) :
    Summable (fun p : ℕ × ℕ ↦ (-1 : ℝ) ^ p.2 *
      (2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2) * x ^ (2 * p.1))) := by
  apply (summable_multiplier_partialFraction_power hx).of_norm_bounded
  intro p
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ 2 / (2 * π * (p.2 + 1 : ℝ)) ^ (2 * p.1 + 2)),
    (even_two_mul p.1).pow_abs]
  exact le_rfl

/-- Expanding each pole geometrically recovers the cosecant Taylor series. -/
theorem cellCenterCoeff_power_eq_partialFractions {x : ℝ} (hx : |x| < 2 * π) :
    (∑' k : ℕ, cellCenterCoeff k * x ^ (2 * k)) =
      ∑' m : ℕ, (-1 : ℝ) ^ m * (2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2)) := by
  simpa only [cellCenterCoeff] using
    weighted_partialFraction_sum_swap (fun m ↦ (-1 : ℝ) ^ m) hx
      (summable_cellCenter_partialFraction_power hx)

/-- Splitting the zeta-two series into even and odd terms gives the constant coefficient
`-𝒩₀(0) = 1/24`. -/
theorem cellCenterCoeff_zero : cellCenterCoeff 0 = 1 / 24 := by
  let f : ℕ → ℝ := fun m ↦ 2 / (2 * π * (m + 1 : ℝ)) ^ 2
  have hs : Summable f := by simpa [f] using summable_multiplierEvenCoeff 0
  have he : Summable (fun m ↦ f (2 * m)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun m ↦ f (2 * m + 1)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ha : Summable (fun m ↦ (-1 : ℝ) ^ m * f m) := by
    simpa [f] using summable_cellCenterCoeff 0
  have hae := ha.comp_injective (i := fun m : ℕ ↦ 2 * m) (fun _ _ h ↦ by dsimp at h; omega)
  have hao := ha.comp_injective (i := fun m : ℕ ↦ 2 * m + 1) (fun _ _ h ↦ by dsimp at h; omega)
  have hsplit := tsum_even_add_odd (f := f) he ho
  have hasplit := tsum_even_add_odd (f := fun m ↦ (-1 : ℝ) ^ m * f m) hae hao
  have hodd : (∑' m, f (2 * m + 1)) = (∑' m, f m) / 4 := by
    rw [← tsum_div_const]
    apply tsum_congr
    intro m
    dsimp [f]
    push_cast
    have heq : 2 * π * (2 * (m : ℝ) + 1 + 1) = 2 * (2 * π * (m + 1)) := by ring
    rw [heq, mul_pow, div_mul_eq_div_div]
    ring
  have htotal : (∑' m, f m) = 1 / 12 := by
    exact (multiplierCoeff_even 0).symm.trans multiplierCoeff_zero
  have heven (m : ℕ) : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]
    norm_num
  simp only [pow_add, heven, pow_one, one_mul, neg_one_mul, tsum_neg] at hasplit
  change (∑' m, (-1 : ℝ) ^ m * f m) = 1 / 24
  rw [hodd, htotal] at hsplit hasplit
  linarith

/-- For `|x| < 2π`, the series `∑ₖ cellCenterCoeff k · x^{2k}` sums to `-𝒩₀(x)`, also at
`x = 0`. -/
theorem cellCenterCoeff_series_eq
    {x : ℝ} (hx : |x| < 2 * π) :
    ((∑' k : ℕ, cellCenterCoeff k * x ^ (2 * k)) : ℝ) = -cellMultiplier 0 x := by
  by_cases hx0 : x = 0
  · subst x
    rw [tsum_eq_single 0]
    · norm_num [cellCenterCoeff_zero, cellMultiplier]
    · intro k hk
      simp [zero_pow (by omega : 2 * k ≠ 0)]
  · rw [cellCenterCoeff_power_eq_partialFractions hx]
    exact (cellCenter_partialFractions_ne_zero hx0 hx).symm

/-- `-𝒩₀(w) = c₀`, the constant of Appendix B. -/
theorem neg_cellMultiplier_zero_eq_c₀ (w : ℝ) :
    -cellMultiplier 0 w = (c₀ w : ℂ) := by
  by_cases hw : w = 0
  · subst w
    norm_num [cellMultiplier, c₀]
  · simp [cellMultiplier, c₀, hw]

/-- The alternating cosecant series gives `c₀(w) ≥ 0` for `0 ≤ w < 2π`. -/
theorem c₀_nonneg_of_width
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 0 ≤ c₀ w := by
  have habs : |w| < 2 * π := by rwa [abs_of_nonneg hw0]
  have heq : ((∑' k : ℕ, cellCenterCoeff k * w ^ (2 * k) : ℝ) : ℂ) = (c₀ w : ℂ) :=
    (cellCenterCoeff_series_eq habs).trans (neg_cellMultiplier_zero_eq_c₀ w)
  have hreal : (∑' k : ℕ, cellCenterCoeff k * w ^ (2 * k)) = c₀ w :=
    Complex.ofReal_injective heq
  rw [← hreal]
  exact tsum_nonneg fun k ↦
    mul_nonneg (cellCenterCoeff_nonneg k) (pow_nonneg hw0 (2 * k))

/-- `κ ≥ 0` for `0 ≤ w < 2π`. -/
theorem κ_nonneg_of_width {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 0 ≤ κ w := by
  unfold κ
  split_ifs with hz
  · norm_num
  · exact div_nonneg (by positivity)
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)).le

/-- The series `∑ₖ cellCenterCoeff k · [Ω,·]^{2k} E`, which is `-𝒩₀([Ω,·])E`. -/
def cellCenterSeriesOp (Ω E : 𝕄) : 𝕄 :=
  ∑' k : ℕ, (cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E

/-- Absolute convergence of the center commutator series follows from its scalar majorant. -/
theorem summable_norm_cellCenterSeriesOp [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    Summable (fun k : ℕ ↦ ‖(cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E‖) := by
  exact summable_norm_adL_series cellCenterCoeff_nonneg (norm_adL_le_width hΩ hw0 hwidth)
    (summable_cellCenterCoeff_power (by rwa [abs_of_nonneg hw0]))

/-- Equation (A.1) for the series of `-𝒩₀`. -/
theorem norm_cellCenterSeriesOp_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    ‖cellCenterSeriesOp Ω E‖ ≤ (∑' k, cellCenterCoeff k * w ^ (2 * k)) * ‖E‖ := by
  exact norm_adL_series_le cellCenterCoeff_nonneg (norm_adL_le_width hΩ hw0 hwidth)
    (summable_cellCenterCoeff_power (by rwa [abs_of_nonneg hw0]))

/-- In an eigenbasis, each entry of the matrix series is its scalar power series. -/
theorem cellCenterSeriesOp_eigenbasis_entry [NeZero d] {Ω E : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * cellCenterSeriesOp Ω E * U) p q =
      (∑' k : ℕ, cellCenterCoeff k *
        (hΩ.eigenvalues p - hΩ.eigenvalues q) ^ (2 * k) : ℝ) *
          (star U * E * U) p q := by
  exact adL_series_eigenbasis_entry hΩ
    (summable_norm_cellCenterSeriesOp hΩ hw0 hw hwidth (E := E)).of_norm p q

/-- Lemma A.1(ii), first bound: `‖Y(0)‖ = ‖𝒩₀([Ω,·])D‖ ≤ -𝒩₀(w) ‖D‖ = c₀ ‖D‖`. -/
theorem norm_cellCenter_le [NeZero d] {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄} (hΩ : IsHermitian Ω)
    (hwidth : HasEigenvalueDifferences Ω w) (D : 𝕄) :
    ‖cellGuess Ω hΩ D 0‖ ≤ c₀ w * ‖D‖ := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let F : 𝕄 := Matrix.of fun p q ↦
    cellMultiplier 0 (hΩ.eigenvalues p - hΩ.eigenvalues q) * (star U * D * U) p q
  have hkey : star U * cellCenterSeriesOp Ω D * U = -F := by
    ext p q
    have hx := abs_eigenvalues_sub_lt_two_pi hΩ hw hwidth p q
    rw [cellCenterSeriesOp_eigenbasis_entry hΩ hw0 hw hwidth,
      cellCenterCoeff_series_eq hx]
    simp [F, U]
  have hU : star U * U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hΩ.eigenvectorUnitary.property
  have hU' : U * star U = 1 := mul_eq_one_comm.mp hU
  have heq : U * F * star U = -cellCenterSeriesOp Ω D := by
    have he : U * (star U * cellCenterSeriesOp Ω D * U) * star U =
        cellCenterSeriesOp Ω D := by
      rw [show U * (star U * cellCenterSeriesOp Ω D * U) * star U =
        (U * star U) * cellCenterSeriesOp Ω D * (U * star U) by noncomm_ring,
        hU', one_mul, mul_one]
    rw [hkey, mul_neg, neg_mul] at he
    simpa only [neg_neg] using congrArg Neg.neg he
  have hc : (∑' k, cellCenterCoeff k * w ^ (2 * k)) = c₀ w := by
    apply Complex.ofReal_injective
    exact (cellCenterCoeff_series_eq (by rwa [abs_of_nonneg hw0])).trans
      (neg_cellMultiplier_zero_eq_c₀ w)
  change ‖U * F * star U‖ ≤ _
  calc
    ‖U * F * star U‖ = ‖cellCenterSeriesOp Ω D‖ := by rw [heq, norm_neg]
    _ ≤ (∑' k, cellCenterCoeff k * w ^ (2 * k)) * ‖D‖ :=
      norm_cellCenterSeriesOp_le hΩ hw0 hw hwidth
    _ = c₀ w * ‖D‖ := by rw [hc]

end RoundedClocks
