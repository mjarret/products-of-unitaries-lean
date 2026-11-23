/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.CellMultiplier
public import RoundedClocks.Appendix.MatrixSeries
public import RoundedClocks.Citations

/-! # Cosecant series at the center of a cell

Lemma A.1 uses the alternating cosecant series to control the corrector at the center of each cell.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real
open Real

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The cosecant pole sum gives the negative center multiplier away from zero. -/
theorem cellCenter_partialFractions_ne_zero (dlmf_4_22_5 : DLMF_4_22_5)
    {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * π) :
    -cellMultiplier 0 x = ((∑' m : ℕ,
      (-1 : ℝ) ^ m * (2 / ((2 * π * (m + 1 : ℝ)) ^ 2 - x ^ 2))) : ℝ) := by
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
  have hc := dlmf_4_22_5 ((x : ℂ) / 2) hnc
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

/-- The even Taylor coefficients obtained directly from the cosecant poles. -/
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

/-- Decreasing positive pole magnitudes make every alternating coefficient nonnegative. -/
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
  let f : ℕ → ℕ → ℝ := fun k m ↦ (-1 : ℝ) ^ m *
    (2 / (2 * π * (m + 1 : ℝ)) ^ (2 * k + 2) * x ^ (2 * k))
  have hrow (k : ℕ) : (∑' m, f k m) = cellCenterCoeff k * x ^ (2 * k) := by
    simp only [f, cellCenterCoeff, ← mul_assoc, tsum_mul_right]
  have hprod : Summable (Function.uncurry f) :=
    summable_cellCenter_partialFraction_power hx
  calc
    _ = ∑' k, ∑' m, f k m := tsum_congr fun k ↦ (hrow k).symm
    _ = ∑' m, ∑' k, f k m := hprod.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro m
      have hm : |x| < 2 * π * (m + 1 : ℝ) := hx.trans_le (by
        calc
          2 * π = 2 * π * 1 := by ring
          _ ≤ 2 * π * (m + 1 : ℝ) := by
            gcongr
            linarith [Nat.cast_nonneg (α := ℝ) m])
      exact ((hasSum_multiplier_geometric (by positivity) hm).mul_left
        ((-1 : ℝ) ^ m)).tsum_eq

/-- Splitting the zeta-two series into even and odd terms gives the diagonal coefficient. -/
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

/-- The negative center multiplier agrees with its cosecant series, including the diagonal. -/
theorem cellCenterCoeff_series_eq (dlmf_4_22_5 : DLMF_4_22_5)
    {x : ℝ} (hx : |x| < 2 * π) :
    ((∑' k : ℕ, cellCenterCoeff k * x ^ (2 * k)) : ℝ) = -cellMultiplier 0 x := by
  by_cases hx0 : x = 0
  · subst x
    rw [tsum_eq_single 0]
    · norm_num [cellCenterCoeff_zero, cellMultiplier]
    · intro k hk
      simp [zero_pow (by omega : 2 * k ≠ 0)]
  · rw [cellCenterCoeff_power_eq_partialFractions hx]
    exact (cellCenter_partialFractions_ne_zero dlmf_4_22_5 hx0 hx).symm

/-- At a nonnegative width the negative center multiplier is the printed constant. -/
theorem neg_cellMultiplier_zero_eq_c₀ (w : ℝ) :
    -cellMultiplier 0 w = (c₀ w : ℂ) := by
  by_cases hw : w = 0
  · subst w
    norm_num [cellMultiplier, c₀]
  · simp [cellMultiplier, c₀, hw]

/-- The alternating cosecant series gives `c₀(w) ≥ 0` for `0 ≤ w < 2π`. -/
theorem c₀_nonneg_of_width (dlmf_4_22_5 : DLMF_4_22_5)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) : 0 ≤ c₀ w := by
  have habs : |w| < 2 * π := by rwa [abs_of_nonneg hw0]
  have heq : ((∑' k : ℕ, cellCenterCoeff k * w ^ (2 * k) : ℝ) : ℂ) = (c₀ w : ℂ) :=
    (cellCenterCoeff_series_eq dlmf_4_22_5 habs).trans (neg_cellMultiplier_zero_eq_c₀ w)
  have hreal : (∑' k : ℕ, cellCenterCoeff k * w ^ (2 * k)) = c₀ w :=
    Complex.ofReal_injective heq
  rw [← hreal]
  exact tsum_nonneg fun k ↦
    mul_nonneg (cellCenterCoeff_nonneg k) (pow_nonneg hw0 (2 * k))

/-- The cosecant series evaluated on the commutator. -/
def cellCenterSeriesOp (Ω E : 𝕄) : 𝕄 :=
  ∑' k : ℕ, (cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E

/-- Absolute convergence of the center commutator series follows from its scalar majorant. -/
theorem summable_norm_cellCenterSeriesOp [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    Summable (fun k : ℕ ↦ ‖(cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E‖) := by
  have hs := (summable_cellCenterCoeff_power (by rwa [abs_of_nonneg hw0])).mul_right ‖E‖
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hs
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cellCenterCoeff_nonneg k)]
  calc
    cellCenterCoeff k * ‖(adL Ω ^ (2 * k)) E‖ ≤
        cellCenterCoeff k * (w ^ (2 * k) * ‖E‖) :=
      mul_le_mul_of_nonneg_left (norm_adL_pow_apply_le hΩ hw0 hwidth (2 * k))
        (cellCenterCoeff_nonneg k)
    _ = cellCenterCoeff k * w ^ (2 * k) * ‖E‖ := by ring

/-- The manuscript's positive-series estimate bounds the center commutator series. -/
theorem norm_cellCenterSeriesOp_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    ‖cellCenterSeriesOp Ω E‖ ≤ (∑' k, cellCenterCoeff k * w ^ (2 * k)) * ‖E‖ := by
  have hs := summable_norm_cellCenterSeriesOp hΩ hw0 hw hwidth (E := E)
  have hb (k : ℕ) : ‖(cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E‖ ≤
      cellCenterCoeff k * w ^ (2 * k) * ‖E‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cellCenterCoeff_nonneg k)]
    calc
      cellCenterCoeff k * ‖(adL Ω ^ (2 * k)) E‖ ≤
          cellCenterCoeff k * (w ^ (2 * k) * ‖E‖) :=
        mul_le_mul_of_nonneg_left (norm_adL_pow_apply_le hΩ hw0 hwidth (2 * k))
          (cellCenterCoeff_nonneg k)
      _ = cellCenterCoeff k * w ^ (2 * k) * ‖E‖ := by ring
  have hscalar :=
    (summable_cellCenterCoeff_power (by rwa [abs_of_nonneg hw0])).mul_right ‖E‖
  calc
    ‖cellCenterSeriesOp Ω E‖ ≤
        ∑' k : ℕ, ‖(cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, cellCenterCoeff k * w ^ (2 * k) * ‖E‖ :=
      hs.tsum_le_tsum hb hscalar
    _ = _ := tsum_mul_right

/-- In an eigenbasis, each entry of the matrix series is its scalar power series. -/
theorem cellCenterSeriesOp_eigenbasis_entry [NeZero d] {Ω E : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * cellCenterSeriesOp Ω E * U) p q =
      (∑' k : ℕ, cellCenterCoeff k *
        (hΩ.eigenvalues p - hΩ.eigenvalues q) ^ (2 * k) : ℝ) *
          (star U * E * U) p q := by
  dsimp only
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hs := (summable_norm_cellCenterSeriesOp hΩ hw0 hw hwidth (E := E)).of_norm
  have hmap := ((matrixEntryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).map_tsum hs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    matrixEntryCLM_apply] at hmap
  have hdiag : star (hΩ.eigenvectorUnitary : 𝕄) * Ω *
      (hΩ.eigenvectorUnitary : 𝕄) =
      Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_apply] using hΩ.conjStarAlgAut_star_eigenvectorUnitary
  change (star U * cellCenterSeriesOp Ω E * U) p q = _
  rw [cellCenterSeriesOp]
  calc
    (star U * (∑' k : ℕ, (cellCenterCoeff k : ℂ) • (adL Ω ^ (2 * k)) E) * U) p q =
        ∑' k : ℕ, (star U * ((cellCenterCoeff k : ℂ) •
          (adL Ω ^ (2 * k)) E) * U) p q := hmap
    _ = (∑' k : ℕ, (cellCenterCoeff k : ℂ) *
        ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ (2 * k)) *
          (star U * E * U) p q := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro k
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      rw [adL_pow_eigenbasis_entry Ω E hΩ.eigenvectorUnitary hΩ.eigenvalues
        hdiag (2 * k) p q]
      ring
    _ = _ := by
      simp only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow]
      rfl

/-- The center bound of Lemma A.1: ‖𝒩_0([Ω,·])D‖ ≤ c₀ ‖D‖. -/
theorem norm_cellCenter_le (dlmf_4_22_5 : DLMF_4_22_5) [NeZero d] {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π) {Ω : 𝕄} (hΩ : IsHermitian Ω)
    (hwidth : HasEigenvalueDifferences Ω w) (D : 𝕄) :
    ‖(hΩ.eigenvectorUnitary : 𝕄) * Matrix.of (fun p q ↦
      cellMultiplier 0 (hΩ.eigenvalues p - hΩ.eigenvalues q) *
        ((hΩ.eigenvectorUnitary : 𝕄)† * D * (hΩ.eigenvectorUnitary : 𝕄)) p q) *
      (hΩ.eigenvectorUnitary : 𝕄)†‖ ≤ c₀ w * ‖D‖ := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let F : 𝕄 := Matrix.of fun p q ↦
    cellMultiplier 0 (hΩ.eigenvalues p - hΩ.eigenvalues q) * (star U * D * U) p q
  have hkey : star U * cellCenterSeriesOp Ω D * U = -F := by
    ext p q
    have hx : |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
      (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
        (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw
    rw [cellCenterSeriesOp_eigenbasis_entry hΩ hw0 hw hwidth,
      cellCenterCoeff_series_eq dlmf_4_22_5 hx]
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
    exact (cellCenterCoeff_series_eq dlmf_4_22_5 (by rwa [abs_of_nonneg hw0])).trans
      (neg_cellMultiplier_zero_eq_c₀ w)
  change ‖U * F * star U‖ ≤ _
  calc
    ‖U * F * star U‖ = ‖cellCenterSeriesOp Ω D‖ := by rw [heq, norm_neg]
    _ ≤ (∑' k, cellCenterCoeff k * w ^ (2 * k)) * ‖D‖ :=
      norm_cellCenterSeriesOp_le hΩ hw0 hw hwidth
    _ = c₀ w * ‖D‖ := by rw [hc]

end RoundedClocks
