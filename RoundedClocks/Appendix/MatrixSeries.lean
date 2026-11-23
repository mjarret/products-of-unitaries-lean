/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Appendix.PositiveSeries

/-! # Commutator power series

The two power-series observations preceding Lemma A.1 give the
spectral midpoint bounds the commutator, and the positive scalar series agrees with the
eigenbasis definition of `𝒩ad`.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real
open Set Complex

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- For complex matrices, the star operation is the conjugate transpose. -/
theorem star_eq_conjTranspose (A : 𝕄) : A† = A.conjTranspose := by
  rfl

/-- The commutator with `Ω`, viewed as a complex continuous linear map. -/
def adL (Ω : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  ContinuousLinearMap.mul ℂ 𝕄 Ω - (ContinuousLinearMap.mul ℂ 𝕄).flip Ω

/-- Applying the commutator map gives `ΩE - EΩ`. -/
@[simp] theorem adL_apply (Ω E : 𝕄) : adL Ω E = Ω * E - E * Ω := rfl

/-- Subtracting a scalar does not change a commutator. -/
theorem adL_shift (Ω E : 𝕄) (c : ℂ) :
    adL Ω E = (Ω - c • 1) * E - E * (Ω - c • 1) := by
  rw [adL_apply, sub_mul, mul_sub, smul_one_mul, mul_smul_one]
  abel

/-- The elementary commutator estimate after a scalar shift. -/
theorem norm_adL_apply_le (Ω E : 𝕄) (c : ℂ) :
    ‖adL Ω E‖ ≤ 2 * ‖Ω - c • 1‖ * ‖E‖ := by
  rw [adL_shift Ω E c]
  exact (norm_sub_le _ _).trans (by
    linarith [norm_mul_le (Ω - c • 1) E, norm_mul_le E (Ω - c • 1)])

/-- A unitary matrix has operator norm one. -/
theorem norm_eq_one_of_unitary [NeZero d] {U : 𝕄} (hU : U† * U = 1) : ‖U‖ = 1 := by
  have hsquare : ‖U‖ * ‖U‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← star_eq_conjTranspose, hU]
    simp
  have hnorm := norm_nonneg U; nlinarith

/-- Multiplication on the right by a unitary matrix preserves the operator norm. -/
theorem norm_mul_unitary_eq [NeZero d] (X : 𝕄) {U : 𝕄} (hU : U† * U = 1) :
    ‖X * U‖ = ‖X‖ := by
  have hUstar : ‖U†‖ = 1 := by
    rw [star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose, norm_eq_one_of_unitary hU]
  apply le_antisymm
  · simpa only [norm_eq_one_of_unitary hU, mul_one] using norm_mul_le X U
  · have hback : X = (X * U) * U† := by
      rw [mul_assoc, mul_eq_one_comm.mp hU, mul_one]
    calc
      ‖X‖ = ‖(X * U) * U†‖ := congrArg norm hback
      _ ≤ ‖X * U‖ * ‖U†‖ := norm_mul_le _ _
      _ = ‖X * U‖ := by rw [hUstar, mul_one]

/-- Multiplication on the left by a unitary matrix preserves the operator norm. -/
theorem norm_unitary_mul_eq [NeZero d] (X : 𝕄) {U : 𝕄} (hU : U† * U = 1) :
    ‖U * X‖ = ‖X‖ := by
  have hUstar : ‖U†‖ = 1 := by
    rw [star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose, norm_eq_one_of_unitary hU]
  apply le_antisymm
  · simpa only [norm_eq_one_of_unitary hU, one_mul] using norm_mul_le U X
  · have hback : X = U† * (U * X) := by rw [← mul_assoc, hU, one_mul]
    calc
      ‖X‖ = ‖U† * (U * X)‖ := congrArg norm hback
      _ ≤ ‖U†‖ * ‖U * X‖ := norm_mul_le _ _
      _ = ‖U * X‖ := by rw [hUstar, one_mul]

/-- Unitary conjugation preserves the operator norm. -/
theorem norm_unitary_conj_eq [NeZero d] (X : 𝕄) {U : 𝕄} (hU : U† * U = 1) :
    ‖U * X * U†‖ = ‖X‖ := by
  have hU' : (U†)† * U† = 1 := by
    rw [star_star]
    exact mul_eq_one_comm.mp hU
  exact (norm_mul_unitary_eq (U * X) hU').trans (norm_unitary_mul_eq X hU)

/-- The norm of a centered diagonal matrix is bounded by half the enclosing interval width. -/
theorem norm_diagonal_center_le [NeZero d] (ev : Fin d → ℝ) {m M w : ℝ}
    (hw0 : 0 ≤ w) (hm : ∀ p, m ≤ ev p) (hM : ∀ p, ev p ≤ M)
    (hMm : M - m ≤ w) :
    ‖Matrix.diagonal (fun p ↦ ((ev p - (m + M) / 2 : ℝ) : ℂ))‖ ≤ w / 2 := by
  rw [Matrix.l2_opNorm_diagonal, Pi.norm_def]
  let f : Fin d → NNReal := fun p ↦ ‖((ev p - (m + M) / 2 : ℝ) : ℂ)‖₊
  let C : NNReal := ⟨w / 2, by positivity⟩
  have hpoint (p : Fin d) : f p ≤ C := by
    apply NNReal.coe_le_coe.mp
    change ‖((ev p - (m + M) / 2 : ℝ) : ℂ)‖ ≤ w / 2
    rw [Complex.norm_real, Real.norm_eq_abs]
    have habs : |ev p - (m + M) / 2| ≤ (M - m) / 2 :=
      abs_le.mpr ⟨by linarith [hm p], by linarith [hM p]⟩
    exact habs.trans (by linarith)
  have hs : (Finset.univ : Finset (Fin d)).sup f ≤ C :=
    Finset.sup_le fun p _ ↦ hpoint p
  change ((↑((Finset.univ : Finset (Fin d)).sup f) : ℝ)) ≤ (C : ℝ)
  exact NNReal.coe_le_coe.mpr hs

/-- The manuscript's midpoint shift: a Hermitian matrix of width `w` lies within `w/2` of a
scalar matrix. -/
theorem exists_spectral_midpoint [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ}
    (hw0 : 0 ≤ w) (hwidth : HasEigenvalueDifferences Ω w) :
    ∃ c : ℝ, ‖Ω - (c : ℂ) • 1‖ ≤ w / 2 := by
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  obtain ⟨pmin, _, hmin⟩ :=
    Finset.exists_min_image Finset.univ hΩ.eigenvalues huniv
  obtain ⟨pmax, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ hΩ.eigenvalues huniv
  let m := hΩ.eigenvalues pmin
  let M := hΩ.eigenvalues pmax
  have hm (p : Fin d) : m ≤ hΩ.eigenvalues p := hmin p (Finset.mem_univ p)
  have hM (p : Fin d) : hΩ.eigenvalues p ≤ M := hmax p (Finset.mem_univ p)
  have hMm : M - m ≤ w := by
    have hd := hwidth M (by
      simpa only [M] using hΩ.eigenvalues_mem_spectrum_real pmax) m (by
      simpa only [m] using hΩ.eigenvalues_mem_spectrum_real pmin)
    rw [abs_of_nonneg (sub_nonneg.mpr (hm pmax))] at hd
    exact hd
  refine ⟨(m + M) / 2, ?_⟩
  let e := Unitary.conjStarAlgAut ℂ 𝕄 (star hΩ.eigenvectorUnitary)
  let V : 𝕄 := star hΩ.eigenvectorUnitary
  have hV : V† * V = 1 := by
    dsimp [V]
    exact Matrix.mem_unitaryGroup_iff'.mp (star hΩ.eigenvectorUnitary).property
  have he : e (Ω - (((m + M) / 2 : ℝ) : ℂ) • 1) =
      Matrix.diagonal (fun p ↦
        ((hΩ.eigenvalues p - (m + M) / 2 : ℝ) : ℂ)) := by
    rw [map_sub, map_smul, map_one,
      Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [Function.comp_def]
    · simp [Matrix.diagonal, hpq]
  calc
    ‖Ω - ((((m + M) / 2 : ℝ)) : ℂ) • 1‖ =
        ‖e (Ω - ((((m + M) / 2 : ℝ)) : ℂ) • 1)‖ := by
          have heval : e (Ω - ((((m + M) / 2 : ℝ)) : ℂ) • 1) =
              V * (Ω - ((((m + M) / 2 : ℝ)) : ℂ) • 1) * V† := by
            exact Unitary.conjStarAlgAut_apply _ _
          rw [heval]
          exact (norm_unitary_conj_eq _ hV).symm
    _ = ‖Matrix.diagonal (fun p ↦
        ((hΩ.eigenvalues p - (m + M) / 2 : ℝ) : ℂ))‖ := congrArg norm he
    _ ≤ w / 2 := norm_diagonal_center_le hΩ.eigenvalues hw0 hm hM hMm

/-- Equation preceding (A.1): the commutator has operator norm at most the spectral width. -/
theorem norm_adL_le_width [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ}
    (hw0 : 0 ≤ w) (hwidth : HasEigenvalueDifferences Ω w) : ‖adL Ω‖ ≤ w := by
  obtain ⟨c, hc⟩ := exists_spectral_midpoint hΩ hw0 hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hw0
  intro E
  exact (norm_adL_apply_le Ω E c).trans (by
    calc
      2 * ‖Ω - (c : ℂ) • 1‖ * ‖E‖ ≤ 2 * (w / 2) * ‖E‖ := by gcongr
      _ = w * ‖E‖ := by ring)

/-- Every commutator power obeys the corresponding width bound. -/
theorem norm_adL_pow_apply_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ}
    (hw0 : 0 ≤ w) (hwidth : HasEigenvalueDifferences Ω w) (n : ℕ) :
    ‖(adL Ω ^ n) E‖ ≤ w ^ n * ‖E‖ := by
  exact ((adL Ω ^ n).le_opNorm E).trans
    (mul_le_mul_of_nonneg_right
      ((norm_pow_le _ n).trans
        (pow_le_pow_left₀ (norm_nonneg _) (norm_adL_le_width hΩ hw0 hwidth) n))
      (norm_nonneg E))

/-- The positive multiplier series evaluated on the commutator with `Ω`. -/
def multiplierSeriesOp (Ω E : 𝕄) : 𝕄 :=
  ∑' n : ℕ, (multiplierCoeff n : ℂ) • (adL Ω ^ n) E

/-- Absolute convergence of the commutator multiplier series under the width hypothesis. -/
theorem summable_norm_multiplierSeriesOp [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    Summable (fun n : ℕ ↦ ‖(multiplierCoeff n : ℂ) • (adL Ω ^ n) E‖) := by
  have hs : Summable (fun n : ℕ ↦ multiplierCoeff n * w ^ n * ‖E‖) :=
    ((summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0])).mul_right ‖E‖)
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hs
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (multiplierCoeff_nonneg n)]
  calc
    multiplierCoeff n * ‖(adL Ω ^ n) E‖ ≤
        multiplierCoeff n * (w ^ n * ‖E‖) :=
      mul_le_mul_of_nonneg_left (norm_adL_pow_apply_le hΩ hw0 hwidth n)
        (multiplierCoeff_nonneg n)
    _ = multiplierCoeff n * w ^ n * ‖E‖ := by ring

/-- Equation (A.1)'s positive-series bound for the multiplier. -/
theorem norm_multiplierSeriesOp_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
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
      rw [multiplierCoeff_series_eq w (by rwa [abs_of_nonneg hw0])]

/-- Iterated commutators are diagonal entrywise in any unitary eigenbasis. -/
theorem adL_pow_eigenbasis_entry (Ω E : 𝕄)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (ev : Fin d → ℝ)
    (hdiag : star (U : 𝕄) * Ω * (U : 𝕄) =
      Matrix.diagonal (fun p ↦ (ev p : ℂ))) (n : ℕ) (p q : Fin d) :
    (star (U : 𝕄) * (adL Ω ^ n) E * (U : 𝕄)) p q =
      ((ev p - ev q : ℝ) : ℂ) ^ n *
        (star (U : 𝕄) * E * (U : 𝕄)) p q := by
  let e := Unitary.conjStarAlgAut ℂ 𝕄 (star U)
  have he (X : 𝕄) : e X = star (U : 𝕄) * X * (U : 𝕄) := by
    simp only [e, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
  have hΩe : e Ω = Matrix.diagonal (fun p ↦ (ev p : ℂ)) := (he Ω).trans hdiag
  simp only [← he]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, adL_apply, map_sub, map_mul, map_mul,
      hΩe]
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [ih, pow_succ]
    push_cast
    ring

/-- Evaluation at one matrix entry is a continuous linear map. -/
def matrixEntryCLM (p q : Fin d) : 𝕄 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ p q)

/-- The entry functional evaluates at its two indices. -/
@[simp] theorem matrixEntryCLM_apply (p q : Fin d) (A : 𝕄) :
    matrixEntryCLM p q A = A p q := rfl

/-- The commutator series has the scalar multiplier on every eigenbasis entry. -/
theorem multiplierSeriesOp_eigenbasis_entry [NeZero d] {Ω E : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * multiplierSeriesOp Ω E * U) p q =
      (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) *
        (star U * E * U) p q := by
  dsimp only
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hs := (summable_norm_multiplierSeriesOp hΩ hw0 hw hwidth (E := E)).of_norm
  have hmap := ((matrixEntryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).map_tsum hs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    matrixEntryCLM_apply] at hmap
  have hdiff : |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
    (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
      (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw
  have hscalar : (∑' n : ℕ, (multiplierCoeff n : ℂ) *
      ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ n) =
      (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) := by
    simpa only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) (multiplierCoeff_series_eq _ hdiff)
  have hdiag : star (hΩ.eigenvectorUnitary : 𝕄) * Ω *
      (hΩ.eigenvectorUnitary : 𝕄) =
      Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Function.comp_apply] using hΩ.conjStarAlgAut_star_eigenvectorUnitary
  change (star U * multiplierSeriesOp Ω E * U) p q = _
  rw [multiplierSeriesOp]
  calc
    (star U * (∑' n : ℕ, (multiplierCoeff n : ℂ) • (adL Ω ^ n) E) * U) p q =
        ∑' n : ℕ, (star U * ((multiplierCoeff n : ℂ) •
          (adL Ω ^ n) E) * U) p q := hmap
    _ = (∑' n : ℕ, (multiplierCoeff n : ℂ) *
        ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ n) *
          (star U * E * U) p q := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      rw [adL_pow_eigenbasis_entry Ω E hΩ.eigenvectorUnitary hΩ.eigenvalues
        hdiag n p q]
      ring
    _ = _ := by rw [hscalar]

/-- Under the width hypothesis, the series interpretation agrees with Definition 4.1. -/
theorem multiplierSeriesOp_eq_𝒩ad [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) : multiplierSeriesOp Ω E = 𝒩ad Ω E := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hstrict (p q : Fin d) :
      |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
    (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
      (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw
  let F : 𝕄 := Matrix.of fun p q ↦
    (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) * (star U * E * U) p q
  have hkey : star U * multiplierSeriesOp Ω E * U = F := by
    ext p q
    exact multiplierSeriesOp_eigenbasis_entry hΩ hw0 hw hwidth p q
  have hU : star U * U = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp hΩ.eigenvectorUnitary.property
  have hU' : U * star U = 1 := mul_eq_one_comm.mp hU
  rw [𝒩ad, dif_pos hΩ, if_pos hstrict]
  change multiplierSeriesOp Ω E = U * F * star U
  calc
    multiplierSeriesOp Ω E =
        U * (star U * multiplierSeriesOp Ω E * U) * star U := by
      rw [show U * (star U * multiplierSeriesOp Ω E * U) * star U =
        (U * star U) * multiplierSeriesOp Ω E * (U * star U) by noncomm_ring,
        hU', one_mul, mul_one]
    _ = U * F * star U := by rw [hkey]

end RoundedClocks
