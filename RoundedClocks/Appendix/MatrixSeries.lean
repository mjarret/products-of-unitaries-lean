/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Appendix.PositiveSeries
public import RoundedClocks.Preliminaries.Basic

/-! # Power series in the commutator `[Ω,·]`

The preamble of Appendix A. For a Hermitian `Ω` with eigenvalue differences of modulus at most
`w`, `‖[Ω,A]‖ ≤ w ‖A‖`, so a power series `g` with nonnegative coefficients satisfies equation
(A.1), `‖g([Ω,·])A‖ ≤ g(w) ‖A‖`, and `g([Ω,·])A` has `(p,q)` entry `g(λ_p - λ_q) A_pq` in an
eigenbasis of `Ω`. For `g = 𝒩` the series agrees with Definition 4.1. Here `adL Ω` is `[Ω,·]` and
`multiplierSeriesOp Ω E` is `∑ₙ νₙ [Ω,·]ⁿ E`.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Real
open Set Complex

noncomputable section

namespace RoundedClocks

attribute [local instance] matrixCStarAlgebra

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Applying the commutator map `adL Ω = [Ω,·]` of `Definitions.lean` gives `ΩE - EΩ`. -/
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

/-- A Hermitian matrix with eigenvalue differences of modulus at most `w` lies within `w/2` of a
scalar matrix. The scalar is `μ + w/2` for the least eigenvalue `μ`. -/
theorem exists_spectral_midpoint [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ}
    (hw0 : 0 ≤ w) (hwidth : HasEigenvalueDifferences Ω w) :
    ∃ c : ℝ, ‖Ω - (c : ℂ) • 1‖ ≤ w / 2 := by
  obtain ⟨p, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ hΩ.eigenvalues Finset.univ_nonempty
  have hsa : IsSelfAdjoint Ω := Matrix.isHermitian_iff_isSelfAdjoint.mp hΩ
  refine ⟨hΩ.eigenvalues p + w / 2, ?_⟩
  have hcfc : Ω - ((hΩ.eigenvalues p + w / 2 : ℝ) : ℂ) • 1 =
      cfc (fun x : ℝ ↦ x - (hΩ.eigenvalues p + w / 2)) Ω := by
    rw [cfc_sub (fun x ↦ x) (fun _ ↦ hΩ.eigenvalues p + w / 2) Ω, cfc_id' ℝ Ω, cfc_const _ Ω,
      Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [hcfc]
  refine norm_cfc_le (by positivity) fun x hx ↦ ?_
  rw [hΩ.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have h1 := hmin i (Finset.mem_univ i)
  have h2 := abs_le.mp (hwidth _ (hΩ.eigenvalues_mem_spectrum_real i) _
    (hΩ.eigenvalues_mem_spectrum_real p))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h2.1, h2.2]

/-- `‖[Ω,A]‖ ≤ w ‖A‖`, the inequality preceding (A.1). -/
theorem norm_adL_le_width [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ}
    (hw0 : 0 ≤ w) (hwidth : HasEigenvalueDifferences Ω w) : ‖adL Ω‖ ≤ w := by
  obtain ⟨c, hc⟩ := exists_spectral_midpoint hΩ hw0 hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hw0
  intro E
  exact (norm_adL_apply_le Ω E c).trans (by
    calc
      2 * ‖Ω - (c : ℂ) • 1‖ * ‖E‖ ≤ 2 * (w / 2) * ‖E‖ := by gcongr
      _ = w * ‖E‖ := by ring)

/-- One term of (A.1): `‖c [Ω,·]ⁿ E‖ ≤ c wⁿ ‖E‖` for `c ≥ 0`. -/
theorem norm_adL_series_term_le [NeZero d] {Ω E : 𝕄} {w c : ℝ} (hc : 0 ≤ c)
    (ha : ‖adL Ω‖ ≤ w) (n : ℕ) :
    ‖(c : ℂ) • (adL Ω ^ n) E‖ ≤ c * w ^ n * ‖E‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hp := ((adL Ω ^ n).le_opNorm E).trans (mul_le_mul_of_nonneg_right
    ((norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) ha n)) (norm_nonneg E))
  exact (mul_le_mul_of_nonneg_left hp hc).trans_eq (mul_assoc _ _ _).symm

/-- The series of (A.1) converges absolutely when `∑ cₙ w^{k(n)}` converges. The exponents `k(n)`
allow a series in even powers. -/
theorem summable_norm_adL_series [NeZero d] {c : ℕ → ℝ} {k : ℕ → ℕ} (hc : ∀ n, 0 ≤ c n)
    {Ω E : 𝕄} {w : ℝ} (ha : ‖adL Ω‖ ≤ w) (hs : Summable (fun n ↦ c n * w ^ k n)) :
    Summable (fun n ↦ ‖(c n : ℂ) • (adL Ω ^ k n) E‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_adL_series_term_le (hc n) ha (k n)) (hs.mul_right ‖E‖)

/-- Equation (A.1) for a series `∑ cₙ x^{k(n)}` with every `cₙ ≥ 0`:
`‖∑ cₙ [Ω,·]^{k(n)} E‖ ≤ (∑ cₙ w^{k(n)}) ‖E‖`. -/
theorem norm_adL_series_le [NeZero d] {c : ℕ → ℝ} {k : ℕ → ℕ} (hc : ∀ n, 0 ≤ c n)
    {Ω E : 𝕄} {w : ℝ} (ha : ‖adL Ω‖ ≤ w) (hs : Summable (fun n ↦ c n * w ^ k n)) :
    ‖∑' n, (c n : ℂ) • (adL Ω ^ k n) E‖ ≤ (∑' n, c n * w ^ k n) * ‖E‖ :=
  tsum_of_norm_bounded (hs.hasSum.mul_right ‖E‖) fun n ↦
    norm_adL_series_term_le (hc n) ha (k n)

/-- The series `∑ₙ νₙ [Ω,·]ⁿ E`: the power-series meaning of `𝒩([Ω,·])E`. -/
def multiplierSeriesOp (Ω E : 𝕄) : 𝕄 :=
  ∑' n : ℕ, (multiplierCoeff n : ℂ) • (adL Ω ^ n) E

/-- The series `∑ₙ νₙ [Ω,·]ⁿ E` converges absolutely under the width hypothesis. -/
theorem summable_norm_multiplierSeriesOp [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    Summable (fun n : ℕ ↦ ‖(multiplierCoeff n : ℂ) • (adL Ω ^ n) E‖) := by
  exact summable_norm_adL_series multiplierCoeff_nonneg (norm_adL_le_width hΩ hw0 hwidth)
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))

/-- Equation (A.1) for `g = 𝒩`: `‖𝒩([Ω,·])E‖ ≤ 𝒩(w) ‖E‖`. -/
theorem norm_multiplierSeriesOp_le [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) :
    ‖multiplierSeriesOp Ω E‖ ≤ 𝒩 w * ‖E‖ := by
  simpa only [multiplierCoeff_series_eq w (by rwa [abs_of_nonneg hw0])] using
    norm_adL_series_le multiplierCoeff_nonneg (norm_adL_le_width hΩ hw0 hwidth)
      (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0])) (E := E)

/-- `([Ω,·]ⁿ A)_pq = (λ_p - λ_q)ⁿ A_pq` in a unitary eigenbasis of `Ω`. -/
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

/-- In the eigenbasis `Ψ` of a Hermitian `Ω`, `Ψ† Ω Ψ` is the diagonal matrix of eigenvalues. -/
theorem eigenvectorUnitary_conj_eq_diagonal {Ω : 𝕄} (hΩ : IsHermitian Ω) :
    (hΩ.eigenvectorUnitary : 𝕄)† * Ω * (hΩ.eigenvectorUnitary : 𝕄) =
      Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) := by
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
    Function.comp_apply] using hΩ.conjStarAlgAut_star_eigenvectorUnitary

/-- Under the width hypothesis, every eigenvalue difference has modulus less than `2π`. -/
theorem abs_eigenvalues_sub_lt_two_pi {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ} (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π :=
  (hwidth _ (hΩ.eigenvalues_mem_spectrum_real p) _
    (hΩ.eigenvalues_mem_spectrum_real q)).trans_lt hw

/-- Evaluation at one matrix entry is a continuous linear map. -/
abbrev matrixEntryCLM (p q : Fin d) : 𝕄 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ p q)

/-- The entry functional evaluates at its two indices. -/
@[simp] theorem matrixEntryCLM_apply (p q : Fin d) (A : 𝕄) :
    matrixEntryCLM p q A = A p q := rfl

/-- `g([Ω,·])A` has `(p,q)` entry `g(λ_p - λ_q) A_pq` in the eigenbasis of `Ω`. -/
theorem adL_series_eigenbasis_entry {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {c : ℕ → ℝ} {k : ℕ → ℕ}
    (hs : Summable (fun n ↦ (c n : ℂ) • (adL Ω ^ k n) E)) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (U† * (∑' n, (c n : ℂ) • (adL Ω ^ k n) E) * U) p q =
      (∑' n, c n * (hΩ.eigenvalues p - hΩ.eigenvalues q) ^ k n : ℝ) *
        (U† * E * U) p q := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hmap := ((matrixEntryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (U†) U)).map_tsum hs
  have hdiag : U† * Ω * U = Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) :=
    eigenvectorUnitary_conj_eq_diagonal hΩ
  change (U† * (∑' n, (c n : ℂ) • (adL Ω ^ k n) E) * U) p q = _
  rw [show (U† * (∑' n, (c n : ℂ) • (adL Ω ^ k n) E) * U) p q =
    ∑' n, (U† * ((c n : ℂ) • (adL Ω ^ k n) E) * U) p q from hmap]
  simp only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  rw [adL_pow_eigenbasis_entry Ω E hΩ.eigenvectorUnitary hΩ.eigenvalues hdiag (k n) p q]
  exact (mul_assoc _ _ _).symm

/-- `∑ₙ νₙ [Ω,·]ⁿ E` has `(p,q)` entry `𝒩(λ_p - λ_q) E_pq` in the eigenbasis of `Ω`. -/
theorem multiplierSeriesOp_eigenbasis_entry [NeZero d] {Ω E : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * multiplierSeriesOp Ω E * U) p q =
      (𝒩 (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) *
        (star U * E * U) p q := by
  have hdiff := abs_eigenvalues_sub_lt_two_pi hΩ hw hwidth p q
  simpa only [multiplierCoeff_series_eq _ hdiff] using adL_series_eigenbasis_entry hΩ
    (summable_norm_multiplierSeriesOp hΩ hw0 hw hwidth (E := E)).of_norm p q

/-- The two meanings of `𝒩([Ω,·])E` agree: under the width hypothesis, the series
`∑ₙ νₙ [Ω,·]ⁿ E` is the matrix of Definition 4.1. -/
theorem multiplierSeriesOp_eq_𝒩ad [NeZero d] {Ω E : 𝕄} (hΩ : IsHermitian Ω)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) : multiplierSeriesOp Ω E = 𝒩ad Ω E := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  have hstrict := abs_eigenvalues_sub_lt_two_pi hΩ hw hwidth
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
