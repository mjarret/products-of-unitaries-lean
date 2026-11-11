/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.ExponentialAverage
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.SinTheta

/-!
# The adjoint map and the conjugation series

## Declarations

- `adL`
- `adL_apply`
- `adPow_apply`
- `conj_eq_tsum`
- `evol_eq_exp`
- `evol_neg_eq_exp`
- `hasSum_conj`
- `hasSum_exp_smul`
- `integral_conj_smul`
- `integral_ofReal_pow`
- `mulL`
- `mulL_apply`
- `mulL_pow_apply`
- `mulR`
- `mulR_apply`
- `neg_mulR_pow_apply`
- `norm_I_smul_adL_le`
- `norm_adL_apply_le`
- `norm_sub_smul_one_le_of_eigenvalues`
- `phiSeries_adL_apply`
- `proj_univ`
- `summable_norm_conj_terms`
- `summable_norm_exp_smul`
- `tsum_apply_of_summable`
-/

@[expose] public section

namespace UnitaryProducts.Corrector

section PsiSummable

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

end PsiSummable

end UnitaryProducts.Corrector

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The adjoint map of `H`, `ad_H E = H E - E H`, as a continuous linear map. -/
noncomputable def adL (H : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  ContinuousLinearMap.mul ℂ 𝕄 H - (ContinuousLinearMap.mul ℂ 𝕄).flip H

/-- The adjoint map acts by the commutator, as in the commutator definition before Lemma A.1. -/
theorem adL_apply (H E : 𝕄) : adL H E = H * E - E * H := rfl

/-- **The commutator sees only the spread of `H`**: `‖H E - E H‖ ≤ 2 ‖H - c‖ ‖E‖`, because the
scalar `c` commutes with `E`. -/
theorem norm_adL_apply_le (H E : 𝕄) (c : ℂ) : ‖adL H E‖ ≤ 2 * ‖H - c • 1‖ * ‖E‖ := by
  have hshift : adL H E = (H - c • 1) * E - E * (H - c • 1) := by
    rw [adL_apply, sub_mul, mul_sub, smul_one_mul, mul_smul_one]
    abel
  rw [hshift]
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_mul_le (H - c • 1) E, norm_mul_le E (H - c • 1)]

/-- `‖i·ad_H‖ ≤ 2 ‖H - c‖`. -/
theorem norm_I_smul_adL_le (H : 𝕄) (c : ℂ) : ‖I • adL H‖ ≤ 2 * ‖H - c • 1‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun E ↦ by
    rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_I, one_mul]
    exact norm_adL_apply_le H E c

/-- The projection onto the whole spectrum is the identity. -/
theorem proj_univ (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (ev : Fin d → ℝ)
    (x : EuclideanSpace ℂ (Fin d)) : proj b ev Set.univ x = x :=
  ext_basis b fun j ↦ by rw [inner_proj]; simp

/-- **The spectral width bounds the shifted norm.**  A Hermitian `H` with eigenvalues in
`[m, m + w]` is within `w/2` of `(m + w/2)·1`.  (`0 ≤ w` is needed only for `d = 0`, where the
eigenvalue hypothesis is vacuous.) -/
theorem norm_sub_smul_one_le_of_eigenvalues {H : 𝕄} (hH : H.IsHermitian) {m w : ℝ}
    (hw0 : 0 ≤ w) (hev : ∀ i, hH.eigenvalues i ∈ Icc m (m + w)) :
    ‖H - (((m + w / 2 : ℝ)) : ℂ) • 1‖ ≤ w / 2 := by
  refine norm_le_of_apply_le (by linarith) fun x ↦ ?_
  rw [map_sub, map_smul, map_one]
  have hbound := norm_shift_proj_le hH.eigenvectorBasis hH.eigenvalues (m := m + w / 2)
    (c := w / 2) (by linarith) (isDiag_eigenvectorBasis hH) (S := Set.univ)
    (fun i _ ↦ abs_le.mpr ⟨by linarith [(hev i).1], by linarith [(hev i).2]⟩) x
  rwa [proj_univ] at hbound

/-- Left multiplication by `X` on matrices: Mathlib's `ContinuousLinearMap.mul ℂ 𝕄 X`, named. -/
noncomputable def mulL (X : 𝕄) : 𝕄 →L[ℂ] 𝕄 := ContinuousLinearMap.mul ℂ 𝕄 X

/-- Right multiplication by `X` on matrices: Mathlib's `(ContinuousLinearMap.mul ℂ 𝕄).flip X`,
named. -/
noncomputable def mulR (X : 𝕄) : 𝕄 →L[ℂ] 𝕄 := (ContinuousLinearMap.mul ℂ 𝕄).flip X

theorem mulL_apply (X E : 𝕄) : mulL X E = X * E := rfl

theorem mulR_apply (X E : 𝕄) : mulR X E = E * X := rfl

theorem mulL_pow_apply (X : 𝕄) (n : ℕ) : ∀ E : 𝕄, (mulL X ^ n) E = X ^ n * E := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro E; rw [pow_succ, ContinuousLinearMap.mul_apply, ih, mulL_apply, pow_succ, mul_assoc]

theorem neg_mulR_pow_apply (X : 𝕄) (n : ℕ) :
    ∀ E : 𝕄, ((-(mulR X)) ^ n) E = (-1 : ℂ) ^ n • (E * X ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro E
    rw [pow_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply, mulR_apply,
      ih (-(E * X)), pow_succ ((-1 : ℂ)), pow_succ' X, neg_mul, mul_assoc, smul_neg, ← neg_smul,
      mul_comm ((-1 : ℂ) ^ n) (-1 : ℂ), neg_one_mul]

/-- **The iterated commutator, expanded.**  `(i·ad_H)ⁿ E = ∑ₖ (-1)^{n-k} C(n,k) Xᵏ E X^{n-k}` with
`X = iH`. -/
theorem adPow_apply (H : 𝕄) (n : ℕ) (E : 𝕄) :
    ((I • adL H) ^ n) E = ∑ k ∈ Finset.range (n + 1),
      (((-1 : ℂ)) ^ (n - k) * (n.choose k : ℂ)) • ((I • H) ^ k * E * (I • H) ^ (n - k)) := by
  set X : 𝕄 := I • H with hXdef
  have hcomm : Commute (mulL X) (-(mulR X)) := Commute.neg_right
    (show Commute (mulL X) (mulR X) from ContinuousLinearMap.ext fun E ↦ by
      simp only [ContinuousLinearMap.mul_apply, mulL_apply, mulR_apply, mul_assoc])
  have hsplit : I • adL H = mulL X + -(mulR X) := ContinuousLinearMap.ext fun E ↦ by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, adL_apply, mulL_apply, mulR_apply, sub_eq_add_neg, smul_add,
      smul_neg, smul_mul_assoc, mul_smul_comm, hXdef]
  rw [hsplit, hcomm.add_pow, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.natCast_apply,
    neg_mulR_pow_apply, mulL_pow_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp [smul_smul, mul_assoc, mul_comm]

theorem evol_neg_eq_exp (H : 𝕄) (τ : ℝ) : evol H (-τ) = exp ((τ : ℂ) • (I • H)) := by
  rw [evol, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, smul_smul]
  norm_num

theorem evol_eq_exp (H : 𝕄) (τ : ℝ) : evol H τ = exp (-((τ : ℂ) • (I • H))) := by
  rw [evol, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, ← neg_smul, smul_smul]
  norm_num

theorem hasSum_exp_smul (X : 𝕄) (z : ℂ) :
    HasSum (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ * z ^ n) • X ^ n) (exp (z • X)) := by
  simpa [NormedSpace.expSeries_apply_eq, smul_pow, smul_smul] using
    NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (z • X)

theorem summable_norm_exp_smul (X : 𝕄) (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖((Nat.factorial n : ℂ)⁻¹ * z ^ n) • X ^ n‖) := by
  simpa [smul_pow, smul_smul] using NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) (z • X)

/-- The terms of the conjugation series are absolutely summable. -/
theorem summable_norm_conj_terms [NeZero d] (H E : 𝕄) (τ : ℝ) :
    Summable (fun n : ℕ ↦ ‖((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ n) • (((I • adL H) ^ n) E)‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    ((Real.summable_pow_div_factorial (|τ| * ‖I • adL H‖)).mul_right ‖E‖)
  have hv : ‖((I • adL H) ^ n) E‖ ≤ ‖I • adL H‖ ^ n * ‖E‖ :=
    (((I • adL H) ^ n).le_opNorm E).trans
      (mul_le_mul_of_nonneg_right (norm_pow_le _ n) (norm_nonneg E))
  rw [norm_smul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by rw [mul_pow]; ring)

/-- **The conjugation is the exponential of the adjoint map**, as a Cauchy product of the two
exponential series. -/
theorem conj_eq_tsum (H E : 𝕄) (τ : ℝ) :
    evol H (-τ) * E * evol H τ
      = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ n) • (((I • adL H) ^ n) E) := by
  set X : 𝕄 := I • H with hXdef
  set f : ℕ → 𝕄 := fun k ↦ ((Nat.factorial k : ℂ)⁻¹ * (τ : ℂ) ^ k) • X ^ k with hf
  set g : ℕ → 𝕄 := fun l ↦ ((Nat.factorial l : ℂ)⁻¹ * (-(τ : ℂ)) ^ l) • X ^ l with hg
  have hfsum : HasSum f (exp ((τ : ℂ) • X)) := hasSum_exp_smul X _
  have hgsum : HasSum g (exp ((-(τ : ℂ)) • X)) := hasSum_exp_smul X _
  have hnf : Summable (fun k ↦ ‖f k * E‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ norm_mul_le _ _)
      ((summable_norm_exp_smul X (τ : ℂ)).mul_right ‖E‖)
  have hng : Summable (fun l ↦ ‖g l‖) := summable_norm_exp_smul X (-(τ : ℂ))
  have hlhs : evol H (-τ) * E * evol H τ = (∑' k, f k * E) * (∑' l, g l) := by
    rw [Summable.tsum_mul_right E hfsum.summable, hfsum.tsum_eq, hgsum.tsum_eq,
      evol_neg_eq_exp, evol_eq_exp, neg_smul]
  rw [hlhs, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hnf hng]
  refine tsum_congr fun n ↦ ?_
  rw [adPow_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (τ : ℂ) ^ k * (τ : ℂ) ^ (n - k) = (τ : ℂ) ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  simp only [hf, hg, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [Nat.cast_choose ℂ hkn, neg_pow, ← hpow]
  linear_combination (-((τ : ℂ) ^ k * (τ : ℂ) ^ (n - k) * (-1 : ℂ) ^ (n - k)
    * (Nat.factorial k : ℂ)⁻¹ * (Nat.factorial (n - k) : ℂ)⁻¹))
    * inv_mul_cancel₀ ((Nat.cast_ne_zero (R := ℂ)).mpr (Nat.factorial_ne_zero n))

/-- **The conjugation is the exponential of the adjoint map.**
`e^{iτH} E e^{-iτH} = ∑ τⁿ/n! (i·ad_H)ⁿ E`. -/
theorem hasSum_conj [NeZero d] (H E : 𝕄) (τ : ℝ) :
    HasSum (fun n : ℕ ↦ ((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ n) • (((I • adL H) ^ n) E))
      (evol H (-τ) * E * evol H τ) := by
  rw [conj_eq_tsum H E τ]
  exact (summable_norm_conj_terms H E τ).of_norm.hasSum

/-- The scalar moments of the unit step: `∫₀¹ τ^{n+p} dτ = 1/(n+p+1)`. -/
theorem integral_ofReal_pow (m : ℕ) :
    (∫ τ in (0 : ℝ)..1, (τ : ℂ) ^ m) = ((m : ℂ) + 1)⁻¹ := by
  simp_rw [← Complex.ofReal_pow, intervalIntegral.integral_ofReal, integral_pow]
  norm_num

/-- **The moments of the conjugation.**  `∫₀¹ τ^p e^{iτH} E e^{-iτH} dτ = ∑ (i·ad_H)ⁿ
E/(n!(n+p+1))`. -/
theorem integral_conj_smul [NeZero d] (H E : 𝕄) (p : ℕ) :
    (∫ τ in (0 : ℝ)..1, ((τ : ℂ) ^ p) • (evol H (-τ) * E * evol H τ))
      = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹ * ((n : ℂ) + p + 1)⁻¹) • (((I • adL H) ^ n) E) := by
  set v : ℕ → 𝕄 := fun n ↦ ((I • adL H) ^ n) E with hv
  set F : ℕ → ℝ → 𝕄 := fun n τ ↦ ((Nat.factorial n : ℂ)⁻¹ * (τ : ℂ) ^ (n + p)) • v n with hF
  have hcont : ∀ n, Continuous (F n) := fun n ↦
    ((continuous_const.mul ((Complex.continuous_ofReal).pow _)).smul continuous_const)
  have hInt : ∀ n, MeasureTheory.IntegrableOn (F n) (Ioc (0 : ℝ) 1) := fun n ↦
    (hcont n).integrableOn_Ioc
  have hb : Summable (fun n ↦ (Nat.factorial n : ℝ)⁻¹ * ‖v n‖) :=
    (summable_norm_conj_terms H E 1).congr fun n ↦ by rw [norm_smul]; simp [hv]
  have hptwise (n : ℕ) (τ : ℝ) (hτ : τ ∈ Ioc (0 : ℝ) 1) :
      ‖F n τ‖ ≤ (Nat.factorial n : ℝ)⁻¹ * ‖v n‖ := by
    simp only [hF, norm_smul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ.1]
    gcongr
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hτ.1.le hτ.2)
  have hbnd (n : ℕ) : (∫ τ in Ioc (0 : ℝ) 1, ‖F n τ‖) ≤ (Nat.factorial n : ℝ)⁻¹ * ‖v n‖ := by
    simpa using MeasureTheory.setIntegral_mono_on (hInt n).norm
      (MeasureTheory.integrableOn_const (C := (Nat.factorial n : ℝ)⁻¹ * ‖v n‖) (by simp))
      measurableSet_Ioc (hptwise n)
  have hsummable_int : Summable (fun n ↦ ∫ τ in Ioc (0 : ℝ) 1, ‖F n τ‖) :=
    Summable.of_nonneg_of_le
      (fun n ↦ MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _) hbnd hb
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)) hInt hsummable_int
  -- the pointwise sum
  have hpt (τ : ℝ) : (∑' n, F n τ) = ((τ : ℂ) ^ p) • (evol H (-τ) * E * evol H τ) := by
    rw [← ((hasSum_conj H E τ).const_smul ((τ : ℂ) ^ p)).tsum_eq]
    exact tsum_congr fun n ↦ by simp only [hF, hv, smul_smul, pow_add]; ring_nf
  have hterm (n : ℕ) : (∫ τ in Ioc (0 : ℝ) 1, F n τ)
      = ((Nat.factorial n : ℂ)⁻¹ * ((n : ℂ) + p + 1)⁻¹) • v n := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    simp only [hF, intervalIntegral.integral_smul_const, intervalIntegral.integral_const_mul,
      integral_ofReal_pow]
    congr 2; push_cast; ring
  rw [intervalIntegral.integral_of_le zero_le_one, ← tsum_congr hterm, hHS.tsum_eq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun τ _ ↦ (hpt τ).symm

/-- Evaluating a convergent series of operators term by term. -/
theorem tsum_apply_of_summable {T : ℕ → 𝕄 →L[ℂ] 𝕄} (hT : Summable T) (E : 𝕄) :
    (∑' n, T n) E = ∑' n, (T n) E := by
  simpa using (ContinuousLinearMap.apply ℂ 𝕄 E).map_tsum hT

/-- **The averaging operator is the series `Φ`.**  `Φ(i·ad_H) E = ∫₀¹ e^{iτH} E e^{-iτH} dτ`. -/
theorem phiSeries_adL_apply [NeZero d] (H E : 𝕄) :
    phiSeries (I • adL H) E = ∫ τ in (0 : ℝ)..1, evol H (-τ) * E * evol H τ := by
  have hsum : Summable (fun n : ℕ ↦ ((Nat.factorial (n + 1) : ℂ)⁻¹) • (I • adL H) ^ n) :=
    (summable_norm_phiSeries_term (I • adL H)).of_norm
  have hkey := integral_conj_smul H E 0
  simp only [pow_zero, one_smul, Nat.cast_zero, add_zero] at hkey
  rw [phiSeries, tsum_apply_of_summable hsum, hkey]
  refine tsum_congr fun n ↦ ?_
  simp only [ContinuousLinearMap.smul_apply, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, mul_inv]
  ring_nf

end UnitaryProducts
