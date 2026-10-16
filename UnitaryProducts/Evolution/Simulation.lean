/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib

/-!
# Frozen evolutions, products of unitaries, and bit truncation

## Declarations

- `norm_pow_sub_pow_le`
- `pow_sub_pow_sum`
- `SolvesSchrodinger`
- `mono`
- `star_mul_self_eq`
- `abs_sub_level_lt`
- `abs_sub_truncBits_le`
- `abs_sub_truncBits_lt`
- `commute_evol`
- `evalCLM`
- `evalCLM_apply`
- `evol`
- `evol_add`
- `evol_mem_unitary`
- `evol_neg_mul_self`
- `evol_zero`
- `hasDerivAt_evol`
- `isHermitian_truncHerm`
- `level`
- `level_neg`
- `norm_evalCLM_apply_le`
- `norm_evol_le`
- `norm_le_add_of_abs_re_inner_deriv_le_off_countable`
- `norm_le_one_of_hermitian_off_countable`
- `norm_le_one_of_star_mul_self`
- `norm_sub_le_mul_sub_off_countable`
- `norm_sub_le_of_norm_sub_le_off_countable`
- `norm_sub_le_off_countable_of_contraction`
- `pieceProduct`
- `re_inner_I_smul_hermitian_eq_zero`
- `solvesSchrodinger_evol`
- `star_evol_mul_self`
- `star_truncBitsC`
- `switchTime`
- `switchTime_mono`
- `switchTime_succ`
- `switchTime_zero`
- `toEuclideanCLM_injective`
- `truncBits`
- `truncBitsC`
- `truncBits_eq_self_iff`
- `truncBits_neg`
- `truncHerm`
-/

@[expose] public section

open scoped BigOperators

namespace UnitaryProducts.Paper.UnitStepsProse

/-- Section 4, power-series argument: the exact noncommutative telescoping identity. -/
theorem pow_sub_pow_sum {A : Type*} [Ring A] (a b : A) (n : ℕ) :
    a ^ n - b ^ n = ∑ k ∈ Finset.range n, a ^ k * (a - b) * b ^ (n - 1 - k) := by
  have he : ∀ k ∈ Finset.range n,
      a ^ k * (a - b) * b ^ (n - 1 - k) =
        a ^ (k + 1) * b ^ (n - (k + 1)) - a ^ k * b ^ (n - k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h₁ : n - 1 - k = n - (k + 1) := by omega
    have h₂ : n - k = (n - (k + 1)) + 1 := by omega
    rw [h₁, h₂, pow_succ a, pow_succ' b]
    noncomm_ring
  rw [Finset.sum_congr rfl he,
    Finset.sum_range_sub (fun k ↦ a ^ k * b ^ (n - k))]
  simp

end UnitaryProducts.Paper.UnitStepsProse

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormOneClass A]

/-- Bound the full noncommutative telescope term by term, then sum its
scalar geometric majorant. This is the finite-sum argument of the product comparison bound. -/
theorem norm_pow_sub_pow_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * r ^ (n - 1) * ‖a - b‖ := by
  rw [UnitaryProducts.Paper.UnitStepsProse.pow_sub_pow_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖a ^ k * (a - b) * b ^ (n - 1 - k)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, r ^ k * ‖a - b‖ * r ^ (n - 1 - k) := by
      apply Finset.sum_le_sum
      intro k _
      have hleft := (norm_pow_le a k).trans
        (pow_le_pow_left₀ (norm_nonneg a) ha k)
      have hright := (norm_pow_le b (n - 1 - k)).trans
        (pow_le_pow_left₀ (norm_nonneg b) hb (n - 1 - k))
      exact norm_mul_le_of_le (norm_mul_le_of_le hleft le_rfl) hright
    _ = (∑ k ∈ Finset.range n, r ^ k * r ^ (n - 1 - k)) * ‖a - b‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [geom_sum₂_self]

end UnitaryProducts.Corrector

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory NormedSpace

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Mean-value inequality off a countable set: a continuous real $f$ on $[a,b]$ with $|f'| \le C$
outside a countable set satisfies $|f(b) - f(a)| \le C(b - a)$. -/
theorem norm_sub_le_mul_sub_off_countable {f f' : ℝ → ℝ} {a b C : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Ioo a b, t ∉ S → ‖f' t‖ ≤ C) :
    ‖f b - f a‖ ≤ C * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hC : 0 ≤ C := by
    by_contra hn
    have hsub : Ioo a b ⊆ S := fun t ht ↦ by
      by_contra htS
      exact hn ((norm_nonneg _).trans (hb t ht htS))
    have hz : volume (Ioo a b) = 0 := measure_mono_null hsub (hS.measure_zero volume)
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hz
    linarith
  classical
  let D := (Ioo a b \ S).indicator (deriv f)
  have hDb : ∀ t, ‖D t‖ ≤ C := fun t ↦ by
    by_cases ht : t ∈ Ioo a b \ S
    · rw [show D t = deriv f t from Set.indicator_of_mem ht _, (hd t ht.1 ht.2).deriv]
      exact hb t ht.1 ht.2
    · simpa only [show D t = 0 from Set.indicator_of_notMem ht _, norm_zero] using hC
  have hm : StronglyMeasurable D :=
    (stronglyMeasurable_deriv f).indicator (isOpen_Ioo.measurableSet.diff hS.measurableSet)
  have hi : IntervalIntegrable D volume a b :=
    (intervalIntegrable_const (a := a) (b := b) (c := C)).mono_fun hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t ↦ (hDb t).trans (le_abs_self C))
  have he := integral_eq_of_hasDerivAt_off_countable_of_le f D hab hS hc
    (fun t ht ↦ (hd t ht.1 ht.2).congr_deriv (by
      rw [show D t = deriv f t from Set.indicator_of_mem ht _, (hd t ht.1 ht.2).deriv])) hi
  rw [← he]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (fun t _ ↦ hDb t))

/-- **A mean-value bound in the radial direction.**  A curve in an inner-product space whose
velocity has radial component at most `C` in absolute value moves at most `C (b - a)` away from
the origin: the estimate is obtained from `‖y‖ = lim √(‖y‖² + ε)`, whose derivative is
`Re ⟪y, y'⟫/√(‖y‖² + ε)`. -/
theorem norm_le_add_of_abs_re_inner_deriv_le_off_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {y y' : ℝ → E} {a b C : ℝ} (S : Set ℝ) (hS : S.Countable) (hab : a ≤
      b) (hC : 0 ≤ C)
    (hyc : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Ioo a b, t ∉ S → HasDerivWithinAt y (y' t) (Icc a b) t)
    (hre : ∀ t ∈ Ioo a b, t ∉ S → |(inner ℂ (y t) (y' t) : ℂ).re| ≤ C * ‖y t‖) :
    ‖y b‖ ≤ ‖y a‖ + C * (b - a) := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- Step 1: g = √(‖y‖² + ε²) is differentiable even where y = 0, with
  -- g' = Re⟨y, y'⟩ / g, of absolute value at most C.
  set Q : ℝ → ℝ := fun t ↦ ‖y t‖ ^ 2 + ε ^ 2 with hQ
  have hQpos : ∀ t, 0 < Q t := fun t ↦ by positivity
  have hnormle : ∀ t, ‖y t‖ ≤ Real.sqrt (Q t) := fun t ↦
    Real.le_sqrt_of_sq_le (by simp only [hQ]; linarith [sq_nonneg ε])
  set g : ℝ → ℝ := fun t ↦ Real.sqrt (Q t) with hg
  have hgd : ∀ t ∈ Ioo a b, t ∉ S → HasDerivWithinAt g
      (1 / (2 * Real.sqrt (Q t)) * (2 * (inner ℂ (y t) (y' t) : ℂ).re)) (Icc a b) t := by
    intro t ht hn
    have hq : HasDerivWithinAt (fun s ↦ (inner ℂ (y s) (y s) : ℂ))
        ((inner ℂ (y t) (y' t) : ℂ) + (inner ℂ (y' t) (y t) : ℂ)) (Icc a b) t :=
      (hy t ht hn).inner ℂ (hy t ht hn)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hq
    have hc : (inner ℂ (y' t) (y t) : ℂ) = (starRingEnd ℂ) (inner ℂ (y t) (y' t) : ℂ) :=
      (inner_conj_symm _ _).symm
    have hval : (Complex.reCLM ((inner ℂ (y t) (y' t) : ℂ) + (inner ℂ (y' t) (y t) : ℂ)))
        = 2 * (inner ℂ (y t) (y' t) : ℂ).re := by
      rw [Complex.reCLM_apply, hc, Complex.add_re, Complex.conj_re]
      ring
    have hself : ∀ s : ℝ, (Complex.reCLM ∘ fun s ↦ (inner ℂ (y s) (y s) : ℂ)) s = ‖y s‖ ^ 2 :=
      fun s ↦ by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (y s)
    have h3 : HasDerivWithinAt (fun s ↦ ‖y s‖ ^ 2) (2 * (inner ℂ (y t) (y' t) : ℂ).re)
        (Icc a b) t :=
      (h2.congr_deriv hval).congr (fun s _ ↦ (hself s).symm) (hself t).symm
    have h4 : HasDerivWithinAt Q (2 * (inner ℂ (y t) (y' t) : ℂ).re) (Icc a b) t :=
      h3.add_const _
    exact (Real.hasDerivAt_sqrt (ne_of_gt (hQpos t))).comp_hasDerivWithinAt t h4
  have hbound : ∀ t ∈ Ioo a b, t ∉ S →
      ‖1 / (2 * Real.sqrt (Q t)) * (2 * (inner ℂ (y t) (y' t) : ℂ).re)‖ ≤ C := by
    intro t ht hn
    have hs : 0 < Real.sqrt (Q t) := Real.sqrt_pos.mpr (hQpos t)
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.sqrt (Q t))),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 1 / (2 * Real.sqrt (Q t)) * (2 * |(inner ℂ (y t) (y' t) : ℂ).re|)
        ≤ 1 / (2 * Real.sqrt (Q t)) * (2 * (C * ‖y t‖)) := by gcongr; exact hre t ht hn
      _ = C * (‖y t‖ / Real.sqrt (Q t)) := by field_simp
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left ((div_le_one hs).mpr (hnormle t)) hC
      _ = C := mul_one C
  -- Step 2: the mean-value inequality off S gives g(b) ≤ g(a) + C(b - a), and
  -- ‖y b‖ ≤ g(b), g(a) ≤ ‖y a‖ + ε; then let ε → 0.
  have hgc : ContinuousOn g (Icc a b) :=
    (hyc.norm.pow 2 |>.add continuousOn_const).sqrt
  have hmvt := (le_abs_self (g b - g a)).trans (norm_sub_le_mul_sub_off_countable S hS hab hgc
    (fun t ht hn ↦ (hgd t ht hn).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hbound)
  have hga : g a ≤ ‖y a‖ + ε := by
    have h1 : Q a ≤ (‖y a‖ + ε) ^ 2 := by
      simp only [hQ]; linarith [(by positivity : (0:ℝ) ≤ 2 * ‖y a‖ * ε)]
    exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (by positivity))
  linarith [hnormle b]

/-- Evaluation $X \mapsto Xv$ of a matrix at a vector $v$, as a continuous linear map in the matrix,
of norm at most $\|v\|$. It reduces operator-norm estimates to estimates on vectors. -/
noncomputable def evalCLM (v : EuclideanSpace ℂ (Fin d)) : 𝕄 →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.mkContinuous
    { toFun := fun X ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) X v
      map_add' := by intro X Y; simp
      map_smul' := by intro c X; simp }
    ‖v‖ fun X ↦ by
      rw [mul_comm, ← Matrix.l2_opNorm_toEuclideanCLM X]
      exact ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) X) v

/-- `evalCLM v X` is $Xv$. -/
theorem evalCLM_apply (v : EuclideanSpace ℂ (Fin d)) (X : 𝕄) :
    evalCLM v X = Matrix.toEuclideanCLM (𝕜 := ℂ) X v := rfl

/-- $\|Xv\| \le \|X\|\,\|v\|$. -/
theorem norm_evalCLM_apply_le (v : EuclideanSpace ℂ (Fin d)) (X : 𝕄) :
    ‖evalCLM v X‖ ≤ ‖X‖ * ‖v‖ := by
  rw [evalCLM_apply, ← Matrix.l2_opNorm_toEuclideanCLM X]
  exact ContinuousLinearMap.le_opNorm _ _

/-- The radial component of `-i H y` vanishes for Hermitian `H`: this is why a Hermitian
generator does not change the length of the state. -/
theorem re_inner_I_smul_hermitian_eq_zero {X : 𝕄} (hX : X.IsHermitian)
    (y : EuclideanSpace ℂ (Fin d)) :
    (inner ℂ y ((-I : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) X y)) : ℂ).re = 0 := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℂ) X with hT
  have hsa : IsSelfAdjoint T := by
    rw [IsSelfAdjoint, hT, ← map_star, show star X = X from hX.eq]
  have him : (inner ℂ y (T y) : ℂ).im = 0 := hsa.isSymmetric.im_inner_self_apply y
  rw [inner_smul_right]
  simp [Complex.mul_re, him]

/-- **A Hermitian generator keeps a contraction a contraction**, the equation being required only
outside a countable set `S`: for every vector `v` the radial component of `-i K U v` vanishes. -/
theorem norm_le_one_of_hermitian_off_countable {K U : ℝ → 𝕄} {a b : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hK : ∀ t ∈ Icc a b, t ∉ S → (K t).IsHermitian)
    (hUc : ContinuousOn U (Icc a b))
    (hU : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U (-I • (K t * U t)) (Icc a b) t)
    (hUa : ‖U a‖ ≤ 1) : ∀ t ∈ Icc a b, ‖U t‖ ≤ 1 := by
  intro t ht
  rw [← Matrix.l2_opNorm_toEuclideanCLM (U t)]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hv := norm_le_add_of_abs_re_inner_deriv_le_off_countable
    (y := fun s ↦ evalCLM v (U s))
    (y' := fun s ↦ evalCLM v (-I • (K s * U s))) S hS ht.1 (le_refl 0)
    (((evalCLM v).continuous.comp_continuousOn hUc).mono hsub)
    (fun s hs hn ↦ ((evalCLM v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s
      ((hU s (hsub (Ioo_subset_Icc_self hs)) hn).mono hsub))
    (fun s hs hn ↦ by
      have he : evalCLM v (-I • (K s * U s)) =
          (-I : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) (K s) (evalCLM v (U s))) := by
        simp only [map_smul, evalCLM_apply, map_mul, ContinuousLinearMap.mul_apply]
      dsimp only
      rw [he, re_inner_I_smul_hermitian_eq_zero (hK s (hsub (Ioo_subset_Icc_self hs)) hn),
        abs_zero, zero_mul])
  exact ((by simpa only [zero_mul, add_zero] using hv :
    ‖evalCLM v (U t)‖ ≤ ‖evalCLM v (U a)‖).trans ((norm_evalCLM_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right hUa (norm_nonneg _))))

/-- **Duhamel against a Hermitian generator.**  If `U` is a contraction on `[a, b]` and `K'` is
Hermitian, continuous evolutions under `K` and `K'` whose generators stay within `η` of each other
drift apart by at most `η (b - a)`.  The equations and the bound are required only outside the
countable set `S`, and nothing is asked of `K` itself. -/
theorem norm_sub_le_off_countable_of_contraction {K K' U U' : ℝ → 𝕄} {a b η : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b)
    (hK' : ∀ t ∈ Icc a b, t ∉ S → (K' t).IsHermitian)
    (hUc : ContinuousOn U (Icc a b)) (hU'c : ContinuousOn U' (Icc a b))
    (hU : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U (-I • (K t * U t)) (Icc a b) t)
    (hU' : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U' (-I • (K' t * U' t)) (Icc a b) t)
    (hUnit : ∀ t ∈ Icc a b, ‖U t‖ ≤ 1)
    (hη : ∀ t ∈ Icc a b, t ∉ S → ‖K t - K' t‖ ≤ η) :
    ‖U b - U' b‖ ≤ ‖U a - U' a‖ + η * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [sub_self, mul_zero, add_zero, le_refl]
  obtain ⟨t₀, hn₀, ht₀⟩ := (hS.dense_compl ℝ).exists_between hab
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη t₀ (Ioo_subset_Icc_self ht₀) hn₀)
  -- Step 1: Y = U - U' solves Y' = -iK'Y + F with ‖F‖ = ‖(K - K')U‖ ≤ η off S.
  set Y : ℝ → 𝕄 := fun t ↦ U t - U' t with hYdef
  set F : ℝ → 𝕄 := fun t ↦ -I • ((K t - K' t) * U t) with hFdef
  have hYd : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt Y (-I • (K' t * Y t) + F t) (Icc a b) t :=
    fun t ht hn ↦ by
    refine ((hU t ht hn).sub (hU' t ht hn)).congr_deriv ?_
    change -I • (K t * U t) - -I • (K' t * U' t)
      = -I • (K' t * (U t - U' t)) + -I • ((K t - K' t) * U t)
    rw [mul_sub, sub_mul, smul_sub, smul_sub]
    abel
  have hFnorm : ∀ t ∈ Icc a b, t ∉ S → ‖F t‖ ≤ η := fun t ht hn ↦ by
    simp only [hFdef, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact (norm_mul_le_of_le (hη t ht hn) (hUnit t ht)).trans_eq (mul_one η)
  -- Step 2: for each vector v, the radial part of -iK'Yv vanishes because K' is Hermitian, so
  -- ‖Y(b)v‖ ≤ ‖Y(a)v‖ + η‖v‖(b - a); taking the supremum over v bounds the operator norm.
  have hvec : ∀ v : EuclideanSpace ℂ (Fin d),
      ‖evalCLM v (Y b)‖ ≤ (‖Y a‖ + η * (b - a)) * ‖v‖ := by
    intro v
    have hyd : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt (fun s ↦ evalCLM v (Y s))
        (evalCLM v (-I • (K' t * Y t) + F t)) (Icc a b) t := fun t ht hn ↦
      ((evalCLM v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hYd t ht hn)
    have hre : ∀ t ∈ Icc a b, t ∉ S →
        |(inner ℂ (evalCLM v (Y t)) (evalCLM v (-I • (K' t * Y t) + F t)) : ℂ).re|
          ≤ (η * ‖v‖) * ‖evalCLM v (Y t)‖ := by
      intro t ht hn
      have hsplit : evalCLM v (-I • (K' t * Y t) + F t)
          = (-I : ℂ) • (Matrix.toEuclideanCLM (𝕜 := ℂ) (K' t) (evalCLM v (Y t)))
            + evalCLM v (F t) := by
        rw [map_add, map_smul]; congr 2; simp [evalCLM_apply]
      rw [hsplit, inner_add_right, Complex.add_re,
        re_inner_I_smul_hermitian_eq_zero (hK' t ht hn), zero_add]
      calc |(inner ℂ (evalCLM v (Y t)) (evalCLM v (F t)) : ℂ).re|
          ≤ ‖(inner ℂ (evalCLM v (Y t)) (evalCLM v (F t)) : ℂ)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖evalCLM v (Y t)‖ * ‖evalCLM v (F t)‖ := norm_inner_le_norm _ _
        _ ≤ ‖evalCLM v (Y t)‖ * (η * ‖v‖) :=
            mul_le_mul_of_nonneg_left ((norm_evalCLM_apply_le v (F t)).trans
              (mul_le_mul_of_nonneg_right (hFnorm t ht hn) (norm_nonneg v))) (norm_nonneg _)
        _ = (η * ‖v‖) * ‖evalCLM v (Y t)‖ := by ring
    have hmain := norm_le_add_of_abs_re_inner_deriv_le_off_countable S hS hab.le
      (mul_nonneg hη0 (norm_nonneg v))
      ((evalCLM v).continuous.comp_continuousOn (hUc.sub hU'c))
      (fun t ht hn ↦ hyd t (Ioo_subset_Icc_self ht) hn)
      (fun t ht hn ↦ hre t (Ioo_subset_Icc_self ht) hn)
    calc ‖evalCLM v (Y b)‖ ≤ ‖evalCLM v (Y a)‖ + (η * ‖v‖) * (b - a) := hmain
      _ ≤ ‖Y a‖ * ‖v‖ + (η * ‖v‖) * (b - a) := add_le_add (norm_evalCLM_apply_le v (Y a)) le_rfl
      _ = (‖Y a‖ + η * (b - a)) * ‖v‖ := by ring
  rw [← Matrix.l2_opNorm_toEuclideanCLM (Y b)]
  exact ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (mul_nonneg hη0 (by linarith))) hvec

/-- **Duhamel for two Hamiltonians, with a countable exceptional set** (the comparison lemma).
Continuous evolutions under Hermitian `K` and `K'` that stay within `η` of each other on
`[a, b] \ S` drift apart by at most `η (b - a)`, when `U` starts as a contraction (the evolution
then keeps `‖U‖ ≤ 1`).  The equations and the bound are required only outside the countable set
`S`. -/
theorem norm_sub_le_of_norm_sub_le_off_countable {K K' U U' : ℝ → 𝕄} {a b η : ℝ}
    (S : Set ℝ) (hS : S.Countable) (hab : a ≤ b) (hK : ∀ t ∈ Icc a b, t ∉ S → (K t).IsHermitian)
    (hK' : ∀ t ∈ Icc a b, t ∉ S → (K' t).IsHermitian)
    (hUc : ContinuousOn U (Icc a b)) (hU'c : ContinuousOn U' (Icc a b))
    (hU : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U (-I • (K t * U t)) (Icc a b) t)
    (hU' : ∀ t ∈ Icc a b, t ∉ S → HasDerivWithinAt U' (-I • (K' t * U' t)) (Icc a b) t) (hUa : ‖U
      a‖ ≤ 1)
    (hη : ∀ t ∈ Icc a b, t ∉ S → ‖K t - K' t‖ ≤ η) :
    ‖U b - U' b‖ ≤ ‖U a - U' a‖ + η * (b - a) :=
  norm_sub_le_off_countable_of_contraction S hS hab hK' hUc hU'c hU hU'
    (norm_le_one_of_hermitian_off_countable S hS hK hUc hU hUa) hη

end UnitaryProducts

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Finset

variable {d : ℕ}

/-- `d × d` complex matrices, with the operator norm. -/
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- An isometry has operator norm at most one (the C⋆-identity). -/
theorem norm_le_one_of_star_mul_self {X : 𝕄} (h : star X * X = 1) : ‖X‖ ≤ 1 := by
  nontriviality 𝕄
  exact (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff'.mpr h)).le

/-- $U$ solves $iU'(s) = H(s)U(s)$ at every point of $[a,b]$, one-sided at the ends. This is
stronger than "generates" in the sense of §2 (`Paper.IsEvolution`), which
allows countably many exceptions; it is the notion used for continuous Hamiltonians. For $b < a$
it holds vacuously. -/
def SolvesSchrodinger (H U : ℝ → 𝕄) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, HasDerivWithinAt U (-I • (H s * U s)) (Icc a b) s

/-- A solution on $[a,b]$ is a solution on every subinterval. -/
theorem SolvesSchrodinger.mono {H U : ℝ → 𝕄} {a b a' b' : ℝ} (h : SolvesSchrodinger H U a b)
    (hsub : Icc a' b' ⊆ Icc a b) : SolvesSchrodinger H U a' b' :=
  fun s hs ↦ (h s (hsub hs)).mono hsub

/-- **Evolution under a Hermitian Hamiltonian preserves unitarity**:
`(U s)⋆ U s` is constant, because its derivative is `i U⋆ H⋆ U - i U⋆ H U = 0`. -/
theorem SolvesSchrodinger.star_mul_self_eq {H U : ℝ → 𝕄} {a b : ℝ}
    (hH : ∀ s ∈ Icc a b, (H s).IsHermitian) (hU : SolvesSchrodinger H U a b) :
    ∀ s ∈ Icc a b, star (U s) * U s = star (U a) * U a := by
  intro s hs
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun y ↦ star (U y) * U y) (0 : 𝕄) (Icc a b) x := by
    intro x hx
    convert (hU x hx).star.mul (hU x hx) using 1
    simp [star_smul, star_mul, show star (H x) = H x from (hH x hx).eq, conj_I, neg_neg, mul_assoc]
  simpa [sub_eq_zero] using
    norm_image_sub_le_of_norm_deriv_le_segment' hderiv (C := 0) (fun x _ ↦ by simp) s hs

/-- The frozen evolution $e^{-iuG}$ of the constant Hamiltonian $G$ for time $u$, the factor of
(2.5). It is defined for every $G$ and $u$, and is unitary when $G$ is Hermitian
(`star_evol_mul_self`). -/
noncomputable def evol (G : 𝕄) (u : ℝ) : 𝕄 := exp (u • (-I • G))

/-- $e^{-i0G} = 1$. -/
theorem evol_zero (G : 𝕄) : evol G 0 = 1 := by simp [evol]

/-- $e^{-i(u+v)G} = e^{-iuG}e^{-ivG}$. -/
theorem evol_add (G : 𝕄) (u v : ℝ) : evol G (u + v) = evol G u * evol G v := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol, add_smul]
  exact exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)

/-- $\frac{d}{du}e^{-iuG} = -iG\,e^{-iuG}$: Mathlib's `hasDerivAt_exp_smul_const'`, stated for
`evol`. -/
theorem hasDerivAt_evol (G : 𝕄) (u : ℝ) :
    HasDerivAt (evol G) ((-I • G) * evol G u) u :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) _ _

/-- $-iG$ commutes with $e^{-iuG}$. -/
theorem commute_evol (G : 𝕄) (u : ℝ) : Commute (-I • G) (evol G u) :=
  ((Commute.refl (-I • G)).smul_right (u : ℝ)).exp_right

/-- `e^{-iuG}` solves the Schrödinger equation for the constant Hamiltonian `G`. -/
theorem solvesSchrodinger_evol (G : 𝕄) (a b : ℝ) :
    SolvesSchrodinger (fun _ ↦ G) (evol G) a b := fun s _ ↦ by
  simpa [smul_mul_assoc] using (hasDerivAt_evol G s).hasDerivWithinAt

/-- `e^{-iuG}` is unitary for Hermitian `G`: `-iuG` is skew-adjoint, and Mathlib's
`NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` applies. -/
theorem evol_mem_unitary {G : 𝕄} (hG : G.IsHermitian) (u : ℝ) : evol G u ∈ unitary 𝕄 := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem u (hG.isSelfAdjoint.smul_mem_skewAdjoint hI))

/-- `(e^{-iuG})⋆ e^{-iuG} = 1` for Hermitian `G`. -/
theorem star_evol_mul_self {G : 𝕄} (hG : G.IsHermitian) (u : ℝ) :
    star (evol G u) * evol G u = 1 :=
  Unitary.star_mul_self_of_mem (evol_mem_unitary hG u)

/-- $\|e^{-iuG}\| \le 1$ for Hermitian $G$. -/
theorem norm_evol_le {G : 𝕄} (hG : G.IsHermitian) (u : ℝ) : ‖evol G u‖ ≤ 1 :=
  norm_le_one_of_star_mul_self (star_evol_mul_self hG u)

/-- The switch times $t_j = \tau_0 + \dots + \tau_{j-1}$ of the partition with durations $\tau$,
starting at $t_0 = 0$. -/
def switchTime (τ : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, τ i

/-- $t_{j+1} = t_j + \tau_j$. -/
theorem switchTime_succ (τ : ℕ → ℝ) (j : ℕ) : switchTime τ (j + 1) = switchTime τ j + τ j :=
  sum_range_succ _ _

/-- Nonnegative durations give nondecreasing switch times. -/
theorem switchTime_mono {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j) : Monotone (switchTime τ) :=
  monotone_nat_of_le_succ fun j ↦ by rw [switchTime_succ]; linarith [hτ j]

/-- $t_0 = 0$. -/
theorem switchTime_zero (τ : ℕ → ℝ) : switchTime τ 0 = 0 := by simp [switchTime]

/-- The product of unitaries (2.5) induced by a piecewise-constant family (equation (2.5)):
$e^{-i\tau_{n-1}G_{n-1}} \cdots e^{-i\tau_0G_0}$, one factor per piece, the latest piece on the
left. The empty product is $1$, and a piece of duration $0$ contributes the factor $1$. -/
noncomputable def pieceProduct (τ : ℕ → ℝ) (G : ℕ → 𝕄) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => evol (G n) (τ n) * pieceProduct τ G n

/-- The integer $2^k[x]_k$ of Example 3.2: $\lfloor 2^kx \rfloor$ for $x \ge 0$ and
$\lceil 2^kx \rceil$ for $x < 0$, so $2^kx$ rounded toward zero. -/
noncomputable def level (k : ℕ) (x : ℝ) : ℤ :=
  if 0 ≤ x then ⌊(2 : ℝ) ^ k * x⌋ else ⌈(2 : ℝ) ^ k * x⌉

/-- Bit truncation $[x]_k = \operatorname{sgn}(x)\,2^{-k}\lfloor 2^k|x| \rfloor$ of Example 3.2: $x$
rounded toward zero to $k$ binary places, computed as `level k x / 2^k`. -/
noncomputable def truncBits (k : ℕ) (x : ℝ) : ℝ := (level k x : ℝ) / 2 ^ k

/-- $|2^kx - 2^k[x]_k| < 1$. -/
theorem abs_sub_level_lt (k : ℕ) (x : ℝ) : |(2 : ℝ) ^ k * x - level k x| < 1 := by
  rw [abs_lt, level]
  split_ifs with hx
  · constructor <;> linarith [Int.floor_le ((2 : ℝ) ^ k * x), Int.lt_floor_add_one ((2 : ℝ) ^ k *
    x)]
  · constructor <;> linarith [Int.le_ceil ((2 : ℝ) ^ k * x), Int.ceil_lt_add_one ((2 : ℝ) ^ k * x)]

/-- Rounding toward zero is odd. -/
theorem level_neg (k : ℕ) (x : ℝ) : level k (-x) = -level k x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [level, level, if_pos (by linarith), if_neg (by linarith), mul_neg, Int.floor_neg]
  · simp [level]
  · rw [level, level, if_neg (by linarith), if_pos hx.le, mul_neg, Int.ceil_neg]

/-- $|x - [x]_k| < 2^{-k}$ (Example 3.2, proof of (ii)). -/
theorem abs_sub_truncBits_lt (k : ℕ) (x : ℝ) : |x - truncBits k x| < ((2 : ℝ) ^ k)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have e : x - truncBits k x = ((2 : ℝ) ^ k * x - level k x) / 2 ^ k := by
    rw [truncBits]; field_simp
  rw [e, abs_div, abs_of_pos hp, div_lt_iff₀ hp, inv_mul_cancel₀ hp.ne']
  exact abs_sub_level_lt k x

/-- $|x - [x]_k| \le 2^{-k}$. -/
theorem abs_sub_truncBits_le (k : ℕ) (x : ℝ) : |x - truncBits k x| ≤ ((2 : ℝ) ^ k)⁻¹ :=
  (abs_sub_truncBits_lt k x).le

/-- Bit truncation is odd (Example 3.2(i)). -/
theorem truncBits_neg (k : ℕ) (x : ℝ) : truncBits k (-x) = -truncBits k x := by
  rw [truncBits, truncBits, level_neg, Int.cast_neg, neg_div]

/-- $[x]_k=x$ exactly when $x\in2^{-k}\mathbb Z$, so bit truncation changes a number exactly when
it is not a multiple of $2^{-k}$ (the paragraph before Example 3.2). -/
theorem truncBits_eq_self_iff (k : ℕ) (x : ℝ) : truncBits k x = x ↔ ∃ m : ℤ, x = m / 2 ^ k := by
  refine ⟨fun h ↦ ⟨level k x, h.symm⟩, ?_⟩
  rintro ⟨m, rfl⟩
  -- `2^k x` is the integer `m`, so rounding it toward zero returns `m`.
  have hl : level k ((m : ℝ) / 2 ^ k) = m := by
    rw [level, show (2 : ℝ) ^ k * ((m : ℝ) / 2 ^ k) = m by field_simp]
    split_ifs
    exacts [Int.floor_intCast m, Int.ceil_intCast m]
  rw [truncBits, hl]

/-- Bit truncation of a complex number, applied to its real and imaginary parts, as a real
function acts on entries in §3.1. -/
noncomputable def truncBitsC (k : ℕ) (z : ℂ) : ℂ := ⟨truncBits k z.re, truncBits k z.im⟩

/-- Truncation commutes with complex conjugation. -/
theorem star_truncBitsC (k : ℕ) (z : ℂ) : star (truncBitsC k z) = truncBitsC k (star z) := by
  apply Complex.ext <;> simp [truncBitsC, truncBits_neg]

/-- The entrywise $k$-bit truncation $H^{(k)}$ of Example 3.2. Since the truncation of a number is
odd, it commutes with conjugation, so the truncation of a Hermitian matrix is again Hermitian
(`isHermitian_truncHerm`). -/
noncomputable def truncHerm (k : ℕ) (A : 𝕄) : 𝕄 :=
  Matrix.of fun i j ↦ truncBitsC k (A i j)

/-- $H^{(k)}$ is Hermitian when $H$ is. -/
theorem isHermitian_truncHerm (k : ℕ) {A : 𝕄} (hA : A.IsHermitian) :
    (truncHerm k A).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, truncHerm, Matrix.of_apply, star_truncBitsC, hA.apply]

/-- $e^{iuG}e^{-iuG} = 1$. -/
theorem evol_neg_mul_self (G : 𝕄) (u : ℝ) : evol G (-u) * evol G u = 1 := by
  rw [← evol_add, neg_add_cancel, evol_zero]

/-- Matrices that act equally on every vector are equal. -/
theorem toEuclideanCLM_injective {M N : 𝕄} (h : ∀ v, Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M
    v = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) N v) : M = N :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective (ContinuousLinearMap.ext h)

end UnitaryProducts
