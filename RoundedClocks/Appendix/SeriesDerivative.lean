/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.JacobiTelescope
public import RoundedClocks.Citations
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Equation (A.2): termwise differentiation of a commutator series

For `Ω(s)` and `A(s)` continuously differentiable with `‖[Ω(s),·]‖ ≤ w`, and a power series
`g(x) = ∑ gₙ xⁿ` with every `gₙ ≥ 0`, termwise differentiation gives the first
line of (A.2),
`(g([Ω,·])A)' = g([Ω,·])A' + ∑ₙ gₙ ∑_{k<n} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} A]`
(`hasDerivWithinAt_adL_series`). Each of the `n` terms with coefficient `gₙ` has norm at most
`2 gₙ w^{n-1} ‖Ω'‖ ‖A‖`, which gives the second line,
`‖(g([Ω,·])A)'‖ ≤ g(w) ‖A'‖ + 2g'(w) ‖Ω'‖ ‖A‖` (`norm_adL_series_deriv_le`). The sum over `k` is
`powDeriv (adL Ω) (adL Ω') n A`. For `g = 𝒩`, `g'(w) = ∑ n νₙ w^{n-1}` is `𝒩'(w)`
(`deriv_𝒩_eq_tsum`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

attribute [local instance] continuousSMul_real_clm

/-! ## Each term and its derivative -/

/-- `‖[Ω,·]‖ ≤ 2 ‖Ω‖`. -/
theorem norm_adL_le_two_mul (Ω : 𝕄) : ‖adL Ω‖ ≤ 2 * ‖Ω‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro E
  simpa only [zero_smul, sub_zero] using norm_adL_apply_le Ω E 0

/-- The map `Ω ↦ [Ω,·]`, which is complex-linear and continuous. -/
def adLCLM : 𝕄 →L[ℂ] (𝕄 →L[ℂ] 𝕄) :=
  ContinuousLinearMap.mul ℂ 𝕄 - (ContinuousLinearMap.mul ℂ 𝕄).flip

/-- One term of the first line of (A.2):
`(c [Ω,·]ⁿ A)' = c ([Ω,·]ⁿ A' + ∑_{k<n} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} A])`. -/
theorem hasDerivWithinAt_adL_series_term (Ω A : ℝ → 𝕄) (Ω' A' : 𝕄)
    (S : Set ℝ) (s c : ℝ) (n : ℕ)
    (hΩ : HasDerivWithinAt Ω Ω' S s) (hA : HasDerivWithinAt A A' S s) :
    HasDerivWithinAt (fun t ↦ (c : ℂ) • ((adL (Ω t) ^ n) (A t)))
      ((c : ℂ) • (((adL (Ω s) ^ n) A') +
        (powDeriv (adL (Ω s)) (adL Ω') n) (A s))) S s := by
  let L : 𝕄 →L[ℝ] (𝕄 →L[ℂ] 𝕄) :=
    (adLCLM (d := d)).restrictScalars ℝ
  have hL₀ : HasFDerivAt L L (Ω s) := L.hasFDerivAt
  have hL : HasDerivWithinAt (fun t ↦ adL (Ω t)) (adL Ω') S s := by
    exact HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
      (F := 𝕄) (E := 𝕄 →L[ℂ] 𝕄) s hL₀ hΩ
  have hP : HasDerivWithinAt (fun t ↦ adL (Ω t) ^ n)
      (powDeriv (adL (Ω s)) (adL Ω') n) S s := by
    simpa only [powDeriv, Nat.pred_eq_sub_one] using
      HasDerivWithinAt.fun_pow' (𝕜 := ℝ) (𝔸 := 𝕄 →L[ℂ] 𝕄) hL n
  have hR := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
    (F := 𝕄 →L[ℂ] 𝕄) (E := 𝕄 →L[ℝ] 𝕄) s
    (ContinuousLinearMap.restrictScalarsL ℂ 𝕄 𝕄 ℝ ℝ).hasFDerivAt hP
  simpa only [Function.comp_apply, Pi.smul_apply, add_comm] using
    (hR.clm_apply hA).const_smul (c : ℂ)

/-- One term of the second line of (A.2): the `n` terms with coefficient `c` have total norm at
most `2 c n w^{n-1} ‖B‖ ‖A‖`. Width `0` and `n = 0` are included. -/
theorem norm_powDeriv_series_term_le [NeZero d] {Ω B A : 𝕄} {w c : ℝ}
    (hw0 : 0 ≤ w) (hc : 0 ≤ c) (ha : ‖adL Ω‖ ≤ w) (n : ℕ) :
    ‖(c : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖ ≤
      2 * c * (n : ℝ) * w ^ (n - 1) * ‖B‖ * ‖A‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ c * (‖powDeriv (adL Ω) (adL B) n‖ * ‖A‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ A) hc
    _ ≤ c * (((n : ℝ) * w ^ (n - 1) * (2 * ‖B‖)) * ‖A‖) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg A)
      exact (norm_powDeriv_le (b := adL B) ha n).trans
        (mul_le_mul_of_nonneg_left (norm_adL_le_two_mul B)
          (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hw0 _)))
    _ = _ := by ring

/-- The series of sums over `k` converges absolutely when `∑ n cₙ w^{n-1}` converges. -/
theorem summable_norm_powDeriv_series [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {Ω B A : 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * n * w ^ (n - 1))) :
    Summable (fun n ↦ ‖(c n : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖) := by
  have hm := ((hs.mul_left 2).mul_right ‖B‖).mul_right ‖A‖
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hm
  exact (norm_powDeriv_series_term_le hw0 (hc n) ha n).trans_eq (by ring)

/-- The second term in the second line of (A.2):
`‖∑ₙ cₙ ∑_{k<n} [Ω,·]^k [B, [Ω,·]^{n-1-k} A]‖ ≤ 2 (∑ n cₙ w^{n-1}) ‖B‖ ‖A‖`. -/
theorem norm_powDeriv_series_le [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {Ω B A : 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * n * w ^ (n - 1))) :
    ‖∑' n, (c n : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖ ≤
      2 * (∑' n, c n * n * w ^ (n - 1)) * ‖B‖ * ‖A‖ :=
  tsum_of_norm_bounded (((hs.hasSum.mul_left 2).mul_right ‖B‖).mul_right ‖A‖) fun n ↦
    (norm_powDeriv_series_term_le hw0 (hc n) ha n).trans_eq (by ring)

/-- For `t ∈ [a,b]`, the terms of the differentiated series have a summable majorant, as `A`,
`Ω'`, and `A'` are bounded on the compact interval. -/
theorem adL_series_deriv_majorant [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ} (hw0 : 0 ≤ w)
    (hs : Summable (fun n ↦ c n * w ^ n))
    (hs' : Summable (fun n ↦ c n * n * w ^ (n - 1)))
    {Ω A Ω' A' : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hA : ContinuousOn A (Icc a b))
    (hΩ' : ContinuousOn Ω' (Icc a b)) (hA' : ContinuousOn A' (Icc a b)) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n, ∀ t ∈ Icc a b,
      ‖(c n : ℂ) • (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))‖ ≤ u n := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn hΩ'
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hA'
  refine ⟨fun n ↦ c n * w ^ n * max Q 0 +
    2 * (c n * n * w ^ (n - 1)) * max P 0 * max M 0,
    (hs.mul_right _).add (((hs'.mul_left 2).mul_right _).mul_right _), ?_⟩
  intro n t ht
  have hpow : ‖(c n : ℂ) • ((adL (Ω t) ^ n) (A' t))‖ ≤
      c n * w ^ n * max Q 0 :=
    (norm_adL_series_term_le (hc n) (ha t ht) n).trans
      (mul_le_mul_of_nonneg_left ((hQ t ht).trans (le_max_left _ _))
        (mul_nonneg (hc n) (pow_nonneg hw0 n)))
  have hins : ‖(c n : ℂ) •
      ((powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))‖ ≤
      2 * (c n * n * w ^ (n - 1)) * max P 0 * max M 0 := by
    calc
      _ ≤ 2 * c n * n * w ^ (n - 1) * ‖Ω' t‖ * ‖A t‖ :=
        norm_powDeriv_series_term_le hw0 (hc n) (ha t ht) n
      _ ≤ 2 * c n * n * w ^ (n - 1) * max P 0 * max M 0 := by
        have hn : 0 ≤ 2 * c n * (n : ℝ) * w ^ (n - 1) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hc n))
            (Nat.cast_nonneg n)) (pow_nonneg hw0 _)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left ((hP t ht).trans (le_max_left _ _)) hn)
          ((hM t ht).trans (le_max_left _ _)) (norm_nonneg _)
          (mul_nonneg hn (le_max_right _ _))
      _ = _ := by ring
  rw [smul_add]
  exact (norm_add_le _ _).trans (add_le_add hpow hins)

/-- `t ↦ [Ω(t),·]ⁿ` is continuous when `Ω` is. -/
theorem continuousOn_adL_pow {Ω : ℝ → 𝕄} {a b : ℝ} (hΩ : ContinuousOn Ω (Icc a b)) (n : ℕ) :
    ContinuousOn (fun t ↦ adL (Ω t) ^ n) (Icc a b) := by
  letI := ContinuousLinearMap.toNormedRing (𝕜 := ℂ) (E := 𝕄)
  exact (adLCLM.continuous.comp_continuousOn hΩ).pow n

/-- The differentiated series is continuous for `t ∈ [a,b]`. -/
theorem continuousOn_adL_series_deriv [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ} (hw0 : 0 ≤ w)
    (hs : Summable (fun n ↦ c n * w ^ n))
    (hs' : Summable (fun n ↦ c n * n * w ^ (n - 1)))
    {Ω A Ω' A' : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hΩ : ContinuousOn Ω (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (hΩ' : ContinuousOn Ω' (Icc a b)) (hA' : ContinuousOn A' (Icc a b)) :
    ContinuousOn (fun t ↦ ∑' n, (c n : ℂ) •
      (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))) (Icc a b) := by
  obtain ⟨u, hu, hb⟩ := adL_series_deriv_majorant hc hw0 hs hs' ha hA hΩ' hA'
  have hL' : ContinuousOn (fun t ↦ adL (Ω' t)) (Icc a b) :=
    adLCLM.continuous.comp_continuousOn hΩ'
  have hpow := continuousOn_adL_pow hΩ
  apply continuousOn_tsum _ hu hb
  intro n
  have hP : ContinuousOn
      (fun t ↦ powDeriv (adL (Ω t)) (adL (Ω' t)) n) (Icc a b) := by
    unfold powDeriv
    apply continuousOn_finset_sum
    intro j hj
    exact ((hpow (n - 1 - j)).clm_comp hL').clm_comp (hpow j)
  exact ((hpow n).clm_apply hA' |>.add (hP.clm_apply hA)).const_smul _

/-! ## From a countable exceptional set to every point -/

/-- A continuous `f` whose derivative at all but countably many points of `[a,b]` is a continuous
`g` has derivative `g` at every point of `[a,b]`, one-sided at `a` and `b`. -/
theorem hasDerivWithinAt_of_derivativeOffCountable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hd : DerivativeOffCountable f g a b) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  let G : ℝ → E := fun t ↦ g (projIcc a b hab t)
  have hG : Continuous G := hg.restrict.comp continuous_projIcc
  have he (t : ℝ) (ht : t ∈ Icc a b) : G t = g t := by
    simp only [G, projIcc_of_mem hab ht]
  obtain ⟨D, hD, hd⟩ := hd
  have hprim (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ x in a..t, G x) = f t - f a := by
    apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le f G ht.1 hD
    · exact hf.mono (Icc_subset_Icc le_rfl ht.2)
    · intro x hx
      have hx' : x ∈ Icc a b := ⟨hx.1.1.le, hx.1.2.le.trans ht.2⟩
      rw [he x hx']
      exact (hd x hx' hx.2).hasDerivAt
        (Icc_mem_nhds hx.1.1 (hx.1.2.trans_le ht.2))
    · exact hG.intervalIntegrable _ _
  intro t ht
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (hG.intervalIntegrable a t) hG.stronglyMeasurable.stronglyMeasurableAtFilter
    hG.continuousAt).hasDerivWithinAt (s := Icc a b)
  have hp' := hp.add_const (f a)
  rw [he t ht] at hp'
  exact hp'.congr (fun x hx ↦ by rw [hprim x hx]; abel)
    (by rw [hprim t ht]; abel)

/-- The series `∑ cₙ [Ω(t),·]ⁿ A(t)` is continuous for `t ∈ [a,b]`. -/
theorem continuousOn_adL_series [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ}
    (hs : Summable (fun n ↦ c n * w ^ n)) {Ω A : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hΩ : ContinuousOn Ω (Icc a b)) (hA : ContinuousOn A (Icc a b)) :
    ContinuousOn (fun t ↦ ∑' n, (c n : ℂ) • ((adL (Ω t) ^ n) (A t)))
      (Icc a b) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  have hpow := continuousOn_adL_pow hΩ
  apply continuousOn_tsum (fun n ↦ ((hpow n).clm_apply hA).const_smul _)
    (hs.mul_right (max M 0))
  intro n t ht
  have hw0 : 0 ≤ w := (norm_nonneg (adL (Ω t))).trans (ha t ht)
  exact (norm_adL_series_term_le (hc n) (ha t ht) n).trans
    (mul_le_mul_of_nonneg_left ((hM t ht).trans (le_max_left _ _))
      (mul_nonneg (hc n) (pow_nonneg hw0 n)))

/-! ## The series and its derivative -/

/-- Termwise differentiation at every point of `[a,b]`: Mathlib differentiates the series on
the open interval, and continuity of `∑ fₙ` and `∑ gₙ` gives the endpoints. -/
theorem hasDerivWithinAt_tsum_Icc
    {f g : ℕ → ℝ → 𝕄} {u : ℕ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ n, ∀ t ∈ Icc a b, HasDerivWithinAt (f n) (g n t) (Icc a b) t)
    (hs : ∀ t ∈ Icc a b, Summable (fun n ↦ f n t))
    (hu : Summable u) (hb : ∀ n, ∀ t ∈ Icc a b, ‖g n t‖ ≤ u n)
    (hF : ContinuousOn (fun t ↦ ∑' n, f n t) (Icc a b))
    (hG : ContinuousOn (fun t ↦ ∑' n, g n t) (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun t ↦ ∑' n, f n t)
      (∑' n, g n t) (Icc a b) t := by
  refine hasDerivWithinAt_of_derivativeOffCountable hab hF hG
    ⟨{a, b}, (Set.toFinite {a, b}).countable, fun t ht hnot ↦ ?_⟩
  have htI : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht.1 fun h ↦ hnot (by simp [h]), lt_of_le_of_ne ht.2 fun h ↦ hnot (by simp [h])⟩
  exact (hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y hy ↦ (hd n y (Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2))
    (fun n y hy ↦ hb n y (Ioo_subset_Icc_self hy)) htI (hs t ht) htI).hasDerivWithinAt

/-- The first line of (A.2):
`(g([Ω,·])A)' = g([Ω,·])A' + ∑ₙ cₙ ∑_{k<n} [Ω,·]^k [Ω', [Ω,·]^{n-1-k} A]`, for `g(x) = ∑ cₙ xⁿ`
with every `cₙ ≥ 0`. -/
theorem hasDerivWithinAt_adL_series [NeZero d]
    {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {w a b : ℝ} (hw0 : 0 ≤ w) (hab : a ≤ b)
    (hs : Summable (fun n ↦ c n * w ^ n))
    (hs' : Summable (fun n ↦ c n * n * w ^ (n - 1)))
    {Ω A Ω' A' : ℝ → 𝕄}
    (ha : ∀ t ∈ Icc a b, ‖adL (Ω t)‖ ≤ w)
    (hdΩ : ∀ t ∈ Icc a b, HasDerivWithinAt Ω (Ω' t) (Icc a b) t)
    (hdA : ∀ t ∈ Icc a b, HasDerivWithinAt A (A' t) (Icc a b) t)
    (hΩ' : ContinuousOn Ω' (Icc a b)) (hA' : ContinuousOn A' (Icc a b)) :
    ∀ t ∈ Icc a b, HasDerivWithinAt
      (fun t ↦ ∑' n, (c n : ℂ) • ((adL (Ω t) ^ n) (A t)))
      (∑' n, (c n : ℂ) • (((adL (Ω t) ^ n) (A' t)) +
        (powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))) (Icc a b) t := by
  have hΩ : ContinuousOn Ω (Icc a b) := fun t ht ↦ (hdΩ t ht).continuousWithinAt
  have hA : ContinuousOn A (Icc a b) := fun t ht ↦ (hdA t ht).continuousWithinAt
  obtain ⟨u, hu, hb⟩ := adL_series_deriv_majorant hc hw0 hs hs' ha hA hΩ' hA'
  exact hasDerivWithinAt_tsum_Icc hab
    (fun n t ht ↦ hasDerivWithinAt_adL_series_term Ω A (Ω' t) (A' t)
      (Icc a b) t (c n) n (hdΩ t ht) (hdA t ht))
    (fun t ht ↦ (summable_norm_adL_series hc (ha t ht) hs).of_norm) hu hb
    (continuousOn_adL_series hc hs ha hΩ hA)
    (continuousOn_adL_series_deriv hc hw0 hs hs' ha hΩ hA hΩ' hA')

/-- The second line of (A.2):
`‖g([Ω,·])A' + ∑ₙ cₙ ∑_{k<n} [Ω,·]^k [B, [Ω,·]^{n-1-k} A]‖ ≤ g(w) ‖A'‖ + 2g'(w) ‖B‖ ‖A‖`, with
`g(w) = ∑ cₙ wⁿ` and `g'(w) = ∑ n cₙ w^{n-1}`; the paper has `B = Ω'`. -/
theorem norm_adL_series_deriv_le [NeZero d] {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    {Ω B A A' : 𝕄} {w : ℝ} (hw0 : 0 ≤ w) (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * w ^ n))
    (hs' : Summable (fun n ↦ c n * n * w ^ (n - 1))) :
    ‖∑' n, (c n : ℂ) • ((adL Ω ^ n) A' + (powDeriv (adL Ω) (adL B) n) A)‖ ≤
      (∑' n, c n * w ^ n) * ‖A'‖ + 2 * (∑' n, c n * n * w ^ (n - 1)) * ‖B‖ * ‖A‖ := by
  have hsum := (summable_norm_adL_series hc ha hs (E := A')).of_norm
  have hins := (summable_norm_powDeriv_series hc hw0 ha hs' (B := B) (A := A)).of_norm
  simp only [smul_add, hsum.tsum_add hins]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_adL_series_le hc ha hs) (norm_powDeriv_series_le hc hw0 ha hs'))

/-- `𝒩'(w) = ∑ n νₙ w^{n-1}` for `0 ≤ w < 2π`: the `g'(w)` of (A.2) for `g = 𝒩`. -/
theorem deriv_𝒩_eq_tsum {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    deriv 𝒩 w = ∑' n : ℕ, multiplierCoeff n * n * w ^ (n - 1) := by
  obtain ⟨r, hwr, hr⟩ := exists_between hw
  have hr0 : 0 ≤ r := hw0.trans hwr.le
  let f : ℕ → ℝ → ℝ := fun n t ↦ multiplierCoeff n * t ^ n
  let g : ℕ → ℝ → ℝ := fun n t ↦ multiplierCoeff n * n * t ^ (n - 1)
  have hd (n : ℕ) (t : ℝ) : HasDerivAt (f n) (g n t) t := by
    simpa only [f, g, mul_assoc, Pi.pow_apply, id_eq, mul_one] using
      ((hasDerivAt_id t).pow n).const_mul (multiplierCoeff n)
  have hb (n : ℕ) (t : ℝ) (ht : t ∈ Ioo (-r) r) :
      ‖g n t‖ ≤ multiplierCoeff n * n * r ^ (n - 1) := by
    rw [show g n t = (multiplierCoeff n * n) * t ^ (n - 1) from rfl,
      norm_mul, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (multiplierCoeff_nonneg n) (Nat.cast_nonneg n)), norm_pow,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg t) (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) _)
      (mul_nonneg (multiplierCoeff_nonneg n) (Nat.cast_nonneg n))
  have hwI : w ∈ Ioo (-r) r := ⟨by linarith, hwr⟩
  have hreal := hasDerivAt_tsum_of_isPreconnected (summable_multiplierCoeff_deriv hr0 hr)
    isOpen_Ioo (convex_Ioo (-r) r).isPreconnected (fun n t _ ↦ hd n t) hb hwI
    (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0])) hwI
  have heq : 𝒩 =ᶠ[𝓝 w] (fun t ↦ ∑' n, f n t) := by
    filter_upwards [Ioo_mem_nhds hwI.1 hwI.2] with t ht
    exact (multiplierCoeff_series_eq t ((abs_lt.mpr ht).trans hr)).symm
  exact (hreal.congr_of_eventuallyEq heq).deriv

end RoundedClocks
