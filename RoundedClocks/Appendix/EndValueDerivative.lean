/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueCurve
public import RoundedClocks.Citations

/-! # Finite commutator-series derivatives

Equation (A.2) follows first for finite commutator sums by differentiating each insertion of the
Hamiltonian and the matrix family.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

attribute [local instance] endValue_continuousSMul_real

/-- The commutator operator has norm at most twice the norm of its generator. -/
theorem endValue_norm_adL_le (Ω : 𝕄) : ‖adL Ω‖ ≤ 2 * ‖Ω‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro E
  simpa only [zero_smul, sub_zero] using norm_adL_apply_le Ω E 0

/-- The commutator depends continuously and complex-linearly on its generator. -/
def endValue_adLCLM : 𝕄 →L[ℂ] (𝕄 →L[ℂ] 𝕄) := by
  let L : 𝕄 →ₗ[ℂ] (𝕄 →L[ℂ] 𝕄) :=
    { toFun := adL
      map_add' := by
        intro Ω B
        apply ContinuousLinearMap.ext
        intro A
        simp only [adL_apply, ContinuousLinearMap.add_apply, add_mul, mul_add]
        abel
      map_smul' := by
        intro c Ω
        apply ContinuousLinearMap.ext
        intro A
        simp only [adL_apply, ContinuousLinearMap.smul_apply, smul_mul_assoc,
          mul_smul_comm, smul_sub, RingHom.id_apply] }
  have hL : ∀ Ω : 𝕄, ‖L Ω‖ ≤ (2 : ℝ) * ‖Ω‖ := by
    intro Ω
    exact endValue_norm_adL_le Ω
  exact LinearMap.mkContinuous (𝕜 := ℂ) (E := 𝕄) (F := 𝕄 →L[ℂ] 𝕄)
    L (2 : ℝ) hL

/-- Differentiate a finite commutator power with an independent input curve. -/
theorem endValue_hasDerivWithinAt_term (Ω A : ℝ → 𝕄) (Ω' A' : 𝕄)
    (S : Set ℝ) (s c : ℝ) (n : ℕ)
    (hΩ : HasDerivWithinAt Ω Ω' S s) (hA : HasDerivWithinAt A A' S s) :
    HasDerivWithinAt (fun t ↦ (c : ℂ) • ((adL (Ω t) ^ n) (A t)))
      ((c : ℂ) • (((adL (Ω s) ^ n) A') +
        (powDeriv (adL (Ω s)) (adL Ω') n) (A s))) S s := by
  let L : 𝕄 →L[ℝ] (𝕄 →L[ℂ] 𝕄) :=
    (endValue_adLCLM (d := d)).restrictScalars ℝ
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

/-- The finite insertion majorant includes zero width and degree zero. -/
theorem endValue_norm_insertionTerm_le [NeZero d] {Ω B A : 𝕄} {w c : ℝ}
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
        (mul_le_mul_of_nonneg_left (endValue_norm_adL_le B)
          (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hw0 _)))
    _ = _ := by ring

/-- The general commutator series converges absolutely under its scalar majorant. -/
theorem endValue_summable_norm_series [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {Ω A : 𝕄} {w : ℝ} (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * w ^ n)) :
    Summable (fun n ↦ ‖(c n : ℂ) • ((adL Ω ^ n) A)‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (hs.mul_right ‖A‖)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
  have hp : ‖(adL Ω ^ n) A‖ ≤ w ^ n * ‖A‖ :=
    ((adL Ω ^ n).le_opNorm A).trans (mul_le_mul_of_nonneg_right
      ((norm_pow_le _ n).trans (pow_le_pow_left₀ (norm_nonneg _) ha n))
      (norm_nonneg A))
  exact (mul_le_mul_of_nonneg_left hp (hc n)).trans_eq (by ring)

/-- The insertion series converges absolutely under the derivative scalar majorant. -/
theorem endValue_summable_norm_insertion [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {Ω B A : 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * n * w ^ (n - 1))) :
    Summable (fun n ↦ ‖(c n : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖) := by
  have hm := ((hs.mul_left 2).mul_right ‖B‖).mul_right ‖A‖
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hm
  exact (endValue_norm_insertionTerm_le hw0 (hc n) ha n).trans_eq (by ring)

/-- Summing the insertion majorant gives the second term of (series-derivative). -/
theorem endValue_norm_insertionSeries_le [NeZero d] {c : ℕ → ℝ}
    (hc : ∀ n, 0 ≤ c n) {Ω B A : 𝕄} {w : ℝ}
    (hw0 : 0 ≤ w) (ha : ‖adL Ω‖ ≤ w)
    (hs : Summable (fun n ↦ c n * n * w ^ (n - 1))) :
    ‖∑' n, (c n : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖ ≤
      2 * (∑' n, c n * n * w ^ (n - 1)) * ‖B‖ * ‖A‖ := by
  have hi := endValue_summable_norm_insertion hc hw0 ha hs (B := B) (A := A)
  have hm := ((hs.mul_left 2).mul_right ‖B‖).mul_right ‖A‖
  calc
    _ ≤ ∑' n, ‖(c n : ℂ) • ((powDeriv (adL Ω) (adL B) n) A)‖ :=
      norm_tsum_le_tsum_norm hi
    _ ≤ ∑' n, 2 * (c n * n * w ^ (n - 1)) * ‖B‖ * ‖A‖ := by
      apply hi.tsum_le_tsum _ hm
      intro n
      exact (endValue_norm_insertionTerm_le hw0 (hc n) ha n).trans_eq (by ring)
    _ = _ := by rw [tsum_mul_right, tsum_mul_right, tsum_mul_left]

/-- A summable majorant gives the local uniform convergence required by Dieudonné. -/
theorem endValue_locallyUniformlyConvergesOn {f : ℕ → ℝ → 𝕄} {u : ℕ → ℝ}
    {a b : ℝ} (hu : Summable u)
    (hb : ∀ n, ∀ t ∈ Icc a b, ‖f n t‖ ≤ u n) :
    LocallyUniformlyConvergesOn
      (fun N t ↦ ∑ n ∈ Finset.range N, f n t) (fun t ↦ ∑' n, f n t) a b := by
  have h := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_tsum_nat hu hb)
  intro x hx
  refine ⟨1, zero_lt_one, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h ε hε)
  refine ⟨N, fun n hn y hy _ ↦ ?_⟩
  simpa only [dist_comm] using hN n hn y hy

/-- Apply the cited differentiation theorem to partial sums, retaining its exceptional set. -/
theorem endValue_dieudonne_partialSums
    (dieudonne_8_6_4 : Dieudonne_8_6_4)
    {f g : ℕ → ℝ → 𝕄} {u : ℕ → ℝ} {a b t₀ : ℝ}
    (hd : ∀ n, ∀ t ∈ Icc a b, HasDerivWithinAt (f n) (g n t) (Icc a b) t)
    (ht₀ : t₀ ∈ Icc a b) (hs₀ : Summable (fun n ↦ f n t₀))
    (hu : Summable u) (hb : ∀ n, ∀ t ∈ Icc a b, ‖g n t‖ ≤ u n) :
    ∃ fLim, LocallyUniformlyConvergesOn
        (fun N t ↦ ∑ n ∈ Finset.range N, f n t) fLim a b ∧
      DerivativeOffCountable fLim (fun t ↦ ∑' n, g n t) a b := by
  apply dieudonne_8_6_4 d
    (fun N t ↦ ∑ n ∈ Finset.range N, f n t)
    (fun N t ↦ ∑ n ∈ Finset.range N, g n t)
    (fun t ↦ ∑' n, g n t) a b t₀
  · intro N
    have hN (t : ℝ) (ht : t ∈ Icc a b) :
        HasDerivWithinAt (fun t ↦ ∑ n ∈ Finset.range N, f n t)
          (∑ n ∈ Finset.range N, g n t) (Icc a b) t := by
      simpa only [Finset.sum_apply, ← Finset.sum_fn] using
        HasDerivWithinAt.sum (fun n (_ : n ∈ Finset.range N) ↦ hd n t ht)
    exact ⟨fun t ht ↦ (hN t ht).continuousWithinAt,
      ⟨∅, Set.countable_empty, fun t ht _ ↦ hN t ht⟩⟩
  · exact ht₀
  · exact ⟨∑' n, f n t₀, hs₀.hasSum.tendsto_sum_nat⟩
  · exact endValue_locallyUniformlyConvergesOn hu hb

/-- A locally uniform partial-sum limit equals the series at every interval point. -/
theorem endValue_partialSum_limit_eq {f : ℕ → ℝ → 𝕄} {F : ℝ → 𝕄}
    {a b t : ℝ}
    (hF : LocallyUniformlyConvergesOn
      (fun N t ↦ ∑ n ∈ Finset.range N, f n t) F a b)
    (ht : t ∈ Icc a b) (hs : Summable (fun n ↦ f n t)) :
    F t = ∑' n, f n t := by
  obtain ⟨δ, hδ, hδF⟩ := hF t ht
  have hlim : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, f n t) atTop (𝓝 (F t)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hδF ε hε
    exact ⟨N, fun n hn ↦ hN n hn t ht (by simpa using hδ)⟩
  exact tendsto_nhds_unique hlim hs.hasSum.tendsto_sum_nat

/-- The partial-sum limit equals the series on the same exceptional set. -/
theorem endValue_dieudonne_series
    (dieudonne_8_6_4 : Dieudonne_8_6_4)
    {f g : ℕ → ℝ → 𝕄} {u : ℕ → ℝ} {a b t₀ : ℝ}
    (hd : ∀ n, ∀ t ∈ Icc a b, HasDerivWithinAt (f n) (g n t) (Icc a b) t)
    (ht₀ : t₀ ∈ Icc a b)
    (hs : ∀ t ∈ Icc a b, Summable (fun n ↦ f n t))
    (hu : Summable u) (hb : ∀ n, ∀ t ∈ Icc a b, ‖g n t‖ ≤ u n) :
    DerivativeOffCountable (fun t ↦ ∑' n, f n t) (fun t ↦ ∑' n, g n t) a b := by
  obtain ⟨F, hF, D, hD, hdF⟩ :=
    endValue_dieudonne_partialSums dieudonne_8_6_4 hd ht₀ (hs t₀ ht₀) hu hb
  have heq : EqOn (fun t ↦ ∑' n, f n t) F (Icc a b) := by
    intro t ht
    exact (endValue_partialSum_limit_eq hF ht (hs t ht)).symm
  refine ⟨D, hD, fun t ht hnot ↦ ?_⟩
  exact (hdF t ht hnot).congr heq (heq ht)

/-- Compact curve bounds give a summable majorant for the differentiated series. -/
theorem endValue_curve_derivative_majorant [NeZero d] {c : ℕ → ℝ}
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
      c n * w ^ n * max Q 0 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
    calc
      _ ≤ c n * (‖adL (Ω t) ^ n‖ * ‖A' t‖) :=
        mul_le_mul_of_nonneg_left ((adL (Ω t) ^ n).le_opNorm _) (hc n)
      _ ≤ c n * (w ^ n * max Q 0) := by
        apply mul_le_mul_of_nonneg_left _ (hc n)
        have hp : ‖adL (Ω t) ^ n‖ ≤ w ^ n :=
          (norm_pow_le (adL (Ω t)) n).trans
            (pow_le_pow_left₀ (norm_nonneg (adL (Ω t))) (ha t ht) n)
        exact mul_le_mul hp
          ((hQ t ht).trans (le_max_left _ _)) (norm_nonneg _) (pow_nonneg hw0 n)
      _ = _ := by ring
  have hins : ‖(c n : ℂ) •
      ((powDeriv (adL (Ω t)) (adL (Ω' t)) n) (A t))‖ ≤
      2 * (c n * n * w ^ (n - 1)) * max P 0 * max M 0 := by
    calc
      _ ≤ 2 * c n * n * w ^ (n - 1) * ‖Ω' t‖ * ‖A t‖ :=
        endValue_norm_insertionTerm_le hw0 (hc n) (ha t ht) n
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

/-- The compact majorant makes the differentiated series continuous, including endpoints. -/
theorem endValue_continuousOn_derivativeSeries [NeZero d] {c : ℕ → ℝ}
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
  obtain ⟨u, hu, hb⟩ := endValue_curve_derivative_majorant hc hw0 hs hs' ha hA hΩ' hA'
  have hL : ContinuousOn (fun t ↦ adL (Ω t)) (Icc a b) :=
    endValue_adLCLM.continuous.comp_continuousOn hΩ
  have hL' : ContinuousOn (fun t ↦ adL (Ω' t)) (Icc a b) :=
    endValue_adLCLM.continuous.comp_continuousOn hΩ'
  have hpow (n : ℕ) : ContinuousOn (fun t ↦ adL (Ω t) ^ n) (Icc a b) := by
    induction n with
    | zero => simpa only [pow_zero] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (1 : 𝕄 →L[ℂ] 𝕄)) (Icc a b))
    | succ n ih => simpa only [pow_succ] using ih.clm_comp hL
  apply continuousOn_tsum _ hu hb
  intro n
  have hP : ContinuousOn
      (fun t ↦ powDeriv (adL (Ω t)) (adL (Ω' t)) n) (Icc a b) := by
    unfold powDeriv
    apply continuousOn_finset_sum
    intro j hj
    exact ((hpow (n - 1 - j)).clm_comp hL').clm_comp (hpow j)
  exact ((hpow n).clm_apply hA' |>.add (hP.clm_apply hA)).const_smul _

end RoundedClocks
