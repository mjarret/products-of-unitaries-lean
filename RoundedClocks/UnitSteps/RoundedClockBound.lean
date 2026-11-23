/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Appendix
public import RoundedClocks.Appendix.MatrixSeries
public import RoundedClocks.Appendix.MultiplierMonotonicity

/-! # The jumps of Theorem 4.4

The proof of Theorem 4.4 bounds each jump `Δ_j` of Theorem 4.2 by interpolating `H` linearly
between the samples `H(l)` and `H(r)`, `l = (j-1)/T`, `r = j/T`. This file proves the steps of
that display: the width of the interpolation, the Taylor bounds `‖H'(r) - TΩ'‖ ≤ L/(2T)`, the
series bound (A.1), Lemma A.3(i) with `Ω'' = 0`, and the sum over `1 ≤ j ≤ T`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Real
open Set

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ### Width of the linear interpolation -/

/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_real_smul {X : 𝕄} (hX : IsHermitian X) (u : ℝ) : IsHermitian (u • X) := by
  change Matrix.conjTranspose (u • X) = u • X
  rw [Matrix.conjTranspose_smul, star_trivial, hX.eq]

/-- Proof of Theorem 4.4: every `A + u (B - A)` with `u ∈ [0,1]` between Hermitian matrices of
width at most `w` has width at most `w`: every eigenvalue lies between the extreme Rayleigh
quotients, whose supremum is convex in the matrix and whose infimum is concave. -/
theorem hasEigenvalueDifferences_segment [NeZero d] {A B : 𝕄} (hA : IsHermitian A)
    (hB : IsHermitian B) {w u : ℝ} (hw0 : 0 ≤ w) (hAw : HasEigenvalueDifferences A w)
    (hBw : HasEigenvalueDifferences B w) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasEigenvalueDifferences (A + u • (B - A)) w := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let E := EuclideanSpace ℂ (Fin d)
  let S := Metric.sphere (0 : E) 1
  let upper := fun X : 𝕄 ↦ ⨆ v : S, (T X).rayleighQuotient v
  let lower := fun X : 𝕄 ↦ ⨅ v : S, (T X).rayleighQuotient v
  let v₀ : S := ⟨hA.eigenvectorBasis 0, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact hA.eigenvectorBasis.orthonormal.norm_eq_one 0⟩
  letI : Nonempty S := ⟨v₀⟩
  have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
  have hBddAbove (X : 𝕄) : BddAbove (range fun v : S ↦ (T X).rayleighQuotient v) := by
    refine ⟨‖T X‖, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact (le_abs_self _).trans ((T X).rayleighQuotient_le_norm v)
  have hBddBelow (X : 𝕄) : BddBelow (range fun v : S ↦ (T X).rayleighQuotient v) := by
    refine ⟨-‖T X‖, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact (abs_le.mp ((T X).rayleighQuotient_le_norm v)).1
  -- Extreme Rayleigh quotients are eigenvalues and enclose every eigenvalue.
  have henclose (X : 𝕄) (hX : IsHermitian X) {x : ℝ} (hx : x ∈ spectrum ℝ X) :
      lower X ≤ x ∧ x ≤ upper X := by
    rw [hX.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have hvnorm : ‖hX.eigenvectorBasis i‖ = 1 :=
      hX.eigenvectorBasis.orthonormal.norm_eq_one i
    have hvsphere : hX.eigenvectorBasis i ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hvnorm
    let v : S := ⟨hX.eigenvectorBasis i, hvsphere⟩
    have hq : (T X).rayleighQuotient v = hX.eigenvalues i := by
      rw [ContinuousLinearMap.rayleighQuotient.eq_1]
      have hvnorm' : ‖(v : E)‖ ^ 2 = 1 := by
        rw [show ‖(v : E)‖ = 1 by exact hvnorm]
        norm_num
      rw [hvnorm', div_one]
      have heigen : T X (hX.eigenvectorBasis i) =
          (hX.eigenvalues i : ℂ) • hX.eigenvectorBasis i := by
        change WithLp.toLp 2 (X.mulVec (hX.eigenvectorBasis i).ofLp) =
          WithLp.toLp 2 ((hX.eigenvalues i : ℂ) • (hX.eigenvectorBasis i).ofLp)
        rw [hX.mulVec_eigenvectorBasis, Complex.coe_smul]
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [show T X (v : E) = (hX.eigenvalues i : ℂ) • (v : E) by exact heigen,
        inner_smul_left]
      simp [show ‖(v : E)‖ = 1 by exact hvnorm]
    exact ⟨(ciInf_le (hBddBelow X) v).trans_eq hq,
      hq.symm.trans_le (le_ciSup (hBddAbove X) v)⟩
  have hextreme (X : 𝕄) (hX : IsHermitian X) :
      upper X ∈ spectrum ℝ X ∧ lower X ∈ spectrum ℝ X := by
    have hsym : (T X).toLinearMap.IsSymmetric := by
      simpa only [T, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        Matrix.isHermitian_iff_isSymmetric.mp hX
    have hmaxeig : Module.End.HasEigenvalue (T X).toLinearMap (upper X : ℂ) := by
      have h := hsym.hasEigenvalue_iSup_of_finiteDimensional
      have h' : Module.End.HasEigenvalue (T X).toLinearMap
          (((⨆ x : {x : E // x ≠ 0}, (T X).rayleighQuotient x) : ℝ) : ℂ) := by
        simpa only [ContinuousLinearMap.rayleighQuotient.eq_1,
          ContinuousLinearMap.coe_coe] using h
      rw [(T X).iSup_rayleigh_eq_iSup_rayleigh_sphere (r := 1) zero_lt_one] at h'
      simpa only [upper, S] using h'
    have hmineig : Module.End.HasEigenvalue (T X).toLinearMap (lower X : ℂ) := by
      have h := hsym.hasEigenvalue_iInf_of_finiteDimensional
      have h' : Module.End.HasEigenvalue (T X).toLinearMap
          (((⨅ x : {x : E // x ≠ 0}, (T X).rayleighQuotient x) : ℝ) : ℂ) := by
        simpa only [ContinuousLinearMap.rayleighQuotient.eq_1,
          ContinuousLinearMap.coe_coe] using h
      rw [(T X).iInf_rayleigh_eq_iInf_rayleigh_sphere (r := 1) zero_lt_one] at h'
      simpa only [lower, S] using h'
    constructor
    · have hm := hmaxeig.mem_spectrum
      change (upper X : ℂ) ∈ spectrum ℂ (Matrix.toEuclideanLin X) at hm
      rw [show Matrix.toEuclideanLin X = (Matrix.toLpLin 2 2) X by rfl,
        Matrix.spectrum_toLpLin, hX.spectrum_eq_image_range] at hm
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hm
      rw [Complex.ofReal_injective hi.symm]
      exact hX.eigenvalues_mem_spectrum_real i
    · have hm := hmineig.mem_spectrum
      change (lower X : ℂ) ∈ spectrum ℂ (Matrix.toEuclideanLin X) at hm
      rw [show Matrix.toEuclideanLin X = (Matrix.toLpLin 2 2) X by rfl,
        Matrix.spectrum_toLpLin, hX.spectrum_eq_image_range] at hm
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hm
      rw [Complex.ofReal_injective hi.symm]
      exact hX.eigenvalues_mem_spectrum_real i
  -- The largest Rayleigh quotient is convex and the least is concave.
  have hconvex : upper ((1 - u) • A + u • B) ≤ (1 - u) * upper A + u * upper B ∧
      (1 - u) * lower A + u * lower B ≤ lower ((1 - u) • A + u • B) := by
    have hq (v : S) : (T ((1 - u) • A + u • B)).rayleighQuotient v =
        (1 - u) * (T A).rayleighQuotient v + u * (T B).rayleighQuotient v := by
      have hvnorm : ‖(v : E)‖ = 1 := by
        have hv := v.property
        rw [Metric.mem_sphere, dist_zero_right] at hv
        exact hv
      simp only [ContinuousLinearMap.rayleighQuotient.eq_1,
        show ‖(v : E)‖ ^ 2 = 1 by rw [hvnorm]; norm_num, div_one]
      change RCLike.re (inner ℂ (T ((1 - u) • A + u • B) v) v) = _
      rw [show T ((1 - u) • A + u • B) v =
        (((1 - u : ℝ) : ℂ)) • T A v + ((u : ℝ) : ℂ) • T B v by
          change T (((1 - u : ℝ) : ℂ) • A + (u : ℂ) • B) v = _
          rw [map_add, map_smul, map_smul]
          rfl]
      unfold ContinuousLinearMap.reApplyInnerSelf
      simp [map_add]
      ring
    constructor
    · refine ciSup_le fun v ↦ ?_
      rw [hq]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_ciSup (hBddAbove A) v) hu1)
        (mul_le_mul_of_nonneg_left (le_ciSup (hBddAbove B) v) hu.1)
    · refine le_ciInf fun v ↦ ?_
      rw [hq]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (ciInf_le (hBddBelow A) v) hu1)
        (mul_le_mul_of_nonneg_left (ciInf_le (hBddBelow B) v) hu.1)
  -- The endpoint widths bound the width of the convex combination.
  have hpath : A + u • (B - A) = (1 - u) • A + u • B := by module
  have hpathH : IsHermitian ((1 - u) • A + u • B) :=
    (isHermitian_real_smul hA (1 - u)).add (isHermitian_real_smul hB u)
  have hExtA := hextreme A hA
  have hExtB := hextreme B hB
  have hwidthA : upper A - lower A ≤ w :=
    (le_abs_self _).trans (hAw (upper A) hExtA.1 (lower A) hExtA.2)
  have hwidthB : upper B - lower B ≤ w :=
    (le_abs_self _).trans (hBw (upper B) hExtB.1 (lower B) hExtB.2)
  rw [hpath]
  intro x hx y hy
  have hx' := henclose _ hpathH hx
  have hy' := henclose _ hpathH hy
  calc
    |x - y| ≤ upper ((1 - u) • A + u • B) - lower ((1 - u) • A + u • B) := by
      rw [abs_le]
      constructor <;> linarith
    _ ≤ (1 - u) * (upper A - lower A) + u * (upper B - lower B) := by
      linarith [hconvex.1, hconvex.2]
    _ ≤ (1 - u) * w + u * w :=
      add_le_add (mul_le_mul_of_nonneg_left hwidthA hu1)
        (mul_le_mul_of_nonneg_left hwidthB hu.1)
    _ = w := by
      have : 0 ≤ (1 - u) * w + u * w :=
        add_nonneg (mul_nonneg hu1 hw0) (mul_nonneg hu.1 hw0)
      ring

/-! ### Taylor bounds from the Lipschitz derivative -/

/-- The right derivative of `σ ↦ H(σ) - H(a) - (σ - a) V` at `σ ∈ [0,1)` is `H'(σ) - V`. -/
theorem hasDerivWithinAt_taylor {H : ℝ → 𝕄} (hH : DifferentiableOn ℝ H (Icc 0 1))
    {a σ : ℝ} (V : 𝕄) (hσ : σ ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (fun s ↦ H s - H a - (s - a) • V) (∂H σ - V) (Ici σ) σ := by
  have hd : HasDerivWithinAt H (∂H σ) (Ici σ) σ :=
    (hH σ (Ico_subset_Icc_self hσ)).hasDerivWithinAt.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hσ)
  have hl : HasDerivWithinAt (fun s : ℝ ↦ (s - a) • V) ((1 : ℝ) • V) (Ici σ) σ :=
    ((hasDerivWithinAt_id σ (Ici σ)).sub_const a).smul_const V
  simpa only [one_smul] using (hd.sub_const (H a)).sub hl

/-- Continuity of `σ ↦ H(σ) - H(a) - (σ - a) V` on `[a,b] ⊆ [0,1]`. -/
theorem continuousOn_taylor {H : ℝ → 𝕄} (hH : DifferentiableOn ℝ H (Icc 0 1)) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (V : 𝕄) :
    ContinuousOn (fun s ↦ H s - H a - (s - a) • V) (Icc a b) :=
  ((hH.continuousOn.mono (Icc_subset_Icc ha hb)).sub continuousOn_const).sub
    ((continuousOn_id.sub continuousOn_const).smul continuousOn_const)

/-- Proof of Theorem 4.4: `‖H(b) - H(a) - (b - a) H'(a)‖ ≤ L (b - a)²/2` for `0 ≤ a ≤ b ≤ 1`. -/
theorem norm_taylor_left_le {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖H b - H a - (b - a) • ∂H a‖ ≤ L * (b - a) ^ 2 / 2 := by
  have hB (σ : ℝ) : HasDerivAt (fun s ↦ L * (s - a) ^ 2 / 2) (L * (σ - a)) σ := by
    have h := ((hasDerivAt_id' σ).sub_const a).mul ((hasDerivAt_id' σ).sub_const a)
    convert (h.const_mul L).div_const 2 using 1
    · funext s
      dsimp
      ring
    · dsimp
      ring
  have hbound : ∀ σ ∈ Ico a b, ‖∂H σ - ∂H a‖ ≤ L * (σ - a) := by
    intro σ hσ
    have h := hL.2 σ ⟨ha.trans hσ.1, hσ.2.le.trans hb⟩ a ⟨ha, hab.trans hb⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hσ.1)] at h
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary (continuousOn_taylor hL.1 ha hb _)
    (fun σ hσ ↦ hasDerivWithinAt_taylor hL.1 (∂H a) ⟨ha.trans hσ.1, hσ.2.trans_le hb⟩)
    (by simp) hB hbound (right_mem_Icc.2 hab)

/-- Proof of Theorem 4.4: `‖H(b) - H(a) - (b - a) H'(b)‖ ≤ L (b - a)²/2` for `0 ≤ a ≤ b ≤ 1`. -/
theorem norm_taylor_right_le {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖H b - H a - (b - a) • ∂H b‖ ≤ L * (b - a) ^ 2 / 2 := by
  have hB (σ : ℝ) : HasDerivAt (fun s ↦ L * ((b - a) ^ 2 - (b - s) ^ 2) / 2) (L * (b - σ)) σ := by
    have h := ((hasDerivAt_const σ b).sub (hasDerivAt_id' σ)).mul
      ((hasDerivAt_const σ b).sub (hasDerivAt_id' σ))
    convert (((hasDerivAt_const σ ((b - a) ^ 2)).sub h).const_mul L).div_const 2 using 1
    · funext s
      dsimp
      ring
    · dsimp
      ring
  have hbound : ∀ σ ∈ Ico a b, ‖∂H σ - ∂H b‖ ≤ L * (b - σ) := by
    intro σ hσ
    have h := hL.2 σ ⟨ha.trans hσ.1, hσ.2.le.trans hb⟩ b ⟨ha.trans hab, hb⟩
    rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hσ.2.le)] at h
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary (continuousOn_taylor hL.1 ha hb _)
    (fun σ hσ ↦ hasDerivWithinAt_taylor hL.1 (∂H b) ⟨ha.trans hσ.1, hσ.2.trans_le hb⟩)
    (by simp) hB hbound (right_mem_Icc.2 hab)
  exact h.trans_eq (by ring)

/-- `‖H'(s)‖ ≤ ‖H'‖∞` for `s ∈ [0,1]`; the supremum is finite as `H'` is Lipschitz. -/
theorem norm_deriv_le_supNorm {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖∂H s‖ ≤ ‖∂H‖∞ := by
  refine le_csSup ⟨‖∂H 0‖ + |L|, ?_⟩ (mem_image_of_mem (fun t ↦ ‖∂H t‖) hs)
  rintro y ⟨t, ht, rfl⟩
  have h := hL.2 t ht 0 (left_mem_Icc.2 zero_le_one)
  have h1 : L * |t - 0| ≤ |L| := by
    rw [sub_zero, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right (le_abs_self L) ht.1).trans
      (mul_le_of_le_one_right (abs_nonneg L) ht.2)
  have h2 := norm_sub_norm_le (∂H t) (∂H 0)
  dsimp only
  linarith

/-- The mean value bound `‖H(b) - H(a)‖ ≤ ‖H'‖∞ |b - a|` on `[0,1]`. -/
theorem norm_sub_le_supNorm_mul {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖H b - H a‖ ≤ ‖∂H‖∞ * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_derivWithin_le hL.1 (fun _ hx ↦ norm_deriv_le_supNorm hL hx)
    (convex_Icc 0 1) ha hb

/-- `E ↦ 𝒩([Ω,·])E` preserves differences. -/
theorem 𝒩ad_sub (Ω E F : 𝕄) : 𝒩ad Ω (E - F) = 𝒩ad Ω E - 𝒩ad Ω F := by
  unfold 𝒩ad
  split_ifs with hΩ hgap
  · dsimp only
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext p q
    simp [Matrix.sub_mul, mul_sub]
  · simp
  · simp

/-- `E ↦ 𝒩([Ω,·])E` commutes with real multiples. -/
theorem 𝒩ad_smul (Ω E : 𝕄) (c : ℝ) : 𝒩ad Ω (c • E) = c • 𝒩ad Ω E := by
  unfold 𝒩ad
  split_ifs with hΩ hgap
  · dsimp only
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext p q
    simp [Complex.real_smul, mul_left_comm]
  · simp
  · simp

/-- Equation (A.1): under the width hypothesis, `‖𝒩([Ω,·])E‖ ≤ 𝒩(w) ‖E‖`. -/
theorem norm_𝒩ad_le [NeZero d] {Ω : 𝕄} (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) (hwidth : HasEigenvalueDifferences Ω w) (E : 𝕄) :
    ‖𝒩ad Ω E‖ ≤ 𝒩 w * ‖E‖ := by
  rw [← multiplierSeriesOp_eq_𝒩ad hΩ hw0 hw hwidth]
  exact norm_multiplierSeriesOp_le hΩ hw0 hw hwidth

/-! ### The jumps -/

/-- Integrating a continuous derivative gives the endpoint difference, bounded by the
integral of its norm and then by a constant over the unit interval. -/
theorem norm_sub_le_integrated_deriv {F : ℝ → 𝕄} {C : ℝ}
    (hF : DifferentiableOn ℝ F (Icc 0 1))
    (hF' : ContinuousOn (∂F) (Icc 0 1))
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖∂F u‖ ≤ C) : ‖F 1 - F 0‖ ≤ C := by
  have hint := hF'.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hFTC : (∫ u in (0 : ℝ)..1, ∂F u) = F 1 - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one
      hF.continuousOn _ hint
    intro u hu
    exact ((hF u (Ioo_subset_Icc_self hu)).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).hasDerivWithinAt
  calc
    ‖F 1 - F 0‖ = ‖∫ u in (0 : ℝ)..1, ∂F u‖ := by rw [hFTC]
    _ ≤ ∫ u in (0 : ℝ)..1, ‖∂F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _u in (0 : ℝ)..1, C :=
      intervalIntegral.integral_mono_on zero_le_one hint.norm
        intervalIntegrable_const hbound
    _ = C := by simp

/-- Proof of Theorem 4.4, Lemma A.3(i) along `Ω(u) = H(l) + u (H(r) - H(l))`, where `Ω'' = 0`:
`‖𝒩([H(r),·])Ω' - 𝒩([H(l),·])Ω'‖ ≤ 2𝒩'(w) ‖Ω'‖²`. -/
theorem norm_𝒩ad_segment_le (dieudonne_8_6_4 : Dieudonne_8_6_4)
    [NeZero d] {A B : 𝕄} (hA : IsHermitian A) (hB : IsHermitian B) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) (hAw : HasEigenvalueDifferences A w) (hBw : HasEigenvalueDifferences B w) :
    ‖𝒩ad B (B - A) - 𝒩ad A (B - A)‖ ≤ 2 * deriv 𝒩 w * ‖B - A‖ ^ 2 := by
  set Ω : ℝ → 𝕄 := fun u ↦ A + u • (B - A) with hΩdef
  have hΩH : IsTimeDepHamiltonian Ω := fun u _ ↦ hA.add (isHermitian_real_smul (hB.sub hA) u)
  have hΩw : ∀ u ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω u) w :=
    fun u hu ↦ hasEigenvalueDifferences_segment hA hB hw0 hAw hBw hu
  have hΩC2 : IsC2Family Ω := (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
  have hΩd (u : ℝ) : HasDerivAt Ω (B - A) u := by
    simpa only [Ω, one_smul] using
      ((hasDerivAt_id u).smul_const (B - A)).const_add A
  have hΩ' : ∀ u ∈ Icc (0 : ℝ) 1, ∂Ω u = B - A := fun u hu ↦
    (hΩd u).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one u hu)
  have hΩ'' : ∀ u ∈ Icc (0 : ℝ) 1, ∂∂Ω u = 0 := by
    intro u hu
    change derivWithin (∂Ω) (Icc 0 1) u = 0
    rw [derivWithin_congr (f := fun _ ↦ B - A) (fun x hx ↦ hΩ' x hx) (hΩ' u hu)]
    simp
  obtain ⟨hC1, hbd⟩ := end_value dieudonne_8_6_4 hw0 hw hΩH hΩw hΩC2
  have hf : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖∂(fun t ↦ 𝒩ad (Ω t) (∂Ω t)) u‖ ≤ 2 * deriv 𝒩 w * ‖B - A‖ ^ 2 := by
    intro u hu
    have h := (hbd u hu).1
    rwa [hΩ'' u hu, hΩ' u hu, norm_zero, mul_zero, zero_add] at h
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  have hend := norm_sub_le_integrated_deriv
    (hC1.differentiableOn (by norm_num))
    (hC1.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)) hf
  have hΩ0 : Ω 0 = A := by simp [hΩdef]
  have hΩ1 : Ω 1 = B := by simp [hΩdef]
  simp only [hΩ0, hΩ1, hΩ' 0 h0, hΩ' 1 h1] at hend
  exact hend

/-- Proof of Theorem 4.4, first five lines of the display: for `1 ≤ j ≤ T`,
`‖Δ_j‖ ≤ (𝒩(w) L + 2𝒩'(w) ‖H'‖∞²)/T²`. -/
theorem norm_Δ_le (dieudonne_8_6_4 : Dieudonne_8_6_4) [NeZero d]
    {T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖Δ H T j‖ ≤ (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T ^ 2 := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjT' : (j : ℝ) ≤ T := by exact_mod_cast hjT
  unfold Δ
  set l : ℝ := ((j : ℝ) - 1) / T with hl_def
  set r : ℝ := (j : ℝ) / T with hr_def
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hT.le
  have hr1 : r ≤ 1 := (div_le_one hT).2 hjT'
  have hrl : r - l = 1 / T := by
    rw [hl_def, hr_def]
    field_simp
    ring
  have hlr : l ≤ r := by
    have : (0 : ℝ) < 1 / T := by positivity
    linarith
  have hlI : l ∈ Icc (0 : ℝ) 1 := ⟨hl0, hlr.trans hr1⟩
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hl0.trans hlr, hr1⟩
  have hHl := hH l hlI
  have hHr := hH r hrI
  have hwr : HasEigenvalueDifferences (H r) w := hwidth j hjT
  have hwl : HasEigenvalueDifferences (H l) w := by
    have h := hwidth (j - 1) (by omega)
    rwa [Nat.cast_sub hj, Nat.cast_one] at h
  have hN0 := 𝒩_nonneg_of_width hw0 hw
  have hN'0 := deriv_𝒩_nonneg hw0 hw
  -- `‖H'(r) - T Ω'‖ ≤ L/(2T)` and `‖T Ω' - H'(l)‖ ≤ L/(2T)`, with `Ω' = H(r) - H(l)`.
  have hscale {X : 𝕄} (hX : ‖X‖ ≤ L * (r - l) ^ 2 / 2) : ‖(T : ℝ) • X‖ ≤ L / (2 * T) := by
    rw [norm_smul, Real.norm_of_nonneg hT.le]
    calc
      _ ≤ (T : ℝ) * (L * (r - l) ^ 2 / 2) := mul_le_mul_of_nonneg_left hX hT.le
      _ = L / (2 * T) := by
        rw [hrl]
        field_simp
  have hTr : ‖∂H r - (T : ℝ) • (H r - H l)‖ ≤ L / (2 * T) := by
    have he : ∂H r - (T : ℝ) • (H r - H l) =
        -((T : ℝ) • (H r - H l - (r - l) • ∂H r)) := by
      rw [hrl, smul_sub (T : ℝ) (H r - H l), smul_smul,
        mul_one_div_cancel hT.ne', one_smul]
      abel
    rw [he, norm_neg]
    exact hscale (norm_taylor_right_le hL hl0 hlr hr1)
  have hTl : ‖(T : ℝ) • (H r - H l) - ∂H l‖ ≤ L / (2 * T) := by
    have he : (T : ℝ) • (H r - H l) - ∂H l =
        (T : ℝ) • (H r - H l - (r - l) • ∂H l) := by
      rw [hrl, smul_sub (T : ℝ) (H r - H l), smul_smul, mul_one_div_cancel hT.ne', one_smul]
    rw [he]
    exact hscale (norm_taylor_left_le hL hl0 hlr hr1)
  -- `‖Ω'‖ ≤ ‖H'‖∞/T`.
  have hD : ‖H r - H l‖ ≤ ‖∂H‖∞ / T := by
    have h := norm_sub_le_supNorm_mul hL hlI hrI
    rwa [hrl, Real.norm_of_nonneg (by positivity), mul_one_div] at h
  have hjump := norm_𝒩ad_segment_le dieudonne_8_6_4 hHl hHr hw0 hw hwl hwr
  -- Add and subtract `𝒩([H(r),·]) T Ω'` and `𝒩([H(l),·]) T Ω'`.
  have hsplit : 𝒩ad (H r) (∂H r) - 𝒩ad (H l) (∂H l) =
      𝒩ad (H r) (∂H r - (T : ℝ) • (H r - H l)) + 𝒩ad (H l) ((T : ℝ) • (H r - H l) - ∂H l) +
        (T : ℝ) • (𝒩ad (H r) (H r - H l) - 𝒩ad (H l) (H r - H l)) := by
    rw [𝒩ad_sub, 𝒩ad_sub, 𝒩ad_smul, 𝒩ad_smul, smul_sub]
    abel
  have h1 : ‖𝒩ad (H r) (∂H r - (T : ℝ) • (H r - H l))‖ ≤ 𝒩 w * (L / (2 * T)) :=
    (norm_𝒩ad_le hHr hw0 hw hwr _).trans (mul_le_mul_of_nonneg_left hTr hN0)
  have h2 : ‖𝒩ad (H l) ((T : ℝ) • (H r - H l) - ∂H l)‖ ≤ 𝒩 w * (L / (2 * T)) :=
    (norm_𝒩ad_le hHl hw0 hw hwl _).trans (mul_le_mul_of_nonneg_left hTl hN0)
  have h3 : ‖(T : ℝ) • (𝒩ad (H r) (H r - H l) - 𝒩ad (H l) (H r - H l))‖ ≤
      T * (2 * deriv 𝒩 w * (‖∂H‖∞ / T) ^ 2) := by
    rw [norm_smul, Real.norm_of_nonneg hT.le]
    refine mul_le_mul_of_nonneg_left (hjump.trans ?_) hT.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hD 2) (by linarith)
  rw [norm_smul, Real.norm_of_nonneg (by positivity), hsplit]
  calc
    _ ≤ 1 / T * (𝒩 w * (L / (2 * T)) + 𝒩 w * (L / (2 * T)) +
          T * (2 * deriv 𝒩 w * (‖∂H‖∞ / T) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3))
        (by positivity)
    _ = (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T ^ 2 := by
      field_simp
      ring

/-- Proof of Theorem 4.4, summing the jump bound over `1 ≤ j ≤ T`:
`∑_{j=1}^T ‖Δ_j‖ ≤ (𝒩(w) L + 2𝒩'(w) ‖H'‖∞²)/T`. -/
theorem sum_norm_Δ_le (dieudonne_8_6_4 : Dieudonne_8_6_4)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤ (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 T, (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T ^ 2 :=
      Finset.sum_le_sum fun j hj ↦ norm_Δ_le dieudonne_8_6_4
        (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hH hL hw0 hw hwidth
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp

/-- The width is nonnegative: `H(0)` has an eigenvalue, whose difference with itself is `0`. -/
theorem width_nonneg [NeZero d] {T : ℕ} {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ}
    (hwidth : HasSampleWidth H T w) : 0 ≤ w := by
  have h0 := hwidth 0 (Nat.zero_le T)
  have hH0 : IsHermitian (H (((0 : ℕ) : ℝ) / T)) := hH _ ⟨by simp, by simp⟩
  have hx := hH0.eigenvalues_mem_spectrum_real 0
  simpa using h0 _ hx _ hx

end RoundedClocks
