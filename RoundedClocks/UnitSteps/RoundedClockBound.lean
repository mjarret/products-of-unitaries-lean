/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.RoundedClockComparison
public import RoundedClocks.Appendix
public import RoundedClocks.Appendix.MatrixSeries
public import RoundedClocks.Appendix.MultiplierMonotonicity

/-! # The jumps of Theorem 4.4

The proof of Theorem 4.4 (`rounded_clock_bound`) bounds each jump `Δ_j` of Theorem 4.2 by
interpolating `H` linearly between the samples `H(l)` and `H(r)`, `l = (j-1)/T`, `r = j/T`. This
file proves the steps of its display, in the paper's order:

* every `Ω(u) = (1-u) H(l) + u H(r)` has eigenvalue differences of modulus at most `w`
  (`hasEigenvalueDifferences_segment`);
* the series bound (A.1) for `𝒩([Ω,·])` (`norm_𝒩ad_le`);
* the change of `𝒩([Ω(u),·])Ω'` from `u = 0` to `u = 1` is at most the integral of the norm of
  its derivative, which Lemma A.3(i) bounds with `Ω'' = 0` (`norm_𝒩ad_segment_le`);
* the bounds `‖H'(r) - TΩ'‖ ≤ L/(2T)` and `‖TΩ' - H'(l)‖ ≤ L/(2T)` (`norm_taylor_right_le`,
  `norm_taylor_left_le`);
* the first five lines of the display (`norm_Δ_le`) and their sum over `1 ≤ j ≤ T`
  (`sum_norm_Δ_le`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Real MatrixOrder
open Set

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ### Width of the linear interpolation -/

/-- Proof of Theorem 4.4: "Every `Ω(u)` has eigenvalue differences of modulus at most `w`, as the
largest eigenvalue is convex in the matrix and the least concave." Here `Ω(u) = A + u (B - A)` for
`u ∈ [0,1]` and Hermitian `A` and `B` with eigenvalue differences of modulus at most `w`.
The Loewner-order bounds by scalar matrices express this convexity and concavity,
and add under interpolation. -/
theorem hasEigenvalueDifferences_segment [NeZero d] {A B : 𝕄} (hA : IsHermitian A)
    (hB : IsHermitian B) {w u : ℝ} (hAw : HasEigenvalueDifferences A w)
    (hBw : HasEigenvalueDifferences B w) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasEigenvalueDifferences (A + u • (B - A)) w := by
  have extrema {X : 𝕄} (hX : X.IsHermitian) :
      IsLeast (spectrum ℝ X) (sInf (spectrum ℝ X)) ∧
        IsGreatest (spectrum ℝ X) (sSup (spectrum ℝ X)) := by
    rw [hX.spectrum_real_eq_range_eigenvalues]
    exact ⟨(Set.finite_range _).isCompact.isLeast_sInf (Set.range_nonempty _),
      (Set.finite_range _).isCompact.isGreatest_sSup (Set.range_nonempty _)⟩
  have bounds {X : 𝕄} (hX : X.IsHermitian) :
      algebraMap ℝ 𝕄 (sInf (spectrum ℝ X)) ≤ X ∧
        X ≤ algebraMap ℝ 𝕄 (sSup (spectrum ℝ X)) :=
    ⟨(algebraMap_le_iff_le_spectrum hX.isSelfAdjoint).mpr fun x hx ↦ (extrema hX).1.2 hx,
      (le_algebraMap_iff_spectrum_le hX.isSelfAdjoint).mpr fun x hx ↦ (extrema hX).2.2 hx⟩
  obtain ⟨hA1, hA2⟩ := bounds hA
  obtain ⟨hB1, hB2⟩ := bounds hB
  have hAw' := (abs_le.mp (hAw _ (extrema hA).2.1 _ (extrema hA).1.1)).2
  have hBw' := (abs_le.mp (hBw _ (extrema hB).2.1 _ (extrema hB).1.1)).2
  have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
  have hXs : IsSelfAdjoint ((1 - u) • A + u • B) :=
    ((IsSelfAdjoint.all (1 - u)).smul hA.isSelfAdjoint).add
      ((IsSelfAdjoint.all u).smul hB.isSelfAdjoint)
  -- The least eigenvalue is concave and the largest eigenvalue is convex in the matrix.
  have hlo : algebraMap ℝ 𝕄 ((1 - u) * sInf (spectrum ℝ A) + u * sInf (spectrum ℝ B)) ≤
      (1 - u) • A + u • B := by
    have := add_le_add (smul_le_smul_of_nonneg_left hA1 hu1) (smul_le_smul_of_nonneg_left hB1 hu.1)
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul, ← add_smul] using this
  have hhi : (1 - u) • A + u • B ≤
      algebraMap ℝ 𝕄 ((1 - u) * sSup (spectrum ℝ A) + u * sSup (spectrum ℝ B)) := by
    have := add_le_add (smul_le_smul_of_nonneg_left hA2 hu1) (smul_le_smul_of_nonneg_left hB2 hu.1)
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul, ← add_smul] using this
  have hwidth := add_le_add (mul_le_mul_of_nonneg_left hAw' hu1)
    (mul_le_mul_of_nonneg_left hBw' hu.1)
  rw [show A + u • (B - A) = (1 - u) • A + u • B by module]
  intro x hx y hy
  have hx1 := (algebraMap_le_iff_le_spectrum hXs).mp hlo x hx
  have hx2 := (le_algebraMap_iff_spectrum_le hXs).mp hhi x hx
  have hy1 := (algebraMap_le_iff_le_spectrum hXs).mp hlo y hy
  have hy2 := (le_algebraMap_iff_spectrum_le hXs).mp hhi y hy
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Taylor bounds from the Lipschitz derivative -/

/-- Proof of Theorem 4.4, fourth line: `‖H(b) - H(a) - (b - a) H'(a)‖ ≤ L (b - a)²/2` for
`0 ≤ a ≤ b ≤ 1`, the bound on `∫_a^b (H'(σ) - H'(a)) dσ`. -/
theorem norm_taylor_left_le {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖H b - H a - (b - a) • ∂H a‖ ≤ L * (b - a) ^ 2 / 2 := by
  simpa only [div_mul_eq_mul_div] using
    taylor_lipschitz (fun x hx ↦ (hL.1 x hx).hasDerivWithinAt) hL.2
      ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩

/-- Proof of Theorem 4.4, fourth line: `‖H(b) - H(a) - (b - a) H'(b)‖ ≤ L (b - a)²/2` for
`0 ≤ a ≤ b ≤ 1`, the bound on `∫_a^b (H'(b) - H'(σ)) dσ`. -/
theorem norm_taylor_right_le {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖H b - H a - (b - a) • ∂H b‖ ≤ L * (b - a) ^ 2 / 2 := by
  have h := taylor_lipschitz (fun x hx ↦ (hL.1 x hx).hasDerivWithinAt) hL.2
    ⟨ha.trans hab, hb⟩ ⟨ha, hab.trans hb⟩
  change ‖H a - H b - (a - b) • ∂H b‖ ≤ L / 2 * (a - b) ^ 2 at h
  rw [show H a - H b - (a - b) • ∂H b =
    -(H b - H a - (b - a) • ∂H b) by module, norm_neg] at h
  rw [show (a - b) ^ 2 = (b - a) ^ 2 by ring] at h
  simpa only [div_mul_eq_mul_div] using h

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

/-- Proof of Theorem 4.4, third line: `F(1) - F(0)` is the integral of `F'` over `[0,1]`, so its
norm is at most the integral of `‖F'‖`, which is at most `C` when `‖F'(u)‖ ≤ C` for `u ∈ [0,1]`. -/
theorem norm_sub_le_integrated_deriv {F : ℝ → 𝕄} {C : ℝ}
    (hF : DifferentiableOn ℝ F (Icc 0 1))
    (hF' : ContinuousOn (∂F) (Icc 0 1))
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖∂F u‖ ≤ C) : ‖F 1 - F 0‖ ≤ C := by
  have hint := hF'.intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hFTC : F 1 - F 0 = ∫ u in (0 : ℝ)..1, ∂F u :=
    sub_eq_integral_deriv01 hF hF' (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
      zero_le_one
  calc
    ‖F 1 - F 0‖ = ‖∫ u in (0 : ℝ)..1, ∂F u‖ := by rw [hFTC]
    _ ≤ ∫ u in (0 : ℝ)..1, ‖∂F u‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ _u in (0 : ℝ)..1, C :=
      intervalIntegral.integral_mono_on zero_le_one hint.norm
        intervalIntegrable_const hbound
    _ = C := by simp

/-- Proof of Theorem 4.4, third and fourth lines: along `Ω(u) = A + u (B - A)`, where
`Ω' = B - A` and `Ω'' = 0`, the integral of the norm of the derivative and Lemma A.3(i) give
`‖𝒩([B,·])Ω' - 𝒩([A,·])Ω'‖ ≤ 2𝒩'(w) ‖Ω'‖²`. The proof of Theorem 4.4 takes `A = H(l)` and
`B = H(r)`. -/
theorem norm_𝒩ad_segment_le
    [NeZero d] {A B : 𝕄} (hA : IsHermitian A) (hB : IsHermitian B) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) (hAw : HasEigenvalueDifferences A w) (hBw : HasEigenvalueDifferences B w) :
    ‖𝒩ad B (B - A) - 𝒩ad A (B - A)‖ ≤ 2 * deriv 𝒩 w * ‖B - A‖ ^ 2 := by
  set Ω : ℝ → 𝕄 := fun u ↦ A + u • (B - A) with hΩdef
  have hΩH : IsTimeDepHamiltonian Ω := fun {u} _ ↦ hA.add (isHermitian_real_smul (hB.sub hA) u)
  have hΩw : ∀ u ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (Ω u) w :=
    fun u hu ↦ hasEigenvalueDifferences_segment hA hB hAw hBw hu
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
  obtain ⟨hC1, hbd⟩ := end_value hw0 hw hΩC2 hΩH hΩw
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
  simp only [endValue, hΩ0, hΩ1, hΩ' 0 h0, hΩ' 1 h1] at hend
  exact hend

/-- Proof of Theorem 4.4, first five lines of the display: for `1 ≤ j ≤ T`,
`‖Δ_j‖ ≤ (𝒩(w) L + 2𝒩'(w) ‖H'‖∞²)/T²`. -/
theorem norm_Δ_le [NeZero d]
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
  have hHl := @hH l hlI
  have hHr := @hH r hrI
  have hwr : HasEigenvalueDifferences (H r) w := hwidth j hjT
  have hwl : HasEigenvalueDifferences (H l) w := by
    have h := hwidth (j - 1) (by omega)
    rwa [Nat.cast_sub hj, Nat.cast_one] at h
  have hN0 := 𝒩_nonneg_of_width hw0 hw
  have hN'0 := deriv_𝒩_nonneg hw0 hw
  -- Fourth line: `‖H'(r) - T Ω'‖ ≤ L/(2T)` and `‖T Ω' - H'(l)‖ ≤ L/(2T)`, with
  -- `Ω' = H(r) - H(l)`.
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
  -- Fifth line: `‖Ω'‖ ≤ ‖H'‖∞/T`.
  have hD : ‖H r - H l‖ ≤ ‖∂H‖∞ / T := by
    have h := norm_sub_le_supNorm_mul hL hlI hrI
    rwa [hrl, Real.norm_of_nonneg (by positivity), mul_one_div] at h
  -- Third and fourth lines: the change of `𝒩([Ω(u),·])Ω'` from `u = 0` to `u = 1`.
  have hjump := norm_𝒩ad_segment_le hHl hHr hw0 hw hwl hwr
  -- First two lines: add and subtract `𝒩([Ω(1),·]) TΩ'` and `𝒩([Ω(0),·]) TΩ'`, as
  -- `Ω(0) = H(l)` and `Ω(1) = H(r)`.
  have hsplit : 𝒩ad (H r) (∂H r) - 𝒩ad (H l) (∂H l) =
      𝒩ad (H r) (∂H r - (T : ℝ) • (H r - H l)) + 𝒩ad (H l) ((T : ℝ) • (H r - H l) - ∂H l) +
        (T : ℝ) • (𝒩ad (H r) (H r - H l) - 𝒩ad (H l) (H r - H l)) := by
    rw [𝒩ad_sub, 𝒩ad_sub, 𝒩ad_smul, 𝒩ad_smul, smul_sub]
    abel
  /- The display of the proof of Theorem 4.4 for `T ‖Δ_j‖`, which is the norm of
  `𝒩([H(r),·])H'(r) - 𝒩([H(l),·])H'(l)`, with `Ω' = H(r) - H(l)`. -/
  have hdisplay : ‖𝒩ad (H r) (∂H r) - 𝒩ad (H l) (∂H l)‖ ≤
      𝒩 w * (L / (2 * T)) + 𝒩 w * (L / (2 * T)) +
        T * (2 * deriv 𝒩 w * (‖∂H‖∞ / T) ^ 2) := by
    calc ‖𝒩ad (H r) (∂H r) - 𝒩ad (H l) (∂H l)‖
      -- Lines 1 and 2: add and subtract `𝒩([Ω(1),·]) TΩ'` and `𝒩([Ω(0),·]) TΩ'`.
      _ ≤ ‖𝒩ad (H r) (∂H r - (T : ℝ) • (H r - H l))‖ +
          ‖𝒩ad (H l) ((T : ℝ) • (H r - H l) - ∂H l)‖ +
          T * ‖𝒩ad (H r) (H r - H l) - 𝒩ad (H l) (H r - H l)‖ := by
        rw [hsplit]
        refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_of_eq ?_))
        rw [norm_smul, Real.norm_of_nonneg hT.le]
      -- Line 3: (A.1) for the first two terms; the integral of the norm of the derivative, with
      -- Lemma A.3(i) and `Ω'' = 0`, for the last.
      _ ≤ 𝒩 w * ‖∂H r - (T : ℝ) • (H r - H l)‖ + 𝒩 w * ‖(T : ℝ) • (H r - H l) - ∂H l‖ +
          T * (2 * deriv 𝒩 w * ‖H r - H l‖ ^ 2) :=
        add_le_add (add_le_add (norm_𝒩ad_le hHr hw0 hw hwr _) (norm_𝒩ad_le hHl hw0 hw hwl _))
          (mul_le_mul_of_nonneg_left hjump hT.le)
      -- Line 4: `‖H'(r) - TΩ'‖ ≤ L/(2T)` and `‖TΩ' - H'(l)‖ ≤ L/(2T)`.
      _ ≤ 𝒩 w * (L / (2 * T)) + 𝒩 w * (L / (2 * T)) +
          T * (2 * deriv 𝒩 w * ‖H r - H l‖ ^ 2) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hTr hN0)
          (mul_le_mul_of_nonneg_left hTl hN0)) le_rfl
      -- Line 5: `‖Ω'‖ ≤ ‖H'‖∞/T`.
      _ ≤ 𝒩 w * (L / (2 * T)) + 𝒩 w * (L / (2 * T)) +
          T * (2 * deriv 𝒩 w * (‖∂H‖∞ / T) ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hD 2) (by linarith)) hT.le)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ 1 / T * (𝒩 w * (L / (2 * T)) + 𝒩 w * (L / (2 * T)) +
          T * (2 * deriv 𝒩 w * (‖∂H‖∞ / T) ^ 2)) :=
      mul_le_mul_of_nonneg_left hdisplay (by positivity)
    _ = (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T ^ 2 := by
      field_simp
      ring

/-- Proof of Theorem 4.4, summing the jump bound over `1 ≤ j ≤ T`:
`∑_{j=1}^T ‖Δ_j‖ ≤ (𝒩(w) L + 2𝒩'(w) ‖H'‖∞²)/T`. -/
theorem sum_norm_Δ_le
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤ (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 T, (𝒩 w * L + 2 * deriv 𝒩 w * ‖∂H‖∞ ^ 2) / T ^ 2 :=
      Finset.sum_le_sum fun j hj ↦ norm_Δ_le
        (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hH hL hw0 hw hwidth
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp

end RoundedClocks
