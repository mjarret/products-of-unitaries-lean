/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Citations
public import RoundedClocks.Appendix
public import RoundedClocks.Appendix.MultiplierMonotonicity
public import RoundedClocks.UnitSteps.Basic
public import RoundedClocks.UnitSteps.OrderedEigenvalueContinuity
public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-!
# The steps of the proof of Theorem 4.6

The proof of Theorem 4.6 (`unitary_products`) uses, in the paper's order:

* `W = e^{-iH}` is `C²` and satisfies (4.7) with `a` the least eigenvalue of `H`, which is
  continuous by the Loewner-order spectral bound, so `H` is the logarithm of Lemma A.2, and
  `‖H'‖ ≤ κ ‖W'‖` and `‖H''‖ ≤ κ ‖W''‖ + ‖W'‖²/cos²(w/4)` (`log_derivative_bounds`);
* the first two lines of the display: `T ‖Δ_j‖` is the norm of the integral of
  `(𝒩([H,·])H')'` over `[(j-1)/T, j/T]`, which Lemma A.3(ii) bounds by its suprema
  (`jump_sum_le`);
* a `C²` family has a Lipschitz derivative with `L = ‖H''‖∞`
  (`IsC2Family.hasLipschitzDerivative`), for Theorem 4.2 with this `L`;
* `κ ≥ 0` and the suprema `‖·‖∞` of continuous functions, for the last
  lines of the display.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ## Suprema over `[0,1]` -/

/-- `‖f(s)‖ ≤ ‖f‖∞` for `f` continuous on `[0,1]` and `s ∈ [0,1]`. -/
theorem norm_le_supNorm_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖f s‖ ≤ ‖f‖∞ :=
  le_csSup (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove (mem_image_of_mem _ hs)

/-- A pointwise bound on `[0,1]` bounds `‖f‖∞`. -/
theorem supNorm_le_of_forall {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {C : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ‖f s‖ ≤ C) : ‖f‖∞ ≤ C :=
  csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr h)

/-- `‖f‖∞ ≥ 0` for `f` continuous on `[0,1]`. -/
theorem supNorm_nonneg_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) : 0 ≤ ‖f‖∞ :=
  (norm_nonneg _).trans (norm_le_supNorm_of_continuousOn hf ⟨le_rfl, zero_le_one⟩)

/-! ## Calculus of `C²` families -/

/-- The derivative `H'` of a `C²` family is `C¹` on `[0,1]`. -/
theorem IsC2Family.deriv_contDiffOn {A : ℝ → 𝕄} (hC2 : IsC2Family A) :
    ContDiffOn ℝ 1 (∂A) (Icc (0 : ℝ) 1) :=
  hC2.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)

/-- The second derivative `H''` of a `C²` family is continuous on `[0,1]`. -/
theorem IsC2Family.continuousOn_deriv2 {A : ℝ → 𝕄} (hC2 : IsC2Family A) :
    ContinuousOn (∂∂A) (Icc (0 : ℝ) 1) :=
  hC2.deriv_contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl

/-- A `C²` family has a Lipschitz derivative with constant `L = ‖H''‖∞` (mean value
inequality for `H'`). -/
theorem IsC2Family.hasLipschitzDerivative {A : ℝ → 𝕄} (hC2 : IsC2Family A) :
    HasLipschitzDerivative A ‖∂∂A‖∞ := by
  refine ⟨hC2.differentiableOn (by norm_num), fun s₁ hs₁ s₂ hs₂ ↦ ?_⟩
  have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_derivWithin_le
    (hC2.deriv_contDiffOn.differentiableOn (by norm_num))
    (fun s hs ↦ norm_le_supNorm_of_continuousOn hC2.continuousOn_deriv2 hs) hs₂ hs₁
  rwa [Real.norm_eq_abs] at h

/-- `W = e^{-iH}` is `C²` when `H` is. -/
theorem IsC2Family.exp {H : ℝ → 𝕄} (hC2 : IsC2Family H) :
    IsC2Family (fun s ↦ exp (-I • H s)) := by
  intro s hs
  have hanal : AnalyticAt ℂ (NormedSpace.exp : 𝕄 → 𝕄) (-I • H s) :=
    NormedSpace.exp_analytic (𝕂 := ℂ) _
  exact (hanal.contDiffAt.restrict_scalars ℝ).comp_contDiffWithinAt s
    ((hC2 s hs).const_smul (-I))

/-! ## Lemma A.2 for `W = e^{-iH}` -/

/-- Proof of Theorem 4.6: "As `W` is `C²` and satisfies (4.7) with `a` the least eigenvalue of
`H`, `H` is the logarithm of Lemma A.2, so `‖H'‖ ≤ κ ‖W'‖` and
`‖H''‖ ≤ κ ‖W''‖ + ‖W'‖²/cos²(w/4)`." Here `W = e^{-iH}`. -/
theorem log_derivative_bounds
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) (hC2 : IsC2Family H)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) w) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      ‖∂H s‖ ≤ κ w * ‖∂(fun t ↦ exp (-I • H t)) s‖ ∧
      ‖∂∂H s‖ ≤ κ w * ‖∂∂(fun t ↦ exp (-I • H t)) s‖ +
        ‖∂(fun t ↦ exp (-I • H t)) s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  let a : ℝ → ℝ := fun s ↦ sInf (spectrum ℝ (H s))
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  have hmin (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : IsLeast (spectrum ℝ (H s)) (a s) := by
    dsimp only [a]
    rw [(show (H s).IsHermitian from @hH s hs).spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).isCompact.isLeast_sInf (Set.range_nonempty _)
  -- Every eigenvalue of `H(s)` lies in `[a(s), a(s) + w]`.
  have hspectrum (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasRealSpectrumIn (H s) (Icc (a s) (a s + w)) := by
    intro x hx
    refine ⟨(hmin s hs).2 hx, ?_⟩
    have hd := (abs_le.mp (hwidth s hs x hx (a s) (hmin s hs).1)).2
    linarith
  have ha : IsContinuousFamily a :=
    continuousOn_sInf_spectrum hH hC2.continuousOn
  have hW : IsUnitaryFamily W 0 1 := by
    intro s hs
    simpa [W, smul_smul] using exp_neg_I_smul_isUnitary (@hH s hs) 1
  -- (4.7): the spectrum of `W(s)` lies in the arc `{e^{-iθ} : a(s) ≤ θ ≤ a(s) + w}`.
  have harc : HasSpectrumInPhaseInterval W a w := by
    intro s hs z hz
    change z ∈ spectrum ℂ (exp (-I • H s)) at hz
    rw [spectrum_exp (@hH s hs)] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hspectrum s hs hx, rfl⟩
  obtain ⟨H₀, -, -, hunique, -, hb₀⟩ := walk_log hw0 hw ha hW harc hC2.exp
  -- `H` is the logarithm of Lemma A.2, by its uniqueness.
  have heq : EqOn H₀ H (Icc (0 : ℝ) 1) := fun s hs ↦
    (hunique s hs (H s) (@hH s hs) (hspectrum s hs) rfl).symm
  have hfirst : EqOn (∂H₀) (∂H) (Icc (0 : ℝ) 1) := fun _ hs ↦ derivWithin_congr heq (heq hs)
  have hsecond : EqOn (∂∂H₀) (∂∂H) (Icc (0 : ℝ) 1) :=
    fun _ hs ↦ derivWithin_congr hfirst (hfirst hs)
  intro s hs
  rw [← hfirst hs, ← hsecond hs]
  exact hb₀ s hs

/-! ## The jumps (Lemma A.3(ii)) -/

/-- First two lines of the display in the proof of Theorem 4.6, summed over `1 ≤ j ≤ T`.
Lemma A.3(ii) for `Ω = H`, with `W = e^{-iH}`, bounded by its suprema and integrated over each
`[(j-1)/T, j/T]`, gives
`Σ_j ‖Δ_j‖ ≤ (𝒩(w)‖H''‖∞ + 2𝒩'(w)‖W'‖∞‖H'‖∞ + (𝒩(w) - 𝒩(0))‖H'‖∞²)/T`. -/
theorem jump_sum_le
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : ∀ s ∈ Icc (0 : ℝ) 1, HasEigenvalueDifferences (H s) w)
    (hC2 : IsC2Family H) :
    ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤
      (𝒩 w * ‖∂∂H‖∞ + 2 * deriv 𝒩 w * ‖∂(fun t ↦ exp (-I • H t))‖∞ * ‖∂H‖∞ +
        (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2) / T := by
  -- `F = 𝒩([H,·])H'`, whose values at `j/T` and `(j-1)/T` give `T Δ_j`, and `W = e^{-iH}`.
  let F : ℝ → 𝕄 := fun s ↦ 𝒩ad (H s) (∂H s)
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  set C := 𝒩 w * ‖∂∂H‖∞ + 2 * deriv 𝒩 w * ‖∂W‖∞ * ‖∂H‖∞ + (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2
  obtain ⟨hF, hb⟩ := end_value hw0 hw hC2 hH hwidth
  have hN := 𝒩_nonneg_of_width hw0 hw
  have hN' := deriv_𝒩_nonneg hw0 hw
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := sub_nonneg.mpr (𝒩_zero_le hw0 hw)
  have hH1 := hC2.deriv_contDiffOn.continuousOn
  have hH2 := hC2.continuousOn_deriv2
  have hW1 : ContinuousOn (∂W) (Icc (0 : ℝ) 1) := hC2.exp.deriv_contDiffOn.continuousOn
  have hW0 := supNorm_nonneg_of_continuousOn hW1
  -- Lemma A.3(ii) for `Ω = H`, bounded by its suprema over `[0,1]`.
  have hsup : ∀ s ∈ Icc (0 : ℝ) 1, ‖∂F s‖ ≤ C := by
    intro s hs
    have hHs := norm_le_supNorm_of_continuousOn hH1 hs
    have hH2s := norm_le_supNorm_of_continuousOn hH2 hs
    have hWs := norm_le_supNorm_of_continuousOn hW1 hs
    calc
      _ ≤ 𝒩 w * ‖∂∂H s‖ + 2 * deriv 𝒩 w * ‖∂W s‖ * ‖∂H s‖ +
          (𝒩 w - 𝒩 0) * ‖∂H s‖ ^ 2 := (hb s hs).2
      _ ≤ C := by
        dsimp [C]
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hH2s hN)
            (mul_le_mul (mul_le_mul_of_nonneg_left hWs (by positivity)) hHs
              (norm_nonneg _) (by positivity)))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hHs 2) htail)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- One jump, with `l = (j-1)/T` and `r = j/T`.
  have hjump : ∀ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤ C / T ^ 2 := by
    intro j hj
    obtain ⟨hj1, hjT⟩ := Finset.mem_Icc.mp hj
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjT' : (j : ℝ) ≤ T := by exact_mod_cast hjT
    unfold Δ
    set l : ℝ := ((j : ℝ) - 1) / T with hl_def
    set r : ℝ := (j : ℝ) / T with hr_def
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hTpos.le
    have hr1 : r ≤ 1 := (div_le_one hTpos).2 hjT'
    have hrl : r - l = 1 / T := by
      rw [hl_def, hr_def]
      field_simp
      ring
    have hlr : l ≤ r := by
      have : (0 : ℝ) < 1 / T := by positivity
      linarith
    have hlI : l ∈ Icc (0 : ℝ) 1 := ⟨hl0, hlr.trans hr1⟩
    have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hl0.trans hlr, hr1⟩
    -- First line of the display: `T ‖Δ_j‖ = ‖∫_l^r (𝒩([H,·])H')' ds‖`.
    have hintegral : F r - F l = ∫ s in l..r, ∂F s :=
      sub_eq_integral_deriv01 (hF.differentiableOn (by norm_num))
        (hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl) hlI hrI hlr
    -- Second line: Lemma A.3(ii), bounded by its suprema, over an interval of length `1/T`.
    have hbound : ‖∫ s in l..r, ∂F s‖ ≤ C * (1 / T) := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := ∂F) (C := C) (a := l) (b := r) (fun s hs ↦ hsup s (by
          rw [uIoc_of_le hlr] at hs
          exact ⟨hl0.trans hs.1.le, hs.2.trans hr1⟩))
      rwa [abs_of_nonneg (sub_nonneg.2 hlr), hrl] at hi
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc 1 / (T : ℝ) * ‖𝒩ad (H r) (∂H r) - 𝒩ad (H l) (∂H l)‖
      _ = 1 / T * ‖F r - F l‖ := rfl
      _ = 1 / T * ‖∫ s in l..r, ∂F s‖ := by rw [hintegral]
      _ ≤ 1 / T * (C * (1 / T)) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = C / T ^ 2 := by ring
  -- The sum over `1 ≤ j ≤ T`.
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 T, C / T ^ 2 := Finset.sum_le_sum hjump
    _ = T * (C / T ^ 2) := by simp
    _ = C / T := by field_simp

end RoundedClocks
