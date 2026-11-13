/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.UnifiedProducts
public import UnitaryProducts.Spectral.TrackedCircularBand

/-! # The Hamiltonian and unitary-family consequences of the jump comparison. -/
@[expose] public section
open Real Complex Set Filter MeasureTheory
open UnitaryProducts.Corrector UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Appendix B: the reflected sine equals
`sin (θ/2)`, which is asymptotic to `θ/2` as the empty arc shrinks. -/
theorem free_arc_sine_equivalent :
    (∀ θ : ℝ, Real.sin ((2 * π - θ) / 2) = Real.sin (θ / 2)) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun θ : ℝ ↦ Real.sin (θ / 2)) (fun θ ↦ θ / 2) := by
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨fun θ ↦ (UnitaryProducts.Prose.free_arc_reflections θ).1, ?_⟩
  have hhalf : Tendsto (fun θ : ℝ ↦ θ / 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div] using hid.div_const 2
  simpa only [Function.comp_def, id_eq] using
    Real.isEquivalent_sin.comp_tendsto hhalf

/-- Appendix B: the endpoint coefficient in its stated sine form.
The sine equivalent gives the leading term, and the remaining term vanishes. -/
theorem cellConstant_walk_endpoint_equivalent :
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun θ ↦ cellConstant (2 * π - θ) * walkLogSlope (2 * π - θ))
      (fun θ ↦ 1 / θ ^ 2) := by
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  obtain ⟨hreflect, hsine⟩ := free_arc_sine_equivalent
  have hsin_ne : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Real.sin (θ / 2) ≠ 0 := by
    filter_upwards [hev] with θ hθ
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, pi_pos])).ne'
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one hsin_ne).mp hsine.symm
  have hscaled : Tendsto (fun θ : ℝ ↦ θ / Real.sin (θ / 2))
      (𝓝[>] 0) (𝓝 2) := by
    have hh := hratio.const_mul 2
    norm_num only [mul_one] at hh
    apply hh.congr'
    filter_upwards [] with θ
    simp only [Pi.div_apply]
    ring
  have hwidth : Tendsto (fun θ : ℝ ↦ 2 * π - θ) (𝓝[>] 0) (𝓝 (2 * π)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hid
  have hmain := ((hscaled.pow 2).div_const 4).sub
    ((hscaled.mul hid).div (hwidth.const_mul 2) (by positivity : 2 * (2 * π) ≠ 0))
  have hlimit : Tendsto
      (fun θ ↦ (cellConstant (2 * π - θ) * walkLogSlope (2 * π - θ)) * θ ^ 2)
      (𝓝[>] 0) (𝓝 1) := by
    norm_num at hmain
    apply hmain.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    have hwn : 2 * π - θ ≠ 0 := by linarith [hθ.2, pi_pos]
    have hsn : Real.sin (θ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, pi_pos])).ne'
    rw [cellConstant, if_neg hwn, ← walkLogSlope_closed hw0 hw, if_neg hwn, hreflect]
    field_simp
    ring
  apply Asymptotics.isEquivalent_of_tendsto_one
  simpa only [Pi.div_def, div_div_eq_mul_div, div_one] using hlimit

set_option maxHeartbeats 1200000 in
-- Collecting the logarithm comparison expands the three scalar coefficient formulas.
/-- The arc-coordinate auxiliary for **Theorem 4.6** (`cor:walks`): use the logarithm of Lemma A.2,
the C² jump bound in Theorem 4.6, and Theorem 4.2. Collect the three
coefficients and retain their Appendix B equivalents as the empty arc shrinks. -/
theorem unitary_products_of_arc [NeZero d] (T : ℕ) (hT : 0 < T) :
    ∀ (a : ℝ → ℝ) (θ : ℝ)
    (_hθ : 0 < θ) (_hθmax : θ ≤ 2 * π) (W : ℝ → 𝕄)
    (_ha : ContinuousOn a (Icc (0 : ℝ) 1)) (_hunit : (walk W 1).1)
    (_harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ α ∈ Icc (a s) (a s + (2 * π - θ)), z = Complex.exp (-I * (α : ℂ)))
    (_hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (H : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (_hlog : ∀ s ∈ Icc (0 : ℝ) 1, evol (H s) 1 = W s)
    (_hwindow : ∀ s (hs : s ∈ Icc (0 : ℝ) 1),
      ∀ i, (hH s hs).eigenvalues i ∈ Icc (a s) (a s + (2 * π - θ))),
    let w : ℝ := 2 * π - θ
    let Wd := derivWithin W (Icc (0 : ℝ) 1)
    let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
    let c₀ : ℝ := cellConstant w
    let κ : ℝ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
    let c₂ : ℝ := (1 / 24 + frameBound w) / Real.cos (w / 4) ^ 2 +
      (c₀ / 4 + 1 / 64) * κ ^ 2 + 2 * frameLip w * κ +
      (frameBound w - frameBound 0) * κ ^ 2
    (∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ H (t / T)) U 0 T →
        let V := evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2))
        ‖V - U T‖ ≤
          (1 / T) * (c₀ * κ * (‖Wd 0‖ + ‖Wd 1‖) +
            (1 / 24 + frameBound w) * κ * unitSupNorm Wdd + c₂ * unitSupNorm Wd ^ 2)) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ cellConstant (2 * π - δ) * walkLogSlope (2 * π - δ)) (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ (1 / 24 + frameBound (2 * π - δ)) * walkLogSlope (2 * π - δ))
      (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun δ ↦ walk_square (2 * π - δ))
      (fun δ ↦ (8 / π + 5 * π / 2 + 2) / δ ^ 3) := by
  intro a θ hθ hθmax W ha hunit harc hc H hH hlog hwindow
  have hw0 : 0 ≤ 2 * π - θ := sub_nonneg.mpr hθmax
  have hw : 2 * π - θ < 2 * π := by linarith
  refine ⟨?_, cellConstant_walk_endpoint_equivalent,
    walk_uniform_coefficient_equivalents.2.1,
    walk_leading_equivalents.1.trans walk_leading_equivalents.2⟩
  intro U hU
  have hwalk := unified_products_walk hT a hw W ha hunit harc hc H hH hlog hwindow U hU
  simp only [walk_square, uniform_c1, uniform_c0, cellConstant_eq_frameBound hw0 hw,
    walkLogSlope_closed hw0 hw] at hwalk ⊢
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hwalk


/-- Section 4.3: the least eigenvalue is a continuous choice of the left endpoint.
The width hypothesis places every eigenvalue in that window, and spectral mapping
places the exponential in its image arc. -/
theorem hamiltonian_window_arc [NeZero d] (H : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hc : ContinuousOn H (Icc (0 : ℝ) 1)) {w : ℝ}
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w) :
    ContinuousOn (fun s ↦ spectralBottom (H s)) (Icc (0 : ℝ) 1) ∧
    (∀ s (hs : s ∈ Icc (0 : ℝ) 1) i,
      (hH s hs).eigenvalues i ∈ Icc (spectralBottom (H s)) (spectralBottom (H s) + w)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (evol (H s) 1),
      ∃ α ∈ Icc (spectralBottom (H s)) (spectralBottom (H s) + w),
        z = Complex.exp (-I * (α : ℂ))) := by
  have hwindow (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (i : Fin d) :
      (hH s hs).eigenvalues i ∈ Icc (spectralBottom (H s)) (spectralBottom (H s) + w) := by
    have hmin := isLeast_spectralBottom (hH s hs)
    obtain ⟨j, hj⟩ := (hH s hs).spectrum_real_eq_range_eigenvalues ▸ hmin.1
    refine ⟨hmin.2 ((hH s hs).eigenvalues_mem_spectrum_real i), ?_⟩
    have hdiff := (abs_le.mp (hwidth s hs i j)).2
    rw [hj] at hdiff
    linarith
  refine ⟨continuous_spectralBottom.comp_continuousOn hc, hwindow, ?_⟩
  intro s hs z hz
  rw [spectrum_evol_image (hH s hs)] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [(hH s hs).spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨_, hwindow s hs i, rfl⟩

/-- The operator-series comparison with hypotheses on the Hamiltonian.
Use its least eigenvalue to obtain the arc, then the unique logarithm of Lemma A.2
is the given Hamiltonian. The arc-coordinate proof uses the stated jump integral,
the C² jump bound in Theorem 4.6, and Theorem 4.2. -/
theorem unitary_products_series_bound [NeZero d] (T : ℕ) (hT : 0 < T)
    (H : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π) (hcH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w) :
    let W := fun s ↦ evol (H s) 1
    let Wd := derivWithin W (Icc (0 : ℝ) 1)
    let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
    let c₀ : ℝ := cellConstant w
    let κ : ℝ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
    let c₂ : ℝ := (1 / 24 + frameBound w) / Real.cos (w / 4) ^ 2 +
      (c₀ / 4 + 1 / 64) * κ ^ 2 + 2 * frameLip w * κ +
      (frameBound w - frameBound 0) * κ ^ 2
    (∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ H (t / T)) U 0 T →
        let V := evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2))
        ‖V - U T‖ ≤
          (1 / T) * (c₀ * κ * (‖Wd 0‖ + ‖Wd 1‖) +
            (1 / 24 + frameBound w) * κ * unitSupNorm Wdd + c₂ * unitSupNorm Wd ^ 2)) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ cellConstant (2 * π - δ) * walkLogSlope (2 * π - δ)) (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ (1 / 24 + frameBound (2 * π - δ)) * walkLogSlope (2 * π - δ))
      (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun δ ↦ walk_square (2 * π - δ))
      (fun δ ↦ (8 / π + 5 * π / 2 + 2) / δ ^ 3) := by
  dsimp only
  have hw0 : 0 ≤ w := by
    simpa only [sub_self, abs_zero] using hwidth 0 (by norm_num) 0 0
  obtain ⟨ha, hwindow, harc⟩ := hamiltonian_window_arc H hH hcH.continuousOn hwidth
  have hcW : ContDiffOn ℝ 2 (fun s ↦ evol (H s) 1) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact ((contDiffAt_evol_one (H s)).restrict_scalars ℝ).comp_contDiffWithinAt s (hcH s hs)
  have hunit : (walk (fun s ↦ evol (H s) 1) 1).1 := by
    intro s hs
    exact Matrix.mem_unitaryGroup_iff'.mp (evol_mem_unitary (hH s hs) 1)
  have hwidthId : 2 * π - (2 * π - w) = w := by ring
  have result := unitary_products_of_arc T hT (fun s ↦ spectralBottom (H s))
    (2 * π - w) (by linarith) (by linarith) (fun s ↦ evol (H s) 1) ha hunit
    (by simpa only [hwidthId] using harc) hcW H hH (fun _ _ ↦ rfl)
    (by simpa only [hwidthId] using hwindow)
  simpa only [hwidthId] using result


/-- Appendix B: the coefficient `c₂`, with Definition 4.1's closed function. -/
def paperWalkSquare (w : ℝ) : ℝ :=
  let c₁ := cellConstant w / 4 + 1 / 64
  let κ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
  (1 / 24 + frameMult w) / Real.cos (w / 4) ^ 2 +
    c₁ * κ ^ 2 + 2 * deriv frameMult w * κ +
    (frameMult w - frameMult 0) * κ ^ 2

/-- The closed coefficient agrees with its convergent-series calculation. -/
theorem paperWalkSquare_eq_series {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    paperWalkSquare w = walk_square w := by
  simp only [paperWalkSquare, walk_square, uniform_c1, uniform_c0,
    paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw,
    paperFrameMult_eq_series (le_refl 0) (by positivity : (0 : ℝ) < 2 * π),
    cellConstant_eq_frameBound hw0 hw, ← walkLogSlope_closed hw0 hw]

/-- Appendix B: the assigned values of `c₀` and `κ` at width zero are
limits of their closed formulas. The first follows from the analytic frame
multiplier, and the second from continuity of the sinc function. -/
theorem constants_zero_limits :
    Tendsto cellConstant (𝓝 (0 : ℝ)) (𝓝 (1 / 24)) ∧
    Tendsto (fun w : ℝ ↦ if w = 0 then 1 else (w / 2) / Real.sin (w / 2))
      (𝓝 0) (𝓝 1) := by
  have hframe := UnitaryProducts.Separation.analyticAt_frameMult_zero.continuousAt
  have hhalf : ContinuousAt (fun w : ℝ ↦ w / 2) 0 :=
    continuousAt_id.div_const 2
  have hframe_half : ContinuousAt (fun w : ℝ ↦ frameMult (w / 2)) 0 :=
    hframe.comp_of_eq hhalf (by simp)
  have hcell : ContinuousAt (fun w : ℝ ↦ frameMult w - frameMult (w / 2) / 2) 0 :=
    hframe.sub (hframe_half.div_const 2)
  have hcell_eq : cellConstant =ᶠ[𝓝 (0 : ℝ)]
      (fun w ↦ frameMult w - frameMult (w / 2) / 2) := by
    filter_upwards [eventually_abs_sub_lt (0 : ℝ) (by positivity : 0 < 2 * π)] with w hw
    exact cellConstant_eq_frameMult (by simpa only [sub_zero] using hw)
  have hsinc : ContinuousAt (fun w : ℝ ↦ Real.sinc (w / 2)) 0 :=
    Real.continuous_sinc.continuousAt.comp (by simpa only [zero_div] using hhalf)
  have hsinc_ne : Real.sinc ((0 : ℝ) / 2) ≠ 0 := by simp
  have hkappa := (hsinc.inv₀ hsinc_ne).tendsto
  refine ⟨?_, ?_⟩
  · simpa only [cellConstant, if_pos rfl] using
      (hcell.congr_of_eventuallyEq hcell_eq).tendsto
  · have hkappa_eq (w : ℝ) : (Real.sinc (w / 2))⁻¹ =
        if w = 0 then 1 else (w / 2) / Real.sin (w / 2) := by
      by_cases hw : w = 0
      · simp [hw]
      · rw [if_neg hw, Real.sinc_of_ne_zero (div_ne_zero hw (by norm_num)), inv_div]
    simpa only [zero_div, Real.sinc_zero, inv_one, hkappa_eq] using hkappa

/-- Appendix B and Theorem 4.6: each of the three coefficients of
`𝓔̃_w(W)` is bounded by a constant times the inverse cube of the free arc.
The first two exact equivalents are inverse squares, hence give the weaker
common bound after multiplying their scaled limits by the free arc. -/
theorem paper_walk_coefficients_isBigO :
    let κ : ℝ → ℝ := fun w ↦ if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
    Asymptotics.IsBigO (𝓝[>] 0)
      (fun θ ↦ cellConstant (2 * π - θ) * κ (2 * π - θ))
      (fun θ : ℝ ↦ 1 / θ ^ 3) ∧
    Asymptotics.IsBigO (𝓝[>] 0)
      (fun θ ↦ (1 / 24 + frameMult (2 * π - θ)) * κ (2 * π - θ))
      (fun θ : ℝ ↦ 1 / θ ^ 3) ∧
    Asymptotics.IsBigO (𝓝[>] 0) (fun θ ↦ paperWalkSquare (2 * π - θ))
      (fun θ : ℝ ↦ 1 / θ ^ 3) := by
  intro κ
  have of_scaled_limit (f : ℝ → ℝ) (c : ℝ)
      (h : Tendsto (fun θ ↦ f θ * θ ^ 3) (𝓝[>] 0) (𝓝 c)) :
      Asymptotics.IsBigO (𝓝[>] 0) f (fun θ : ℝ ↦ 1 / θ ^ 3) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ c ?_
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact fun hzero ↦ False.elim ((one_div_ne_zero (pow_ne_zero _ (ne_of_gt hθ))) hzero)
    · simpa only [Pi.div_def, div_div_eq_mul_div, div_one] using h
  obtain ⟨hend, hsecond, hsquare⟩ := walk_coefficient_limits
  have hid : Tendsto (fun θ : ℝ ↦ θ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  refine ⟨of_scaled_limit _ 0 ?_, of_scaled_limit _ 0 ?_,
    of_scaled_limit _ (8 / π + 5 * π / 2 + 2) ?_⟩
  · have h := hend.mul hid
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    dsimp only [κ]
    rw [walkLogSlope_closed hw0 hw, cellConstant_eq_frameBound hw0 hw]
    dsimp only [uniform_c0]
    ring
  · have h := hsecond.mul hid
    rw [mul_zero] at h
    apply h.congr'
    filter_upwards [hev] with θ hθ
    have hw0 : 0 ≤ 2 * π - θ := by linarith [hθ.2, pi_pos]
    have hw : 2 * π - θ < 2 * π := by linarith [hθ.1]
    dsimp only [κ]
    rw [walkLogSlope_closed hw0 hw, paperFrameMult_eq_series hw0 hw]
    dsimp only [walkUniformSecond]
    ring
  · apply hsquare.congr'
    filter_upwards [hev] with θ hθ
    rw [paperWalkSquare_eq_series (by linarith [hθ.2, pi_pos]) (by linarith [hθ.1])]

/-- **Fact B.2** (`fact:arc`): the three equivalents of Appendix B and
the common inverse-cube bound for every walk-energy coefficient. -/
theorem fact_arc :
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ cellConstant (2 * π - δ) * walkLogSlope (2 * π - δ)) (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ (1 / 24 + frameMult (2 * π - δ)) * walkLogSlope (2 * π - δ))
      (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun δ ↦ paperWalkSquare (2 * π - δ))
      (fun δ ↦ (8 / π + 5 * π / 2 + 2) / δ ^ 3) ∧
    (let κ : ℝ → ℝ := fun x ↦ if x = 0 then 1 else (x / 2) / Real.sin (x / 2);
      HasInverseCubeGrowth (fun x ↦ cellConstant x * κ x) ∧
      HasInverseCubeGrowth (fun x ↦ (1 / 24 + frameMult x) * κ x) ∧
      HasInverseCubeGrowth paperWalkSquare) := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  refine ⟨cellConstant_walk_endpoint_equivalent, ?_, ?_, paper_walk_coefficients_isBigO⟩
  · apply walk_coefficient_equivalents.2.1.congr_left
    filter_upwards [hev] with δ hδ
    rw [paperFrameMult_eq_series (by linarith [hδ.2, pi_pos]) (by linarith [hδ.1])]
    rfl
  · apply (walk_leading_equivalents.1.trans walk_leading_equivalents.2).congr_left
    filter_upwards [hev] with δ hδ
    rw [paperWalkSquare_eq_series (by linarith [hδ.2, pi_pos]) (by linarith [hδ.1])]

end UnitaryProducts.PaperProof

namespace UnitaryProducts.Paper

/-- Appendix B: the coefficient `𝓔̃_w(W)` used in Theorem 4.6, including the
continuous value `κ = 1` at width zero. -/
def walkEnergy {d : ℕ} (w : ℝ) (W : ℝ → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  let Wd := derivWithin W (Icc (0 : ℝ) 1)
  let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
  let κ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
  PaperProof.cellConstant w * κ * (‖Wd 0‖ + ‖Wd 1‖) +
    (1 / 24 + frameMult w) * κ * unitSupNorm Wdd +
    PaperProof.paperWalkSquare w * unitSupNorm Wd ^ 2

end UnitaryProducts.Paper

namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Theorem 4.6** (`cor:walks`): the unitary-family comparison with the
constants of Appendix B and multiplier of Definition 4.1. The bound compares the
rounded and continuous evolutions, identifies the rounded endpoint with the phased
unitary product, and gives inverse-cube growth for all three coefficients. -/
theorem thm_unitary_products [NeZero d] (T : ℕ) (hT : 0 < T)
    (H : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H) {w : ℝ}
    (hw : w < 2 * π) (hcH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hwidth : HasWidth H w) :
    let W := fun s ↦ evol (H s) 1
    let κ : ℝ → ℝ := fun x ↦ if x = 0 then 1 else (x / 2) / Real.sin (x / 2)
    ‖roundedEvolution H T T - evolution H T T‖ ≤ walkEnergy w W / T ∧
    HasInverseCubeGrowth (fun x ↦ cellConstant x * κ x) ∧
    HasInverseCubeGrowth (fun x ↦ (1 / 24 + frameMult x) * κ x) ∧
    HasInverseCubeGrowth paperWalkSquare ∧
    roundedEvolution H T T =
      evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2)) := by
  have hwidth := (hasWidth_iff hH).1 hwidth
  dsimp only
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (by norm_num) (0 : Fin d) 0
  have hseries := unitary_products_series_bound T hT H hH hw hcH hwidth
  dsimp only at hseries
  have harc := fact_arc.2.2.2
  refine ⟨?_, harc.1, harc.2.1, harc.2.2, ?_⟩
  · rw [roundedEvolution_endpoint hT hH,
      div_eq_mul_one_div (walkEnergy w _) (T : ℝ),
      mul_comm (walkEnergy w _) (1 / (T : ℝ))]
    simp only [walkEnergy, paperWalkSquare]
    rw [paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw,
      paperFrameMult_eq_series (w := 0) le_rfl (by positivity)]
    have hprod : (walk (fun s ↦ evol (H s) 1) T).2 = (unitProduct H T).1 :=
      UnitaryProducts.stepProduct_eq_pieceProduct (fun _ _ ↦ rfl) T le_rfl
    rw [← hprod]
    exact hseries.1 _ (evolution_spec (Nat.cast_pos.mpr hT) hH
      (UnitaryProducts.Prose.regulated_of_continuousOn hcH.continuousOn))
  · have hprod : (walk (fun s ↦ evol (H s) 1) T).2 = (unitProduct H T).1 :=
      UnitaryProducts.stepProduct_eq_pieceProduct (fun _ _ ↦ rfl) T le_rfl
    rw [hprod]
    exact roundedEvolution_endpoint hT hH

end UnitaryProducts.PaperProof
