/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
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

/-- The last paragraph of Theorem 4.5: the reflected sine equals
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

/-- The endpoint coefficient in Theorem 4.5, in its stated sine form.
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
/-- The arc-coordinate auxiliary for **Theorem 4.5** (`cor:walks`): use the logarithm of Lemma A.2,
Theorem 4.4(ii), and Theorem 4.2. Collect the three
coefficients and prove their stated equivalents as the empty arc shrinks. -/
theorem unitary_products_of_arc [NeZero d] (T : ℕ) (hT : 0 < T) :
    ∀ (a : ℝ → ℝ) (θ : ℝ)
    (_hθ : 0 < θ) (_hθmax : θ ≤ 2 * π) (W : ℝ → 𝕄)
    (_ha : ContinuousOn a (Icc (0 : ℝ) 1)) (_hunit : (walk W 1).1)
    (_harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ α ∈ Icc (a s) (a s + (2 * π - θ)), z = Complex.exp (-I * (α : ℂ)))
    (_hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (H : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
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
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
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
Theorem 4.4(ii), and Theorem 4.2. -/
theorem unitary_products_series_bound [NeZero d] (T : ℕ) (hT : 0 < T)
    (H : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
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


/-- The coefficient `c₂` of Theorem 4.5, with Definition 4.1's closed function. -/
def paperWalkSquare (w : ℝ) : ℝ :=
  let κ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
  (1 / 24 + frameMult w) / Real.cos (w / 4) ^ 2 +
    (cellConstant w / 4 + 1 / 64) * κ ^ 2 + 2 * deriv frameMult w * κ +
    (frameMult w - frameMult 0) * κ ^ 2

/-- The closed coefficient agrees with its convergent-series calculation. -/
theorem paperWalkSquare_eq_series {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    paperWalkSquare w = walk_square w := by
  simp only [paperWalkSquare, walk_square, uniform_c1, uniform_c0,
    paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw,
    paperFrameMult_eq_series (le_refl 0) (by positivity : (0 : ℝ) < 2 * π),
    cellConstant_eq_frameBound hw0 hw, ← walkLogSlope_closed hw0 hw]

/-- **Theorem 4.5** (`cor:walks`): the unitary-family comparison with the
closed constants of Definition 4.1. The phased product is the endpoint of the
rounded Hamiltonian evolution. The unused Lipschitz premise is omitted, and the rounded evolution
is also constructed. -/
theorem thm_unitary_products [NeZero d] (T : ℕ) (hT : 0 < T)
    (H : ℝ → 𝕄) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    {w : ℝ} (hw : w < 2 * π) (hcH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w) :
    let W := fun s ↦ evol (H s) 1
    let Wd := derivWithin W (Icc (0 : ℝ) 1)
    let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
    let c₀ : ℝ := cellConstant w
    let κ : ℝ := if w = 0 then 1 else (w / 2) / Real.sin (w / 2)
    let c₂ : ℝ := (1 / 24 + frameMult w) / Real.cos (w / 4) ^ 2 +
      (c₀ / 4 + 1 / 64) * κ ^ 2 + 2 * deriv frameMult w * κ +
      (frameMult w - frameMult 0) * κ ^ 2
    (∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ H (t / T)) U 0 T →
        let V := evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2))
        ‖V - U T‖ ≤
          (1 / T) * (c₀ * κ * (‖Wd 0‖ + ‖Wd 1‖) +
            (1 / 24 + frameMult w) * κ * unitSupNorm Wdd + c₂ * unitSupNorm Wd ^ 2)) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ cellConstant (2 * π - δ) * walkLogSlope (2 * π - δ)) (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0)
      (fun δ ↦ (1 / 24 + frameMult (2 * π - δ)) * walkLogSlope (2 * π - δ))
      (fun δ ↦ 1 / δ ^ 2) ∧
    Asymptotics.IsEquivalent (𝓝[>] 0) (fun δ ↦ paperWalkSquare (2 * π - δ))
      (fun δ ↦ (8 / π + 5 * π / 2 + 2) / δ ^ 3) ∧
    (∃ V : ℝ → 𝕄,
      IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T ∧
      V T = evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2))) := by
  dsimp only
  have hw0 : 0 ≤ w := by
    simpa using hwidth 0 (by norm_num) (0 : Fin d) 0
  have hseries := unitary_products_series_bound T hT H hH hw hcH hwidth
  dsimp only at hseries
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 π := Ioo_mem_nhdsGT pi_pos
  refine ⟨?_, hseries.2.1, ?_, ?_, ?_⟩
  · rw [paperFrameMult_eq_series hw0 hw, paperFrameMult_deriv_eq_series hw0 hw,
      paperFrameMult_eq_series (le_refl 0) (by positivity)]
    exact hseries.1
  · apply hseries.2.2.1.congr_left
    filter_upwards [hev] with δ hδ
    rw [paperFrameMult_eq_series (by linarith [hδ.2, pi_pos]) (by linarith [hδ.1])]
  · apply hseries.2.2.2.congr_left
    filter_upwards [hev] with δ hδ
    rw [paperWalkSquare_eq_series (by linarith [hδ.2, pi_pos]) (by linarith [hδ.1])]
  · have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
    obtain ⟨V, hV, heV⟩ := exists_rounded_evolution ht hT H hH
    refine ⟨V, hV, ?_⟩
    have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
    have hprod : (walk (fun s ↦ evol (H s) 1) T).2 = (unitProduct H T).1 :=
      UnitaryProducts.stepProduct_eq_pieceProduct (fun _ _ ↦ rfl) T le_rfl
    simpa only [div_self ht.ne', one_smul, hhalf, ← hprod] using heV

end UnitaryProducts.PaperProof
