/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Algebra.Order.Round
public import UnitaryProducts.Comparison.OneSize
public import UnitaryProducts.Spectral.CircularBands

/-!
# Prose steps for unit steps and walks

## Declarations

- `bounded_walkLogResolvent`
- `chord_square_antitone`
- `cot_half_width_reflect`
- `eigenvalues_mem_open_turn_of_norm`
- `eventually_window_avoids_cut`
- `eventually_window_in_principal_turn`
- `exists_uniform_walkLogResolvent_bound`
- `exp_neg_I_mem_slitPlane`
- `frameOp_eq_positive_series`
- `hasDerivAt_log_denominator`
- `isGreatest_inv_chord_phase`
- `isGreatest_inv_chord_phase_radius`
- `isGreatest_norm_walkLogResolvent`
- `isGreatest_spectralTop`
- `log_derivative_integral_norm_chain`
- `log_exp_I_mul`
- `log_product_rule_eq_sandwich`
- `norm_adL_apply_le_twice`
- `norm_center_lt_pi_of_open_turn`
- `norm_chord_endpoint_eq_sqrt`
- `norm_log_sandwich_integral_le`
- `rounded_clock_half_distance`
- `rounded_clock_nearest`
- `sin_sq_half_le_sin_sq_half`
- `tendsto_frameBound_half_width`
- `tendsto_scaled_cot_half_width`
- `unit_rhs_le_step_polynomial`
- `unit_rhs_uniform_step_limit`
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory UnitaryProducts.Corrector
open scoped Topology Matrix.Norms.L2Operator

noncomputable section

namespace UnitaryProducts.Prose

/-- Section 4, the logarithm lemma: a neighborhood with half the omitted-arc length as margin. -/
theorem eventually_window_in_principal_turn {a : ℝ → ℝ} {s₀ θ : ℝ} {S : Set ℝ}
    (ha : ContinuousWithinAt a S s₀) (hθ : 0 < θ) :
    ∀ᶠ s in 𝓝[S] s₀, |a s - a s₀| < θ / 2 ∧
      ∀ x ∈ Icc (a s) (a s + (2 * π - θ)),
        x - (a s₀ + (2 * π - θ) / 2) ∈ Ioo (-π) π := by
  have he : ∀ᶠ s in 𝓝[S] s₀, |a s - a s₀| < θ / 2 := by
    have ht := (ha.sub (continuousWithinAt_const (b := a s₀))).abs
    have hl := ht.eventually (gt_mem_nhds (show |a s₀ - a s₀| < θ / 2 by
      simpa using half_pos hθ))
    exact hl
  filter_upwards [he] with s hs
  refine ⟨hs, fun x hx ↦ ?_⟩
  obtain ⟨hl, hr⟩ := abs_lt.mp hs
  constructor <;> linarith [hx.1, hx.2]

/-- Section 4, proof of the logarithm lemma: the principal scalar logarithm on the open turn. -/
theorem log_exp_I_mul {θ : ℝ} (hθ : |θ| < π) :
    Complex.log (Complex.exp (I * (θ : ℂ))) = I * (θ : ℂ) := by
  apply Complex.log_exp
  · simpa using (abs_lt.mp hθ).1
  · simpa using (abs_lt.mp hθ).2.le

/-- Section 4, derivative of the denominator immediately after the logarithm integral. -/
theorem hasDerivAt_log_denominator {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {V : ℝ → A} {D : A} {s u : ℝ} (hV : HasDerivAt V D s) :
    HasDerivAt (fun r ↦ 1 + u • (V r - 1)) (u • D) s :=
  ((hV.sub_const 1).const_smul u).const_add 1

/-- Section 4, proof of the logarithm lemma: compact two-variable resolvent bound. -/
theorem bounded_walkLogResolvent {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {V : ℝ → A} {S : Set ℝ} (hS : IsCompact S)
    (hV : ContinuousOn V S)
    (hu : ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ∃ C : ℝ, ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, ‖walkLogResolvent (V s) u‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hS.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_walkLogResolvent hV hu)
  exact ⟨C, fun s hs u hu ↦ hC (s, u) ⟨hs, hu⟩⟩

/-- Section 4, first-derivative integral: the unsimplified product rule equals the sandwich. -/
theorem log_product_rule_eq_sandwich {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (V D : A) (u : ℝ) (hu : IsUnit (1 + u • (V - 1))) :
    D * walkLogResolvent V u + (V - 1) *
      (-u • (walkLogResolvent V u * D * walkLogResolvent V u)) =
      walkLogResolvent V u * D * walkLogResolvent V u := by
  let Z := walkLogResolvent V u
  have hsum : Z + u • ((V - 1) * Z) = 1 := by
    calc
      _ = (1 + u • (V - 1)) * Z := by rw [add_mul, one_mul, smul_mul_assoc]
      _ = 1 := Ring.mul_inverse_cancel _ hu
  have hid : Z = 1 - u • ((V - 1) * Z) := eq_sub_iff_add_eq.mpr hsum
  change D * Z + (V - 1) * (-u • (Z * D * Z)) = Z * D * Z
  calc
    _ = (1 - u • ((V - 1) * Z)) * D * Z := by
      simp only [sub_eq_add_neg, add_mul, neg_mul, one_mul, smul_mul_assoc,
        mul_smul_comm, neg_smul, mul_neg, mul_assoc]
    _ = _ := by rw [← hid]

/-- Section 4, cotangent reflection as the complementary open-arc length tends to zero. -/
theorem cot_half_width_reflect (θ : ℝ) :
    Real.cot ((2 * π - θ) / 2) = -Real.cot (θ / 2) := by
  rw [show (2 * π - θ) / 2 = π - θ / 2 by ring]
  simp [Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- Section 4, the bounded half-width term tends to `N(π)`. -/
theorem tendsto_frameBound_half_width :
    Tendsto (fun θ : ℝ ↦ frameBound ((2 * π - θ) / 2)) (𝓝[>] 0)
      (𝓝 (frameBound π)) := by
  have hc := (hasDerivAt_frameBound (x := π)
    (by rw [abs_of_pos pi_pos]; linarith [pi_pos])).continuousAt
  apply hc.tendsto.comp
  have he : (2 * π - (0 : ℝ)) / 2 = π := by ring
  have hw : Tendsto (fun θ : ℝ ↦ 2 * π - θ) (𝓝[>] 0) (𝓝 (2 * π - 0)) :=
    tendsto_const_nhds.sub nhdsWithin_le_nhds
  simpa only [he] using hw.div_const 2

/-- Section 5, rounding the clock: distance to the chosen integer is at most one half. -/
theorem rounded_clock_half_distance (x : ℝ) :
    |x - (⌊x + 1 / 2⌋ : ℤ)| ≤ 1 / 2 := by
  have hl := Int.floor_le (x + 1 / 2)
  have hr := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

section Blocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end Blocks

section Spectral

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, the first equality in the resolvent maximum display: normality gives an
attained spectral maximum, not merely an upper bound. -/
theorem isGreatest_norm_walkLogResolvent (V : 𝕄) [IsStarNormal V]
    (hV : spectrum ℂ V ⊆ Complex.slitPlane) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    IsGreatest ((fun z : ℂ ↦ ‖(1 + u • (z - 1))⁻¹‖) '' spectrum ℂ V)
      ‖walkLogResolvent V u‖ := by
  have hn : ∀ z ∈ spectrum ℂ V, 1 + u • (z - 1) ≠ 0 :=
    fun z hz ↦ chord_ne_zero_of_slitPlane (hV hz) hu
  have he : cfc (fun z : ℂ ↦ (1 + u • (z - 1))⁻¹) V = walkLogResolvent V u := by
    rw [cfc_inv (p := IsStarNormal) (fun z : ℂ ↦ 1 + u • (z - 1)) V hn
      (by fun_prop) inferInstance, cfc_unit_chord]
    rfl
  rw [← he]
  exact IsGreatest.norm_cfc (p := IsStarNormal) _ V
    ((by fun_prop : ContinuousOn (fun z : ℂ ↦ 1 + u • (z - 1))
      (spectrum ℂ V)).inv₀ hn) inferInstance

end Spectral

section MatrixPaths

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end MatrixPaths

/-- Proof of Lemma A.2, the warrant for the resolvent display: `sin²(φ/2) ≤ sin²(ψ/2)` for
`0 ≤ φ ≤ ψ ≤ π`; the paper applies it at `|φ| ≤ w/2`, where `sin²(ψ/2) = sin²(w/4)`. -/
theorem sin_sq_half_le_sin_sq_half {φ ψ : ℝ} (hφ : 0 ≤ φ) (hφψ : φ ≤ ψ) (hψ : ψ ≤ π) :
    Real.sin (φ / 2) ^ 2 ≤ Real.sin (ψ / 2) ^ 2 := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hφ hψ hφψ
  have hcφ := Real.cos_two_mul (φ / 2)
  have hcψ := Real.cos_two_mul (ψ / 2)
  have hsφ := Real.sin_sq_add_cos_sq (φ / 2)
  have hsψ := Real.sin_sq_add_cos_sq (ψ / 2)
  rw [show 2 * (φ / 2) = φ by ring] at hcφ
  rw [show 2 * (ψ / 2) = ψ by ring] at hcψ
  linarith

/-- Section 4, the scalar chord square is decreasing with the absolute angle on `[0,π]`. -/
theorem chord_square_antitone {u φ ψ : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hφ : 0 ≤ φ) (hφψ : φ ≤ ψ) (hψ : ψ ≤ π) :
    1 - 4 * u * (1 - u) * Real.sin (ψ / 2) ^ 2 ≤
      1 - 4 * u * (1 - u) * Real.sin (φ / 2) ^ 2 := by
  have hs := sin_sq_half_le_sin_sq_half hφ hφψ hψ
  have hm : 0 ≤ 4 * u * (1 - u) :=
    mul_nonneg (mul_nonneg (by norm_num) hu.1) (sub_nonneg.mpr hu.2)
  linarith [mul_le_mul_of_nonneg_left hs hm]

/-- Section 4, the scalar maximum over the phase interval in the resolvent display. -/
theorem isGreatest_inv_chord_phase {w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    IsGreatest ((fun φ : ℝ ↦ ‖(1 + u • (Complex.exp ((φ : ℂ) * I) - 1))⁻¹‖) ''
      Icc (-w / 2) (w / 2))
      (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ := by
  have hc : -1 < Real.cos (w / 2) := by
    simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith : 0 ≤ w / 2) le_rfl (by linarith : w / 2 < π)
  have hre (φ : ℝ) : (Complex.exp ((φ : ℂ) * I)).re = Real.cos φ := by
    simp [Complex.exp_re]
  constructor
  · refine ⟨w / 2, ⟨by linarith, le_rfl⟩, ?_⟩
    have he := norm_sq_unit_chord (Complex.exp (((w / 2 : ℝ) : ℂ) * I))
      (Complex.norm_exp_ofReal_mul_I _) u
    rw [hre] at he
    have hn : ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖ =
        Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))) := by
      rw [← he, Real.sqrt_sq (norm_nonneg _)]
    dsimp only
    rw [norm_inv, hn]
  · rintro _ ⟨φ, hφ, rfl⟩
    apply norm_inv_unit_chord_le (Complex.norm_exp_ofReal_mul_I φ) hc
      (Real.cos_le_one _) hu
    rw [hre]
    have ha : |φ| ≤ w / 2 := abs_le.mpr ⟨by linarith [hφ.1], hφ.2⟩
    simpa only [Real.cos_abs] using Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg φ) (by linarith : w / 2 ≤ π) ha


/-- Section 5, the one-size scalar comparison bound is uniformly bounded in total time
by a polynomial in the step length, using `N ≥ 2`. -/
theorem unit_rhs_le_step_polynomial {T N A B h : ℝ} (hT : 0 < T) (hN : 2 ≤ N)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) :
    T / N ^ 2 * (A * h + B * T * h ^ 2 / N) ≤
      (A * h * (T / N) + B * h ^ 2 * (T / N) ^ 2) / 2 := by
  have hNp : 0 < N := by linarith
  have he : T / N ^ 2 * (A * h + B * T * h ^ 2 / N) =
      (A * h * (T / N) + B * h ^ 2 * (T / N) ^ 2) / N := by field_simp
  rw [he]
  apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hN

/-- Section 5, uniform-in-time vanishing of the scalar comparison bound with step length. -/
theorem unit_rhs_uniform_step_limit {A B h : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h) :
    ∀ ε > 0, ∃ δ > 0, ∀ T N : ℝ, 0 < T → 2 ≤ N → T / N < δ →
      T / N ^ 2 * (A * h + B * T * h ^ 2 / N) < ε := by
  intro ε hε
  let K := A * h + B * h ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨min 1 (ε / K), lt_min one_pos (div_pos hε hK), ?_⟩
  intro T N hT hN hδ
  have hNp : 0 < N := by linarith
  have hd0 : 0 < T / N := div_pos hT hNp
  have hd1 : T / N < 1 := lt_of_lt_of_le hδ (min_le_left _ _)
  have hdε : T / N < ε / K := lt_of_lt_of_le hδ (min_le_right _ _)
  have hdε' : K * (T / N) < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hK).mp hdε
  have hs : (T / N) ^ 2 ≤ T / N := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hd1.le hd0.le
  have hpow := mul_le_mul_of_nonneg_left hs (mul_nonneg hB (sq_nonneg h))
  have he := unit_rhs_le_step_polynomial hT hN hA hB hh
  dsimp [K] at hdε'
  linarith

/-- Section 4, the principal open turn maps into the slit plane. -/
theorem exp_neg_I_mem_slitPlane {φ : ℝ} (hφ : φ ∈ Ioo (-π) π) :
    Complex.exp (-I * (φ : ℂ)) ∈ Complex.slitPlane := by
  have hangle : |(-φ) - 0| < π := by
    rw [sub_zero, abs_neg]
    exact abs_lt.mpr hφ
  have hh := exp_mul_I_mem_argDomain hangle
  have he : -I * (φ : ℂ) = ((-φ : ℝ) : ℂ) * I := by push_cast; ring
  rw [he]
  simpa only [argDomain, neg_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Set.mem_setOf_eq] using hh

/-- Section 4, freezing the center: half the omitted-arc length as margin puts every phase
in the principal turn, whose exponential avoids the logarithmic cut. -/
theorem eventually_window_avoids_cut {a : ℝ → ℝ} {s₀ θ : ℝ} {S : Set ℝ}
    (ha : ContinuousWithinAt a S s₀) (hθ : 0 < θ) :
    ∀ᶠ s in 𝓝[S] s₀, |a s - a s₀| < θ / 2 ∧
      ∀ x ∈ Icc (a s) (a s + (2 * π - θ)),
        x - (a s₀ + (2 * π - θ) / 2) ∈ Ioo (-π) π ∧
        Complex.exp (-I * ((x - (a s₀ + (2 * π - θ) / 2) : ℝ) : ℂ)) ∈
          Complex.slitPlane := by
  filter_upwards [eventually_window_in_principal_turn ha hθ] with s hs
  exact ⟨hs.1, fun x hx ↦ ⟨hs.2 x hx, exp_neg_I_mem_slitPlane (hs.2 x hx)⟩⟩

/-- Section 4, the cotangent term has a simple pole as the omitted-arc length tends to zero. -/
theorem tendsto_scaled_cot_half_width :
    Tendsto (fun θ : ℝ ↦ θ * Real.cot ((2 * π - θ) / 2)) (𝓝[>] 0) (𝓝 (-2)) := by
  have hc : ContinuousAt (fun θ : ℝ ↦
      -2 * Real.cos (θ / 2) / Real.sinc (θ / 2)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · exact Real.continuous_sinc.continuousAt.comp (by fun_prop)
    · simp
  have hl : Tendsto (fun θ : ℝ ↦ -2 * Real.cos (θ / 2) / Real.sinc (θ / 2))
      (𝓝[>] 0) (𝓝 (-2)) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hn : θ ≠ 0 := ne_of_gt hθ
  rw [cot_half_width_reflect, Real.cot_eq_cos_div_sin,
    Real.sinc_of_ne_zero (div_ne_zero hn two_ne_zero)]
  field_simp

/-- Section 5, nearest-sample characterization of the rounded clock, including ties. -/
theorem rounded_clock_nearest (x : ℝ) (j : ℤ) :
    |x - (⌊x + 1 / 2⌋ : ℤ)| ≤ |x - j| := by
  simpa only [round_eq] using round_le x j

section OpenTurn

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, uniqueness in an open turn: finite spectrum gives a strictly smaller
closed centered ball, although no uniform margin was assumed. -/
theorem norm_center_lt_pi_of_open_turn {H : 𝕄} (hH : H.IsHermitian) {α : ℝ}
    (hev : ∀ i, hH.eigenvalues i ∈ Ioo α (α + 2 * π)) :
    ‖H - ((α + π : ℝ) : ℂ) • 1‖ < π := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ |hH.eigenvalues i - (α + π)|) Finset.univ_nonempty
  let r := |hH.eigenvalues i - (α + π)|
  have hr : r < π := by
    apply abs_lt.mpr
    constructor <;> linarith [(hev i).1, (hev i).2]
  have hbound := norm_sub_smul_one_le_of_eigenvalues hH (m := α + π - r) (w := 2 * r)
    (by dsimp [r]; positivity) (fun j ↦ ?_)
  · rw [show α + π - r + 2 * r / 2 = α + π by ring] at hbound
    exact hbound.trans_lt (by linarith)
  · have hj := abs_le.mp (hi j (Finset.mem_univ j))
    constructor <;> dsimp [r] at * <;> linarith [hj.1, hj.2]

end OpenTurn

section OpenTurnExistence

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, the norm description of a centered open turn implies its spectral description. -/
theorem eigenvalues_mem_open_turn_of_norm {H : 𝕄} (hH : H.IsHermitian) {α : ℝ}
    (hn : ‖H - ((α + π : ℝ) : ℂ) • 1‖ < π) :
    ∀ i, hH.eigenvalues i ∈ Ioo α (α + 2 * π) := by
  intro i
  have hm : (hH.eigenvalues i : ℂ) ∈ spectrum ℂ H := by
    rw [hH.spectrum_eq_image_range]
    exact ⟨hH.eigenvalues i, ⟨i, rfl⟩, rfl⟩
  have hmem : (hH.eigenvalues i : ℂ) - ((α + π : ℝ) : ℂ) ∈
      spectrum ℂ (H - algebraMap ℂ 𝕄 ((α + π : ℝ) : ℂ)) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hm rfl
  have hb := spectrum.norm_le_norm_of_mem hmem
  rw [Algebra.algebraMap_eq_smul_one] at hb
  have he : ‖(hH.eigenvalues i : ℂ) - ((α + π : ℝ) : ℂ)‖ =
      |hH.eigenvalues i - (α + π)| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he] at hb
  have hh := abs_lt.mp (hb.trans_lt hn)
  constructor <;> linarith [hh.1, hh.2]

end OpenTurnExistence


/-- Section 4, the endpoint chord has exactly the scalar radius used in the maximum display. -/
theorem norm_chord_endpoint_eq_sqrt (w u : ℝ) :
    ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖ =
      Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))) := by
  have he := norm_sq_unit_chord (Complex.exp (((w / 2 : ℝ) : ℂ) * I))
    (Complex.norm_exp_ofReal_mul_I _) u
  have hre : (Complex.exp (((w / 2 : ℝ) : ℂ) * I)).re = Real.cos (w / 2) := by
    simp [Complex.exp_re]
  rw [hre] at he
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

/-- Section 4, the last maximum in the resolvent display is exactly `1/r_u`.
Changing the sign of the phase does not change its symmetric allowed interval. -/
theorem isGreatest_inv_chord_phase_radius {w u : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    IsGreatest ((fun φ : ℝ ↦ ‖(1 + u • (Complex.exp ((φ : ℂ) * I) - 1))⁻¹‖) ''
      Icc (-w / 2) (w / 2))
      (1 / ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖) := by
  rw [norm_chord_endpoint_eq_sqrt, one_div]
  exact isGreatest_inv_chord_phase hw0 hw hu

/-- Appendix A, the operator identity `N(ad Ω)(D) = ∑ νₙ ad_Ωⁿ(D)`,
with coefficients obtained from the cotangent partial fractions. -/
theorem frameOp_eq_positive_series {d : ℕ} [NeZero d]
    (H D : Matrix (Fin d) (Fin d) ℂ) (hw : ‖adL H‖ < 2 * π) :
    frameOp H D = ∑' n : ℕ, (frameCoeff n : ℂ) • (adL H ^ n) D := by
  unfold frameOp positiveFrameSeries
  have hs := (summable_norm_positiveFrameSeries (adL H) hw).of_norm
  rw [tsum_apply_of_summable hs]
  simp only [ContinuousLinearMap.smul_apply]


section LocalOpenTurn

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, transfer paragraph: `-spectralBottom (-A)` is the largest eigenvalue. -/
theorem isGreatest_spectralTop {A : 𝕄} (hA : A.IsHermitian) :
    IsGreatest (spectrum ℝ A) (-spectralBottom (-A)) := by
  have hl := isLeast_spectralBottom hA.neg
  have hm : -spectralBottom (-A) ∈ spectrum ℝ A := by
    have := hl.1
    rw [← spectrum.neg_eq] at this
    simpa using this
  refine ⟨hm, fun x hx ↦ ?_⟩
  have hx' : -x ∈ spectrum ℝ (-A) := by
    rw [← spectrum.neg_eq]
    simpa using hx
  have := hl.2 hx'
  linarith

end LocalOpenTurn

section BlockSeries

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end BlockSeries

section LocalResolvent

attribute [local instance] matrixCStarAlgebra
open UnitaryProducts.Paper
open scoped Pointwise
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 4, immediately after the logarithm integral: freezing the center of the
walk's moving spectral window gives a resolvent bound uniform in `s` and `u`, on a
closed relative neighborhood (including endpoints of the walk). -/
theorem exists_uniform_walkLogResolvent_bound (a : ℝ → ℝ) (w : ℝ) (W : ℝ → 𝕄)
    (hw : w < 2 * π) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hW : ContinuousOn W (Icc (0 : ℝ) 1)) (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ x ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (x : ℂ)))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, |s - s₀| ≤ δ →
      spectrum ℂ (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s) ⊆
        Complex.slitPlane ∧
      ∀ u ∈ Icc (0 : ℝ) 1,
        ‖walkLogResolvent (Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ)) • W s) u‖ ≤ C := by
  let z := Complex.exp (I * ((a s₀ + w / 2 : ℝ) : ℂ))
  let V : ℝ → 𝕄 := fun s ↦ z • W s
  have hev := eventually_window_avoids_cut (ha s₀ hs₀)
    (show 0 < 2 * π - w by linarith)
  simp only [sub_sub_cancel] at hev
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhdsWithin_iff.mp hev
  let K := Icc (0 : ℝ) 1 ∩ Icc (s₀ - ε / 2) (s₀ + ε / 2)
  have hphase (s : ℝ) (hs : s ∈ K) : spectrum ℂ (V s) ⊆ Complex.slitPlane := by
    have hd : dist s s₀ < ε := by
      rw [Real.dist_eq]
      have hb : |s - s₀| ≤ ε / 2 := abs_le.mpr
        ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
      linarith
    have ht := (he ⟨hd, hs.1⟩).2
    intro q hq
    rw [show V s = z • W s from rfl,
      spectrum.smul_eq_smul z (W s) (spectrum.nonempty _)] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨x, hx, rfl⟩ := harc s hs.1 y hy
    have hex : z • Complex.exp (-I * (x : ℂ)) =
        Complex.exp (-I * ((x - (a s₀ + w / 2) : ℝ) : ℂ)) := by
      rw [smul_eq_mul, ← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    change z • Complex.exp (-I * (x : ℂ)) ∈ Complex.slitPlane
    rw [hex]
    exact (ht x hx).2
  have hn (s : ℝ) (hs : s ∈ K) : IsStarNormal (V s) := by
    have hz : z ∈ unitary ℂ := by
      apply Unitary.mem_iff_star_mul_self.mpr
      change (starRingEnd ℂ) z * z = 1
      rw [Complex.conj_mul']
      dsimp [z]
      rw [Complex.norm_exp_I_mul_ofReal]
      norm_num
    have hv := Unitary.smul_mem_of_mem hz
      (Matrix.mem_unitaryGroup_iff'.mpr (hunit s hs.1))
    exact ⟨hv.1.trans hv.2.symm⟩
  have hu : ∀ s ∈ K, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1)) := by
    intro s hs u hu
    letI := hn s hs
    rw [← cfc_unit_chord (V s) u]
    apply isUnit_cfc (p := IsStarNormal) (fun q : ℂ ↦ 1 + u • (q - 1)) (V s)
      (by fun_prop) (hn s hs)
    exact fun q hq ↦ chord_ne_zero_of_slitPlane (hphase s hs hq) hu
  obtain ⟨C, hC⟩ := bounded_walkLogResolvent
    (isCompact_Icc.inter isCompact_Icc)
    ((continuousOn_const.smul hW).mono (show K ⊆ Icc (0 : ℝ) 1 from inter_subset_left)) hu
  refine ⟨ε / 2, half_pos hε, C, fun s hs hd ↦ ?_⟩
  have hsK : s ∈ K := ⟨hs, by
    have hb := abs_le.mp hd
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩⟩
  exact ⟨hphase s hsK, hC s hsK⟩

end LocalResolvent

section WalkDiagonalBound

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- Section 4, the commutator norm estimate used in every three-link term. -/
theorem norm_adL_apply_le_twice (D X : 𝕄) : ‖adL D X‖ ≤ 2 * ‖D‖ * ‖X‖ := by
  simpa only [zero_smul, sub_zero] using norm_adL_apply_le D X 0

end WalkDiagonalBound

section TermwiseDerivative

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end TermwiseDerivative

section ThreeRows

open UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end ThreeRows

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Proof of the spectral comparison, the second inequality of its display: for `θ ≤ φ ≤ θ + 2π`,
the
integer minimum `min_k |θ - φ + 2πk|` is at most `min {φ - θ, 2π - (φ - θ)}`, from `k = 0`
and `k = 1`. -/
theorem circular_phase_inf_le_min {θ φ : ℝ} (hθφ : θ ≤ φ) (hφθ : φ - θ ≤ 2 * π) :
    sInf (Set.range (fun k : ℤ ↦ |θ - φ + 2 * π * k|)) ≤ min (φ - θ) (2 * π - (φ - θ)) := by
  have hb : BddBelow (Set.range (fun k : ℤ ↦ |θ - φ + 2 * π * k|)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact abs_nonneg _⟩
  refine le_min ?_ ?_
  · have h := csInf_le hb (mem_range_self (f := fun k : ℤ ↦ |θ - φ + 2 * π * k|) 0)
    rw [Int.cast_zero, mul_zero, add_zero, abs_of_nonpos (by linarith)] at h
    linarith
  · have h := csInf_le hb (mem_range_self (f := fun k : ℤ ↦ |θ - φ + 2 * π * k|) 1)
    rw [Int.cast_one, mul_one, abs_of_nonneg (by linarith)] at h
    linarith


/-- Section 4, the logarithm in an open turn is unique under precisely the open-turn
spectral hypotheses, with no preassigned closed-window margin. -/
theorem eq_of_evol_eq_open_turn {H K : 𝕄} (hH : H.IsHermitian) (hK : K.IsHermitian)
    {α : ℝ} (hevH : ∀ i, hH.eigenvalues i ∈ Ioo α (α + 2 * π))
    (hevK : ∀ i, hK.eigenvalues i ∈ Ioo α (α + 2 * π))
    (he : evol H 1 = evol K 1) : H = K := by
  have hnH := norm_center_lt_pi_of_open_turn hH hevH
  have hnK := norm_center_lt_pi_of_open_turn hK hevK
  apply eq_of_evol_eq (α := -(α + π))
    (r := max ‖H - ((α + π : ℝ) : ℂ) • 1‖ ‖K - ((α + π : ℝ) : ℂ) • 1‖)
    (max_lt hnH hnK) hH ?_ hK ?_ he
  · simpa only [neg_neg] using le_max_left
      ‖H - ((α + π : ℝ) : ℂ) • 1‖ ‖K - ((α + π : ℝ) : ℂ) • 1‖
  · simpa only [neg_neg] using le_max_right
      ‖H - ((α + π : ℝ) : ℂ) • 1‖ ‖K - ((α + π : ℝ) : ℂ) • 1‖


/-- Section 4, a nonspectral lower endpoint determines exactly one Hermitian logarithm
with spectrum in the open turn. -/
theorem existsUnique_log_open_turn (W : unitary 𝕄) (α : ℝ)
    (hcut : Complex.exp (-I * (α : ℂ)) ∉ spectrum ℂ (W : 𝕄)) :
    ∃! H : 𝕄, ∃ hH : H.IsHermitian,
      (∀ i, hH.eigenvalues i ∈ Ioo α (α + 2 * π)) ∧ evol H 1 = (W : 𝕄) := by
  obtain ⟨G, _, hG, hlog⟩ := continuous_log_of_cut (fun _ : Unit ↦ W) (fun _ ↦ α)
    continuous_const continuous_const (fun _ ↦ hcut)
  refine ⟨G (), ⟨hG (), eigenvalues_mem_open_turn_of_norm (hG ()) (hlog ()).2,
    (hlog ()).1⟩, ?_⟩
  rintro K ⟨hK, hev, he⟩
  exact eq_of_evol_eq_open_turn hK (hG ()) hev
    (eigenvalues_mem_open_turn_of_norm (hG ()) (hlog ()).2) (he.trans (hlog ()).1.symm)


/-- Section 4, transfer paragraph: nonempty band and complementary arc imply
`l < β < r`, for the logarithm whose spectrum lies in the open turn. -/
theorem spectral_extrema_straddle_cut {A U : 𝕄} (hA : A.IsHermitian) {α β : ℝ}
    (hU : spectrum ℂ U = (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ A)
    (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π)) (hβ : β < α + 2 * π)
    (hband : ∃ θ ∈ Ioo α β, Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U)
    (hcomp : ∃ θ ∈ Ioo β (α + 2 * π),
      Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U) :
    spectralBottom A < β ∧ β < -spectralBottom (-A) := by
  obtain ⟨b, hb, hbs⟩ := hband
  obtain ⟨c, hc, hcs⟩ := hcomp
  have hphase : ∀ θ ∈ Ioo α (α + 2 * π),
      Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ U → θ ∈ spectrum ℝ A := by
    intro θ hθ hs
    rw [hU] at hs
    obtain ⟨x, hx, hex⟩ := hs
    exact (Paper.phase_inj (hopen x hx) hθ hex) ▸ hx
  exact ⟨((isLeast_spectralBottom hA).2
    (hphase b ⟨hb.1, hb.2.trans hβ⟩ hbs)).trans_lt hb.2,
    hc.1.trans_le ((isGreatest_spectralTop hA).2
      (hphase c ⟨hb.1.trans (hb.2.trans hc.1), hc.2⟩ hcs))⟩

end UnitaryProducts.Prose
