/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.JacobiTelescope
public import RoundedClocks.Preliminaries.PiecewiseEvolution

/-! # Lemma A.3: Duhamel's formula for `(e^{-iΩ})'`

The proof of Lemma A.3 uses Duhamel's formula
`(e^{-iΩ})' = -i∫₀¹ e^{-iσΩ} Ω' e^{-i(1-σ)Ω} dσ` without proof. This file proves it: the map
`X ↦ e^{-iX}` is differentiable at a Hermitian `X₀`, with derivative
`E ↦ -i∫₀¹ e^{-i(1-u)X₀} E e^{-iuX₀} du`. Here `evol G u` is `e^{-iuG}` and `evolDeriv X₀` is that
derivative.
-/

@[expose] public section
noncomputable section
open NormedSpace Complex Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace RoundedClocks.EndValue
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `evol G u` is `e^{-iuG}`. -/
abbrev evol (G : 𝕄) (u : ℝ) : 𝕄 := frozenEvolution G u

/-- `e^{-i0G} = 1`. -/
theorem evol_zero (G : 𝕄) : evol G 0 = 1 := by simp [evol, frozenEvolution]

/-- `e^{-i(u+v)G} = e^{-iuG} e^{-ivG}`. -/
theorem evol_add (G : 𝕄) (u v : ℝ) : evol G (u + v) = evol G u * evol G v := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol, frozenEvolution, add_smul]
  exact exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)

/-- `(e^{-iuG})' = -iG e^{-iuG}`, the derivative in `u`. -/
theorem hasDerivAt_evol (G : 𝕄) (u : ℝ) :
    HasDerivAt (evol G) ((-I • G) * evol G u) u :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) _ _

/-- `-iG` commutes with `e^{-iuG}`. -/
theorem commute_evol (G : 𝕄) (u : ℝ) : Commute (-I • G) (evol G u) :=
  ((Commute.refl (-I • G)).smul_right (u : ℝ)).exp_right

/-- `‖e^{-iuG}‖ ≤ 1` for Hermitian `G`. -/
theorem norm_evol_le {G : 𝕄} (hG : G.IsHermitian) (u : ℝ) : ‖evol G u‖ ≤ 1 :=
  unitary_norm_le_one (by simpa only [evol, frozenEvolution, Complex.coe_smul] using
    exp_neg_I_smul_isUnitary hG u)

/-- `u ↦ e^{-iuG}` is continuous. -/
theorem continuous_evol (G : 𝕄) : Continuous (evol G) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_evol G u).continuousAt

/-- Duhamel's formula for two constant matrices:
`e^{-iA} - e^{-iB} = -i∫₀¹ e^{-i(1-u)A} (A - B) e^{-iuB} du`. -/
theorem evol_sub_evol (A B : 𝕄) :
    evol A 1 - evol B 1 = -I • ∫ u in (0:ℝ)..1, evol A (1 - u) * (A - B) * evol B u := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ ↦ evol A (1 - u) * evol B u)
      (evol A (1 - u) * (I • (A - B)) * evol B u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ ↦ evol A (1 - u)) (-((-I • A) * evol A (1 - u))) u := by
      simpa [Function.comp_def] using
        (hasDerivAt_evol A (1 - u)).scomp u ((hasDerivAt_id u).const_sub 1)
    convert h1.mul (hasDerivAt_evol B u) using 1
    rw [(commute_evol A (1 - u)).eq]
    simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_smul, neg_mul,
      mul_neg, neg_neg, mul_assoc]
    abel
  have hcont : Continuous (fun u : ℝ ↦ evol A (1 - u) * (I • (A - B)) * evol B u) := by
    exact (((continuous_evol A).comp (continuous_const.sub continuous_id)).mul
      continuous_const).mul (continuous_evol B)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ ↦
      evol A (1 - u) * evol B u) (fun u _ ↦ hderiv u) (hcont.intervalIntegrable 0 1)
  have hsmul : (∫ u in (0:ℝ)..1, evol A (1 - u) * (I • (A - B)) * evol B u)
      = I • ∫ u in (0:ℝ)..1, evol A (1 - u) * (A - B) * evol B u := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr fun u _ ↦ by simp
  rw [hsmul] at hFTC
  simp only [sub_self, sub_zero, evol_zero, one_mul, mul_one] at hFTC
  rw [neg_smul, hFTC, neg_sub]

/-- `u ↦ e^{-i(1-u)B} E e^{-iuB}` is continuous. -/
theorem continuous_integrand (B E : 𝕄) :
    Continuous (fun u : ℝ ↦ evol B (1 - u) * E * evol B u) :=
  (((continuous_evol B).comp (continuous_const.sub continuous_id)).mul
    continuous_const).mul (continuous_evol B)

/-- The derivative of `X ↦ e^{-iX}` at `B`, as a linear map: `E ↦ -i∫₀¹ e^{-i(1-u)B} E e^{-iuB} du`.
-/
def evolDeriv (B : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun E ↦ -I • ∫ u in (0 : ℝ)..1, evol B (1 - u) * E * evol B u
      map_add' := by
        intro E F
        simp only [mul_add, add_mul]
        rw [intervalIntegral.integral_add
          ((continuous_integrand B E).intervalIntegrable 0 1)
          ((continuous_integrand B F).intervalIntegrable 0 1), smul_add]
      map_smul' := by
        intro c E
        simp only [mul_smul_comm, smul_mul_assoc, intervalIntegral.integral_smul]
        exact smul_comm _ _ _ }

/-- `evolDeriv B E = -i∫₀¹ e^{-i(1-u)B} E e^{-iuB} du`. -/
theorem evolDeriv_apply (B E : 𝕄) :
    evolDeriv B E = -I • ∫ u in (0 : ℝ)..1, evol B (1 - u) * E * evol B u := rfl

/-- `‖∫_a^t f‖ ≤ C (t - a)` when `‖f‖ ≤ C` on `[a,t]`. -/
theorem norm_intervalIntegral_le {f : ℝ → 𝕄} {a t C : ℝ} (hat : a ≤ t)
    (h : ∀ s ∈ Icc a t, ‖f s‖ ≤ C) : ‖∫ s in a..t, f s‖ ≤ C * (t - a) := by
  simpa [abs_of_nonneg (sub_nonneg.mpr hat)] using
    intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := a) (b := t) (C := C)
      fun s hs ↦ h s (Ioc_subset_Icc_self (by rwa [uIoc_of_le hat] at hs))

/-- The remainder in Duhamel's formula: if `‖e^{-ivA} - e^{-ivB}‖ ≤ Q` for `0 ≤ v ≤ 1` and `B` is
Hermitian, then `‖e^{-iA} - e^{-iB} + i∫₀¹ e^{-i(1-u)B} (A - B) e^{-iuB} du‖ ≤ Q ‖A - B‖`. -/
theorem norm_evol_duhamel_two_le [NeZero d] {A B : 𝕄} {Q : ℝ} (hB : B.IsHermitian)
    (hQ : ∀ v ∈ Icc (0 : ℝ) 1, ‖evol A v - evol B v‖ ≤ Q) :
    ‖evol A 1 - evol B 1 +
      I • (∫ u in (0:ℝ)..1, evol B (1 - u) * (A - B) * evol B u)‖ ≤ Q * ‖A - B‖ := by
  have hAB := evol_sub_evol A B
  have hint (C : 𝕄) : IntervalIntegrable (fun u : ℝ ↦ evol C (1 - u) * (A - B) * evol B u)
      volume 0 1 :=
    ((((continuous_evol C).comp (continuous_const.sub continuous_id))).mul
      continuous_const).mul (continuous_evol B) |>.intervalIntegrable 0 1
  have hkey : evol A 1 - evol B 1 + I • (∫ u in (0:ℝ)..1, evol B (1 - u) * (A - B) * evol B u)
      = -I • ∫ u in (0:ℝ)..1,
          (evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u := by
    rw [hAB, show (∫ u in (0:ℝ)..1, (evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u)
        = (∫ u in (0:ℝ)..1, evol A (1 - u) * (A - B) * evol B u)
          - ∫ u in (0:ℝ)..1, evol B (1 - u) * (A - B) * evol B u by
      rw [← intervalIntegral.integral_sub (hint A) (hint B)]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      simp [sub_mul]]
    module
  rw [hkey, norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg _) (hQ 0 ⟨le_rfl, zero_le_one⟩)
  have hb : ‖∫ u in (0:ℝ)..1, (evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u‖
      ≤ (Q * ‖A - B‖) * (1 - 0) := by
    refine norm_intervalIntegral_le zero_le_one fun u hu ↦ ?_
    have hu' : (1 - u) ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    calc ‖(evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u‖
        ≤ ‖evol A (1 - u) - evol B (1 - u)‖ * ‖A - B‖ * ‖evol B u‖ := norm_mul₃_le
      _ ≤ Q * ‖A - B‖ * 1 := by gcongr; exacts [hQ _ hu', norm_evol_le hB u]
      _ = Q * ‖A - B‖ := mul_one _
  simpa using hb

/-- For `X` within distance `1` of `X₀` and `0 ≤ v ≤ 1`, `‖e^{-ivX} - e^{-ivX₀}‖ ≤ K ‖X - X₀‖` with
one constant `K`, as the exponential is continuously differentiable. -/
theorem evol_lipschitz_on_ball (X₀ : 𝕄) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : 𝕄, ‖X - X₀‖ ≤ 1 →
      ∀ v ∈ Icc (0 : ℝ) 1, ‖evol X v - evol X₀ v‖ ≤ K * ‖X - X₀‖ := by
  have hc : ContDiff ℝ 1 (exp : 𝕄 → 𝕄) := contDiff_iff_contDiffAt.mpr fun X ↦
    (NormedSpace.exp_analytic (𝕂 := ℂ) X).contDiffAt.restrict_scalars ℝ
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : 𝕄) (‖X₀‖ + 1)) (isCompact_closedBall _ _)
  have hball {X : 𝕄} (hX : ‖X‖ ≤ ‖X₀‖ + 1) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
      v • (-I • X) ∈ Metric.closedBall (0 : 𝕄) (‖X₀‖ + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_smul,
      norm_neg, Complex.norm_I, one_mul, Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact (mul_le_of_le_one_left (norm_nonneg X) hv.2).trans hX
  refine ⟨K + 1, by positivity, fun X hX v hv ↦ ?_⟩
  have hnorm : ‖X‖ ≤ ‖X₀‖ + 1 := by
    have hn : ‖X‖ ≤ ‖X₀‖ + ‖X - X₀‖ := by simpa using norm_add_le X₀ (X - X₀)
    exact hn.trans (add_le_add le_rfl hX)
  have h := hK.norm_sub_le (hball hnorm hv)
    (hball (X := X₀) (le_add_of_nonneg_right zero_le_one) hv)
  change ‖evol X v - evol X₀ v‖ ≤ _ at h
  have hdiff : ‖v • (-I • X) - v • (-I • X₀)‖ = v * ‖X - X₀‖ := by
    rw [← smul_sub, ← smul_sub, norm_smul, norm_smul,
      norm_neg, Complex.norm_I, one_mul, Real.norm_eq_abs, abs_of_nonneg hv.1]
  rw [hdiff] at h
  exact h.trans (mul_le_mul (le_add_of_nonneg_right zero_le_one : (K : ℝ) ≤ K + 1)
    (mul_le_of_le_one_left (norm_nonneg _) hv.2)
    (mul_nonneg hv.1 (norm_nonneg _)) (by positivity))

/-- `X ↦ e^{-iX}` is differentiable at a Hermitian `X₀`, with derivative `evolDeriv X₀`: the
remainder in Duhamel's formula is quadratic in `‖X - X₀‖`. -/
theorem hasFDerivAt_evol_one [NeZero d] {X₀ : 𝕄} (hX₀ : X₀.IsHermitian) :
    HasFDerivAt (fun X : 𝕄 ↦ evol X 1) (evolDeriv X₀) X₀ := by
  obtain ⟨K, hK, hbound⟩ := evol_lipschitz_on_ball X₀
  refine HasFDerivAtFilter.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : 0 < min 1 (ε / K) := lt_min zero_lt_one (div_pos hε hK)
  filter_upwards [Metric.ball_mem_nhds X₀ hδ] with X hX
  have hx := (mem_ball_iff_norm.mp hX).le
  have hQ := hbound X (hx.trans (min_le_left _ _))
  change ‖evol X 1 - evol X₀ 1 - evolDeriv X₀ (X - X₀)‖ ≤ ε * ‖X - X₀‖
  rw [evolDeriv_apply, neg_smul, sub_neg_eq_add]
  have hsmall : K * ‖X - X₀‖ ≤ ε := by
    simpa only [mul_comm] using (le_div_iff₀ hK).mp (hx.trans (min_le_right _ _))
  exact (norm_evol_duhamel_two_le hX₀ hQ).trans
    (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))

/-- Duhamel's formula along a curve: `(e^{-iΩ})' = -i∫₀¹ e^{-i(1-u)Ω} Ω' e^{-iuΩ} du` at a point
where `Ω` is Hermitian, for a derivative within any set. -/
theorem hasDerivWithinAt_evol_curve [NeZero d] {Ω : ℝ → 𝕄} {D : 𝕄}
    {S : Set ℝ} {s : ℝ} (hΩ : (Ω s).IsHermitian)
    (hd : HasDerivWithinAt Ω D S s) :
    HasDerivWithinAt (fun t ↦ exp (-I • Ω t)) (evolDeriv (Ω s) D) S s := by
  have h := ((hasFDerivAt_evol_one hΩ).restrictScalars ℝ).comp_hasDerivWithinAt s hd
  simpa only [evol, frozenEvolution, one_smul] using h

end RoundedClocks.EndValue
