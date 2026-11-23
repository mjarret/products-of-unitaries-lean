/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.EndValueCurve
public import RoundedClocks.Preliminaries.PiecewiseEvolution

/-! # Duhamel differential of the exponential

Lemma A.3 differentiates the matrix exponential by the Duhamel integral. Evolution identities
give its centered decomposition.
-/

@[expose] public section
noncomputable section
open NormedSpace Complex Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace RoundedClocks.EndValue
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The fixed-generator evolution used in the Duhamel integral. -/
abbrev evol (G : 𝕄) (u : ℝ) : 𝕄 := frozenEvolution G u

/-- $e^{-i0G} = 1$. -/
theorem evol_zero (G : 𝕄) : evol G 0 = 1 := by simp [evol, frozenEvolution]

/-- $e^{-i(u+v)G} = e^{-iuG}e^{-ivG}$. -/
theorem evol_add (G : 𝕄) (u v : ℝ) : evol G (u + v) = evol G u * evol G v := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol, frozenEvolution, add_smul]
  exact exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)

/-- $\frac{d}{du}e^{-iuG} = -iG\,e^{-iuG}$: Mathlib's `hasDerivAt_exp_smul_const'`, stated for
`evol`. -/
theorem hasDerivAt_evol (G : 𝕄) (u : ℝ) :
    HasDerivAt (evol G) ((-I • G) * evol G u) u :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) _ _

/-- $-iG$ commutes with $e^{-iuG}$. -/
theorem commute_evol (G : 𝕄) (u : ℝ) : Commute (-I • G) (evol G u) :=
  ((Commute.refl (-I • G)).smul_right (u : ℝ)).exp_right

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

/-- An isometry has norm at most one, including dimension zero. -/
theorem norm_le_one_of_star_mul_self {X : 𝕄} (h : star X * X = 1) : ‖X‖ ≤ 1 := by
  nontriviality 𝕄
  exact (CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff'.mpr h)).le

/-- $\|e^{-iuG}\| \le 1$ for Hermitian $G$. -/
theorem norm_evol_le {G : 𝕄} (hG : G.IsHermitian) (u : ℝ) : ‖evol G u‖ ≤ 1 :=
  norm_le_one_of_star_mul_self (star_evol_mul_self hG u)

/-- The evolution is continuous in its time parameter. -/
theorem continuous_evol (G : 𝕄) : Continuous (evol G) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_evol G u).continuousAt

/-- **Growth of real exponentials** (Grönwall): `‖e^{sX}‖ ≤ e^{s‖X‖}` for `s ≥ 0`. -/
theorem norm_exp_smul_le (X : 𝕄) {s : ℝ} (hs : 0 ≤ s) : ‖exp (s • X)‖ ≤ Real.exp (s * ‖X‖) := by
  have h1 : ‖exp ((0 : ℝ) • X)‖ ≤ 1 := by
    rw [zero_smul, NormedSpace.exp_zero]; exact norm_le_one_of_star_mul_self (by simp)
  simpa [gronwallBound_ε0, mul_comm] using norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun u : ℝ ↦ exp (u • X)) (f' := fun u ↦ X * exp (u • X)) (δ := 1) (K := ‖X‖) (ε := 0)
    (a := 0) (b := s)
    (fun u _ ↦ (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X u).continuousAt.continuousWithinAt)
    (fun u _ ↦ (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X u).hasDerivWithinAt) h1
    (fun u _ ↦ by simpa using norm_mul_le X (exp (u • X))) s ⟨hs, le_rfl⟩

/-- **Lipschitz bound for the exponential**: `‖e^{A} - e^{B}‖ ≤ ‖A - B‖ e^{max(‖A‖, ‖B‖)}`.
Differentiate `v ↦ e^{vA} e^{(1-v)B}`, whose derivative is `e^{vA} (A - B) e^{(1-v)B}`. -/
theorem norm_exp_sub_exp_le (A B : 𝕄) :
    ‖exp A - exp B‖ ≤ ‖A - B‖ * Real.exp (max ‖A‖ ‖B‖) := by
  set φ : ℝ → 𝕄 := fun v ↦ exp (v • A) * exp ((1 - v) • B)
  have hderiv : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (exp (v • A) * (A - B) * exp ((1 - v) • B)) (Icc 0 1) v := by
    intro v _
    have hB : HasDerivAt (fun v : ℝ ↦ exp ((1 - v) • B)) (-(B * exp ((1 - v) • B))) v := by
      simpa [Function.comp_def] using
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (1 - v)).scomp v ((hasDerivAt_id v).const_sub 1)
    convert ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) A v).mul hB).hasDerivWithinAt using 1
    rw [((Commute.refl A).smul_right v).exp_right.eq]
    noncomm_ring
  have hbound : ∀ v ∈ Ico (0 : ℝ) 1, ‖exp (v • A) * (A - B) * exp ((1 - v) • B)‖
      ≤ ‖A - B‖ * Real.exp (max ‖A‖ ‖B‖) := by
    intro v hv
    have h1 := norm_exp_smul_le A hv.1
    have h2 := norm_exp_smul_le B (by linarith [hv.2] : 0 ≤ 1 - v)
    have hexp : Real.exp (v * ‖A‖) * Real.exp ((1 - v) * ‖B‖) ≤ Real.exp (max ‖A‖ ‖B‖) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith [mul_le_mul_of_nonneg_left (le_max_left ‖A‖ ‖B‖) hv.1,
        mul_le_mul_of_nonneg_left (le_max_right ‖A‖ ‖B‖) (sub_nonneg.mpr hv.2.le)]
    calc _ ≤ Real.exp (v * ‖A‖) * ‖A - B‖ * Real.exp ((1 - v) * ‖B‖) :=
          norm_mul_le_of_le (norm_mul_le_of_le h1 le_rfl) h2
      _ = ‖A - B‖ * (Real.exp (v * ‖A‖) * Real.exp ((1 - v) * ‖B‖)) := by ring
      _ ≤ _ := by gcongr
  simpa [φ] using norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩

/-- `‖e^{-ivA} - e^{-ivB}‖ ≤ |v| ‖A - B‖ e^{max(‖A‖, ‖B‖)}` for `|v| ≤ 1`. -/
theorem norm_evol_sub_evol_le_exp (A B : 𝕄) {v : ℝ} (hv : |v| ≤ 1) :
    ‖evol A v - evol B v‖ ≤ |v| * ‖A - B‖ * Real.exp (max ‖A‖ ‖B‖) := by
  have hkey := norm_exp_sub_exp_le (v • (-I • A)) (v • (-I • B))
  have h1 : ‖v • (-I • A) - v • (-I • B)‖ = |v| * ‖A - B‖ := by
    rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, norm_smul, norm_neg,
      Complex.norm_I, one_mul]
  have h2 : ∀ X : 𝕄, ‖v • (-I • X)‖ ≤ ‖X‖ := by
    intro X
    rw [norm_smul, Real.norm_eq_abs, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg X) hv
  change ‖exp (v • (-I • A)) - exp (v • (-I • B))‖ ≤ _
  refine hkey.trans ?_
  rw [h1]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (max_le_max (h2 A) (h2 B)))
    (by positivity)

/-- **Duhamel for two constant Hamiltonians**:
`e^{-iA} - e^{-iB} = -i ∫₀¹ e^{-i(1-u)A} (A - B) e^{-iuB} du`. -/
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

/-- The integral defining the differential is continuous in the time variable. -/
theorem continuous_integrand (B E : 𝕄) :
    Continuous (fun u : ℝ ↦ evol B (1 - u) * E * evol B u) :=
  (((continuous_evol B).comp (continuous_const.sub continuous_id)).mul
    continuous_const).mul (continuous_evol B)

/-- The Duhamel differential, defined directly by its integral. -/
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

/-- Evaluation of the differential is the Duhamel integral. -/
theorem evolDeriv_apply (B E : 𝕄) :
    evolDeriv B E = -I • ∫ u in (0 : ℝ)..1, evol B (1 - u) * E * evol B u := rfl

/-- A uniform integrand bound gives its interval length bound. -/
theorem norm_intervalIntegral_le {f : ℝ → 𝕄} {a t C : ℝ} (hat : a ≤ t)
    (h : ∀ s ∈ Icc a t, ‖f s‖ ≤ C) : ‖∫ s in a..t, f s‖ ≤ C * (t - a) := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦
    h s (Ioc_subset_Icc_self (by rwa [uIoc_of_le hat] at hs))
  rwa [abs_of_nonneg (sub_nonneg.mpr hat)] at hn

/-- **The second-order Duhamel expansion.**  If `e^{-ivA}` and `e^{-ivB}` stay within `Q` of each
other on `[0, 1]` and `B` is Hermitian, then
the Duhamel remainder has norm at most `Q ‖A - B‖`. -/
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

/-- **`X ↦ e^{-iX}` is differentiable**, with differential `evolDeriv X₀` at a Hermitian `X₀`
(the second-order Duhamel expansion gives a quadratic remainder). -/
theorem hasFDerivAt_evol_one [NeZero d] {X₀ : 𝕄} (hX₀ : X₀.IsHermitian) :
    HasFDerivAt (fun X : 𝕄 ↦ evol X 1) (evolDeriv X₀) X₀ := by
  set M : ℝ := Real.exp (‖X₀‖ + 1) with hMdef
  have hM0 : 0 < M := Real.exp_pos _
  refine HasFDerivAtFilter.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ0 : 0 < min 1 (ε / M) := lt_min zero_lt_one (by positivity)
  have hball : ∀ᶠ X in nhds X₀, ‖X - X₀‖ ≤ min 1 (ε / M) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds X₀ hδ0) fun X hX ↦ (mem_ball_iff_norm.mp hX).le
  filter_upwards [hball] with X hX
  have hx1 : ‖X - X₀‖ ≤ 1 := hX.trans (min_le_left _ _)
  have hx2 : ‖X - X₀‖ ≤ ε / M := hX.trans (min_le_right _ _)
  have hQ : ∀ v ∈ Icc (0 : ℝ) 1, ‖evol X v - evol X₀ v‖ ≤ ‖X - X₀‖ * M := by
    intro v hv
    have hv1 : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; exact hv.2
    refine (norm_evol_sub_evol_le_exp X X₀ hv1).trans ?_
    have hnt : ‖X‖ ≤ ‖X₀‖ + ‖X - X₀‖ := by simpa using norm_add_le X₀ (X - X₀)
    have hmax : max ‖X‖ ‖X₀‖ ≤ ‖X₀‖ + 1 := max_le (by linarith) (by linarith)
    calc |v| * ‖X - X₀‖ * Real.exp (max ‖X‖ ‖X₀‖)
        ≤ 1 * ‖X - X₀‖ * Real.exp (‖X₀‖ + 1) := by gcongr
      _ = ‖X - X₀‖ * M := by rw [one_mul, hMdef]
  have hR := norm_evol_duhamel_two_le (A := X) (B := X₀) hX₀ hQ
  have hid : evol X 1 - evol X₀ 1 - evolDeriv X₀ (X - X₀)
      = evol X 1 - evol X₀ 1 + I • (∫ u in (0:ℝ)..1, evol X₀ (1 - u) * (X - X₀) * evol X₀ u) := by
    rw [evolDeriv_apply, neg_smul, sub_neg_eq_add]
  change ‖evol X 1 - evol X₀ 1 - evolDeriv X₀ (X - X₀)‖ ≤ ε * ‖X - X₀‖
  rw [hid]
  exact hR.trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ hM0).mp hx2) (norm_nonneg _))


/-- The Duhamel derivative along a curve holds on an arbitrary domain, including endpoints. -/
theorem hasDerivWithinAt_evol_curve [NeZero d] {Ω : ℝ → 𝕄} {D : 𝕄}
    {S : Set ℝ} {s : ℝ} (hΩ : (Ω s).IsHermitian)
    (hd : HasDerivWithinAt Ω D S s) :
    HasDerivWithinAt (fun t ↦ exp (-I • Ω t)) (evolDeriv (Ω s) D) S s := by
  have h := ((hasFDerivAt_evol_one hΩ).restrictScalars ℝ).comp_hasDerivWithinAt s hd
  simpa only [evol, frozenEvolution, one_smul] using h

end RoundedClocks.EndValue
