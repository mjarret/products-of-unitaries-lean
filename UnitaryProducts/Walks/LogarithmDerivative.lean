/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PowerSeries

/-!
# The differential of the matrix exponential

## Declarations

- `contDiffAt_evol_one`
- `evolDeriv`
- `evolDeriv_apply`
- `evol_mul_phiSeries_eq`
- `evol_sub_evol`
- `hasFDerivAt_evol_one`
- `norm_evol_duhamel_two_le`
- `norm_evol_sub_evol_le_exp`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open scoped Real
open NormedSpace Complex Set MeasureTheory UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

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
  rw [evol, evol]
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

/-- The averaging operator as a Duhamel integral:
`e^{-iB} Φ_B(E) = ∫₀¹ e^{-i(1-u)B} E e^{-iuB} du`. -/
theorem evol_mul_phiSeries_eq [NeZero d] (B E : 𝕄) :
    evol B 1 * phiSeries (I • adL B) E = ∫ u in (0:ℝ)..1, evol B (1 - u) * E * evol B u := by
  have hint : IntervalIntegrable (fun u : ℝ ↦ evol B (-u) * E * evol B u) volume 0 1 :=
    ((((continuous_evol B).comp continuous_neg).mul continuous_const).mul
      (continuous_evol B)).intervalIntegrable 0 1
  rw [phiSeries_adL_apply]
  have hcomm := (mulL (evol B 1)).intervalIntegral_comp_comm hint
  simp only [mulL_apply] at hcomm
  rw [← hcomm]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  show evol B 1 * (evol B (-u) * E * evol B u) = evol B (1 - u) * E * evol B u
  rw [← mul_assoc, ← mul_assoc, ← evol_add]
  ring_nf

/-- **The second-order Duhamel expansion.**  If `e^{-ivA}` and `e^{-ivB}` stay within `Q` of each
other on `[0, 1]` and `B` is Hermitian, then
`‖e^{-iA} - e^{-iB} + i e^{-iB} Φ_B(A - B)‖ ≤ Q ‖A - B‖`. -/
theorem norm_evol_duhamel_two_le [NeZero d] {A B : 𝕄} {Q : ℝ} (hB : B.IsHermitian)
    (hQ : ∀ v ∈ Icc (0 : ℝ) 1, ‖evol A v - evol B v‖ ≤ Q) :
    ‖evol A 1 - evol B 1 + I • (evol B 1 * phiSeries (I • adL B) (A - B))‖ ≤ Q * ‖A - B‖ := by
  have hAB := evol_sub_evol A B
  have hBB := evol_mul_phiSeries_eq B (A - B)
  have hint (C : 𝕄) : IntervalIntegrable (fun u : ℝ ↦ evol C (1 - u) * (A - B) * evol B u)
      volume 0 1 :=
    ((((continuous_evol C).comp (continuous_const.sub continuous_id))).mul
      continuous_const).mul (continuous_evol B) |>.intervalIntegrable 0 1
  have hkey : evol A 1 - evol B 1 + I • (evol B 1 * phiSeries (I • adL B) (A - B))
      = -I • ∫ u in (0:ℝ)..1,
          (evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u := by
    rw [hAB, hBB, show (∫ u in (0:ℝ)..1, (evol A (1 - u) - evol B (1 - u)) * (A - B) * evol B u)
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

/-- The differential of `X ↦ e^{-iX}` at `X`: `E ↦ -i e^{-iX} Φ_X(E)`. -/
noncomputable def evolDeriv (X : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  (-I) • (mulL (evol X 1) * phiSeries (I • adL X))

/-- `evolDeriv` applied to `E`. -/
theorem evolDeriv_apply (X E : 𝕄) :
    evolDeriv X E = -I • (evol X 1 * phiSeries (I • adL X) E) := rfl

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
      = evol X 1 - evol X₀ 1 + I • (evol X₀ 1 * phiSeries (I • adL X₀) (X - X₀)) := by
    rw [evolDeriv_apply, neg_smul, sub_neg_eq_add]
  change ‖evol X 1 - evol X₀ 1 - evolDeriv X₀ (X - X₀)‖ ≤ ε * ‖X - X₀‖
  rw [hid]
  exact hR.trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ hM0).mp hx2) (norm_nonneg _))

/-- `X ↦ e^{-iX}` is analytic, hence smooth. -/
theorem contDiffAt_evol_one (X₀ : 𝕄) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (fun X : 𝕄 ↦ evol X 1) X₀ := by
  have hanal : AnalyticAt ℂ (NormedSpace.exp : 𝕄 → 𝕄) ((-I) • X₀) :=
    NormedSpace.exp_analytic (𝕂 := ℂ) _
  have hlin : ContDiffAt ℂ n (fun X : 𝕄 ↦ (-I : ℂ) • X) X₀ :=
    (contDiff_id.const_smul _).contDiffAt
  have heq : (fun X : 𝕄 ↦ evol X 1) = (NormedSpace.exp : 𝕄 → 𝕄) ∘ fun X : 𝕄 ↦ (-I : ℂ) • X := by
    funext X; simp [evol]
  rw [heq]
  exact hanal.contDiffAt.comp X₀ hlin

end UnitaryProducts
