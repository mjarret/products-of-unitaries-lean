/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import UnitaryProducts.Corrector.SeparatedFrame

/-!
# A Schwartz extension of $\mathcal N$, and Fourier inversion

## Declarations

- `allowedDifferences`
- `analyticAt_frameMult`
- `analyticAt_frameMult_zero`
- `analyticOnNhd_frameSeries`
- `exists_schwartz_extension`
- `exists_schwartz_frameMult`
- `isCompact_allowedDifferences`
- `kernelSymbol_fourier`
- `zero_or_sin_half_ne_zero`
- `nonresonant_of_allowed`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ContDiff FourierTransform Manifold
open Complex MeasureTheory Set Filter Function

noncomputable section
namespace UnitaryProducts.Separation

/-- Analyticity of the frame series inside its convergence disk, used only at zero. -/
theorem analyticOnNhd_frameSeries : AnalyticOnNhd ℂ
    (UnitaryProducts.Corrector.frameSeries : ℂ → ℂ) (Metric.ball 0 (2 * Real.pi)) := by
  refine UnitaryProducts.Corrector.analyticOnNhd_tsum_coeff (by positivity) fun r hr0 hr ↦ ?_
  refine (UnitaryProducts.Corrector.summable_frameBound_majorant hr0 hr).congr fun n ↦ ?_
  rw [norm_div, norm_ratCast, RCLike.norm_natCast]; ring

/-- The apparent singularity of the scalar frame multiplier at zero is removable analytically. -/
theorem analyticAt_frameMult_zero : AnalyticAt ℝ UnitaryProducts.Corrector.frameMult 0 := by
  have hi : AnalyticAt ℝ (fun x : ℝ ↦ (x : ℂ) * I) 0 :=
    (Complex.ofRealCLM.analyticAt 0).mul analyticAt_const
  apply ((Complex.reCLM.analyticAt _).comp ((analyticOnNhd_frameSeries 0
    (by simp [Real.pi_pos])).restrictScalars.comp_of_eq hi (by simp))).congr
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
    (by simpa using Real.pi_pos : |(0 : ℝ)| < 2 * Real.pi)] with x hx
  change (UnitaryProducts.Corrector.frameSeries ((x : ℂ) * I)).re =
    UnitaryProducts.Corrector.frameMult x
  rw [UnitaryProducts.Corrector.frameSeries_ofReal_mul_I, Complex.ofReal_re,
    UnitaryProducts.Corrector.frameBound_abs_eq_frameMult hx]

/-- Away from zero the only singularities are zeros of sin(x/2). -/
theorem analyticAt_frameMult {x : ℝ} (hx : x = 0 ∨ Real.sin (x / 2) ≠ 0) :
    AnalyticAt ℝ UnitaryProducts.Corrector.frameMult x := by
  rcases hx with rfl | hx
  · exact analyticAt_frameMult_zero
  have hx0 : x ≠ 0 := fun he ↦ hx (by simp [he])
  have hi : AnalyticAt ℝ (fun y : ℝ ↦ y/2) x := analyticAt_id.div_const
  have hf : AnalyticAt ℝ
      (fun y : ℝ ↦ (1 - (y/2) * (Real.cos (y/2) / Real.sin (y/2))) / y^2) x :=
    (analyticAt_const.sub (hi.mul ((Real.analyticAt_cos.comp hi).div (Real.analyticAt_sin.comp hi)
      hx))).div (analyticAt_id.pow 2) (pow_ne_zero 2 hx0)
  apply hf.congr
  filter_upwards [eventually_ne_nhds hx0] with y hy
  simp only [UnitaryProducts.Corrector.frameMult, if_neg hy, Real.cot_eq_cos_div_sin]

/-- The eigenvalue differences the separated frame handles: the points of $[-W, W]$ that are $0$ or
at distance at least $\varepsilon$ from every $2\pi n$, $n \ne 0$. It is compact
(`isCompact_allowedDifferences`), and for $\varepsilon > 0$ `frameMult` is analytic on it. Every
non-resonant Hermitian matrix has all its eigenvalue differences in one such set
(`exists_hasSeparatedSpectrum_of_nonresonant`, `Spectral/GapDistance.lean`). -/
def allowedDifferences (ε W : ℝ) : Set ℝ :=
  Icc (-W) W ∩ ({0} ∪ {x : ℝ | ∀ n : ℤ, n ≠ 0 → ε ≤ |x - 2 * Real.pi * n|})

/-- The allowed set is compact: a closed subset of $[-W, W]$. -/
theorem isCompact_allowedDifferences (ε W : ℝ) : IsCompact (allowedDifferences ε W) := by
  refine isCompact_Icc.inter_right (isClosed_singleton.union ?_)
  simp only [setOf_forall]
  exact isClosed_iInter fun n : ℤ ↦ isClosed_iInter fun _ : n ≠ 0 ↦
    isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)

/-- Nonresonance excludes the nonzero zeros of the half-angle sine. -/
theorem zero_or_sin_half_ne_zero {x : ℝ}
    (hnr : ∀ n : ℤ, n ≠ 0 → x ≠ 2 * Real.pi * n) :
    x = 0 ∨ Real.sin (x / 2) ≠ 0 := by
  refine or_iff_not_imp_left.mpr fun hx hs ↦ ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
  exact hnr n (fun h ↦ hx (by subst h; simp only [Int.cast_zero, zero_mul] at hn; linarith))
    (by linarith)

/-- The separation hypothesis excludes every nonzero pole of the cotangent formula. -/
theorem nonresonant_of_allowed {ε W x : ℝ} (hε : 0 < ε)
    (hx : x ∈ allowedDifferences ε W) : x = 0 ∨ Real.sin (x/2) ≠ 0 := by
  rcases hx.2 with hx0 | hx
  · exact Or.inl (mem_singleton_iff.mp hx0)
  apply zero_or_sin_half_ne_zero
  intro n hn he
  exact (not_le_of_gt hε) (by simpa only [he, sub_self, abs_zero] using hx n hn)

/-- A smooth compact extension of a real function analytic on a prescribed compact set. -/
theorem exists_schwartz_extension {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hf : ∀ x ∈ K, AnalyticAt ℝ f x) :
    ∃ F : SchwartzMap ℝ ℂ, ∀ x ∈ K, F x = (f x : ℂ) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let U : Set ℝ := {x | AnalyticAt ℝ f x} ∩ Ioo (-(|R|+1)) (|R|+1)
  have hU : IsOpen U := (isOpen_analyticAt ℝ f).inter isOpen_Ioo
  have hKU : K ⊆ U := fun x hx ↦ ⟨hf x hx, abs_lt.mp (((by simpa [Real.dist_eq] using hR hx :
    |x| ≤ R).trans (le_abs_self R)).trans_lt (lt_add_one _))⟩
  obtain ⟨b, hb0, hb1, hb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, ℝ)) hU.isClosed_compl hK.isClosed
    (disjoint_left.mpr fun x hx hxK ↦ hx (hKU hxK)) (n := (⊤ : ℕ∞))
  let F : ℝ → ℝ := fun x ↦ b x * f x
  have hFd : ContDiff ℝ ∞ F := by
    refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
    by_cases hx : x ∈ U
    · exact b.contMDiff.contDiff.contDiffAt.mul ((hx.1).contDiffAt)
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hb0.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp only [F, hy, zero_mul]
  have hFc : HasCompactSupport F := by
    refine (isCompact_Icc : IsCompact (Icc (-(|R|+1)) (|R|+1))).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx ↦ Classical.byContradiction fun hxI ↦ hx ?_) isClosed_Icc)
    simp only [F, hb0.self_of_nhdsSet x fun h ↦ hxI ⟨h.2.1.le, h.2.2.le⟩, zero_mul]
  refine ⟨(hFc.comp_left (g := fun x : ℝ ↦ (x : ℂ)) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hFd), fun x hx ↦ ?_⟩
  change ((b x * f x : ℝ) : ℂ) = (f x : ℂ)
  rw [hb1.self_of_nhdsSet x hx, one_mul]

/-- There is a single Schwartz extension for all allowed differences at fixed ε and W. -/
theorem exists_schwartz_frameMult {ε : ℝ} (hε : 0 < ε) (W : ℝ) :
    ∃ F : SchwartzMap ℝ ℂ, ∀ x ∈ allowedDifferences ε W,
      F x = (UnitaryProducts.Corrector.frameMult x : ℂ) :=
  exists_schwartz_extension (isCompact_allowedDifferences ε W)
    fun _ hx ↦ analyticAt_frameMult (nonresonant_of_allowed hε hx)

/-- Fourier inversion, using the angular-frequency convention of kernelSymbol. -/
theorem kernelSymbol_fourier (F : SchwartzMap ℝ ℂ) (x : ℝ) :
    kernelSymbol (𝓕 F : SchwartzMap ℝ ℂ) (2 * Real.pi * x) = F x := by
  have hi := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f x)
    (show (𝓕⁻ (𝓕 F : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) = F from
      FourierTransform.fourierInv_fourier_eq F)
  change ((𝓕⁻ (𝓕 F : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = F x at hi
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hi
  rw [← hi]
  unfold kernelSymbol
  apply integral_congr_ae
  exact Eventually.of_forall fun s ↦ by
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    rw [mul_comm]; congr 2; push_cast; ring

end UnitaryProducts.Separation
