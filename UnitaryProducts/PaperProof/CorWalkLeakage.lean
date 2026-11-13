/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.LemWalkBands
public import UnitaryProducts.PaperProof.CorProducts
public import UnitaryProducts.PaperProof.PropTransfer
public import UnitaryProducts.PaperProof.WalkBandProjector
public import UnitaryProducts.Paper.UnitComparisonObjects

/-! # Leakage of a product of a unitary family with a gapped band -/

@[expose] public section
open Real Complex Set Filter
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector
open UnitaryProducts.Paper.UnitStepsProse
open scoped Topology Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1

omit [NeZero d] in
/-- The circular gap of a nonempty proper band is positive: the phases in one
open turn form a finite set, and all its cross-band circular distances are positive. -/
theorem circular_band_gap_pos (W : ℝ → 𝕄) (α β : ℝ → ℝ)
    (hband : circularBand W α β) {s : ℝ} (hs : s ∈ K) :
    0 < circularGap (W s) (α s) (β s) := by
  let S := {x : ℝ | x ∈ Ioo (α s) (α s + 2 * π) ∧
    Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ (W s)}
  have hfinite : S.Finite := by
    apply Set.Finite.of_finite_image (f := fun x : ℝ ↦ Complex.exp (-I * (x : ℂ)))
    · exact (Matrix.finite_spectrum (W s)).subset (by rintro z ⟨x, hx, rfl⟩; exact hx.2)
    · intro x hx y hy heq
      exact phase_inj hx.1 hy.1 heq
  let D := {g : ℝ | ∃ x y : ℝ, x ∈ Ioo (α s) (β s) ∧
    y ∈ Ioo (β s) (α s + 2 * π) ∧
    Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ (W s) ∧
    Complex.exp (-I * (y : ℂ)) ∈ spectrum ℂ (W s) ∧
    g = min (y - x) (2 * π - (y - x))}
  have hDfinite : D.Finite := by
    apply ((hfinite.prod hfinite).image
      (fun p : ℝ × ℝ ↦ min (p.2 - p.1) (2 * π - (p.2 - p.1)))).subset
    rintro g ⟨x, y, hx, hy, hxs, hys, rfl⟩
    exact ⟨(x, y), ⟨⟨⟨hx.1, hx.2.trans (hband.2.2 s hs).2.1⟩, hxs⟩,
      ⟨⟨(hband.2.2 s hs).1.trans hy.1, hy.2⟩, hys⟩⟩, rfl⟩
  have hDne : D.Nonempty := by
    obtain ⟨x, hx, hxs⟩ := (hband.2.2 s hs).2.2.2.2.1
    obtain ⟨y, hy, hys⟩ := (hband.2.2 s hs).2.2.2.2.2
    exact ⟨_, x, y, hx, hy, hxs, hys, rfl⟩
  obtain ⟨x, y, hx, hy, _, _, heq⟩ := hDne.csInf_mem hDfinite
  change 0 < sInf D
  rw [heq]
  exact lt_min (by linarith [hx.2, hy.1]) (by linarith [hx.1, hy.2])

omit [NeZero d] in
/-- The least continuous circular gap on `[0,1]` is positive and bounds every
pointwise gap. Compactness supplies an attained minimum. -/
theorem walk_band_gap_minimum (W : ℝ → 𝕄) (α β : ℝ → ℝ)
    (hband : circularBand W α β) (hu : (walk W 1).1)
    (hgc : ContinuousOn (fun s ↦ spectralWindowGap true (W s) (α s) (β s)) K) :
    let ϑ := sInf ((fun s ↦ spectralWindowGap true (W s) (α s) (β s)) '' K)
    0 < ϑ ∧ ∀ s ∈ K, ϑ ≤ spectralWindowGap true (W s) (α s) (β s) := by
  let g := fun s ↦ spectralWindowGap true (W s) (α s) (β s)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr zero_le_one) hgc
  have hleast : IsLeast (g '' K) (g s₀) :=
    ⟨⟨s₀, hs₀, rfl⟩, by rintro y ⟨s, hs, rfl⟩; exact hmin hs⟩
  change 0 < sInf (g '' K) ∧ _
  rw [hleast.csInf_eq]
  refine ⟨?_, fun s hs ↦ hmin hs⟩
  change 0 < spectralWindowGap true (W s₀) (α s₀) (β s₀)
  rw [walk_band_gap_eq W α β hband hu hs₀]
  exact circular_band_gap_pos W α β hband hs₀

omit [NeZero d] in
/-- In the open turn supplied by Theorem 4.7, selecting eigenvectors by membership
of their exponential phases in the walk band is exactly the interval projector.
It is orthogonal and commutes with every half-step phase of the logarithm. -/
theorem open_turn_band_projector {A : 𝕄} (hA : A.IsHermitian) {α β : ℝ}
    (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π))
    (hβ : β < α + 2 * π) :
    let B := {x : ℝ | ∃ θ ∈ Ioo α β,
      Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ))}
    specProj hA B = specProj hA (Ioo α β) ∧
      IsStarProjection (specProj hA B) ∧
      ∀ t : ℝ, Commute (specProj hA B) (evol A t) := by
  intro B
  have hselect (i : Fin d) : hA.eigenvalues i ∈ B ↔ hA.eigenvalues i ∈ Ioo α β := by
    constructor
    · rintro ⟨θ, hθ, he⟩
      have heq := phase_inj ⟨hθ.1, hθ.2.trans hβ⟩
        (hopen _ (hA.eigenvalues_mem_spectrum_real i)) he
      exact heq ▸ hθ
    · intro hi
      exact ⟨_, hi, rfl⟩
  have hidx : idx hA.eigenvalues B = idx hA.eigenvalues (Ioo α β) := by
    ext i
    simpa only [idx, Finset.mem_filter, Finset.mem_univ, true_and] using hselect i
  refine ⟨?_, isStarProjection_specProj hA B,
    fun t ↦ commute_evol_right (commute_specProj hA B) t⟩
  simp only [specProj, proj, hidx]

/-- Theorem 4.6 applied to an explicitly given logarithm. Agreement on `[0,1]`
identifies both walk derivatives and all sampled factors. -/
theorem walk_comparison_of_log (T : ℕ) (hT : 0 < T)
    (W H : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π) (hcH : ContDiffOn ℝ 2 H K)
    (hlog : ∀ s ∈ K, evol (H s) 1 = W s)
    (hwidth : ∀ s (hs : s ∈ K) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w)
    (U : ℝ → 𝕄) (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    ‖evol (H 1) (1 / 2) * (walk W T).2 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      walkEnergy w W / T := by
  have hb := (thm_unitary_products T hT H hH hw hcH ((hasWidth_iff hH).2 hwidth)).1
  rw [roundedEvolution_endpoint hT hH,
    ← evolution_eqOn (Nat.cast_pos.mpr hT) hH
      (UnitaryProducts.Prose.regulated_of_continuousOn hcH.continuousOn)
      hU (show (T : ℝ) ∈ Icc (0 : ℝ) T from ⟨by positivity, le_rfl⟩)] at hb
  have hprod0 : (walk (fun s ↦ evol (H s) 1) T).2 = (unitProduct H T).1 :=
    UnitaryProducts.stepProduct_eq_pieceProduct (fun _ _ ↦ rfl) T le_rfl
  rw [← hprod0] at hb
  have hw0 : 0 ≤ w := (abs_nonneg _).trans
    (hwidth 0 (by norm_num) (0 : Fin d) (0 : Fin d))
  have hfirst : EqOn (derivWithin (fun s ↦ evol (H s) 1) K) (derivWithin W K) K :=
    fun s hs ↦ derivWithin_congr hlog (hlog s hs)
  have hsecond : EqOn (derivWithin (derivWithin (fun s ↦ evol (H s) 1) K) K)
      (derivWithin (derivWithin W K) K) K :=
    fun s hs ↦ derivWithin_congr hfirst (hfirst hs)
  have hsup {f g : ℝ → 𝕄} (he : EqOn f g K) : unitSupNorm f = unitSupNorm g := by
    unfold unitSupNorm
    congr 1
    apply Set.image_congr
    intro s hs
    exact congrArg norm (he hs)
  have hprod : (walk (fun s ↦ evol (H s) 1) T).2 = (walk W T).2 := by
    have ha := stepProduct_eq_pieceProduct
      (fun j hj ↦ hlog _ (walkCubic_sample hj.le)) T le_rfl
    have hb := stepProduct_eq_pieceProduct (W := fun s ↦ evol (H s) 1) (G := H)
      (fun (_j : ℕ) (_hj : _j < T) ↦ rfl :
        ∀ j : ℕ, j < T → evol (H (j / T)) 1 = evol (H (j / T)) 1) T le_rfl
    exact hb.trans ha.symm
  simpa only [walkEnergy, paperWalkSquare, hprod, hfirst (show (0 : ℝ) ∈ K by norm_num),
    hfirst (show (1 : ℝ) ∈ K by norm_num), hsup hfirst, hsup hsecond,
    paperFrameMult_eq_series hw0 hw,
    paperFrameMult_eq_series (w := 0) le_rfl (by positivity),
    paperFrameMult_deriv_eq_series hw0 hw] using hb

/-- **Theorem 4.7** (`cor:walk-leakage`). The shifted principal-log formula supplies
 the unique Hermitian logarithm in the prescribed open turn. The extreme-pair gap
 estimate and Lemma A.2 give its width and C² regularity. Its endpoint projectors
 select precisely those eigenvectors whose walk phases lie in the specified arcs.
 The sampled walk leakage is bounded by its continuous evolution leakage plus
 `𝓔̃_w(W)/T`. The proof applies Theorem 4.6
 and Proposition 2.4 with the two half-step phases, whose product is the
 rounded-clock evolution. The conclusion explicitly supplies existence, pointwise
 uniqueness, regularity, and width of the logarithm named in the paper. The fixed band rank is not
needed for this comparison. -/
theorem cor_walk_leakage (W : ℝ → 𝕄) (α β : ℝ → ℝ)
    (hband : HasUnitaryBand W α β) (hc : ContDiffOn ℝ 2 W K) :
    let ϑ := sInf ((fun s ↦ spectralWindowGap true (W s) (α s) (β s)) '' K)
    let w := 2 * π - ϑ
    let P := spectralWindowProjector true (W 0) (α 0) (β 0)
    let Q := spectralWindowProjector true (W 1) (α 1) (β 1)
    ∃ H : ℝ → 𝕄, IsBandLogarithm W α H ∧ ContDiffOn ℝ 2 H K ∧ HasWidth H w ∧
      ∀ (T : ℕ), 1 ≤ T →
        ‖(1 - Q) * (walk W T).2 * P‖ ≤
          ‖(1 - Q) * evolution H T T * P‖ + walkEnergy w W / T := by
  obtain ⟨hu, horder, hband, hgc⟩ := hband
  intro ϑ w
  have hband' : circularBand W α β := (walk_band_family_iff W α β hu horder).2 hband
  obtain ⟨hϑ, hϑg⟩ := walk_band_gap_minimum W α β hband' hu hgc
  obtain ⟨H, hH, hcH, hlog, hopen, hwidth, _⟩ :=
    walk_band_log_support W α β ϑ hu hc horder hband hgc hϑ hϑg
  have hunique : ∀ s ∈ K, ∀ (B : 𝕄), B.IsHermitian →
      (∀ x ∈ spectrum ℝ B, x ∈ Ioo (α s) (α s + 2 * π)) →
      evol B 1 = W s → B = H s := by
    intro s hs B hB hBopen hBlog
    exact UnitaryProducts.Prose.eq_of_evol_eq_open_turn hB (hH s hs)
      (fun i ↦ hBopen _ (hB.eigenvalues_mem_spectrum_real i))
      (fun i ↦ hopen s hs _ ((hH s hs).eigenvalues_mem_spectrum_real i))
      (hBlog.trans (hlog s hs).symm)
  intro P Q
  refine ⟨H, ⟨hH, hlog, hopen, hunique⟩, hcH, (hasWidth_iff hH).2 hwidth, ?_⟩
  intro T hT
  let U := evolution H T
  have hU := evolution_spec (Nat.cast_pos.mpr (show 0 < T by omega))
    hH
      (UnitaryProducts.Prose.regulated_of_continuousOn hcH.continuousOn)
  have hP := open_turn_band_projector (hH 0 (by norm_num))
    (hopen 0 (by norm_num)) (horder 0 (by norm_num)).2
  have hQ := open_turn_band_projector (hH 1 (by norm_num))
    (hopen 1 (by norm_num)) (horder 1 (by norm_num)).2
  have heP : P = specProj (hH 0 (by norm_num)) {x : ℝ | ∃ θ ∈ Ioo (α 0) (β 0),
      Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ))} := by
    dsimp only [P]
    rw [← hlog 0 (by norm_num)]
    exact spectralWindowProjector_evol (hH 0 (by norm_num)) (α 0) (β 0)
  have heQ : Q = specProj (hH 1 (by norm_num)) {x : ℝ | ∃ θ ∈ Ioo (α 1) (β 1),
      Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (x : ℂ))} := by
    dsimp only [Q]
    rw [← hlog 1 (by norm_num)]
    exact spectralWindowProjector_evol (hH 1 (by norm_num)) (α 1) (β 1)
  rw [heP, heQ]
  have hcomparison := walk_comparison_of_log T (by omega) W H hH
    (by linarith) hcH hlog hwidth U hU
  have htransfer := prop_transfer (U := U T) (W := (walk W T).2) hP.2.1 hQ.2.1 hP.2.1 hQ.2.1
    (evol_mem_unitary (hH 1 (by norm_num)) (1 / 2))
    (evol_mem_unitary (hH 0 (by norm_num)) (-(1 / 2)))
    (hQ.2.2 (1 / 2)).symm (hP.2.2 (-(1 / 2))).symm
  simp only [sub_self, norm_zero, add_zero, mul_zero] at htransfer
  have hdiff := (le_abs_self _).trans (htransfer.trans hcomparison)
  linarith

end UnitaryProducts.PaperProof
