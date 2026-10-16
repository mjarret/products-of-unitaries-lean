/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.SpectralProofSteps
public import UnitaryProducts.PaperProof.PrincipalLog
public import UnitaryProducts.Prose.WalkBandTransfer
public import UnitaryProducts.PaperProof.WalkBandGap

/-!
# The band-to-arc lemma

Corollary 4.7 belongs downstream of `LemWalkLog`:
importing that module into `Walks.BandMultiplicity` would create a cycle.
-/

@[expose] public section
open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
noncomputable section
namespace UnitaryProducts.PaperProof
-- This C*-algebra structure uses the same L2 operator norm as the paper.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "K" => Icc (0 : ℝ) 1


/-- Corollary 4.7: the shifted principal-log guess has exactly the Hermitian
spectrum in the selected open turn and exponentiates to the given unitary. -/
theorem walk_bands_principal_ansatz_verified (W : 𝕄) (α : ℝ)
    (hu : star W * W = 1)
    (hcut : Complex.exp (-I * (α : ℂ)) ∉ spectrum ℂ W) :
    let G := ((α + π : ℝ) : ℂ) • (1 : 𝕄) +
      I • cfc Complex.log (Complex.exp (I * ((α + π : ℝ) : ℂ)) • W)
    ∃ hG : G.IsHermitian,
      (∀ i, hG.eigenvalues i ∈ Ioo α (α + 2 * π)) ∧ evol G 1 = W := by
  obtain ⟨A, ⟨hA, hwin, he⟩, _⟩ := existsUnique_log_open_turn
    ⟨W, Matrix.mem_unitaryGroup_iff'.mpr hu⟩ α hcut
  have hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩
    exact hwin i
  have hformula := (cut_log_eq_principal hA he hopen).2
  dsimp only
  rw [← hformula]
  exact ⟨hA, hwin, he⟩

/-- Corollary 4.7: continuity follows directly from the moving-cut principal-log
formula and Mathlib's continuity of continuous functional calculus on the slit plane. -/
theorem cut_log_continuous_principal (W G : ℝ → 𝕄) (α : ℝ → ℝ)
    (hW : ContinuousOn W K) (ha : ContinuousOn α K)
    (hG : ∀ s ∈ K, (G s).IsHermitian)
    (he : ∀ s ∈ K, evol (G s) 1 = W s)
    (hopen : ∀ s ∈ K, ∀ x ∈ spectrum ℝ (G s), x ∈ Ioo (α s) (α s + 2 * π)) :
    ContinuousOn G K := by
  let V := fun s ↦ Complex.exp (I * ((α s + π : ℝ) : ℂ)) • W s
  have hc : ContinuousOn (fun s ↦ ((α s + π : ℝ) : ℂ)) K :=
    Complex.continuous_ofReal.comp_continuousOn (ha.add continuousOn_const)
  have hV : ContinuousOn V K :=
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hc)).smul hW
  have hcut (s : ℝ) (hs : s ∈ K) := (cut_log_eq_principal (hG s hs) (he s hs) (hopen s hs)).1
  have hnormal (s : ℝ) (hs : s ∈ K) : IsStarNormal (V s) := by
    letI : IsStarNormal (W s) := (he s hs) ▸ isStarNormal_evol_one (hG s hs)
    exact IsStarNormal.smul _ _
  have hlog : ContinuousOn (fun s ↦ cfc Complex.log (V s)) K := by
    apply ContinuousOn.cfc_of_mem_nhdsSet (s := Complex.slitPlane) Complex.log _ hV hnormal
      (fun z hz ↦ (continuousAt_clog hz).continuousWithinAt)
    · apply Complex.isOpen_slitPlane.mem_nhdsSet.mpr
      intro z hz
      obtain ⟨s, hs, hz⟩ := Set.mem_iUnion₂.mp hz
      exact hcut s hs hz
  apply (hc.smul (continuousOn_const (c := (1 : 𝕄))) |>.add (hlog.const_smul I)).congr
  intro s hs
  exact (cut_log_eq_principal (hG s hs) (he s hs) (hopen s hs)).2

omit [NeZero d] in
/-- In a single open turn, membership in the real interval is exactly membership in
the walk's arc, and the circular gap is a lower bound for the real separation: the first
term of the display in the proof of Corollary 4.7 (`band_pair_gap_display`). -/
theorem cut_log_band {A U : 𝕄} (hA : A.IsHermitian) {α β : ℝ}
    (he : evol A 1 = U)
    (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π))
    (hβ2 : β < α + 2 * π)
    (hβ : Complex.exp (-I * (β : ℂ)) ∉ spectrum ℂ U) :
    α ∉ spectrum ℝ A ∧ β ∉ spectrum ℝ A ∧
      (∀ i j, hA.eigenvalues i ∈ Ioo α β → hA.eigenvalues j ∉ Ioo α β →
        circularGap U α β ≤ |hA.eigenvalues i - hA.eigenvalues j|) ∧
      (∀ i, hA.eigenvalues i ∈ Ioo α β ↔
        ∃ θ ∈ Ioo α β, Complex.exp (-I * (θ : ℂ)) =
          Complex.exp (-I * (hA.eigenvalues i : ℂ))) := by
  have himg : ∀ x ∈ spectrum ℝ A, Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U := by
    intro x hx
    rw [← he, spectrum_evol_image hA]
    exact ⟨x, hx, rfl⟩
  have hβs : β ∉ spectrum ℝ A := fun h ↦ hβ (himg β h)
  refine ⟨fun h ↦ lt_irrefl α (hopen α h).1, hβs, ?_, ?_⟩
  · intro i j hi hj
    have hjs := hA.eigenvalues_mem_spectrum_real j
    have hj' : hA.eigenvalues j ∈ Ioo β (α + 2 * π) := by
      refine ⟨?_, (hopen _ hjs).2⟩
      apply lt_of_le_of_ne
      · exact le_of_not_gt fun h ↦ hj ⟨(hopen _ hjs).1, h⟩
      · exact fun h ↦ hβs (h.symm ▸ hjs)
    have hdisplay := band_pair_gap_display hi hj' (himg _ (hA.eigenvalues_mem_spectrum_real i))
      (himg _ hjs)
    have hfirst := (hdisplay.1.trans hdisplay.2).trans (min_le_left _ _)
    rw [abs_sub_comm, abs_of_pos (by linarith [hi.2, hj'.1])]
    exact hfirst
  · intro i
    constructor
    · intro hi
      exact ⟨_, hi, rfl⟩
    · rintro ⟨θ, hθ, hphase⟩
      have heq := phase_inj ⟨hθ.1, hθ.2.trans hβ2⟩
        (hopen _ (hA.eigenvalues_mem_spectrum_real i)) hphase
      exact heq ▸ hθ

/-- Arc-construction auxiliary for Corollary 4.7: a walk band supplies the closed arc and,
for its Hermitian logarithm, the same band with at least the circular gap. -/
theorem walk_band_arc (W : ℝ → 𝕄) (α β : ℝ → ℝ) (ϑ : ℝ)
    (hu : (walk W 1).1) (hc : ContDiffOn ℝ 2 W K)
    (hband : circularBand W α β)
    (hgc : ContinuousOn (fun s ↦ circularGap (W s) (α s) (β s)) K)
    (hϑ : 0 < ϑ) (hϑg : ∀ s ∈ K, ϑ ≤ circularGap (W s) (α s) (β s)) :
    ∃ a : ℝ → ℝ, ContinuousOn a K ∧
      (∀ s ∈ K, ∀ z ∈ spectrum ℂ (W s),
        ∃ θ ∈ Icc (a s) (a s + (2 * π - ϑ)), z = Complex.exp (-I * (θ : ℂ))) ∧
      ∀ (H : ℝ → 𝕄) (hH : ∀ s ∈ K, (H s).IsHermitian),
        (∀ s (hs : s ∈ K), evol (H s) 1 = W s ∧
          ∀ i, (hH s hs).eigenvalues i ∈ Icc (a s) (a s + (2 * π - ϑ))) →
        ∀ s (hs : s ∈ K),
          (∀ x ∈ spectrum ℝ (H s), x ∈ Ioo (α s) (α s + 2 * π)) ∧
          α s ∉ spectrum ℝ (H s) ∧ β s ∉ spectrum ℝ (H s) ∧
          (∀ i j, (hH s hs).eigenvalues i ∈ Ioo (α s) (β s) →
            (hH s hs).eigenvalues j ∉ Ioo (α s) (β s) →
            circularGap (W s) (α s) (β s) ≤
              |(hH s hs).eigenvalues i - (hH s hs).eigenvalues j|) ∧
          (∀ i, (hH s hs).eigenvalues i ∈ Ioo (α s) (β s) ↔
            ∃ θ ∈ Ioo (α s) (β s), Complex.exp (-I * (θ : ℂ)) =
              Complex.exp (-I * ((hH s hs).eigenvalues i : ℂ))) := by
  classical
  have ht := trackedCircularBand_circularGap W α β hband hgc
    (fun s hs ↦ hϑ.trans_le (hϑg s hs))
  obtain ⟨ha, _, _, hb⟩ := ht
  have hex : ∀ s : ℝ, ∃ G : 𝕄, ∃ hG : G.IsHermitian, s ∈ K →
      (∀ i, hG.eigenvalues i ∈ Ioo (α s) (α s + 2 * π)) ∧ evol G 1 = W s := by
    intro s
    by_cases hs : s ∈ K
    · obtain ⟨hG, hwin, he⟩ := walk_bands_principal_ansatz_verified
        (W s) (α s) (hu s hs) (hb s hs).2.2.2.1
      exact ⟨_, hG, fun _ ↦ ⟨hwin, he⟩⟩
    · exact ⟨0, Matrix.isHermitian_zero, fun h ↦ (hs h).elim⟩
  choose G hG hGe using hex
  have hopen : ∀ s ∈ K, ∀ x ∈ spectrum ℝ (G s), x ∈ Ioo (α s) (α s + 2 * π) := by
    intro s hs
    rw [(hG s).spectrum_real_eq_range_eigenvalues]
    rintro x ⟨i, rfl⟩
    exact (hGe s hs).1 i
  have hGc := cut_log_continuous_principal W G α hc.continuousOn ha
    (fun s _ ↦ hG s) (fun s hs ↦ (hGe s hs).2) hopen
  -- Establish the arc correspondence once, before selecting the extreme pair.
  have hGband (s : ℝ) (hs : s ∈ K) :=
    cut_log_band (hG s) (hGe s hs).2 (hopen s hs)
      (hb s hs).2.2.1 (hb s hs).2.2.2.2.1
  let a : ℝ → ℝ := fun s ↦ spectralBottom (G s)
  have hac : ContinuousOn a K := continuous_spectralBottom.comp_continuousOn hGc
  have hwin : ∀ s (hs : s ∈ K), ∀ i,
      (hG s).eigenvalues i ∈ Icc (a s) (a s + (2 * π - ϑ)) := by
    intro s hs i
    obtain ⟨_, _, hβ2, _, _, hB, hC, _⟩ := hb s hs
    have hw := extreme_pair_width (hG s) (hGe s hs).2 (hopen s hs) hβ2 hB hC (hϑg s hs)
    have hm := (hG s).eigenvalues_mem_spectrum_real i
    refine ⟨(isLeast_spectralBottom (hG s)).2 hm, ?_⟩
    have hi := (isGreatest_spectralTop (hG s)).2 hm
    dsimp only [a]
    linarith [hw.1, hw.2]
  have harc : ∀ s ∈ K, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + (2 * π - ϑ)), z = Complex.exp (-I * (θ : ℂ)) := by
    intro s hs z hz
    rw [← (hGe s hs).2, spectrum_evol_image (hG s)] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [(hG s).spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨_, hwin s hs i, rfl⟩
  obtain ⟨L, hL, hLe, huniq, _, _⟩ := lem_walk_log a (2 * π - ϑ)
    (by
      have hi := hwin 0 (by norm_num) 0
      linarith [hi.1, hi.2]) (by linarith) W hac hu harc hc
  refine ⟨a, hac, harc, ?_⟩
  intro H hH hlog s hs
  have hHG : H s = G s :=
    (huniq s hs (H s) (hH s hs) (hlog s hs).2 (hlog s hs).1).trans
      (huniq s hs (G s) (hG s) (hwin s hs) (hGe s hs).2).symm
  -- Uniqueness transfers the already established band correspondence and gap.
  simpa only [hHG] using And.intro (hopen s hs) (hGband s hs)

/-- Unnumbered band-log support for **Corollary 4.7** (`cor:walk-leakage`): the logarithm cut at
the band's
left edge has spectrum in that open turn, width at most `2π - ϑ`, and
separation between its interval band and its complement at least the circular gap.
The principal-log construction and extreme-pair estimate supply its arc; Lemma A.2
then gives its C² regularity. -/
theorem walk_band_log_support (W : ℝ → 𝕄) (α β : ℝ → ℝ) (ϑ : ℝ)
    (hu : (walk W 1).1) (hc : ContDiffOn ℝ 2 W K)
    (horder : ∀ s ∈ K, α s < β s ∧ β s < α s + 2 * π)
    (hband : spectralWindowFamily true W α β)
    (hgc : ContinuousOn (fun s ↦ spectralWindowGap true (W s) (α s) (β s)) K)
    (hϑ : 0 < ϑ) (hϑg : ∀ s ∈ K, ϑ ≤ spectralWindowGap true (W s) (α s) (β s)) :
    ∃ H : ℝ → 𝕄, ∃ hH : ∀ s ∈ K, (H s).IsHermitian,
      ContDiffOn ℝ 2 H K ∧
      (∀ s ∈ K, evol (H s) 1 = W s) ∧
      (∀ s ∈ K, ∀ x ∈ spectrum ℝ (H s), x ∈ Ioo (α s) (α s + 2 * π)) ∧
      (∀ s (hs : s ∈ K), ∀ i j,
        |(hH s hs).eigenvalues i - (hH s hs).eigenvalues j| ≤ 2 * π - ϑ) ∧
      (∀ s (hs : s ∈ K), ∀ i j,
        (hH s hs).eigenvalues i ∈ Ioo (α s) (β s) →
        (hH s hs).eigenvalues j ∉ Ioo (α s) (β s) →
        spectralWindowGap true (W s) (α s) (β s) ≤
          |(hH s hs).eigenvalues i - (hH s hs).eigenvalues j|) := by
  have hband' : circularBand W α β := (walk_band_family_iff W α β hu horder).2 hband
  have hgc' : ContinuousOn (fun s ↦ circularGap (W s) (α s) (β s)) K :=
    hgc.congr (fun s hs ↦ (walk_band_gap_eq W α β hband' hu hs).symm)
  have hϑg' : ∀ s ∈ K, ϑ ≤ circularGap (W s) (α s) (β s) := by
    intro s hs
    simpa only [walk_band_gap_eq W α β hband' hu hs] using hϑg s hs
  obtain ⟨a, ha, harc, htransfer⟩ := walk_band_arc W α β ϑ hu hc hband' hgc' hϑ hϑg'
  have hw0 : 0 ≤ 2 * π - ϑ := by
    obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (W 0)
    obtain ⟨θ, hθ, _⟩ := harc 0 (by norm_num) z hz
    linarith [hθ.1, hθ.2]
  obtain ⟨H, hH, hlog, _, hC, _⟩ :=
    lem_walk_log a (2 * π - ϑ) hw0 (by linarith) W ha hu harc hc
  have hbandH := htransfer H hH fun s hs ↦ ⟨(hlog s hs).2, (hlog s hs).1⟩
  refine ⟨H, hH, hC, fun s hs ↦ (hlog s hs).2,
    fun s hs ↦ (hbandH s hs).1, ?_, ?_⟩
  · intro s hs i j
    have hi := (hlog s hs).1 i
    have hj := (hlog s hs).1 j
    exact abs_le.mpr ⟨by linarith [hi.1, hj.2], by linarith [hi.2, hj.1]⟩
  · intro s hs i j hi hj
    rw [walk_band_gap_eq W α β hband' hu hs]
    exact (hbandH s hs).2.2.2.1 i j hi hj

set_option maxHeartbeats 1600000 in
-- The proof combines finite eigenvalue minima with locally constant spectral selections.
omit [NeZero d] in
/-- Section 4.3: a continuous Hermitian path and continuous interval endpoints
which are never eigenvalues have a continuous exact band gap. Weyl's inequality
makes each ordered eigenvalue continuous; the selected indices are locally constant.
The minimum of their finitely many pairwise distances is therefore continuous. -/
theorem continuous_exactGap_intervals (H : ℝ → 𝕄)
    (hH : ∀ s ∈ K, (H s).IsHermitian) (hc : ContinuousOn H K)
    (α β : ℝ → ℝ) (hα : ContinuousOn α K) (hβ : ContinuousOn β K)
    (hoff : ∀ s ∈ K, α s ∉ spectrum ℝ (H s) ∧ β s ∉ spectrum ℝ (H s)) :
    ContinuousOn (exactGap H hH (fun s ↦ Ioo (α s) (β s))) K := by
  classical
  let ev (s : K) (i : Fin d) := (hH s s.2).eigenvalues i
  have he (i : Fin d) : Continuous (fun s : K ↦ ev s i) := by
    have hl : LipschitzWith 1
        (fun A : {A : 𝕄 // A.IsHermitian} ↦ A.2.eigenvalues i) := by
      apply LipschitzWith.of_dist_le_mul
      intro A B
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq, dist_eq_norm] using
        abs_eigenvalues_sub_le A.2 B.2 i
    exact hl.continuous.comp (hc.restrict.subtype_mk fun s ↦ hH s s.2)
  have horder {f g : K → ℝ} (hf : Continuous f) (hg : Continuous g)
      (s : K) (hne : f s ≠ g s) :
      ∀ᶠ t in 𝓝 s, (f t < g t ↔ f s < g s) := by
    rcases lt_or_gt_of_ne hne with h | h
    · filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt h] with t ht
      exact iff_of_true ht h
    · filter_upwards [hg.continuousAt.eventually_lt hf.continuousAt h] with t ht
      exact iff_of_false (not_lt_of_gt ht) (not_lt_of_gt h)
  let S (s : K) := @Finset.filter (Fin d) (fun i ↦ ev s i ∈ Ioo (α s) (β s))
    (fun _ ↦ Classical.propDecidable _) Finset.univ
  let R (s : K) := @Finset.filter (Fin d) (fun i ↦ ev s i ∉ Ioo (α s) (β s))
    (fun _ ↦ @instDecidableNot _ (Classical.propDecidable _)) Finset.univ
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_iff_continuousAt.mpr
  intro s
  have hidx : ∀ᶠ (t : K) in 𝓝 s, ∀ i, ev t i ∈ Ioo (α t) (β t) ↔
      ev s i ∈ Ioo (α s) (β s) := by
    apply Filter.eventually_all.mpr
    intro i
    have ha : α s ≠ ev s i := fun h ↦ (hoff s s.2).1
      (h.symm ▸ (hH s s.2).eigenvalues_mem_spectrum_real i)
    have hb : ev s i ≠ β s := fun h ↦ (hoff s s.2).2
      (h ▸ (hH s s.2).eigenvalues_mem_spectrum_real i)
    filter_upwards [horder hα.restrict (he i) s ha,
      horder (he i) hβ.restrict s hb] with t ha hb
    exact and_congr ha hb
  have hsets : ∀ᶠ (t : K) in 𝓝 s, S t = S s ∧ R t = R s := by
    filter_upwards [hidx] with t ht
    constructor
    · ext i
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using ht i
    · ext i
      simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using not_congr (ht i)
  by_cases hn : (S s).Nonempty ∧ (R s).Nonempty
  · have hfinite : Continuous (fun t : K ↦
        (S s).inf' hn.1 (fun i ↦ (R s).inf' hn.2 (fun j ↦ |ev t i - ev t j|))) :=
      Continuous.finset_inf'_apply hn.1 fun i _ ↦
        Continuous.finset_inf'_apply hn.2 fun j _ ↦ ((he i).sub (he j)).abs
    apply hfinite.continuousAt.congr_of_eventuallyEq
    filter_upwards [hsets] with t ht
    change exactGap H hH (fun s ↦ Ioo (α s) (β s)) t = _
    simp only [exactGap, dif_pos t.2]
    dsimp only [S, R, ev] at ht hn ⊢
    simp only [ht.1, ht.2, dif_pos hn, finiteSpectralDistance]
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hsets] with t ht
    change exactGap H hH (fun s ↦ Ioo (α s) (β s)) t = 0
    simp only [exactGap, dif_pos t.2]
    dsimp only [S, R, ev] at ht hn
    simp only [ht.1, ht.2, dif_neg hn]

end UnitaryProducts.PaperProof
