/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Citations
public import RoundedClocks.Appendix
public import RoundedClocks.Appendix.MultiplierMonotonicity
public import RoundedClocks.UnitSteps.TruncatedProductBounds

/-!
# Supporting steps for Theorem 4.6

The proof of Theorem 4.6 (`unitary_products`) uses:

* the signs of the constants `c₀`, `𝒩(w)`, `𝒩'(w)` and `𝒩(w) - 𝒩(0)` for `0 ≤ w < 2π`
  (Appendix B, from the positive Taylor series of `𝒩`);
* the least eigenvalue `a(s)` of `H(s)` is continuous (Bhatia, Corollary III.2.6), and the
  spectrum of `e^{-iH(s)}` is the exponential image of that of `H(s)`, so `W = e^{-iH}` satisfies
  (4.6) with this `a`;
* a `C²` family has a Lipschitz derivative with `L = ‖H''‖∞`;
* Lemma A.3(ii), bounded by its suprema over a cell of length `1/T`, summed over the `T` cells.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

/-- Matrices with the operator norm form a C⋆-algebra, for the continuous functional calculus
used in the spectral mapping of the phase. -/
noncomputable def unitaryProductsCStarAlgebra (n : ℕ) :
    CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) where

attribute [local instance] unitaryProductsCStarAlgebra

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "J" => Icc (0 : ℝ) 1

/-! ## The least eigenvalue and the phase (Bhatia, Corollary III.2.6) -/

/-- The decreasing list of eigenvalues of a Hermitian `M`, reindexed by `Fin d`, satisfies the
hypotheses of Bhatia, Corollary III.2.6, and its last entry is the least point of the spectrum. -/
theorem sorted_eigenvalues [NeZero d] {M : 𝕄} (hM : IsHermitian M) :
    IsDecreasingEigenvalueList M (hM.eigenvalues₀ ∘ finCongr (Fintype.card_fin d).symm) ∧
      IsLeast (spectrum ℝ M) ((hM.eigenvalues₀ ∘ finCongr (Fintype.card_fin d).symm)
        ⟨d - 1, Nat.sub_lt (NeZero.pos d) one_pos⟩) := by
  let e : Fin d ≃ Fin (Fintype.card (Fin d)) := finCongr (Fintype.card_fin d).symm
  have hanti : Antitone (hM.eigenvalues₀ ∘ e) :=
    hM.eigenvalues₀_antitone.comp_monotone fun _ _ h ↦ h
  have hspec : spectrum ℝ M = range (hM.eigenvalues₀ ∘ e) := by
    have h : hM.eigenvalues =
        hM.eigenvalues₀ ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm := rfl
    rw [hM.spectrum_real_eq_range_eigenvalues, h, EquivLike.range_comp,
      EquivLike.range_comp]
  refine ⟨⟨hanti, ?_⟩, ?_⟩
  · rw [hM.roots_charpoly_eq_eigenvalues₀, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
    rfl
  · rw [hspec]
    refine ⟨mem_range_self _, forall_mem_range.mpr fun j ↦ hanti ?_⟩
    change j.val ≤ d - 1
    omega

/-- Bhatia, Corollary III.2.6, at the bottom of the spectrum: the least eigenvalues of Hermitian
`A` and `B` differ by at most `‖A - B‖`. -/
theorem abs_sInf_spectrum_sub_le (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    [NeZero d] {A B : 𝕄} (hA : IsHermitian A) (hB : IsHermitian B) :
    |sInf (spectrum ℝ A) - sInf (spectrum ℝ B)| ≤ ‖A - B‖ := by
  rw [(sorted_eigenvalues hA).2.csInf_eq, (sorted_eigenvalues hB).2.csInf_eq]
  exact bhatia_corollary_III_2_6 d A B _ _ hA hB (sorted_eigenvalues hA).1
    (sorted_eigenvalues hB).1 _

/-- The least eigenvalue `a(s)` of a continuous Hermitian family is continuous on `[0,1]`
(Bhatia, Corollary III.2.6). -/
theorem continuousOn_sInf_spectrum (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) (hHc : ContinuousOn H J) :
    IsContinuousFamily (fun s ↦ sInf (spectrum ℝ (H s))) := by
  unfold IsContinuousFamily
  rw [Metric.continuousOn_iff] at hHc ⊢
  intro s hs ε hε
  obtain ⟨δ, hδ, h⟩ := hHc s hs ε hε
  refine ⟨δ, hδ, fun t ht hts ↦ ?_⟩
  rw [Real.dist_eq]
  refine (abs_sInf_spectrum_sub_le bhatia_corollary_III_2_6 (hH t ht) (hH s hs)).trans_lt ?_
  simpa only [dist_eq_norm] using h t ht hts

/-- Spectral mapping for the phase: `spec e^{-iA}` is the exponential image of `spec A`. -/
theorem spectrum_phase_image {A : 𝕄} (hA : IsHermitian A) :
    spectrum ℂ (exp (-I • A)) =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ A := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hn : IsStarNormal A := hsa.isStarNormal
  have he : exp (-I • A) = cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A := by
    have hh : cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A =
        cfc Complex.exp (cfc (fun z : ℂ ↦ -I * z) A) :=
      cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I * z) A hn
        Complex.continuous_exp.continuousOn (continuousOn_const.mul continuousOn_id)
    rw [hh, cfc_const_mul_id (-I) A, CFC.complex_exp_eq_normedSpace_exp]
  rw [he, cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) A hn
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn]
  rw [← hsa.spectrumRestricts.algebraMap_image, Set.image_image]
  rfl

/-! ## Suprema over `[0,1]` -/

/-- `‖f(s)‖ ≤ ‖f‖∞` for `f` continuous on `[0,1]` and `s ∈ [0,1]`. -/
theorem norm_le_supNorm_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f J) {s : ℝ} (hs : s ∈ J) : ‖f s‖ ≤ ‖f‖∞ :=
  le_csSup (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove (mem_image_of_mem _ hs)

/-- A pointwise bound on `[0,1]` bounds `‖f‖∞`. -/
theorem supNorm_le_of_forall {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {C : ℝ}
    (h : ∀ s ∈ J, ‖f s‖ ≤ C) : ‖f‖∞ ≤ C :=
  csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr h)

/-- `‖f‖∞ ≥ 0` for `f` continuous on `[0,1]`. -/
theorem supNorm_nonneg_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : ContinuousOn f J) : 0 ≤ ‖f‖∞ :=
  (norm_nonneg _).trans (norm_le_supNorm_of_continuousOn hf ⟨le_rfl, zero_le_one⟩)

/-! ## Calculus of `C²` families -/

/-- The derivative `H'` of a `C²` family is `C¹` on `[0,1]`. -/
theorem IsC2Family.deriv_contDiffOn {A : ℝ → 𝕄} (hC2 : IsC2Family A) :
    ContDiffOn ℝ 1 (∂A) J :=
  hC2.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)

/-- The second derivative `H''` of a `C²` family is continuous on `[0,1]`. -/
theorem IsC2Family.continuousOn_deriv2 {A : ℝ → 𝕄} (hC2 : IsC2Family A) :
    ContinuousOn (∂∂A) J :=
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

/-- The phase `W = e^{-iH}` of a `C²` family is `C²`. -/
theorem IsC2Family.phase {H : ℝ → 𝕄} (hC2 : IsC2Family H) :
    IsC2Family (fun s ↦ exp (-I • H s)) := by
  intro s hs
  have hanal : AnalyticAt ℂ (exp : 𝕄 → 𝕄) (-I • H s) :=
    NormedSpace.exp_analytic (𝕂 := ℂ) _
  exact (hanal.contDiffAt.restrict_scalars ℝ).comp_contDiffWithinAt s
    ((hC2 s hs).const_smul (-I))

/-! ## Lemma A.2 for `W = e^{-iH}` -/

/-- Lemma A.2 applied to `W = e^{-iH}` with `a(s)` the least eigenvalue of `H(s)`: `H` is the
logarithm of that lemma, so `‖H'‖ ≤ κ ‖W'‖` and `‖H''‖ ≤ κ ‖W''‖ + ‖W'‖²/cos²(w/4)`. -/
theorem phase_log_derivative_bounds (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * π) (hC2 : IsC2Family H)
    (hwidth : ∀ s ∈ J, HasEigenvalueDifferences (H s) w) :
    ∀ s ∈ J,
      ‖∂H s‖ ≤ κ w * ‖∂(fun t ↦ exp (-I • H t)) s‖ ∧
      ‖∂∂H s‖ ≤ κ w * ‖∂∂(fun t ↦ exp (-I • H t)) s‖ +
        ‖∂(fun t ↦ exp (-I • H t)) s‖ ^ 2 / Real.cos (w / 4) ^ 2 := by
  let a : ℝ → ℝ := fun s ↦ sInf (spectrum ℝ (H s))
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  have hmin (s : ℝ) (hs : s ∈ J) : IsLeast (spectrum ℝ (H s)) (a s) := by
    have h := (sorted_eigenvalues (hH s hs)).2
    rwa [← h.csInf_eq] at h
  -- every eigenvalue of `H(s)` lies in `[a(s), a(s) + w]`
  have hwindow (s : ℝ) (hs : s ∈ J) :
      HasRealSpectrumIn (H s) (Icc (a s) (a s + w)) := by
    intro x hx
    refine ⟨(hmin s hs).2 hx, ?_⟩
    have hd := (abs_le.mp (hwidth s hs x hx (a s) (hmin s hs).1)).2
    linarith
  have ha : IsContinuousFamily a :=
    continuousOn_sInf_spectrum bhatia_corollary_III_2_6 hH hC2.continuousOn
  have hW : IsUnitaryFamily W 0 1 := by
    intro s hs
    simpa [W, smul_smul] using phase_isUnitary (hH s hs) 1
  -- (4.6): the spectrum of `W(s)` lies in the arc `{e^{-iθ} : a(s) ≤ θ ≤ a(s) + w}`
  have harc : HasSpectrumInPhaseInterval W a w := by
    intro s hs z hz
    change z ∈ spectrum ℂ (exp (-I • H s)) at hz
    rw [spectrum_phase_image (hH s hs)] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hwindow s hs hx, rfl⟩
  obtain ⟨H₀, -, -, hunique, -, hb₀⟩ := walk_log hw0 hw ha hW harc hC2.phase
  -- `H` is the logarithm of Lemma A.2, by its uniqueness clause
  have heq : EqOn H₀ H J := fun s hs ↦
    (hunique s hs (H s) (hH s hs) (hwindow s hs) rfl).symm
  have hfirst : EqOn (∂H₀) (∂H) J := fun _ hs ↦ derivWithin_congr heq (heq hs)
  have hsecond : EqOn (∂∂H₀) (∂∂H) J := fun _ hs ↦ derivWithin_congr hfirst (hfirst hs)
  intro s hs
  rw [← hfirst hs, ← hsecond hs]
  exact hb₀ s hs

/-- The increment of the corrector is its derivative integral, including boundary cells. -/
theorem unitary_products_increment {F : ℝ → 𝕄} (hF : ContDiffOn ℝ 1 F J)
    {l r : ℝ} (hl : l ∈ J) (hr : r ∈ J) (hlr : l ≤ r) :
    F r - F l = ∫ s in l..r, derivWithin F J s := by
  have hsub : Icc l r ⊆ J := Icc_subset_Icc hl.1 hr.2
  have hc := hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hi : IntervalIntegrable (derivWithin F J)
      MeasureTheory.volume l r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    exact hc.mono hsub
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (hF.continuousOn.mono hsub) _ hi
  intro s hs
  have hsJ : s ∈ Ioo (0 : ℝ) 1 := ⟨hl.1.trans_lt hs.1, hs.2.trans_le hr.2⟩
  exact ((hF.differentiableOn (by norm_num) s
    (Ioo_subset_Icc_self hsJ)).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hsJ.1 hsJ.2)

/-! ## The jumps (Lemma A.3(ii)) -/

/-- Lemma A.3(ii) for `Ω = H`, bounded by its suprema over each cell of length `1/T` and summed
over `1 ≤ j ≤ T`: `Σ ‖Δ_j‖ ≤ (𝒩(w)‖H''‖∞ + 2𝒩'(w)‖W'‖∞‖H'‖∞ + (𝒩(w) - 𝒩(0))‖H'‖∞²)/T`. -/
theorem jump_sum_le (dieudonne_8_6_4 : Dieudonne_8_6_4)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π) (hwidth : ∀ s ∈ J, HasEigenvalueDifferences (H s) w)
    (hC2 : IsC2Family H) :
    ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤
      (𝒩 w * ‖∂∂H‖∞ + 2 * deriv 𝒩 w * ‖∂(fun t ↦ exp (-I • H t))‖∞ * ‖∂H‖∞ +
        (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2) / T := by
  let F : ℝ → 𝕄 := fun s ↦ 𝒩ad (H s) (∂H s)
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  set C := 𝒩 w * ‖∂∂H‖∞ + 2 * deriv 𝒩 w * ‖∂W‖∞ * ‖∂H‖∞ + (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2
  obtain ⟨hF, hb⟩ := end_value dieudonne_8_6_4 hw0 hw hH hwidth hC2
  have hN := 𝒩_nonneg_of_width hw0 hw
  have hN' := deriv_𝒩_nonneg hw0 hw
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := sub_nonneg.mpr (𝒩_zero_le hw0 hw)
  have hH1 := hC2.deriv_contDiffOn.continuousOn
  have hH2 := hC2.continuousOn_deriv2
  have hW1 : ContinuousOn (∂W) J := hC2.phase.deriv_contDiffOn.continuousOn
  have hW0 := supNorm_nonneg_of_continuousOn hW1
  -- Lemma A.3(ii), bounded by the suprema over `[0,1]`
  have hcell : ∀ s ∈ J, ‖derivWithin F J s‖ ≤ C := by
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
  -- one cell `[l, r] = [(j-1)/T, j/T]` of length `1/T`
  have hjump : ∀ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ ≤ C / T ^ 2 := by
    intro j hj
    obtain ⟨hj1, hjT⟩ := Finset.mem_Icc.mp hj
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjT' : (j : ℝ) ≤ T := by exact_mod_cast hjT
    have hr : (j : ℝ) / T ∈ J :=
      ⟨by positivity, (div_le_one hTpos).mpr hjT'⟩
    have hl : ((j : ℝ) - 1) / T ∈ J :=
      ⟨div_nonneg (by linarith) hTpos.le, (div_le_one hTpos).mpr (by linarith)⟩
    have hlr : ((j : ℝ) - 1) / T ≤ (j : ℝ) / T :=
      div_le_div_of_nonneg_right (by linarith) hTpos.le
    have hlen : |(j : ℝ) / T - ((j : ℝ) - 1) / T| = 1 / T := by
      rw [show (j : ℝ) / T - ((j : ℝ) - 1) / T = 1 / T by ring,
        abs_of_pos (by positivity)]
    -- The displayed integral identity precedes the cell estimate.
    have hintegral := unitary_products_increment hF hl hr
      (div_le_div_of_nonneg_right (by linarith : (j : ℝ) - 1 ≤ j) hTpos.le)
    have hidentity : (T : ℝ) * ‖Δ H T j‖ =
        ‖∫ s in (((j : ℝ) - 1) / T)..((j : ℝ) / T), derivWithin F J s‖ := by
      rw [← hintegral, Δ, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    have hbound :
        ‖∫ s in (((j : ℝ) - 1) / T)..((j : ℝ) / T), derivWithin F J s‖ ≤
          C * (1 / T) := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := derivWithin F J) (C := C) (a := ((j : ℝ) - 1) / T)
        (b := (j : ℝ) / T) (fun s hs ↦ hcell s (by
          rw [uIoc_of_le hlr] at hs
          exact ⟨hl.1.trans hs.1.le, hs.2.trans hr.2⟩))
      rwa [hlen] at hi
    calc
      ‖Δ H T j‖ = 1 / T *
          ‖∫ s in (((j : ℝ) - 1) / T)..((j : ℝ) / T), derivWithin F J s‖ := by
        rw [← hidentity]
        field_simp
      _ ≤ 1 / T * (C * (1 / T)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = C / T ^ 2 := by ring
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 T, C / T ^ 2 := Finset.sum_le_sum hjump
    _ = T * (C / T ^ 2) := by simp
    _ = C / T := by field_simp

end RoundedClocks
