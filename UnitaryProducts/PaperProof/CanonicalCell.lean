/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.LocalCell
public import UnitaryProducts.PaperProof.ExponentialDefinitions
public import UnitaryProducts.Corrector.SineBounds
/-! # The canonical cell lemma in Appendix A -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Assemble the canonical pieces by Theorem 2.2 for the two supplied evolutions.
The cell boundary terms and the residual integral are kept separate. -/
theorem canonical_cell_comparison_assembly {T : ℝ} (hT : 0 < T) {N : ℕ}
    (hN1 : 0 < N) (H Hd U Vt : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hVt : IsEvolution (fun t ↦ H (sample N (t / T))) Vt 0 T) (B E : ℝ)
    (hboundary : let Yr := allSampleCorrectorFamily T N H Hd hH
      ‖Yr 0 0‖ + ‖Yr N 0‖ +
        (∑ j ∈ Finset.Icc 1 N, ‖Yr j (-(1 / 2)) - Yr (j - 1) (1 / 2)‖) ≤ B)
    (hR : IntervalIntegrable
      (uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH)) volume 0 1)
    (hres : (∫ s in (0 : ℝ)..1,
      ‖uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH) s‖) ≤ E) :
    ‖Vt T - U T‖ ≤ B + E := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN1
  -- The rounded evolution and the normalized generators TH and TĤ.
  let V := fun s ↦ Vt (T * s)
  obtain ⟨hu, hV⟩ := normalized_rounded_evolutions hT hU hVt
  let Yr := allSampleCorrectorFamily T N H Hd hH
  let R := uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH)
  have hsplit : ‖star (U T) * V 1 - 1‖ ≤ ‖Yr 0 0‖ + ‖Yr N 0‖ +
      (∑ j ∈ Finset.Icc 1 N, ‖Yr j (-(1 / 2)) - Yr (j - 1) (1 / 2)‖) +
        (∫ s in (0 : ℝ)..1, ‖R s‖) := by
    let J := ∑ j ∈ Finset.Icc 1 N, ‖Yr j (-(1 / 2)) - Yr (j - 1) (1 / 2)‖
    let q := fun j : ℕ ↦ max 0 (min 1 (((j : ℝ) - 1 / 2) / N))
    have hcontract (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (A : 𝕄) :
        ‖star (U (T * s)) * A * V s‖ ≤ ‖A‖ := by
      have mem (W : 𝕄) := (Matrix.mem_unitaryGroup_iff' (A := W)).mpr
      rw [CStarRing.norm_mul_mem_unitary _ (mem _ (hV.2.2.1 s hs)),
        CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (mem _ (hu.2.2.1 s hs)))]
    have hqj (j : ℕ) (hj : j < N) : q (j + 1) = ((j : ℝ) + 1 / 2) / N := by
      have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast (show j + 1 ≤ N by omega)
      have he : ((j + 1 : ℕ) : ℝ) - 1 / 2 = j + 1 / 2 := by push_cast; ring
      dsimp [q]; rw [he, min_eq_right ((div_le_one hn).mpr (by linarith)),
        max_eq_right (div_nonneg (by positivity) hn.le)]
    -- The normalized cut points are clamped to [0,1]; the first and last are 0 and 1.
    have hq0 : q 0 = 0 := by simp [q, div_nonpos_iff, hn.le]
    have hqN : q (N + 1) = 1 := by
      simp [q, max_eq_iff, le_div_iff₀ hn]
      constructor <;> linarith
    have hYr := contDiff_uniformCorrectionPiece T N H Hd hH
    have he := (comparison_with_jumps N q
      (monotone_const.max (monotone_const.min ((Nat.mono_cast.add_const _).div_const hn.le)))
      hq0 hqN
      (fun s ↦ T • H s) (fun s ↦ T • H (sample N s)) (fun s ↦ U (T * s)) V R
      (fun j s ↦ Yr j ((N : ℝ) * s - j)) ∅ countable_empty
      hu hV hR
      (fun j _ ↦ (hYr j).continuous.continuousOn)
      (by
        intro j _ s hs _
        -- Inside cell j, |Ns - j| < 1/2. Splitting the two clamps handles
        -- the first and last half-cells along with the interior cells.
        have hclock : clock (N * s) = (j : ℤ) := clock_eq_of_abs_sub_lt (by
          simp only [mem_Ioo, q, max_lt_iff, lt_min_iff, lt_max_iff, min_lt_iff,
            div_lt_iff₀ hn, lt_div_iff₀ hn, Nat.cast_add, Nat.cast_one] at hs
          rcases hs with ⟨⟨hs0, hs1 | hlo⟩, hhi | ⟨hs1', hhi'⟩⟩ <;>
            refine abs_lt.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith)
        convert ((hYr j).differentiable one_ne_zero s).hasDerivAt using 1
        simp only [R, uniformPieceResidual, hclock, globalResidual, uniformCorrectionPiece,
          Yr, Int.cast_natCast, smul_mul_assoc, mul_smul_comm, ← smul_sub]
        abel))
    simp only [smul_sub, ← add_sub_assoc] at he
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      mul_zero, mul_one, sub_self] at he
    rw [he, intervalIntegral.integral_smul, add_sub_assoc, ← smul_sub, ← smul_add, ← smul_sub,
      norm_smul, Complex.norm_I, one_mul]
    calc
      _ ≤ (∫ s in (0 : ℝ)..1, ‖R s‖) + (‖Yr N 0‖ + ‖Yr 0 0‖) + J := by
        apply norm_sub_le_of_le (norm_add_le_of_le ?_ ?_) ?_
        · exact intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Eventually.of_forall fun s hs ↦ hcontract s (Ioc_subset_Icc_self hs) (R s)) hR.norm
        · -- Unitary contraction bounds the two outer endpoint terms.
          simpa only [mul_one] using
            norm_sub_le_of_le (hcontract 1 ⟨zero_le_one, le_rfl⟩ (Yr N 0)) (le_refl ‖Yr 0 0‖)
        · dsimp only [J]
          rw [sum_Icc_one_eq_sum_range]
          simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
          refine norm_sum_le_of_le _ fun j hj ↦ ?_
          refine (hcontract _ ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ _).trans_eq ?_
          norm_num only [hqj j (Finset.mem_range.mp hj), ← mul_div_assoc,
            mul_div_cancel_left₀ _ hn.ne', Nat.cast_add, Nat.cast_one,
            add_sub_add_left_eq_sub, add_sub_cancel_left]
      _ = _ := by ring
  have hglobal := hsplit.trans (add_le_add hboundary hres)
  have hunit := Matrix.mem_unitaryGroup_iff'.mpr (hU.2.2.1 T ⟨hT.le, le_rfl⟩)
  rw [← Prose.unitary_difference_norm ⟨U T, hunit⟩] at hglobal
  simp only [V, mul_one] at hglobal
  exact hglobal

/-- The closed residual and boundary estimates give the comparison on unit cells. -/
theorem canonical_cell_bound_LM [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M w : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    (hw : w < 2 * π) (hwidth : AllSampleWidth T T H hH w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    let c₀ := frameBound w - frameBound (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    let Yb := fun s ↦ frameOp (H s) (Hd s)
    let sigma := ∑ j ∈ Finset.range T,
      ‖Yb (((j : ℝ) + 1) / T) - Yb ((j : ℝ) / T)‖
    ‖V T - U T‖ ≤ (1 / T : ℝ) * (2 * c₀ * L + M / 24 + c₁ * L ^ 2 + sigma) := by
  intro c₀ c₁ Yb sigma
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hb := (lem_boundary_uniform ht hT H Hd hH hd hbd hl hw hwidth).1
  have hr := uniform_residual_integral ht.le hT H Hd hH hd hbd hl hw hwidth
  have hc := canonical_cell_comparison_assembly ht hT H Hd U V hH hU hV _ _ hb hr.1 hr.2.2
  simp only [div_self ht.ne', one_smul, pow_two, div_mul_eq_div_div,
    sum_Icc_one_eq_sum_range, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hc
  exact hc.trans_eq (by dsimp [c₀, c₁, sigma, Yb]; ring)

/-- Pointwise multiplier variation, by the series split and the mean value theorem. -/
theorem canonical_cell_variation (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 2 * π)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hwa : ∀ p q, |(hH a ha).eigenvalues p - (hH a ha).eigenvalues q| ≤ w)
    (hwb : ∀ p q, |(hH b hb).eigenvalues p - (hH b hb).eigenvalues q| ≤ w) :
    ‖frameOp (H b) (Hd b) - frameOp (H a) (Hd a)‖ ≤
      (frameBound w * M + 2 * frameLip w * L ^ 2) * |b - a| := by
  have hsplit : ‖frameOp (H b) (Hd b) - frameOp (H a) (Hd a)‖ ≤
      frameBound w * ‖Hd b - Hd a‖ + 2 * frameLip w * ‖H b - H a‖ * ‖Hd a‖ := by
    rcases Nat.eq_zero_or_pos d with rfl | hdim
    · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
      simp only [hz, norm_zero, mul_zero, add_zero, le_refl]
    · letI : NeZero d := ⟨hdim.ne'⟩
      have hca := norm_sub_smul_one_le_of_eigenvalues (hH a ha) hw₀ (eigen_interval (hH a ha) hwa)
      have hcb := norm_sub_smul_one_le_of_eigenvalues (hH b hb) hw₀ (eigen_interval (hH b hb) hwb)
      exact (Prose.frameOp_change_split (H a) (H b) (Hd a) (Hd b)).trans
        (Prose.frameOp_split_norm_bound hw hca hcb)
  have hHdiff := norm_sub_le_of_derivWithin_le hd hbd a ha b hb
  have hL : 0 ≤ L := (norm_nonneg _).trans (hbd a ha)
  have hN := frameBound_nonneg hw₀
  have hN' := frameLip_nonneg hw₀
  apply hsplit.trans
  calc
    _ ≤ frameBound w * (M * |b-a|) + 2 * frameLip w * (L * |b-a|) * L :=
      add_le_add (mul_le_mul_of_nonneg_left (hl a ha b hb) hN)
        (mul_le_mul (mul_le_mul_of_nonneg_left hHdiff (by positivity)) (hbd a ha)
          (norm_nonneg _) (by positivity))
    _ = _ := by ring


/-- Theorem 4.2: apply the comparison identity, bound the boundary terms,
then integrate the residual profile by its three even cell moments. -/
theorem unit_steps_uncentred [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd U V : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M w : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    (hw : w < 2 * π) (hwidth : AllSampleWidth T T H hH w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) :
    let c₀ := frameBound w - frameBound (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    let Yb := fun s ↦ frameOp (H s) (Hd s)
    let sigma := ∑ j ∈ Finset.range T,
      ‖Yb (((j : ℝ) + 1) / T) - Yb ((j : ℝ) / T)‖
    ‖V T - U T‖ ≤ (1 / T : ℝ) * (c₀ * (‖Hd 0‖ + ‖Hd 1‖) + M / 24 + c₁ * L ^ 2 + sigma) := by
  intro c₀ c₁ Yb sigma
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  -- Start with Theorem 2.2, then supply endpoints, jumps, and the residual moments.
  have hcomparison := canonical_cell_comparison_assembly ht hT H Hd U V hH hU hV
  have hb := uniform_boundary_endpoints ht hT H Hd hH hw hwidth
  have hr := unit_residual_integral hT H Hd hH hd hbd hl hw hwidth
  have hres := cor_residual hT H Hd hH hd hl hw hwidth
  have hsup : unitSupNorm Hd ≤ L :=
    csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr hbd)
  have hsup0 : 0 ≤ unitSupNorm Hd := (norm_nonneg (Hd 0)).trans
    (norm_le_unitSupNorm (continuousOn_of_norm_sub_le hl) (by norm_num))
  have hw0 : 0 ≤ w := by simpa using hwidth 0 (by omega) 0 0
  have hc1 : 0 ≤ (frameBound w - frameBound (w / 2) / 2) / 4 + 1 / 64 := by
    have := center_bound_nonneg hw0 hw
    positivity
  have hresL := hres.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hsup0 hsup 2) hc1)) (by positivity : 0 ≤ (1 / T : ℝ)))
  rw [unitPhysicalResidual_integral hT H Hd hH] at hresL
  have hc := hcomparison _ _ hb hr.1 hresL
  simp only [div_self ht.ne', one_smul, pow_two, div_mul_eq_div_div,
    sum_Icc_one_eq_sum_range, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hc
  exact hc.trans_eq (by dsimp [c₀, c₁, sigma, Yb]; ring)


end UnitaryProducts.PaperProof
