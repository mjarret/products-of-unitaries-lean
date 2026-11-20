/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.UniformTruncation
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.ChainSteps
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.Prose.FineSteps

/-! # Centering and the exact sample error in the unit-step theorem -/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
open UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The two products are endpoints of their piecewise-constant evolutions
by equation `eq:piecewise-product`. Duhamel's bound on `[0,T]`, split into
its `T` unit intervals, counts precisely the sampled generators in the product. -/
theorem unitProduct_sample_error_chain {H A : ℝ → 𝕄} (T : ℕ)
    (hH : IsTimeDepHamiltonian H)
    (hA : IsTimeDepHamiltonian A) :
    ‖(unitProduct A T).1 - (unitProduct H T).1‖ ≤
        (∫ t in (0 : ℝ)..T, ‖H ((⌊t⌋ : ℝ) / T) - A ((⌊t⌋ : ℝ) / T)‖) ∧
      (∫ t in (0 : ℝ)..T, ‖H ((⌊t⌋ : ℝ) / T) - A ((⌊t⌋ : ℝ) / T)‖) =
        ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [unitProduct, pieceProduct]
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  let K := fun (B : ℝ → 𝕄) (t : ℝ) ↦ B ((⌊t⌋ : ℝ) / T)
  have hpieces (B : ℝ → 𝕄) (j : ℕ) (_hj : j < T)
      (t : ℝ) (hmem : t ∈ Ioo (j : ℝ) (j + 1 : ℕ)) :
      K B t = B ((j : ℝ) / T) := by
    have hf : ⌊t⌋ = (j : ℤ) := by
      apply Int.floor_eq_iff.mpr
      simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
        (show (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ) from ⟨hmem.1.le, hmem.2⟩)
    simp only [K, hf, Int.cast_natCast]
  have hr (B : ℝ → 𝕄) : IsRegulated (K B) 0 T := by
    simpa only [Nat.cast_zero] using
      piecewise_regulated (K B) (fun j : ℕ ↦ (j : ℝ)) (fun j ↦ B ((j : ℝ) / T)) T
        (hpieces B)
  have hprod (B : ℝ → 𝕄) :
      pieceProduct (scheduleDuration (fun j : ℕ ↦ (j : ℝ)) T)
        (fun j ↦ B ((j : ℝ) / T)) T = (unitProduct B T).1 := by
    have hacc : ∀ n ≤ T,
        pieceProduct (scheduleDuration (fun j : ℕ ↦ (j : ℝ)) T)
          (fun j ↦ B ((j : ℝ) / T)) n =
        pieceProduct (fun _ ↦ 1) (fun j ↦ B ((j : ℝ) / T)) n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        simp only [pieceProduct, scheduleDuration, if_pos (show n < T by omega),
          Nat.cast_add, Nat.cast_one, add_sub_cancel_left, ih (by omega)]
    exact hacc T le_rfl
  have hexists (B : ℝ → 𝕄) (hB : IsTimeDepHamiltonian B) :
      ∃ U, IsEvolution (K B) U 0 T ∧ (unitProduct B T).1 = U T := by
    have hKB : ∀ t ∈ Icc (0 : ℝ) T, (K B t).IsHermitian := by
      intro t htmem
      apply hB
      refine ⟨div_nonneg ?_ ht.le, (div_le_one ht).mpr ((Int.floor_le t).trans htmem.2)⟩
      exact_mod_cast Int.floor_nonneg.mpr htmem.1
    obtain ⟨U, hU, he⟩ := Prose.pieceProduct_eq_evolution_of_pieces ht hKB T
      (fun j : ℕ ↦ (j : ℝ)) ⟨fun _ _ h ↦ Nat.cast_le.mpr h, by simp, rfl⟩
      (fun j ↦ B ((j : ℝ) / T))
      (fun j hj ↦ hB _ (walkCubic_sample hj.le)) (hpieces B)
    exact ⟨U, hU, (hprod B).symm.trans he⟩
  obtain ⟨U, hU, heU⟩ := hexists H hH
  obtain ⟨V, hV, heV⟩ := hexists A hA
  have hb := duhamel_bound ht.le (hr H) (hr A) hU hV
  have hi := ((hr H).intervalIntegrable_on ht.le).sub ((hr A).intervalIntegrable_on ht.le)
  have hicell (j : ℕ) (hj : j < T) :
      IntervalIntegrable (fun t ↦ ‖K H t - K A t‖) volume (j : ℝ) (j + 1 : ℕ) := by
    apply hi.norm.mono_set
    rw [uIcc_of_le (by exact_mod_cast Nat.le_succ j), uIcc_of_le ht.le]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (Nat.cast_le.mpr hj)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hicell
  simp only [Nat.cast_zero] at hsplit
  refine ⟨?_, hsplit.symm.trans ?_⟩
  · simpa only [heV, heU] using hb
  apply Finset.sum_congr rfl
  intro j hj
  have hjT := Finset.mem_range.mp hj
  calc
    (∫ t in (j : ℝ)..(j + 1 : ℕ), ‖K H t - K A t‖) =
        ∫ _t in (j : ℝ)..(j + 1 : ℕ), ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne ((j + 1 : ℕ) : ℝ)] with t hne
      intro hmem
      rw [uIoc_of_le (by exact_mod_cast Nat.le_succ j)] at hmem
      have hcell : t ∈ Ioo (j : ℝ) (j + 1 : ℕ) :=
        ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩
      rw [hpieces H j hjT t hcell, hpieces A j hjT t hcell]
    _ = ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by simp

/-- The sample sum bound is the last line of the Duhamel chain in the proof
of Theorem 4.2. Both the integral inequality and its cell sum appear above. -/
theorem unitProduct_sample_error {H A : ℝ → 𝕄} (T : ℕ)
    (hH : IsTimeDepHamiltonian H)
    (hA : IsTimeDepHamiltonian A) :
    ‖(unitProduct A T).1 - (unitProduct H T).1‖ ≤
      ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
  obtain ⟨hduhamel, hsum⟩ := unitProduct_sample_error_chain T hH hA
  exact hduhamel.trans_eq hsum

/-- The single triangle-inequality display in the unit-step comparison, after unitary invariance. -/
theorem unitProduct_truncation_split {H A : ℝ → 𝕄} (T : ℕ)
    (hH : IsTimeDepHamiltonian H) (X : 𝕄) :
    ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - X‖ ≤
      ‖(unitProduct A T).1 - (unitProduct H T).1‖ +
        ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - X‖ := by
  rw [← uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num)),
    ← uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

end UnitaryProducts.PaperProof
