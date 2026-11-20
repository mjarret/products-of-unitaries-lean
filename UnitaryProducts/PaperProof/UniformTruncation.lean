/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.ChainSteps
public import Mathlib.Algebra.Order.Round
public import UnitaryProducts.Evolution.RegulatedComparison
public import UnitaryProducts.Evolution.RoundedClockEvolution
public import UnitaryProducts.Spectral.SinTheta
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Analysis.Real.Pi.Bounds
public import UnitaryProducts.PaperProof.ExTruncationBits

/-!
# Entry truncation for the rounded clock

## Declarations

- `exists_rounded_evolution`
- `uniform_bit_sample_error`
- `uniform_bit_sample_error_sigma`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A rounded Hermitian path has an evolution whose final value is the phased unit product. -/
theorem exists_rounded_evolution {T : ℝ} {N : ℕ} (hT : 0 < T) (hN : 0 < N)
    (K : ℝ → 𝕄) (hK : IsTimeDepHamiltonian K) :
    ∃ V, IsEvolution (fun t ↦ K (sample N (t / T))) V 0 T ∧
      V T = evol (K 1) (T / (2 * N)) *
        (unitProduct (fun s ↦ (T / N) • K s) N).1 * evol (K 0) (-(T / (2 * N))) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr : IsRegulated (fun s ↦ K (sample N s)) 0 1 := by
    simpa only [sample, clock, mul_comm] using
      regulated_unscale hn (rounded_hamiltonian_regulated K N)
  obtain ⟨V, hV, -⟩ := exists_unique_evolution
    (fun t ↦ K (sample N (t / T))) T hT
    (fun t ht ↦ hK _ (sample_mem (N := N)
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩))
    (regulated_rescale hT hr)
  refine ⟨V, hV, regulated_evolution_rounded.2 K hK T N hT hN V ?_⟩
  simpa only [sample, clock, mul_div_assoc] using hV

/-- Example 3.2 on the complete sample grid. The sparsity bound is on the error
matrix at each sample; it is exactly the parameter `σ_k` in the bit estimate. -/
theorem uniform_bit_sample_error {H : ℝ → 𝕄} {N : ℕ}
    (hH : IsTimeDepHamiltonian H) (k σ : ℕ)
    (hs : ∀ j : Fin (N + 1), RowSparse σ
      (H ((j : ℝ) / N) - scalarEntryMap (truncBits k) (H ((j : ℝ) / N)))) :
    (⨆ j : Fin (N + 1),
      ‖H ((j : ℝ) / N) - scalarEntryMap (truncBits k) (H ((j : ℝ) / N))‖) ≤
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ := by
  apply ciSup_le
  intro j
  exact (ex_truncation_bits (d := d) k).2 _ σ
    (hH _ (walkCubic_sample (by omega))) (hs j)

/-- Example 3.2 with the paper's literal changed-entry sparsity `σ_k`: the
supremum over all path times and all rows, rather than a supplied sparsity bound.
The error maximum includes both endpoints of the complete sample grid. -/
theorem uniform_bit_sample_error_sigma {H : ℝ → 𝕄} {N : ℕ}
    (hH : IsTimeDepHamiltonian H) (k : ℕ) :
    let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
    (⨆ j : Fin (N + 1),
      ‖H ((j : ℝ) / N) - scalarEntryMap (truncBits k) (H ((j : ℝ) / N))‖) ≤
      Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ := by
  classical
  intro σ
  have hb (s : Icc (0 : ℝ) 1) : BddAbove (Set.range fun i : Fin d ↦
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card) :=
    (Set.finite_range _).bddAbove
  have hbpath : BddAbove (Set.range fun s : Icc (0 : ℝ) 1 ↦
      ⨆ i : Fin d, (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card) := by
    exact ⟨d, Set.forall_mem_range.mpr fun s ↦ ciSup_le' fun i ↦
      (Finset.card_filter_le _ _).trans (by simp)⟩
  apply uniform_bit_sample_error hH k σ
  intro j i
  let s : Icc (0 : ℝ) 1 := ⟨(j : ℝ) / N, walkCubic_sample (by omega)⟩
  change (Finset.univ.filter fun l ↦ H s i l - truncHerm k (H s) i l ≠ 0).card ≤ σ
  simp only [sub_ne_zero]
  simpa only [σ, ne_comm] using (le_ciSup (hb s) i).trans (le_ciSup hbpath s)

end UnitaryProducts.PaperProof
