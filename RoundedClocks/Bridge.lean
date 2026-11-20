/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import UnitaryProducts

/-!
# The definitions of the paper agree with those of the proofs

The proofs in `UnitaryProducts` work with their own encodings of the paper's objects. Each lemma
here identifies one definition of `RoundedClocks.Definitions` with its encoding, so that every
statement of the paper is proved by the corresponding result of `UnitaryProducts`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace Bridge

/-! ## Section 2 -/

theorem evolutionOf_eq (G : ℝ → 𝕄) (T : ℝ) :
    evolutionOf G T = UnitaryProducts.Paper.generatedEvolution G T := rfl

theorem evolution_eq (H : ℝ → 𝕄) (T : ℝ) :
    evolution H T = UnitaryProducts.Paper.evolution H T := rfl

theorem roundedEvolution_eq (H : ℝ → 𝕄) (T : ℕ) :
    roundedEvolution H T = UnitaryProducts.Paper.roundedEvolution H T := by
  unfold roundedEvolution UnitaryProducts.Paper.roundedEvolution
  rw [evolutionOf_eq]
  congr 1
  funext t
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [UnitaryProducts.Paper.UnitStepsProse.sample]
  · rw [UnitaryProducts.Paper.roundedEvolution_clock hT]

/-- `e^{-iuG}` in the paper's notation is `evol G u` in the proofs. -/
theorem evol_eq (G : 𝕄) (u : ℝ) :
    UnitaryProducts.evol G u = exp ((-(u * I)) • G) := by
  simp only [UnitaryProducts.evol]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  ring_nf

theorem pieceProduct_eq (τ : ℕ → ℝ) (G : ℕ → 𝕄) (n : ℕ) :
    UnitaryProducts.pieceProduct τ G n =
      ((List.range n).reverse.map fun j ↦ UnitaryProducts.evol (G j) (τ j)).prod := by
  induction n with
  | zero => simp [UnitaryProducts.pieceProduct]
  | succ n ih => simp [UnitaryProducts.pieceProduct, List.range_succ, ih]

theorem sampleProduct_eq (W : ℝ → 𝕄) (T n : ℕ) :
    UnitaryProducts.stepProduct W T n =
      ((List.range n).reverse.map fun j : ℕ ↦ W (j / T)).prod := by
  induction n with
  | zero => simp [UnitaryProducts.stepProduct]
  | succ n ih => simp [UnitaryProducts.stepProduct, List.range_succ, ih]

theorem sampleProduct_eq_walk (W : ℝ → 𝕄) (T : ℕ) :
    sampleProduct W T = (UnitaryProducts.Paper.walk W T).2 := by
  simp [sampleProduct, UnitaryProducts.Paper.walk, sampleProduct_eq]

theorem stepProduct_eq (H : ℝ → 𝕄) (T : ℕ) :
    stepProduct H T = (UnitaryProducts.Paper.unitProduct H T).1 := by
  simp [stepProduct, sampleProduct, UnitaryProducts.Paper.unitProduct, pieceProduct_eq,
    UnitaryProducts.evol]

theorem isUnitary_iff {A : 𝕄} : IsUnitary A ↔ A ∈ unitary 𝕄 :=
  Matrix.mem_unitaryGroup_iff'.symm

/-! ## Section 3 -/

theorem bitTruncation_eq (k : ℕ) : bitTruncation k = UnitaryProducts.truncBits k := by
  funext x
  rw [UnitaryProducts.PaperProof.truncBits_eq_sign_floor, bitTruncation]

theorem truncHerm_eq (k : ℕ) (A : 𝕄) :
    UnitaryProducts.truncHerm k A = entrywise (bitTruncation k) A := by
  ext p q
  simp [UnitaryProducts.truncHerm, UnitaryProducts.truncBitsC, entrywise,
    bitTruncation_eq]

theorem midpointProduct_eq (A : ℝ → 𝕄) (T : ℝ) (N : ℕ) (s : ℕ → ℝ) :
    midpointProduct A T N s = UnitaryProducts.Paper.midpointProductOver A T N s := by
  rw [UnitaryProducts.Paper.midpointProductOver_eq, pieceProduct_eq, midpointProduct]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' : j < N := by simpa using hj
  simp only [evol_eq, UnitaryProducts.scheduleDuration, if_pos hj']
  congr 2
  push_cast
  ring

/-- The checkpoints `s_0, …, s_N`, held at `s_N` after index `N`. -/
def freeze (N : ℕ) (s : ℕ → ℝ) : ℕ → ℝ := fun j ↦ s (min j N)

theorem freeze_of_le {N j : ℕ} (s : ℕ → ℝ) (hj : j ≤ N) : freeze N s j = s j := by
  simp [freeze, min_eq_left hj]

/-- Held after index `N`, checkpoints form a nondecreasing sequence of the proofs. -/
theorem checkpoints_partition {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    UnitaryProducts.PaperProof.IsCheckpointPartition N (freeze N s) := by
  refine ⟨monotone_nat_of_le_succ fun j ↦ ?_, by simp [freeze, hs.2.1],
    by simp [freeze, hs.2.2]⟩
  rcases lt_or_ge j N with hj | hj
  · rw [freeze_of_le s hj.le, freeze_of_le s hj]
    exact hs.1 j hj
  · simp [freeze, min_eq_right hj, min_eq_right (hj.trans j.le_succ)]

theorem checkpoints_of_partition {N : ℕ} {s : ℕ → ℝ}
    (hs : UnitaryProducts.PaperProof.IsCheckpointPartition N s) : IsCheckpoints N s :=
  ⟨fun j _ ↦ hs.1 j.le_succ, hs.2⟩

theorem midpointProduct_freeze (A : ℝ → 𝕄) (T : ℝ) (N : ℕ) (s : ℕ → ℝ) :
    midpointProduct A T N (freeze N s) = midpointProduct A T N s := by
  unfold midpointProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  have hj' : j < N := by simpa using hj
  rw [freeze_of_le s hj'.le, freeze_of_le s hj']

theorem hasMidpointError_freeze (H : ℝ → 𝕄) (N : ℕ) (s : ℕ → ℝ) (ε : ℝ) :
    HasMidpointError H N (freeze N s) ε ↔ HasMidpointError H N s ε := by
  unfold HasMidpointError
  refine forall_congr' fun j ↦ forall_congr' fun hj ↦ ?_
  rw [freeze_of_le s hj.le, freeze_of_le s hj]

/-- Each row of `H(s) - H^{(k)}(s)` has at most `σ_k` nonzero entries. -/
theorem rowSparse_sparsity (k : ℕ) (H : ℝ → 𝕄) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    UnitaryProducts.RowSparse (sparsity k H) (H s - entrywise (bitTruncation k) (H s)) := by
  intro p
  have hbdd : ∀ t : Icc (0 : ℝ) 1, BddAbove (Set.range fun p : Fin d ↦
      (Finset.univ.filter fun q ↦ entrywise (bitTruncation k) (H t) p q ≠ H t p q).card) :=
    fun t ↦ ⟨d, by rintro _ ⟨p, rfl⟩; exact (Finset.card_filter_le _ _).trans (by simp)⟩
  have hbdd' : BddAbove (Set.range fun t : Icc (0 : ℝ) 1 ↦ ⨆ p : Fin d,
      (Finset.univ.filter fun q ↦ entrywise (bitTruncation k) (H t) p q ≠ H t p q).card) := by
    refine ⟨d, ?_⟩
    rintro _ ⟨t, rfl⟩
    rcases isEmpty_or_nonempty (Fin d) with h | h
    · simp
    exact ciSup_le fun p ↦ (Finset.card_filter_le _ _).trans (by simp)
  calc (Finset.univ.filter fun q ↦ (H s - entrywise (bitTruncation k) (H s)) p q ≠ 0).card
      = (Finset.univ.filter fun q ↦ entrywise (bitTruncation k) (H s) p q ≠ H s p q).card := by
        congr 1; ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Matrix.sub_apply, ne_eq,
          sub_eq_zero]
        exact not_congr eq_comm
    _ ≤ ⨆ p : Fin d,
          (Finset.univ.filter fun q ↦ entrywise (bitTruncation k) (H s) p q ≠ H s p q).card :=
        le_ciSup (hbdd ⟨s, hs⟩) p
    _ ≤ sparsity k H := le_ciSup hbdd' (⟨s, hs⟩ : Icc (0 : ℝ) 1)

/-! ## Section 4 and Appendix B -/

theorem deriv01_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∂f = derivWithin f (Icc (0 : ℝ) 1) := rfl

theorem supNorm_eq {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    ‖f‖∞ = UnitaryProducts.Paper.unitSupNorm f := rfl

theorem HasLipschitzDerivative.paper {H : ℝ → 𝕄} {L : ℝ} (h : HasLipschitzDerivative H L) :
    UnitaryProducts.Paper.HasLipschitzDerivative H (∂H) L :=
  ⟨fun s hs ↦ (h.1 s hs).hasDerivWithinAt, fun s hs t ht ↦ h.2 t ht s hs⟩

theorem HasLipschitzDerivative.continuousOn {H : ℝ → 𝕄} {L : ℝ}
    (h : HasLipschitzDerivative H L) : ContinuousOn H (Icc 0 1) :=
  h.1.continuousOn

theorem ℰ_eq (w L : ℝ) (H : ℝ → 𝕄) : ℰ w L H = UnitaryProducts.Paper.hamiltonianEnergy w L H :=
  rfl

theorem 𝒩ad_eq (Ω E : 𝕄) : 𝒩ad Ω E = UnitaryProducts.Paper.paperFrameOp Ω E := by
  unfold 𝒩ad UnitaryProducts.Paper.paperFrameOp
  have h𝒩 : (𝒩 : ℝ → ℝ) = UnitaryProducts.Corrector.frameMult := rfl
  split_ifs <;> try rfl
  simp [UnitaryProducts.Paper.unitComparisonObjects,
    UnitaryProducts.Paper.UnitStepsProse.complexSpectralMultiplier,
    h𝒩, ← UnitaryProducts.WalkCut.complexFrameMult_ofReal]

theorem Δ_eq (H : ℝ → 𝕄) (T j : ℕ) :
    Δ H T j = UnitaryProducts.PaperProof.paperClockJump H (∂H) T j := by
  simp only [Δ, UnitaryProducts.PaperProof.paperClockJump, 𝒩ad_eq, one_div]

end Bridge

end RoundedClocks
