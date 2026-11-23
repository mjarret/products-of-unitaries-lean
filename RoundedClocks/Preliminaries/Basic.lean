/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Citations

/-!
# Shared preliminary facts

"`G` generates `V`" (equation (2.1)) has four parts: `V` is continuous, `V(a) = 1`, `V` is
unitary-valued, and `i V'(t) = G(t) V(t)` for all but countably many `t`. Checkpoints
`0 = s₀ ≤ ⋯ ≤ s_N = 1` have three parts, and a regulated time-dependent Hamiltonian has two. This
file names each part, so that a proof says which one it uses. It also shows that `evolutionOf G T`
is an evolution of `G` as soon as `G` generates one, and that times `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ` are
nondecreasing in the index. The matrix facts used across sections are collected here as well:
Hermitian exponentials and real multiples, unitary norm identities, decreasing eigenvalue lists,
and spectral projectors.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ## Hermitian matrices and unitaries -/

/-- The exponential `e^{-iuA}` is unitary for Hermitian `A`. -/
theorem exp_neg_I_smul_isUnitary {A : 𝕄} (hA : IsHermitian A) (u : ℝ) :
    IsUnitary (exp ((u : ℂ) • (-I • A))) := by
  letI : NormedAlgebra ℚ 𝕄 := NormedAlgebra.restrictScalars ℚ ℂ 𝕄
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint <|
    skewAdjoint.smul_mem u (hA.isSelfAdjoint.smul_mem_skewAdjoint hI)

/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_real_smul {A : 𝕄} (hA : IsHermitian A) (u : ℝ) :
    IsHermitian (u • A) := (IsSelfAdjoint.all u).smul hA

/-- If `F` is odd and `A` is Hermitian, then `A^{(F)}` and `A - A^{(F)}` are Hermitian. -/
theorem Function.Odd.entrywise_and_sub_isHermitian {F : ℝ → ℝ} (hF : Function.Odd F)
    {A : 𝕄} (hA : A.IsHermitian) :
    (entrywise F A).IsHermitian ∧ (A - entrywise F A).IsHermitian := by
  have hadjoint : (entrywise F A).conjTranspose = entrywise F A.conjTranspose := by
    ext i j
    apply Complex.ext
    · rfl
    · exact (hF (A j i).im).symm
  have hFA : (entrywise F A).IsHermitian := by
    change (entrywise F A).conjTranspose = entrywise F A
    rw [hadjoint, hA.eq]
  exact ⟨hFA, hA.sub hFA⟩

/-- A unitary matrix has operator norm at most one. -/
theorem unitary_norm_le_one {A : 𝕄} (hA : IsUnitary A) : ‖A‖ ≤ 1 := by
  nontriviality 𝕄
  exact (CStarRing.norm_of_mem_unitary hA).le

/-- Unitary conjugation preserves the operator norm. -/
theorem norm_unitary_conj_eq (X : 𝕄) {U : 𝕄} (hU : IsUnitary U) :
    ‖U * X * U†‖ = ‖X‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU),
    CStarRing.norm_mem_unitary_mul _ hU]

/-- Multiplication on the left and right by unitaries does not increase the operator norm. -/
theorem norm_conj_le {A B : 𝕄} (hA : IsUnitary A) (hB : IsUnitary B) (X : 𝕄) :
    ‖A† * X * B‖ ≤ ‖X‖ := ((CStarRing.norm_mul_mem_unitary _ hB).trans
    (CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hA))).le

/-- For a unitary `U`, `‖V - U‖ = ‖U† V - 1‖`. -/
theorem norm_sub_eq_norm_star_mul_sub_one {U : 𝕄} (hU : IsUnitary U) (V : 𝕄) :
    ‖V - U‖ = ‖U† * V - 1‖ := by
  calc
    ‖V - U‖ = ‖U† * (V - U)‖ :=
      (CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hU)).symm
    _ = ‖U† * V - 1‖ := by rw [mul_sub, Unitary.star_mul_self_of_mem hU]

/-! ## Evolutions -/

/-- An evolution is continuous. -/
theorem Generates.continuousOn {G V : ℝ → 𝕄} {a b : ℝ} (h : Generates G V a b) :
    ContinuousOn V (Icc a b) := h.1

/-- An evolution starts at the identity: `V(a) = 1`. -/
theorem Generates.init {G V : ℝ → 𝕄} {a b : ℝ} (h : Generates G V a b) : V a = 1 := h.2.1

/-- An evolution is unitary-valued: `V(t)† V(t) = 1`. -/
theorem Generates.isUnitary {G V : ℝ → 𝕄} {a b : ℝ} (h : Generates G V a b) :
    ∀ t ∈ Icc a b, IsUnitary (V t) := h.2.2.1

/-- An evolution satisfies `i V'(t) = G(t) V(t)` for all but countably many `t`. -/
theorem Generates.deriv {G V : ℝ → 𝕄} {a b : ℝ} (h : Generates G V a b) :
    DerivativeOffCountable V (fun t ↦ -I • (G t * V t)) a b := h.2.2.2

/-- If `G(t)` with `t ∈ [0,T]` generates some evolution, it generates `evolutionOf G T`. -/
theorem generates_evolutionOf_of_exists {G : ℝ → 𝕄} {T : ℝ} (h : ∃ V, Generates G V 0 T) :
    Generates G (evolutionOf G T) 0 T := by
  rw [evolutionOf, dif_pos h]
  exact Classical.choose_spec h

/-! ## Time-dependent Hamiltonians -/

/-- A regulated time-dependent Hamiltonian is regulated. -/
theorem IsRegulatedTimeDepHamiltonian.regulated {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H) : IsRegulated H 0 1 := hH.1

/-- A regulated time-dependent Hamiltonian is a Hermitian family for `s ∈ [0,1]`. -/
theorem IsRegulatedTimeDepHamiltonian.hermitian {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H) : IsTimeDepHamiltonian H := hH.2

/-! ## Partitions and checkpoints -/

/-- Times `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ` are nondecreasing in the index: `tᵢ ≤ tⱼ` for `i ≤ j ≤ n`. -/
theorem partition_mono {t : ℕ → ℝ} {n : ℕ} (ht : ∀ j < n, t j ≤ t (j + 1)) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) : t i ≤ t j := by
  have hm : MonotoneOn t (Iic n) := monotoneOn_of_le_succ ordConnected_Iic
    (fun a _ _ hs ↦ ht a (by simpa using hs))
  exact hm (hij.trans hjn) hjn hij

section Checkpoints

variable {N : ℕ} {s : ℕ → ℝ}

/-- Consecutive checkpoints are ordered: `sⱼ ≤ sⱼ₊₁`. -/
theorem IsCheckpoints.le_succ (hs : IsCheckpoints N s) : ∀ j < N, s j ≤ s (j + 1) := hs.1

/-- The first checkpoint is `s₀ = 0`. -/
theorem IsCheckpoints.zero (hs : IsCheckpoints N s) : s 0 = 0 := hs.2.1

/-- The last checkpoint is `s_N = 1`. -/
theorem IsCheckpoints.last (hs : IsCheckpoints N s) : s N = 1 := hs.2.2

/-- Strict checkpoints `0 = s₀ < ⋯ < s_N = 1` are checkpoints. -/
theorem IsStrictCheckpoints.isCheckpoints (hs : IsStrictCheckpoints N s) : IsCheckpoints N s :=
  hs.1

/-- Consecutive strict checkpoints are strictly ordered: `sⱼ < sⱼ₊₁`. -/
theorem IsStrictCheckpoints.lt_succ (hs : IsStrictCheckpoints N s) :
    ∀ j < N, s j < s (j + 1) := hs.2

end Checkpoints

/-! ## Eigenvalues in decreasing order -/

/-- The equivalence from positions in Mathlib's decreasing eigenvalue list to matrix indices. -/
noncomputable abbrev eigenvalueIndexEquiv (d : ℕ) :
    Fin (Fintype.card (Fin d)) ≃ Fin d :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- The permutation of matrix indices that lists the eigenvalues of a Hermitian matrix in
decreasing order. -/
noncomputable def decreasingOrder {A : 𝕄} (_hA : A.IsHermitian) : Equiv.Perm (Fin d) :=
  (finCongr (Fintype.card_fin d).symm).trans (eigenvalueIndexEquiv d)

/-- The matrix eigenvalue at the index corresponding to position `j` is the `j`-th entry of
Mathlib's decreasing eigenvalue list. -/
theorem eigenvalues_eigenvalueIndexEquiv {A : 𝕄} (hA : A.IsHermitian)
    (j : Fin (Fintype.card (Fin d))) :
    hA.eigenvalues (eigenvalueIndexEquiv d j) = hA.eigenvalues₀ j :=
  congrArg hA.eigenvalues₀ ((eigenvalueIndexEquiv d).symm_apply_apply j)

/-- Reindexing by `decreasingOrder` gives Mathlib's decreasing eigenvalue list. -/
theorem eigenvalues_decreasingOrder {A : 𝕄} (hA : A.IsHermitian) (j : Fin d) :
    hA.eigenvalues (decreasingOrder hA j) =
      hA.eigenvalues₀ (finCongr (Fintype.card_fin d).symm j) := by
  exact eigenvalues_eigenvalueIndexEquiv hA _

/-- The list `λ₁↓ ≥ ⋯ ≥ λ_d↓` is decreasing and contains every eigenvalue with its
multiplicity. -/
theorem isDecreasingEigenvalueList_decreasingOrder {A : 𝕄} (hA : A.IsHermitian) :
    IsDecreasingEigenvalueList A
      (fun j ↦ hA.eigenvalues (decreasingOrder hA j)) := by
  constructor
  · intro i j hij
    change hA.eigenvalues (decreasingOrder hA j) ≤
      hA.eigenvalues (decreasingOrder hA i)
    rw [eigenvalues_decreasingOrder hA, eigenvalues_decreasingOrder hA]
    apply hA.eigenvalues₀_antitone
    simpa only [Fin.le_iff_val_le_val, finCongr_apply] using hij
  · rw [hA.roots_charpoly_eq_eigenvalues]
    have h := Multiset.map_univ_val_equiv (decreasingOrder hA)
    have hm := congrArg (Multiset.map (fun j ↦ (hA.eigenvalues j : ℂ))) h
    simpa only [Multiset.map_map, Function.comp_def] using hm.symm

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

/-! ## Spectral projectors -/

/-- A spectral projector is an orthogonal projector. -/
theorem spectralProjector_isOrthogonal (A : 𝕄) (S : Set ℂ) :
    IsOrthogonalProjector (spectralProjector A S) := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let E := ⨆ z ∈ S, Module.End.eigenspace (T A).toLinearMap z
  have hE : IsStarProjection E.starProjection := isStarProjection_starProjection
  exact ⟨hE.isIdempotentElem.map T.symm, hE.isSelfAdjoint.map T.symm⟩

/-- A spectral projector of a Hermitian matrix commutes with that matrix. -/
theorem spectralProjector_commute {A : 𝕄} (hA : IsHermitian A) (S : Set ℂ) :
    Commute (spectralProjector A S) A := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let E := ⨆ z ∈ S, Module.End.eigenspace (T A).toLinearMap z
  -- the span of eigenspaces is invariant
  have hE : E ∈ Module.End.invtSubmodule (T A).toLinearMap := by
    rw [Module.End.mem_invtSubmodule]
    refine iSup₂_le fun z hz v hv ↦ ?_
    have hv' : (T A).toLinearMap v = z • v := Module.End.mem_eigenspace_iff.mp hv
    rw [Submodule.mem_comap, hv']
    exact E.smul_mem z (Submodule.mem_iSup_of_mem z (Submodule.mem_iSup_of_mem hz hv))
  have hsymm : (T A).toLinearMap.IsSymmetric :=
    ((Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map Matrix.toEuclideanCLM).isSymmetric
  have hcomm : Commute E.starProjection (T A) :=
    (ContinuousLinearMap.IsIdempotentElem.commute_iff
      isStarProjection_starProjection.isIdempotentElem).mpr
      ⟨by rw [Submodule.range_starProjection]; exact hE,
        by rw [Submodule.ker_starProjection]; exact hsymm.orthogonalComplement_mem_invtSubmodule hE⟩
  have hmap : Matrix.toEuclideanCLM.toRingEquiv (spectralProjector A S) = E.starProjection := by
    change T (T.symm E.starProjection) = E.starProjection
    exact T.apply_symm_apply E.starProjection
  apply Matrix.toEuclideanCLM.injective
  rw [map_mul, map_mul, hmap]
  exact hcomm.eq

end RoundedClocks
