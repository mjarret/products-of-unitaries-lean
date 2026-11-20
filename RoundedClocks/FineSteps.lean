/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Bridge

/-!
# Section 3: fine steps

Bit truncation (Example 3.2), checkpoints (Lemma 3.4), the fine-step bound (Theorem 3.6), and its
consequences (Example 3.7, Remark 3.8).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Example 3.2.** (i) Bit truncation is odd. (ii) For a time-dependent Hamiltonian `H` and every
`s ∈ [0,1]`, `‖H(s) - H^{(k)}(s)‖ ≤ √2 σ_k 2^{-k}`. -/
theorem truncation_bits (k : ℕ) :
    Function.Odd (bitTruncation k) ∧
      ∀ H : ℝ → 𝕄, IsTimeDepHamiltonian H → ∀ s ∈ Icc (0 : ℝ) 1,
        ‖H s - entrywise (bitTruncation k) (H s)‖ ≤ √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
  refine ⟨?_, fun H hH s hs ↦ ?_⟩
  · rw [Bridge.bitTruncation_eq]
    exact (UnitaryProducts.PaperProof.ex_truncation_bits (d := d) k).1
  · have h := (UnitaryProducts.PaperProof.ex_truncation_bits (d := d) k).2 (H s) (sparsity k H)
      (hH s hs)
    simp only [UnitaryProducts.Paper.truncation, Bridge.truncHerm_eq] at h
    exact h (Bridge.rowSparse_sparsity k H hs)

/-- The number of binary places `k` that Examples 3.7 and 4.5 choose exists: for every `η > 0`
some `k` has `√2 σ_k 2^{-k} ≤ η`. -/
theorem exists_bits (H : ℝ → 𝕄) {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ η := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (√2 * d / η) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_⟩
  have hσ : (sparsity k H : ℝ) ≤ d := by
    exact_mod_cast ciSup_le' fun s ↦ ciSup_le' fun p ↦
      (Finset.card_filter_le _ _).trans (by simp)
  rw [div_lt_iff₀ hη] at hk
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  nlinarith [Real.sqrt_nonneg 2]

/-- **Lemma 3.4.** For a regulated `H` and `ε > 0` there are checkpoints `0 = s_0 < ⋯ < s_N = 1`
with `‖H(x) - H(y)‖ ≤ ε` whenever `s_j < x, y < s_{j+1}`. In particular, their midpoint error is at
most `ε`. Hermiticity is not needed. -/
theorem exists_checkpoints {H : ℝ → 𝕄} (hH : IsRegulated H 0 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (s : ℕ → ℝ), IsCheckpoints N s ∧ (∀ j < N, s j < s (j + 1)) ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε :=
  let ⟨N, s, hs, h⟩ := UnitaryProducts.PaperProof.exists_oscillation_partition hH hε
  ⟨N, s, Bridge.checkpoints_of_partition hs, h⟩

/-- Checkpoints `0 = s_0 ≤ ⋯ ≤ s_N = 1` have a cell `s_j < s_{j+1}`. -/
private theorem exists_cell {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    ∃ j < N, s j < s (j + 1) := by
  by_contra h
  push_neg at h
  have hle : ∀ j ≤ N, s j ≤ s 0 := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (h j (by omega)).trans (ih (by omega))
  have h1 := hle N le_rfl
  rw [hs.2.1, hs.2.2] at h1
  norm_num at h1

/-- **Theorem 3.6.** Let `F` be odd, let `H` be a regulated time-dependent Hamiltonian with
evolution `U` over time `T > 0`, and let `W` be the midpoint product of `H^{(F)}` over time `T` on
checkpoints `0 = s_0 ≤ ⋯ ≤ s_N = 1`. If `‖H(s) - H^{(F)}(s_{j+1/2})‖ ≤ M` whenever
`s_j < s < s_{j+1}`, then `‖W - U(T)‖ ≤ T M`. The least such `M` is the paper's
`max_j sup_{s_j < s < s_{j+1}} ‖H(s) - H^{(F)}(s_{j+1/2})‖`. -/
theorem fine_steps {F : ℝ → ℝ} (hF : Function.Odd F) {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1)
    (hH : IsTimeDepHamiltonian H) {T : ℝ} (hT : 0 < T) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) {M : ℝ}
    (hM : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ‖H x - entrywise F (H ((s j + s (j + 1)) / 2))‖ ≤ M) :
    ‖midpointProduct (fun x ↦ entrywise F (H x)) T N s - evolution H T T‖ ≤ T * M := by
  have hM0 : 0 ≤ M := by
    obtain ⟨j, hj, hlt⟩ := exists_cell hs
    exact (norm_nonneg _).trans (hM j hj ((s j + s (j + 1)) / 2) ⟨by linarith, by linarith⟩)
  have hs' := Bridge.checkpoints_partition hs
  rw [← Bridge.midpointProduct_freeze, Bridge.midpointProduct_eq]
  refine (UnitaryProducts.PaperProof.thm_fine_steps_sup hT hreg hH F hF N _ hs').trans ?_
  refine mul_le_mul_of_nonneg_left
    (UnitaryProducts.PaperProof.maxCellError_le hs' _ hM0 fun j hj x hx ↦ ?_) hT.le
  simp only [Bridge.freeze_of_le s hj.le, Bridge.freeze_of_le s hj] at hx ⊢
  exact hM j hj x hx

/-- **Example 3.7.** Let `H` be a regulated time-dependent Hamiltonian, let `P` and `Q` be
orthogonal projectors, let `C > 0` and `δ > 0`, and let `T = 2C/δ`. If the evolution `U` of `H`
over time `T` has `‖(1 - Q) U(T) P‖ ≤ C/T`, the checkpoints have midpoint error at most
`δ²/(8C)`, and `√2 σ_k 2^{-k} ≤ δ²/(8C)`, then the midpoint product `W` of `H^{(k)}` over time `T`
satisfies `‖(1 - Q) W P‖ ≤ δ`. -/
theorem jrs_leakage {H : ℝ → 𝕄} (hreg : IsRegulated H 0 1) (hH : IsTimeDepHamiltonian H)
    {P Q : 𝕄} (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) {C δ T : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hT : T = 2 * C / δ)
    (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) (hmid : HasMidpointError H N s (δ ^ 2 / (8 * C))) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ ^ 2 / (8 * C)) :
    ‖(1 - Q) * midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s * P‖ ≤ δ := by
  have hT0 : 0 < T := hT ▸ div_pos (mul_pos two_pos hC) hδ
  subst hT
  have h := UnitaryProducts.PaperProof.cor_jrs_oscillation hreg hH P Q hP hQ hC hδ
    (UnitaryProducts.Paper.evolution_spec hT0 hH hreg) hU N _ (Bridge.checkpoints_partition hs)
    ((Bridge.hasMidpointError_freeze H N s _).2 hmid) k (sparsity k H)
    (fun x hx ↦ by
      change UnitaryProducts.RowSparse _ (H x - UnitaryProducts.truncHerm k (H x))
      rw [Bridge.truncHerm_eq]
      exact Bridge.rowSparse_sparsity k H hx) hk
  have hW : midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) (2 * C / δ) N s =
      UnitaryProducts.Paper.midpointProductOver ((UnitaryProducts.Paper.truncation k).2.2.2 H)
        (2 * C / δ) N (Bridge.freeze N s) := by
    rw [← Bridge.midpointProduct_freeze, Bridge.midpointProduct_eq]
    congr 1
    funext x
    exact (Bridge.truncHerm_eq k (H x)).symm
  rw [hW]
  exact h.2.2

/-- A real number is an eigenvalue of a Hermitian `A` exactly when it is some `λ_i`. -/
private theorem ofReal_mem_spectrum {A : 𝕄} (hA : A.IsHermitian) (x : ℝ) :
    (x : ℂ) ∈ spectrum ℂ A ↔ ∃ i, hA.eigenvalues i = x := by
  rw [hA.spectrum_eq_image_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, h⟩
    exact ⟨i, Complex.ofReal_injective h⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

/-- A real number lies in `interval a b` exactly when it lies in `(a,b)`. -/
private theorem ofReal_mem_interval {a b x : ℝ} : (x : ℂ) ∈ interval a b ↔ x ∈ Ioo a b :=
  Complex.ofReal_injective.mem_set_image

/-- The spectral projector of a Hermitian `A` for a set of real numbers is `specProj`. -/
private theorem spectralProjector_ofReal {A : 𝕄} (hA : A.IsHermitian) (X : Set ℝ) :
    spectralProjector A ((fun x : ℝ ↦ (x : ℂ)) '' X) = UnitaryProducts.specProj hA X := by
  unfold spectralProjector UnitaryProducts.specProj
  congr 1
  rw [UnitaryProducts.PaperProof.starProjection_eigenspaces_eq_proj hA.eigenvectorBasis
    hA.eigenvalues (fun x : ℝ ↦ (x : ℂ)) _ _ (UnitaryProducts.isDiag_eigenvectorBasis hA)]
  congr 1
  ext x
  exact Complex.ofReal_injective.mem_set_image

/-- `specProj` for a set of eigenvalues is the projector onto the eigenvectors it selects. -/
private theorem specProj_eq_bandProj {A : 𝕄} (hA : A.IsHermitian) {S : Finset (Fin d)}
    {X : Set ℝ} (h : ∀ i, i ∈ S ↔ hA.eigenvalues i ∈ X) :
    UnitaryProducts.specProj hA X = UnitaryProducts.Paper.bandProj S A := by
  classical
  have hidx : UnitaryProducts.idx hA.eigenvalues X = S := by
    ext i
    simp [UnitaryProducts.idx, h i]
  unfold UnitaryProducts.Paper.bandProj UnitaryProducts.specProj UnitaryProducts.proj
  rw [dif_pos hA, hidx]

/-- The rank of a matrix is the dimension of the range of its operator. -/
private theorem rank_eq_finrank_range (P : 𝕄) :
    P.rank = Module.finrank ℂ
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) P).toLinearMap.range := by
  rw [Matrix.rank_eq_finrank_range_toLin P (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℂ).toBasis, ← Matrix.toEuclideanLin_eq_toLin_orthonormal,
    ← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

/-- Remark 3.8 at one endpoint: for a band of `A` and a Hermitian `D` with `‖A - D‖` less than
half the spectral gap `Γ`, the two spectral projectors are orthogonal projectors of equal rank,
`‖P - P'‖ = ‖(1 - P') P‖ ≤ ‖A - D‖/(Γ - ‖A - D‖)`, the eigenvalues of `A` outside the band and of
`D` outside `nearBand` are at distance at least `Γ` and `Γ - ‖A - D‖` from the hull `I` of the
band, and `‖A - D‖ < Γ - ‖A - D‖`. -/
private theorem band_endpoint {A D : 𝕄} {a b : ℝ} (hband : IsBand A a b) (hD : D.IsHermitian)
    (hε : ‖A - D‖ < spectralGap A a b / 2) :
    IsStarProjection (spectralProjector A (interval a b)) ∧
    IsStarProjection (spectralProjector D (nearBand A a b ‖A - D‖)) ∧
    (spectralProjector A (interval a b)).rank =
      (spectralProjector D (nearBand A a b ‖A - D‖)).rank ∧
    ‖spectralProjector A (interval a b) - spectralProjector D (nearBand A a b ‖A - D‖)‖ =
      ‖(1 - spectralProjector D (nearBand A a b ‖A - D‖)) *
        spectralProjector A (interval a b)‖ ∧
    ‖(1 - spectralProjector D (nearBand A a b ‖A - D‖)) * spectralProjector A (interval a b)‖ ≤
      ‖A - D‖ / (spectralGap A a b - ‖A - D‖) ∧
    (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ A \ interval a b →
      ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
        (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b ≤ |μ - x|) ∧
    (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ D \ nearBand A a b ‖A - D‖ →
      ∀ x ∈ Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
        (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}),
      spectralGap A a b - ‖A - D‖ ≤ |μ - x|) ∧
    ‖A - D‖ < spectralGap A a b - ‖A - D‖ := by
  classical
  have hA := hband.1
  let S : Finset (Fin d) := Finset.univ.filter fun i ↦ hA.eigenvalues i ∈ Ioo a b
  have hmem : ∀ i, i ∈ S ↔ hA.eigenvalues i ∈ Ioo a b := by simp [S]
  have hne : S.Nonempty := by
    obtain ⟨_, hz, x, hx, rfl⟩ := hband.2.1
    obtain ⟨i, rfl⟩ := (ofReal_mem_spectrum hA x).1 hz
    exact ⟨i, (hmem i).2 hx⟩
  have hR : Sᶜ.Nonempty := by
    obtain ⟨z, hz, hzI⟩ := hband.2.2.1
    rw [hA.spectrum_eq_image_range] at hz
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hz
    exact ⟨i, Finset.mem_compl.2 fun hi ↦ hzI (ofReal_mem_interval.2 ((hmem i).1 hi))⟩
  have hhull : ∀ i, i ∈ S ↔ |hA.eigenvalues i - (S.inf' hne hA.eigenvalues +
      S.sup' hne hA.eigenvalues) / 2| ≤
        (S.sup' hne hA.eigenvalues - S.inf' hne hA.eigenvalues) / 2 := by
    intro i
    rw [abs_le]
    constructor
    · intro hi
      have h1 := S.inf'_le hA.eigenvalues hi
      have h2 := S.le_sup' hA.eigenvalues hi
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      obtain ⟨i₁, hi₁, e₁⟩ := S.exists_mem_eq_inf' hne hA.eigenvalues
      obtain ⟨i₂, hi₂, e₂⟩ := S.exists_mem_eq_sup' hne hA.eigenvalues
      have m₁ := (hmem i₁).1 hi₁
      have m₂ := (hmem i₂).1 hi₂
      exact (hmem i).2 ⟨by linarith [m₁.1], by linarith [m₂.2]⟩
  let hS : UnitaryProducts.Paper.IsBand hA S := ⟨hne, hR, _, _, hhull⟩
  have hgap : spectralGap A a b = UnitaryProducts.Paper.bandGap hA hS := by
    change _ = S.inf' hne fun i ↦ Sᶜ.inf' hR fun j ↦ |hA.eigenvalues i - hA.eigenvalues j|
    apply le_antisymm
    · obtain ⟨i, hi, ei⟩ := S.exists_mem_eq_inf' hne
        fun i ↦ Sᶜ.inf' hR fun j ↦ |hA.eigenvalues i - hA.eigenvalues j|
      obtain ⟨j, hj, ej⟩ := Sᶜ.exists_mem_eq_inf' hR fun j ↦ |hA.eigenvalues i - hA.eigenvalues j|
      rw [ei, ej]
      refine csInf_le ⟨0, ?_⟩ ⟨hA.eigenvalues i, hA.eigenvalues j,
        ⟨(ofReal_mem_spectrum hA _).2 ⟨i, rfl⟩, ofReal_mem_interval.2 ((hmem i).1 hi)⟩,
        ⟨(ofReal_mem_spectrum hA _).2 ⟨j, rfl⟩,
          fun h ↦ Finset.mem_compl.1 hj ((hmem j).2 (ofReal_mem_interval.1 h))⟩, rfl⟩
      rintro r ⟨x, y, -, -, rfl⟩
      exact abs_nonneg _
    · obtain ⟨i, hi⟩ := hne
      obtain ⟨j, hj⟩ := hR
      refine le_csInf ⟨_, hA.eigenvalues i, hA.eigenvalues j,
        ⟨(ofReal_mem_spectrum hA _).2 ⟨i, rfl⟩, ofReal_mem_interval.2 ((hmem i).1 hi)⟩,
        ⟨(ofReal_mem_spectrum hA _).2 ⟨j, rfl⟩,
          fun h ↦ Finset.mem_compl.1 hj ((hmem j).2 (ofReal_mem_interval.1 h))⟩, rfl⟩ ?_
      rintro r ⟨x, y, ⟨hx, hxI⟩, ⟨hy, hyI⟩, rfl⟩
      obtain ⟨i, rfl⟩ := (ofReal_mem_spectrum hA x).1 hx
      obtain ⟨j, rfl⟩ := (ofReal_mem_spectrum hA y).1 hy
      have hi : i ∈ S := (hmem i).2 (ofReal_mem_interval.1 hxI)
      have hj : j ∈ Sᶜ :=
        Finset.mem_compl.2 fun h ↦ hyI (ofReal_mem_interval.2 ((hmem j).1 h))
      exact (S.inf'_le _ hi).trans (Sᶜ.inf'_le _ hj)
  have he : ‖A - D‖ < UnitaryProducts.Paper.bandGap hA hS / 2 := hgap ▸ hε
  have hsep : ∀ i, i ∈ S ↔ hD.eigenvalues i ∈
      Icc (S.inf' hne hA.eigenvalues - ‖A - D‖) (S.sup' hne hA.eigenvalues + ‖A - D‖) :=
    (UnitaryProducts.PaperProof.truncated_endpoint_weyl_separation hA hD hS he).1
  have hsep₂ : ∀ i, i ∉ S → ∀ x ∈ Icc (S.inf' hne hA.eigenvalues) (S.sup' hne hA.eigenvalues),
      UnitaryProducts.Paper.bandGap hA hS ≤ |hA.eigenvalues i - x| ∧
        UnitaryProducts.Paper.bandGap hA hS - ‖A - D‖ ≤ |hD.eigenvalues i - x| :=
    (UnitaryProducts.PaperProof.truncated_endpoint_weyl_separation hA hD hS he).2.1
  have hsep₃ : ‖A - D‖ < UnitaryProducts.Paper.bandGap hA hS - ‖A - D‖ :=
    (UnitaryProducts.PaperProof.truncated_endpoint_weyl_separation hA hD hS he).2.2
  have hRset : {x : ℝ | (x : ℂ) ∈ spectrum ℂ A ∩ interval a b} =
      hA.eigenvalues '' (S : Set (Fin d)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_image, Finset.mem_coe,
      ofReal_mem_spectrum hA, ofReal_mem_interval]
    constructor
    · rintro ⟨⟨i, rfl⟩, hx⟩
      exact ⟨i, (hmem i).2 hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, (hmem i).1 hi⟩
  have hnear : nearBand A a b ‖A - D‖ = (fun x : ℝ ↦ (x : ℂ)) ''
      Icc (S.inf' hne hA.eigenvalues - ‖A - D‖) (S.sup' hne hA.eigenvalues + ‖A - D‖) := by
    rw [Finset.inf'_eq_csInf_image, Finset.sup'_eq_csSup_image, ← hRset]
    rfl
  have hsA := specProj_eq_bandProj hA hmem
  have hsD := specProj_eq_bandProj hD hsep
  have hP : spectralProjector A (interval a b) = UnitaryProducts.Paper.bandProj S A :=
    (spectralProjector_ofReal hA _).trans hsA
  have hP' : spectralProjector D (nearBand A a b ‖A - D‖) = UnitaryProducts.Paper.bandProj S D := by
    rw [hnear]
    exact (spectralProjector_ofReal hD _).trans hsD
  have hI : Icc (sInf {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b})
      (sSup {y : ℝ | (y : ℂ) ∈ spectrum ℂ A ∩ interval a b}) =
        Icc (S.inf' hne hA.eigenvalues) (S.sup' hne hA.eigenvalues) := by
    rw [Finset.inf'_eq_csInf_image S hne, Finset.sup'_eq_csSup_image S hne, hRset]
  have hout : ∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ A \ interval a b →
      ∀ x ∈ Icc (S.inf' hne hA.eigenvalues) (S.sup' hne hA.eigenvalues),
        UnitaryProducts.Paper.bandGap hA hS ≤ |μ - x| := by
    rintro μ ⟨hμ, hμI⟩ x hx
    obtain ⟨i, rfl⟩ := (ofReal_mem_spectrum hA μ).1 hμ
    exact (hsep₂ i (fun h ↦ hμI (ofReal_mem_interval.2 ((hmem i).1 h))) x hx).1
  have hout' : ∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ D \ nearBand A a b ‖A - D‖ →
      ∀ x ∈ Icc (S.inf' hne hA.eigenvalues) (S.sup' hne hA.eigenvalues),
        UnitaryProducts.Paper.bandGap hA hS - ‖A - D‖ ≤ |μ - x| := by
    rintro μ ⟨hμ, hμN⟩ x hx
    obtain ⟨i, rfl⟩ := (ofReal_mem_spectrum hD μ).1 hμ
    rw [hnear] at hμN
    exact (hsep₂ i (fun h ↦ hμN ⟨_, (hsep i).1 h, rfl⟩) x hx).2
  have hn := UnitaryProducts.Prose.endpoint_projector_eq_directed_and_le hA hD hS he
  rw [hP, hP', hgap, hI]
  refine ⟨hsA ▸ UnitaryProducts.isStarProjection_specProj hA _,
    hsD ▸ UnitaryProducts.isStarProjection_specProj hD _, ?_, hn.1, hn.2, hout, hout', hsep₃⟩
  rw [rank_eq_finrank_range, rank_eq_finrank_range,
    UnitaryProducts.PaperProof.bandProj_finrank hA S,
    UnitaryProducts.PaperProof.bandProj_finrank hD S]

/-- **Remark 3.8.** Let `H` be a family of matrices with evolution `U` over time `T > 0`.
For `s ∈ {0,1}`, let `P_s` be the spectral projector of a band `{λ : a_s < λ < b_s}` of `H(s)` with
spectral gap `Γ_s`, let `ε_s = ‖H(s) - H^{(k)}(s)‖ < Γ_s/2`, and let `P'_s` be the spectral
projector of `H^{(k)}(s)` for its eigenvalues within `ε_s` of `[min S_s, max S_s]`, where `S_s` is
the set of eigenvalues in the band. Then `P_s` and `P'_s` have equal rank,
`‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖ ≤ ε_s/(Γ_s - ε_s)`, and for every matrix `W`,
`|‖(1 - P'_1) W P'_0‖ - ‖(1 - P_1) U(T) P_0‖| ≤ ‖W - U(T)‖ + Σ_s ε_s/(Γ_s - ε_s)`. Moreover,
with `I_s = [min S_s, max S_s]`, every eigenvalue of `H(s)` outside the band is at distance at least
`Γ_s` from `I_s`, every eigenvalue of `H^{(k)}(s)` not within `ε_s` of `I_s` is at distance at
least `Γ_s - ε_s` from `I_s`, and `ε_s < Γ_s - ε_s`. -/
theorem truncated_endpoints {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (k : ℕ) {a b : ℝ → ℝ} (hband : ∀ s ∈ ({0, 1} : Set ℝ), IsBand (H s) (a s) (b s))
    (hε : ∀ s ∈ ({0, 1} : Set ℝ),
      ‖H s - entrywise (bitTruncation k) (H s)‖ < spectralGap (H s) (a s) (b s) / 2)
    (W : 𝕄) :
    let ε := fun s ↦ ‖H s - entrywise (bitTruncation k) (H s)‖
    let Γ := fun s ↦ spectralGap (H s) (a s) (b s)
    let P := fun s ↦ spectralProjector (H s) (interval (a s) (b s))
    let P' := fun s ↦
      spectralProjector (entrywise (bitTruncation k) (H s)) (nearBand (H s) (a s) (b s) (ε s))
    let I := fun s ↦ Icc (sInf {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
      (sSup {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
    (∀ s ∈ ({0, 1} : Set ℝ), (P s).rank = (P' s).rank ∧
      ‖P s - P' s‖ = ‖(1 - P' s) * P s‖ ∧ ‖(1 - P' s) * P s‖ ≤ ε s / (Γ s - ε s) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (H s) \ interval (a s) (b s) →
        ∀ x ∈ I s, Γ s ≤ |μ - x|) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (entrywise (bitTruncation k) (H s)) \
          nearBand (H s) (a s) (b s) (ε s) → ∀ x ∈ I s, Γ s - ε s ≤ |μ - x|) ∧
      ε s < Γ s - ε s) ∧
    |‖(1 - P' 1) * W * P' 0‖ - ‖(1 - P 1) * evolution H T T * P 0‖| ≤
      ‖W - evolution H T T‖ + ε 0 / (Γ 0 - ε 0) + ε 1 / (Γ 1 - ε 1) := by
  intro ε Γ P P' I
  have hodd := (truncation_bits (d := d) k).1
  have hend : ∀ s ∈ ({0, 1} : Set ℝ), IsStarProjection (P s) ∧ IsStarProjection (P' s) ∧
      (P s).rank = (P' s).rank ∧ ‖P s - P' s‖ = ‖(1 - P' s) * P s‖ ∧
      ‖(1 - P' s) * P s‖ ≤ ε s / (Γ s - ε s) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (H s) \ interval (a s) (b s) →
        ∀ x ∈ I s, Γ s ≤ |μ - x|) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (entrywise (bitTruncation k) (H s)) \
          nearBand (H s) (a s) (b s) (ε s) → ∀ x ∈ I s, Γ s - ε s ≤ |μ - x|) ∧
      ε s < Γ s - ε s := fun s hs ↦
    band_endpoint (hband s hs)
      (UnitaryProducts.PaperProof.scalarEntryMap_and_error_isHermitian _ hodd (hband s hs).1).1
      (hε s hs)
  have h0 := hend 0 (by simp)
  have h1 := hend 1 (by simp)
  have hU : IsUnitary (evolution H T T) := by
    unfold evolution evolutionOf
    split_ifs with h
    · exact h.choose_spec.2.2.1 T ⟨hT.le, le_rfl⟩
    · simp only [IsUnitary, star_one, one_mul]
  have hUn : ‖evolution H T T‖ ≤ 1 := UnitaryProducts.norm_le_one_of_star_mul_self hU
  refine ⟨fun s hs ↦ (hend s hs).2.2, ?_⟩
  have ht := UnitaryProducts.PaperProof.prop_transfer (A := 1) (B := 1) (W := W)
    (U := evolution H T T) h0.1 h1.1 h0.2.1 h1.2.1 (one_mem _) (one_mem _)
    (Commute.one_left _) (Commute.one_left _)
  have e0 : ‖P' 0 - P 0‖ ≤ ε 0 / (Γ 0 - ε 0) := by
    rw [norm_sub_rev]
    exact h0.2.2.2.1.trans_le h0.2.2.2.2.1
  have e1 : ‖P' 1 - P 1‖ ≤ ε 1 / (Γ 1 - ε 1) := by
    rw [norm_sub_rev]
    exact h1.2.2.2.1.trans_le h1.2.2.2.2.1
  have hm := mul_le_of_le_one_left
    (add_nonneg (norm_nonneg (P' 0 - P 0)) (norm_nonneg (P' 1 - P 1))) hUn
  simp only [one_mul, mul_one] at ht
  linarith

end RoundedClocks
