/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps.FineStepEstimates
public import RoundedClocks.FineSteps.TruncatedEndpoints
public import RoundedClocks.FineSteps.MidpointBoundedness
public import RoundedClocks.FineSteps.FineStepRegularity

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

/-- **Example 3.2.** Fix an integer `k ≥ 0` and a Hermitian family `H(s)` with `s ∈ [0,1]`. Let bit
truncation be `[x]_k = sgn(x) 2^{-k} ⌊2^k |x|⌋`, let `H^{(k)} = H^{([·]_k)}`, and let
`σ_k = max_p max_{s∈[0,1]} #{q : H^{(k)}_{pq}(s) ≠ H_{pq}(s)}` be the largest number of entries
that truncation changes in a row of `H(s)`. Then (i) bit truncation is odd, and (ii) for every
`s ∈ [0,1]`, `‖H(s) - H^{(k)}(s)‖ ≤ √2 σ_k 2^{-k}`. -/
theorem truncation_bits [NeZero d] (k : ℕ) :
    Function.Odd (bitTruncation k) ∧
      ∀ H : ℝ → 𝕄, IsTimeDepHamiltonian H → ∀ s ∈ Icc (0 : ℝ) 1,
        ‖H s - entrywise (bitTruncation k) (H s)‖ ≤ √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
  have hodd : Function.Odd (bitTruncation k) := by
    intro x
    simp only [bitTruncation, Real.sign_neg, abs_neg]
    ring
  refine ⟨hodd, fun H hH s hs ↦ ?_⟩
  let E := H s - entrywise (bitTruncation k) (H s)
  have hE : E.IsHermitian := (entrywise_and_error_isHermitian _ hodd (hH s hs)).2
  have hentry : ∀ i j, ‖E i j‖ ≤ √2 * ((2 : ℝ) ^ k)⁻¹ := by
    intro i j
    simpa only [E, Matrix.sub_apply, entrywise, Matrix.of_apply] using
      norm_sub_entrywise_bitTruncation_le k (H s i j)
  calc
    ‖E‖ ≤ sparsity k H * (√2 * ((2 : ℝ) ^ k)⁻¹) :=
      norm_le_row_sum_of_isHermitian hE (by positivity) fun i ↦
        sum_norm_row_le_of_card (truncation_error_card_le k H hs) hentry i
    _ = √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by ring

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
  have hsqrt := Real.sqrt_nonneg 2; nlinarith

/-- **Lemma 3.4.** Assuming Dieudonné (7.6.1), let `H` be a regulated time-dependent Hamiltonian,
and let `ε > 0`. There are checkpoints `0 = s₀ < ⋯ < s_N = 1` with
`‖H(x) - H(y)‖ ≤ ε` whenever `sⱼ < x,y < sⱼ₊₁` for some `j`. In particular, their midpoint error
is at most `ε`. -/
theorem exists_checkpoints (dieudonne_7_6_1 : Dieudonne_7_6_1) {H : ℝ → 𝕄}
    [NeZero d] (hH : IsRegulatedTimeDepHamiltonian H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε := by
  -- Dieudonné (7.6.1) supplies a step function within ε/2 of H.
  obtain ⟨G, hG, happrox⟩ :=
    dieudonne_7_6_1 d H 0 1 (ε / 2) zero_le_one hH.1 (half_pos hε)
  obtain ⟨N, s, A, hs0, hsN, hstrict, hcell⟩ := hG
  have hs : IsStrictCheckpoints N s :=
    ⟨⟨fun j hj ↦ (hstrict j hj).le, hs0, hsN⟩, hstrict⟩
  -- On each open cell, H is within ε/2 of the constant matrix A j.
  have hA : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), ‖H x - A j‖ ≤ ε / 2 := by
    intro j hj x hx
    have hleft : 0 ≤ s j := by
      have h := checkpoints_mono hs.1 (Nat.zero_le j) (Nat.le_of_lt hj)
      simpa only [hs0] using h
    have hright : s (j + 1) ≤ 1 := by
      have h := checkpoints_mono hs.1 (Nat.succ_le_of_lt hj) (le_refl N)
      simpa only [hsN] using h
    have h := happrox x ⟨hleft.trans hx.1.le, hx.2.le.trans hright⟩
    rw [hcell j hj x hx] at h
    exact h.le
  -- The triangle inequality bounds the oscillation on each open cell by ε.
  have hpair : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε := by
    intro j hj x hx y hy
    calc
      ‖H x - H y‖ ≤ ‖H x - A j‖ + ‖A j - H y‖ :=
        norm_sub_le_norm_sub_add_norm_sub (H x) (A j) (H y)
      _ = ‖H x - A j‖ + ‖H y - A j‖ := by rw [norm_sub_rev (A j) (H y)]
      _ ≤ ε / 2 + ε / 2 := add_le_add (hA j hj x hx) (hA j hj y hy)
      _ = ε := by ring
  refine ⟨N, s, hs, hpair, fun j hj x hx ↦ ?_⟩
  -- Strictness places the midpoint inside its cell, so the pairwise bound applies.
  have hmid : (s j + s (j + 1)) / 2 ∈ Ioo (s j) (s (j + 1)) := by
    constructor <;> linarith [hs.2 j hj]
  exact hpair j hj x hx _ hmid

/-- **Theorem 3.6.** Assuming Dieudonné (7.6.1), Section 8.7, (10.5.4) and (10.6.3) with the remark
(10.4.6), let
`F : ℝ → ℝ` be odd, and let `H` be a regulated time-dependent Hamiltonian with evolution `U` over
time `T > 0`. The midpoint product `W` of `H^{(F)}` over time `T` on any checkpoints
`0 = s₀ ≤ ⋯ ≤ s_N = 1` satisfies
` ‖W - U(T)‖ ≤ T max_j sup_{s_j < x < s_{j+1}}
  ‖H(x) - H^{(F)}(s_{j+1/2})‖`.
A repeated checkpoint contributes `1` to `W` and an empty supremum, taken to be `0`. -/
theorem fine_steps (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {F : ℝ → ℝ} (hF : Function.Odd F) {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H)
    {T : ℝ} (hT : 0 < T) {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    ‖midpointProduct (fun x ↦ entrywise F (H x)) T N s - evolution H T T‖ ≤
      T * midpointApproximationError F H N s := by
  -- Lemma 3.4 bounds the held midpoint family.
  have hpart := fun ε hε ↦ exists_checkpoints dieudonne_7_6_1 hH (ε := ε) hε
  have hbounded := fine_steps_bounded_of_checkpoints hpart
  obtain ⟨K, hKreg, hKherm, hpieces, hbound⟩ :=
    fine_steps_held_family_of_bounded hF hH.2 hbounded hT hs
  let A : ℕ → 𝕄 := fun j ↦ T • entrywise F (H ((s j + s (j + 1)) / 2))
  have hA : ∀ j < N, (A j).IsHermitian := by
    intro j hj
    have hm := checkpoint_midpoint_mem hs hj
    have hsample := (entrywise_and_error_isHermitian F hF (hH.2 _ hm)).1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, hsample.eq]
  obtain ⟨V, hV, hVend⟩ := piecewise_product hs.1 hA hpieces
  have hV' : Generates K V 0 1 := by simpa only [hs.2.1, hs.2.2] using hV
  have hVend' : V 1 = midpointProduct (fun x ↦ entrywise F (H x)) T N s := by
    rw [← hs.2.2, hVend]
    simp only [midpointProduct, A]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [smul_comm (-I * (s (j + 1) - s j : ℝ)) T]
    rw [← smul_assoc]
    congr 1
    apply congrArg (fun z : ℂ ↦ z • entrywise F (H ((s j + s (j + 1)) / 2)))
    apply Complex.ext <;> simp
  -- Reparameterize the true evolution to `[0,1]`, and apply Duhamel (2.3) once.
  let G : ℝ → 𝕄 := fun x ↦ T • H x
  have hGreg : IsRegulated G 0 1 := regulated_const_smul hH.1
  have hphysicalReg : IsRegulated (fun t ↦ H (t / T)) 0 T := regulated_div_time hT hH.1
  have hphysicalHerm : IsHermitianFamily (fun t ↦ H (t / T)) 0 T := by
    intro t ht
    exact hH.2 (t / T) ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
  have hphysical : Generates (fun t ↦ H (t / T)) (evolution H T) 0 T := by
    simpa only [evolution] using
      generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3
        hT.le hphysicalReg hphysicalHerm
  have htrue : Generates G (fun x ↦ evolution H T (T * x)) 0 1 := by
    simpa only [G] using generates_reparameterized hT hphysical
  have hGherm : IsHermitianFamily G 0 1 := by
    intro x hx
    change (T • H x).IsHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (hH.2 x hx).eq]
  have hD := duhamel dieudonne_7_6_1 dieudonne_section_8_7 zero_le_one
    hGreg hGherm hKreg hKherm htrue hV'
  -- Apply Lemma 3.4 to the normalized and held families for the Duhamel integral.
  have hGint := fine_steps_integrable_of_checkpoints
    (fun ε hε ↦ exists_checkpoints dieudonne_7_6_1 ⟨hGreg, hGherm⟩ (ε := ε) hε)
  have hKint := fine_steps_integrable_of_checkpoints
    (fun ε hε ↦ exists_checkpoints dieudonne_7_6_1 ⟨hKreg, hKherm⟩ (ε := ε) hε)
  have hdiff : IntervalIntegrable (fun x ↦ ‖G x - K x‖)
      MeasureTheory.volume 0 1 :=
    (hGint.sub hKint).norm
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖G x - K x‖ := by
      simpa only [hVend', mul_one] using hD
    _ ≤ ∫ _x in (0 : ℝ)..1, T * midpointApproximationError F H N s :=
      intervalIntegral.integral_mono_on zero_le_one hdiff intervalIntegrable_const hbound
    _ = T * midpointApproximationError F H N s := by simp

/-- **Example 3.7.** Assuming Dieudonné (7.6.1), Section 8.7, (10.5.4) and (10.6.3) with the remark
(10.4.6), let `H` be
a regulated time-dependent Hamiltonian, let `P` and `Q` be orthogonal projectors, let `C > 0` and
`δ > 0`, and let `T = 2C/δ`. If the evolution `U` of `H` over time `T` has
`‖(1 - Q) U(T) P‖ ≤ C/T`, the checkpoints have midpoint error at most
`δ²/(8C)`, and `√2 σ_k 2^{-k} ≤ δ²/(8C)`, then the midpoint product `W` of `H^{(k)}` over time `T`
satisfies `‖(1 - Q) W P‖ ≤ δ`. -/
theorem jrs_leakage (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsRegulatedTimeDepHamiltonian H)
    {P Q : 𝕄} (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) {C δ T : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hT : T = 2 * C / δ)
    (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) (hmid : HasMidpointError H N s (δ ^ 2 / (8 * C))) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ ^ 2 / (8 * C)) :
    ‖(1 - Q) * midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s * P‖ ≤ δ := by
  let B := δ ^ 2 / (8 * C)
  have hB : 0 ≤ B := by positivity
  have hpoint : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)),
      ‖H x - entrywise (bitTruncation k) (H ((s j + s (j + 1)) / 2))‖ ≤ B + B := by
    intro j hj x hx
    have hm := checkpoint_midpoint_mem hs hj
    have htrunc := (truncation_bits (d := d) k).2 H hH.2 _ hm
    calc
      _ ≤ ‖H x - H ((s j + s (j + 1)) / 2)‖ +
          ‖H ((s j + s (j + 1)) / 2) -
            entrywise (bitTruncation k) (H ((s j + s (j + 1)) / 2))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B + B := add_le_add (hmid j hj x hx) (htrunc.trans hk)
  have hM : midpointApproximationError (bitTruncation k) H N s ≤ B + B := by
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro r (rfl | ⟨j, hj, x, hx, rfl⟩)
    · positivity
    · exact hpoint j hj x hx
  have hT0 : 0 < T := hT ▸ div_pos (mul_pos two_pos hC) hδ
  have hW := fine_steps (d := d) dieudonne_7_6_1 dieudonne_section_8_7
    dieudonne_10_5_4 dieudonne_10_6_3 (truncation_bits (d := d) k).1 hH hT0 hs
  have hW' : ‖midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s -
      evolution H T T‖ ≤ T * (B + B) :=
    hW.trans (mul_le_mul_of_nonneg_left hM hT0.le)
  have htransfer := transfer (d := d) hP hQ hP hQ (U := evolution H T T)
    (W := midpointProduct (fun x ↦ entrywise (bitTruncation k) (H x)) T N s)
    (A := 1) (B := 1) (by simp [IsUnitary]) (by simp [IsUnitary])
    (Commute.one_left _) (Commute.one_left _)
  simp only [one_mul, mul_one, sub_self, norm_zero, mul_zero, add_zero] at htransfer
  have hleak : ‖(1 - Q) * midpointProduct
      (fun x ↦ entrywise (bitTruncation k) (H x)) T N s * P‖ ≤
      ‖(1 - Q) * evolution H T T * P‖ + T * (B + B) := by
    linarith [le_abs_self (‖(1 - Q) * midpointProduct
      (fun x ↦ entrywise (bitTruncation k) (H x)) T N s * P‖ -
      ‖(1 - Q) * evolution H T T * P‖)]
  calc
    _ ≤ C / T + T * (B + B) := hleak.trans (add_le_add hU le_rfl)
    _ = δ := by
      dsimp [B]
      rw [hT]
      field_simp
      ring

/-- **Remark 3.8.** Assuming Weyl's perturbation theorem (Bhatia, Corollary III.2.6), Bhatia
Exercise VII.1.11, and the Davis--Kahan `sin Θ` theorem (Davis and Kahan 1970, in the form of
Bhatia, Theorem VII.3.1), let `H` be a regulated
time-dependent Hamiltonian with evolution `U` over time `T > 0`.
For `s ∈ {0,1}`, let `P_s` be the spectral projector of a band `{λ : a_s < λ < b_s}` of `H(s)` with
spectral gap `Γ_s`, let `ε_s = ‖H(s) - H^{(k)}(s)‖ < Γ_s/2`, and let `P'_s` be the spectral
projector of `H^{(k)}(s)` for its eigenvalues within `ε_s` of `[min S_s, max S_s]`, where `S_s` is
the set of eigenvalues in the band. Then `P_s` and `P'_s` have equal rank,
`‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖ ≤ ε_s/(Γ_s - ε_s)`, and for every matrix `W`,
`|‖(1 - P'_1) W P'_0‖ - ‖(1 - P_1) U(T) P_0‖| ≤ ‖W - U(T)‖ + Σ_s ε_s/(Γ_s - ε_s)`. Moreover,
with `I_s = [min S_s, max S_s]`, every eigenvalue of `H(s)` outside the band is at distance at least
`Γ_s` from `I_s`, every eigenvalue of `H^{(k)}(s)` not within `ε_s` of `I_s` is at distance at
least `Γ_s - ε_s` from `I_s`, and `ε_s < Γ_s - ε_s`. -/
theorem truncated_endpoints (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    (bhatia_exercise_VII_1_11 : Bhatia_Exercise_VII_1_11)
    (bhatia_theorem_VII_3_1 : Bhatia_Theorem_VII_3_1) [NeZero d] {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H) {T : ℝ} (hT : 0 < T) (k : ℕ)
    {a b : ℝ → ℝ} (hband : HasEndpointBands H a b)
    (hε : ∀ s ∈ ({0, 1} : Set ℝ),
      ‖H s - entrywise (bitTruncation k) (H s)‖ < spectralGap (H s) (a s) (b s) / 2)
    (W : 𝕄) :
    let ε := fun s ↦ ‖H s - entrywise (bitTruncation k) (H s)‖
    let Γ := fun s ↦ spectralGap (H s) (a s) (b s)
    let P := fun s ↦ bandProjector (H s) (a s) (b s)
    let P' := fun s ↦
      spectralProjector (entrywise (bitTruncation k) (H s)) (nearBand (H s) (a s) (b s) (ε s))
    let I := fun s ↦ Icc (sInf {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
      (sSup {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
    (∀ s ∈ ({0, 1} : Set ℝ), HasEqualRank (P s) (P' s) ∧
      ‖P s - P' s‖ = ‖(1 - P' s) * P s‖ ∧ ‖(1 - P' s) * P s‖ ≤ ε s / (Γ s - ε s) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (H s) \ interval (a s) (b s) →
        ∀ x ∈ I s, Γ s ≤ |μ - x|) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (entrywise (bitTruncation k) (H s)) \
          nearBand (H s) (a s) (b s) (ε s) → ∀ x ∈ I s, Γ s - ε s ≤ |μ - x|) ∧
      ε s < Γ s - ε s) ∧
    |‖(1 - P' 1) * W * P' 0‖ - ‖(1 - P 1) * evolution H T T * P 0‖| ≤
      ‖W - evolution H T T‖ + ε 0 / (Γ 0 - ε 0) + ε 1 / (Γ 1 - ε 1) := by
  classical
  dsimp only
  have hpoint (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) := hband s hs
  have hB (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) :=
    (entrywise_and_error_isHermitian _ (truncation_bits (d := d) k).1 (hpoint s hs).1).1
  have hend (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) :
      HasEqualRank (bandProjector (H s) (a s) (b s))
        (spectralProjector (entrywise (bitTruncation k) (H s))
          (nearBand (H s) (a s) (b s) ‖H s - entrywise (bitTruncation k) (H s)‖)) ∧
      ‖bandProjector (H s) (a s) (b s) -
        spectralProjector (entrywise (bitTruncation k) (H s))
          (nearBand (H s) (a s) (b s) ‖H s - entrywise (bitTruncation k) (H s)‖)‖ =
        ‖(1 - spectralProjector (entrywise (bitTruncation k) (H s))
          (nearBand (H s) (a s) (b s) ‖H s - entrywise (bitTruncation k) (H s)‖)) *
          bandProjector (H s) (a s) (b s)‖ ∧
      ‖(1 - spectralProjector (entrywise (bitTruncation k) (H s))
          (nearBand (H s) (a s) (b s) ‖H s - entrywise (bitTruncation k) (H s)‖)) *
          bandProjector (H s) (a s) (b s)‖ ≤
        ‖H s - entrywise (bitTruncation k) (H s)‖ /
          (spectralGap (H s) (a s) (b s) -
            ‖H s - entrywise (bitTruncation k) (H s)‖) := by
    have horiginal (μ : ℝ) :=
      truncated_endpoints_original_separation (hpoint s hs) (μ := μ)
    have hrank := truncated_endpoints_equal_rank bhatia_corollary_III_2_6
      (hpoint s hs) (hB s hs) (hε s hs)
    have hsep {μ : ℝ} := truncated_endpoints_perturbed_separation
      bhatia_corollary_III_2_6 (μ := μ)
      (hpoint s hs) (hB s hs) (hε s hs)
    have hres := truncated_endpoints_residual_gap (hε s hs)
    have hδ := lt_of_le_of_lt (norm_nonneg _) hres
    have heq := bhatia_exercise_VII_1_11 d _ _
      (spectralProjector_isOrthogonal _ _) (spectralProjector_isOrthogonal _ _) hrank
    refine ⟨hrank, heq, ?_⟩
    obtain ⟨hf, hn⟩ := truncated_endpoints_band_extrema (hpoint s hs)
    apply bhatia_theorem_VII_3_1 d (H s) (entrywise (bitTruncation k) (H s))
      _ _ (interval (a s) (b s)) _ _ (hpoint s hs).1 (hB s hs) rfl rfl hδ
      (sInf {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
      (sSup {x : ℝ | (x : ℂ) ∈ spectrum ℂ (H s) ∩ interval (a s) (b s)})
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hz.2
      exact ⟨csInf_le hf.bddBelow ⟨hz.1, ⟨x, hx, rfl⟩⟩,
        le_csSup hf.bddAbove ⟨hz.1, ⟨x, hx, rfl⟩⟩⟩
    · intro z hz
      have hzspec := hz.1
      rw [(hB s hs).spectrum_eq_image_range] at hzspec
      obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hzspec
      exact truncated_endpoints_outside_strip
        (csInf_le hf.bddBelow (hn.csSup_mem hf)) hδ (hsep hz)
  constructor
  · intro s hs
    exact ⟨(hend s hs).1, (hend s hs).2.1, (hend s hs).2.2,
      (fun μ hμ => truncated_endpoints_original_separation (hpoint s hs) hμ),
      (fun μ hμ => truncated_endpoints_perturbed_separation bhatia_corollary_III_2_6
        (hpoint s hs) (hB s hs) (hε s hs) hμ),
      truncated_endpoints_residual_gap (hε s hs)⟩
  · have htransfer := transfer (d := d)
      (P := bandProjector (H 0) (a 0) (b 0))
      (Q := bandProjector (H 1) (a 1) (b 1))
      (P' := spectralProjector (entrywise (bitTruncation k) (H 0))
        (nearBand (H 0) (a 0) (b 0) ‖H 0 - entrywise (bitTruncation k) (H 0)‖))
      (Q' := spectralProjector (entrywise (bitTruncation k) (H 1))
        (nearBand (H 1) (a 1) (b 1) ‖H 1 - entrywise (bitTruncation k) (H 1)‖))
      (U := evolution H T T) (W := W) (A := 1) (B := 1)
      (spectralProjector_isOrthogonal _ _) (spectralProjector_isOrthogonal _ _)
      (spectralProjector_isOrthogonal _ _) (spectralProjector_isOrthogonal _ _)
      (by simp [IsUnitary]) (by simp [IsUnitary])
      (Commute.one_left _) (Commute.one_left _)
    rw [truncated_endpoints_evolution_norm H hT.le] at htransfer
    simp only [one_mul, mul_one] at htransfer
    have hzero := hend 0 (by simp)
    have hone := hend 1 (by simp)
    rw [← hzero.2.1] at hzero
    rw [← hone.2.1] at hone
    have hbound0 := hzero.2.2
    rw [norm_sub_rev] at hbound0
    have hbound1 := hone.2.2
    rw [norm_sub_rev] at hbound1
    linarith

end RoundedClocks
