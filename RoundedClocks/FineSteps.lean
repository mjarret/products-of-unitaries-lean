/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps.BitTruncation
public import RoundedClocks.FineSteps.Checkpoints
public import RoundedClocks.FineSteps.MidpointFamily
public import RoundedClocks.FineSteps.TruncatedEndpoints

/-!
# Section 3: Evolutions as products

In the paper's order:

* Section 3.1, Level truncation:
  * Example 3.2, bit truncation: `truncation_bits`;
* Section 3.2, Midpoint products:
  * Lemma 3.4, checkpoints with midpoint error at most `ε` exist: `exists_checkpoints`;
  * Theorem 3.6, the fine-step bound: `fine_steps`;
  * equation (3.1), the fine-step bound for bit truncation: `fine_steps_bits`, with the number of
    binary places it calls for in `exists_bits`;
* Section 3.3, Finite-precision transfer:
  * Example 3.7, checkpoints and precision for a target leakage: `jrs_leakage`;
  * Remark 3.8, the endpoint projectors of the truncated Hamiltonian: `truncated_endpoints`.

Definitions 3.1, 3.3, and 3.5 are in `Definitions.lean`.

The supporting lemmas are in `FineSteps/`:

* `BitTruncation`: Section 3.1 and the proof of Example 3.2 (the error of bit truncation and the
  Schur test);
* `Checkpoints`: checkpoints and their midpoints lie in `[0,1]`;
* `MidpointFamily`: the piecewise-constant family in the proof of Theorem 3.6;
* `SpectralProjectorRank`, `OrderedEigenvalues`, `EndpointSeparation`, `TruncatedEndpoints`: the
  second paragraph of Remark 3.8.
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

/-! ## Section 3.1: Level truncation -/

/-- **Example 3.2.** Fix an integer `k ≥ 0` and a Hermitian family `H(s)` with `s ∈ [0,1]`. Let bit
truncation be `[x]_k = sgn(x) 2^{-k} ⌊2^k |x|⌋`, let `H^{(k)} = H^{([·]_k)}`, and let
`σ_k = max_p max_{s∈[0,1]} #{q : H^{(k)}_{pq}(s) ≠ H_{pq}(s)}` be the largest number of entries
that truncation changes in a row of `H(s)`. Then (i) bit truncation is odd, and (ii) for every
`s ∈ [0,1]`, `‖H(s) - H^{(k)}(s)‖ ≤ √2 σ_k 2^{-k}`. -/
theorem truncation_bits [NeZero d] (k : ℕ) :
    Function.Odd (bitTruncation k) ∧
      ∀ H : ℝ → 𝕄, IsTimeDepHamiltonian H → ∀ s ∈ Icc (0 : ℝ) 1,
        ‖H s - truncation k H s‖ ≤ √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
  -- (i) Bit truncation is odd.
  have hodd : Function.Odd (bitTruncation k) := bitTruncation_odd k
  refine ⟨hodd, fun H hH s hs ↦ ?_⟩
  -- (ii) The error `E = H(s) - H^{(k)}(s)` is Hermitian by (i).
  let E := H s - truncation k H s
  have hE : E.IsHermitian :=
    (Function.Odd.entrywise_and_sub_isHermitian hodd (hH hs)).2
  -- An entry `z` of `E` has `|z| ≤ √2 2^{-k}`.
  have hentry : ∀ i j, ‖E i j‖ ≤ √2 * ((2 : ℝ) ^ k)⁻¹ := by
    intro i j
    simpa only [E, truncation, entrywiseFamily, Matrix.sub_apply, entrywise, Matrix.of_apply] using
      norm_sub_entrywise_bitTruncation_le k (H s i j)
  -- The Schur test, with at most `σ_k` nonzero entries in each row of `E`:
  -- `‖E‖ ≤ max_p ∑_q |E_pq| ≤ √2 σ_k 2^{-k}`.
  calc
    ‖E‖ ≤ sparsity k H * (√2 * ((2 : ℝ) ^ k)⁻¹) :=
      norm_le_row_sum_of_isHermitian hE (by positivity) fun i ↦
        sum_norm_row_le_of_card (truncation_error_card_le k H hs) hentry i
    _ = √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by ring

/-! ## Section 3.2: Midpoint products -/

/-- **Lemma 3.4.** Assuming Dieudonné (7.6.1), let `H` be a regulated time-dependent Hamiltonian,
and let `ε > 0`. There are checkpoints `0 = s₀ < ⋯ < s_N = 1` with
`‖H(x) - H(y)‖ ≤ ε` whenever `sⱼ < x,y < sⱼ₊₁` for some `j`. In particular, their midpoint error
is at most `ε`. -/
theorem exists_checkpoints (dieudonne_7_6_1 : Dieudonne_7_6_1) {H : ℝ → 𝕄}
    [NeZero d] (hH : IsRegulatedTimeDepHamiltonian H) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (s : ℕ → ℝ), IsStrictCheckpoints N s ∧
      (∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), ∀ y ∈ Ioo (s j) (s (j + 1)), ‖H x - H y‖ ≤ ε) ∧
      HasMidpointError H N s ε := by
  -- By Dieudonné (7.6.1), there are checkpoints `0 = s₀ < ⋯ < s_N = 1` and matrices `Aⱼ` with
  -- `‖H(s) - Aⱼ‖ ≤ ε/2` for `sⱼ < s < sⱼ₊₁`.
  obtain ⟨G, hG, happrox⟩ :=
    dieudonne_7_6_1 d H 0 1 (ε / 2) zero_le_one hH.regulated (half_pos hε)
  obtain ⟨N, s, A, hs0, hsN, hstrict, hG⟩ := hG
  have hs : IsStrictCheckpoints N s :=
    ⟨⟨fun j hj ↦ (hstrict j hj).le, hs0, hsN⟩, hstrict⟩
  have hA : ∀ j < N, ∀ x ∈ Ioo (s j) (s (j + 1)), ‖H x - A j‖ ≤ ε / 2 := by
    intro j hj x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 :=
      ⟨(checkpoint_mem hs.isCheckpoints hj.le).1.trans hx.1.le,
        hx.2.le.trans (checkpoint_mem hs.isCheckpoints (Nat.succ_le_of_lt hj)).2⟩
    have h := happrox x hxI
    rw [hG j hj x hx] at h
    exact h.le
  -- Then `‖H(x) - H(y)‖ ≤ ε` for `sⱼ < x, y < sⱼ₊₁`.
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
  -- The midpoint `s_{j+1/2}` is such a `y`, as `sⱼ < sⱼ₊₁`.
  have hmid : (s j + s (j + 1)) / 2 ∈ Ioo (s j) (s (j + 1)) := by
    constructor <;> linarith [hs.lt_succ j hj]
  exact hpair j hj x hx _ hmid

/-- **Theorem 3.6.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with the
remark (10.4.6), let `F : ℝ → ℝ` be odd, and let `H` be a regulated time-dependent Hamiltonian with
evolution `U` over time `T > 0`. The midpoint product `W` of `H^{(F)}` over time `T` on any
checkpoints `0 = s₀ ≤ ⋯ ≤ s_N = 1` satisfies
`‖W - U(T)‖ ≤ T max_j sup_{s_j < x < s_{j+1}} ‖H(x) - H^{(F)}(s_{j+1/2})‖`.
A repeated checkpoint contributes the factor `1` to `W` and an empty supremum, taken to be `0`.
The right side is `T * midpointApproximationError F H N s`. -/
theorem fine_steps (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {F : ℝ → ℝ} (hF : Function.Odd F) {H : ℝ → 𝕄}
    (hH : IsRegulatedTimeDepHamiltonian H)
    {T : ℝ} (hT : 0 < T) {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s) :
    ‖midpointProduct (entrywiseFamily F H) T N s - evolution H T T‖ ≤
      T * midpointApproximationError F H N s := by
  -- A regulated `H` is bounded (Section 2, after Definition 2.1), so the supremum on the right is
  -- finite.
  obtain ⟨C, hC⟩ := hH.regulated.bounded dieudonne_7_6_1 zero_le_one
  have hbounded : BddAbove ((fun x ↦ ‖H x‖) '' Icc (0 : ℝ) 1) :=
    ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  -- The piecewise-constant family `G(x) = T H^{(F)}(s_{j+1/2})` for `sⱼ < x < sⱼ₊₁` is Hermitian,
  -- as `F` is odd.
  obtain ⟨G, hGreg, _hGherm, hpieces, hbound⟩ :=
    exists_midpoint_family hF hH.hermitian hbounded hT hs
  let A : ℕ → 𝕄 := fun j ↦ T • entrywise F (H ((s j + s (j + 1)) / 2))
  have hA : ∀ j < N, (A j).IsHermitian := fun j hj ↦
    midpoint_sample_isHermitian hF hH.hermitian T hs hj
  -- Its evolution `V` ends at the midpoint product `W` by (2.4).
  obtain ⟨V, hV, hVend⟩ := piecewise_product hs.le_succ hA hpieces
  have hV' : Generates G V 0 1 := by simpa only [hs.zero, hs.last] using hV
  have hVend' : V 1 = midpointProduct (entrywiseFamily F H) T N s := by
    rw [← hs.last, hVend]
    -- The factors of (2.4) are `e^{-i(sⱼ₊₁ - sⱼ)(T H^{(F)}(s_{j+1/2}))}`; those of Definition 3.5
    -- are `e^{-iT(sⱼ₊₁ - sⱼ) H^{(F)}(s_{j+1/2})}`.
    simp only [midpointProduct, orderedProduct, entrywiseFamily, A]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [smul_comm (-I * (s (j + 1) - s j : ℝ)) T]
    rw [← smul_assoc]
    congr 1
    apply congrArg (fun z : ℂ ↦ z • entrywise F (H ((s j + s (j + 1)) / 2)))
    apply Complex.ext <;> simp
  -- With `s = t/T`, `U(Ts)` for `s ∈ [0,1]` is generated by `K(s) = T H(s)` (Section 2).
  let K : ℝ → 𝕄 := fun x ↦ T • H x
  have hKreg : IsRegulated K 0 1 := hH.regulated.const_smul T
  have hHTreg : IsRegulated (fun t ↦ H (t / T)) 0 T := hH.regulated.comp_div hT
  have hHTherm : IsHermitianFamily (fun t ↦ H (t / T)) 0 T := by
    intro t ht
    exact hH.hermitian (unitInterval.div_mem ht.1 hT.le ht.2)
  have hU : Generates (fun t ↦ H (t / T)) (evolution H T) 0 T := by
    simpa only [evolution] using
      generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3
        hT.le hHTreg hHTherm
  have hUK : Generates K (fun x ↦ evolution H T (T * x)) 0 1 := by
    simpa only [K] using generates_reparameterized hT hU
  have hKherm : IsHermitianFamily K 0 1 := by
    intro x hx
    change (T • H x).IsHermitian
    exact isHermitian_real_smul (hH.hermitian hx) T
  -- Duhamel's bound (2.3) for `K` and `G`, whose evolutions end at `U(T)` and at `W`.
  have hD := duhamel dieudonne_7_6_1 zero_le_one
    hKreg hKherm hGreg hUK hV'
  -- Regulated families are integrable.
  have hKint := hKreg.intervalIntegrable dieudonne_7_6_1 zero_le_one
  have hGint := hGreg.intervalIntegrable dieudonne_7_6_1 zero_le_one
  have hdiff : IntervalIntegrable (fun x ↦ ‖K x - G x‖)
      MeasureTheory.volume 0 1 :=
    (hKint.sub hGint).norm
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖K x - G x‖ := by
      -- Duhamel's bound (2.3).
      simpa only [hVend', mul_one] using hD
    _ ≤ ∫ _x in (0 : ℝ)..1, T * midpointApproximationError F H N s :=
      -- Between checkpoints, `‖T H(x) - G(x)‖ = T ‖H(x) - H^{(F)}(s_{j+1/2})‖`.
      intervalIntegral.integral_mono_on zero_le_one hdiff intervalIntegrable_const hbound
    _ = T * midpointApproximationError F H N s := by
      -- The interval lengths sum to one.
      simp

/-- **Equation (3.1).** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with the
remark (10.4.6), let `H` be a regulated time-dependent Hamiltonian with evolution `U` over time
`T > 0`, let `ε ≥ 0`, and let `W` be the midpoint product of `H^{(k)}` over time `T` on checkpoints
with midpoint error at most `ε`. Then `‖W - U(T)‖ ≤ T (ε + √2 σ_k 2^{-k})`. -/
theorem fine_steps_bits (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsRegulatedTimeDepHamiltonian H) {T ε : ℝ} (hT : 0 < T)
    (hε : 0 ≤ ε) (k : ℕ) {N : ℕ} {s : ℕ → ℝ} (hs : IsCheckpoints N s)
    (hmid : HasMidpointError H N s ε) :
    ‖midpointProduct (truncation k H) T N s - evolution H T T‖ ≤
      T * (ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
  -- For `sⱼ < x < sⱼ₊₁`, the midpoint error of the checkpoints and Example 3.2(ii) give
  -- `‖H(x) - H^{(k)}(s_{j+1/2})‖ ≤ ‖H(x) - H(s_{j+1/2})‖ + ‖H(s_{j+1/2}) - H^{(k)}(s_{j+1/2})‖`
  -- `≤ ε + √2 σ_k 2^{-k}`.
  have herr : midpointApproximationError (bitTruncation k) H N s ≤
      ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
    refine csSup_le ⟨0, Or.inl rfl⟩ ?_
    rintro r (rfl | ⟨j, hj, x, hx, rfl⟩)
    · exact add_nonneg hε (by positivity)
    · calc
        _ ≤ ‖H x - H ((s j + s (j + 1)) / 2)‖ +
            ‖H ((s j + s (j + 1)) / 2) - truncation k H ((s j + s (j + 1)) / 2)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := add_le_add (hmid j hj x hx)
          ((truncation_bits k).2 H hH.hermitian _ (checkpoint_midpoint_mem hs hj))
  -- Bit truncation is odd by Example 3.2(i), so Theorem 3.6 gives (3.1).
  exact (fine_steps dieudonne_7_6_1 dieudonne_10_5_4 dieudonne_10_6_3
    (truncation_bits (d := d) k).1 hH hT hs).trans (mul_le_mul_of_nonneg_left herr hT.le)

/-- Section 3.2, after equation (3.1). As `σ_k ≤ d`, increasing the precision makes the truncation
error arbitrarily small: for every `η > 0` some `k` has `√2 σ_k 2^{-k} ≤ η`. Examples 3.7 and 4.5
choose such a `k`. -/
theorem exists_bits (H : ℝ → 𝕄) {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ η := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (√2 * d / η) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_⟩
  have hσ : (sparsity k H : ℝ) ≤ d := by
    exact_mod_cast ciSup_le' fun s ↦ ciSup_le' fun p ↦
      (Finset.card_filter_le _ _).trans (by simp)
  rw [div_lt_iff₀ hη] at hk
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  -- `σ_k ≤ d`, and `k` is chosen with `√2 d < 2^k η`.
  calc
    √2 * (sparsity k H : ℝ) ≤ √2 * d := mul_le_mul_of_nonneg_left hσ (Real.sqrt_nonneg 2)
    _ ≤ η * 2 ^ k := hk.le.trans_eq (mul_comm _ _)

/-! ## Section 3.3: Finite-precision transfer -/

/-- Section 3.3, first sentence. By Proposition 2.4 with `P̃ = P`, `Q̃ = Q`, and `A = B = 1`, the
leakages `‖(1 - Q) W P‖` and `‖(1 - Q) U P‖` of two matrices differ by at most `‖W - U‖`, so
leakage bounds transfer both ways. -/
theorem transfer_same_projectors [NeZero d] {P Q U W : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) :
    |‖(1 - Q) * W * P‖ - ‖(1 - Q) * U * P‖| ≤ ‖W - U‖ := by
  have h := transfer (d := d) (Q := Q) hP hP hQ (U := U) (W := W) (A := 1) (B := 1)
    (by simp [IsUnitary]) (by simp [IsUnitary]) (Commute.one_left _) (Commute.one_left _)
  simpa only [one_mul, mul_one, sub_self, norm_zero, mul_zero, add_zero] using h

/-- **Example 3.7.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with the
remark (10.4.6), let `H` be a regulated time-dependent Hamiltonian, let `P` and `Q` be orthogonal
projectors, and let `C > 0`. For a target leakage `δ > 0`, let `T = 2C/δ`, and assume that the
evolution `U` of `H` over time `T` satisfies `‖(1 - Q) U(T) P‖ ≤ C/T`. Choose checkpoints with
midpoint error at most `δ²/(8C)` and an integer `k ≥ 0` with `√2 σ_k 2^{-k} ≤ δ²/(8C)`. The
midpoint product `W` of `H^{(k)}` on these checkpoints over time `T` satisfies
`‖(1 - Q) W P‖ ≤ δ`. -/
theorem jrs_leakage (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {H : ℝ → 𝕄} (hH : IsRegulatedTimeDepHamiltonian H)
    {P Q : 𝕄} (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) {C δ T : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) (hT : T = 2 * C / δ)
    (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T) {N : ℕ} {s : ℕ → ℝ}
    (hs : IsCheckpoints N s) (hmid : HasMidpointError H N s (δ ^ 2 / (8 * C))) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ ^ 2 / (8 * C)) :
    ‖(1 - Q) * midpointProduct (truncation k H) T N s * P‖ ≤ δ := by
  have hT0 : 0 < T := hT ▸ div_pos (mul_pos two_pos hC) hδ
  -- By Proposition 2.4 with `P̃ = P`, `Q̃ = Q`, and `A = B = 1`, the leakages of `W` and `U(T)`
  -- differ by at most `‖W - U(T)‖`.
  have hleak := (abs_le.mp (transfer_same_projectors (U := evolution H T T)
    (W := midpointProduct (truncation k H) T N s) hP hQ)).2
  -- Equation (3.1) with `ε = δ²/(8C)`.
  have hW := fine_steps_bits dieudonne_7_6_1 dieudonne_10_5_4
    dieudonne_10_6_3 hH hT0 (by positivity) k hs hmid
  -- The display of the paper's proof, with the assumed bound `‖(1 - Q) U(T) P‖ ≤ C/T`.
  calc
    _ ≤ C / T + T * (δ ^ 2 / (8 * C) + √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
      linarith
    _ ≤ C / T + T * (δ ^ 2 / (8 * C) + δ ^ 2 / (8 * C)) := by
      -- the choice of `k`
      gcongr
    _ = δ := by
      -- With `T = 2C/δ`, this is `δ/2 + δ/4 + δ/4`.
      rw [hT]
      field_simp
      ring

/-- **Remark 3.8.** Assuming Weyl's perturbation theorem (Bhatia, Corollary III.2.6), Bhatia,
Exercise VII.1.11, and the Davis–Kahan `sin Θ` theorem (Davis and Kahan 1970, in the form of
Bhatia, Theorem VII.3.1), let `H` be a matrix family with evolution `U` over time `T > 0`. For
`s ∈ {0,1}`, let `P_s` be the spectral projector of a band `S_s` of `H(s)`, its
eigenvalues in `{λ : a_s < λ < b_s}`, with spectral gap `Γ_s`, suppose
`ε_s = ‖H(s) - H^{(k)}(s)‖ < Γ_s/2`, and let `P'_s`, the paper's `P̃_s`, be the spectral projector
of `H^{(k)}(s)` for its eigenvalues within `ε_s` of `I_s = [min S_s, max S_s]`. Then, for
`s ∈ {0,1}`, the eigenvalues of `H(s)` outside `S_s` lie at distance at least `Γ_s` from `I_s`,
`P'_s` and `P_s` have equal rank, the other eigenvalues of `H^{(k)}(s)` lie at distance at least
`Γ_s - ε_s > ε_s` from `I_s`, and `‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖ ≤ ε_s/(Γ_s - ε_s)`. Hence, for
every matrix `W`,
`|‖(1 - P'_1) W P'_0‖ - ‖(1 - P_1) U(T) P_0‖| ≤ ‖W - U(T)‖ + Σ_s ε_s/(Γ_s - ε_s)`.

Below, `hull s` is `I_s`. The statement holds without assuming that `H` is a regulated
time-dependent Hamiltonian; the endpoint-band hypothesis supplies Hermitian endpoints. -/
theorem truncated_endpoints (bhatia_corollary_III_2_6 : Bhatia_Corollary_III_2_6)
    (bhatia_exercise_VII_1_11 : Bhatia_Exercise_VII_1_11)
    (bhatia_theorem_VII_3_1 : Bhatia_Theorem_VII_3_1) [NeZero d] {H : ℝ → 𝕄}
    {T : ℝ} (hT : 0 < T) (k : ℕ)
    {a b : ℝ → ℝ} (hband : HasEndpointBands H a b)
    (hε : ∀ s ∈ ({0, 1} : Set ℝ),
      ‖H s - truncation k H s‖ < spectralGap (H s) (a s) (b s) / 2)
    (W : 𝕄) :
    let ε := fun s ↦ ‖H s - truncation k H s‖
    let Γ := fun s ↦ spectralGap (H s) (a s) (b s)
    let hull := fun s ↦ bandHull (H s) (a s) (b s)
    let P := fun s ↦ bandProjector (H s) (a s) (b s)
    let P' := fun s ↦ spectralProjector (truncation k H s) (nearBand (H s) (a s) (b s) (ε s))
    (∀ s ∈ ({0, 1} : Set ℝ),
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (H s) \ interval (a s) (b s) →
        ∀ x ∈ hull s, Γ s ≤ |μ - x|) ∧
      HasEqualRank (P s) (P' s) ∧
      (∀ μ : ℝ, (μ : ℂ) ∈ spectrum ℂ (truncation k H s) \ nearBand (H s) (a s) (b s) (ε s) →
        ∀ x ∈ hull s, Γ s - ε s ≤ |μ - x|) ∧
      ε s < Γ s - ε s ∧
      ‖P s - P' s‖ = ‖(1 - P' s) * P s‖ ∧
      ‖(1 - P' s) * P s‖ ≤ ε s / (Γ s - ε s)) ∧
    |‖(1 - P' 1) * W * P' 0‖ - ‖(1 - P 1) * evolution H T T * P 0‖| ≤
      ‖W - evolution H T T‖ + ε 0 / (Γ 0 - ε 0) + ε 1 / (Γ 1 - ε 1) := by
  classical
  intro ε Γ hull P P'
  -- The truncations `H^{(k)}(s)` are Hermitian, as bit truncation is odd.
  have hB (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) : (truncation k H s).IsHermitian :=
    (Function.Odd.entrywise_and_sub_isHermitian (bitTruncation_odd k) (hband s hs).1).1
  -- Second paragraph of the remark, at each endpoint: equal rank by Weyl's perturbation theorem,
  -- `‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖` by Bhatia, Exercise VII.1.11, and the Davis–Kahan bound.
  have hend (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) :
      HasEqualRank (P s) (P' s) ∧ ‖P s - P' s‖ = ‖(1 - P' s) * P s‖ ∧
        ‖(1 - P' s) * P s‖ ≤ ε s / (Γ s - ε s) :=
    truncated_endpoint_projectors bhatia_corollary_III_2_6 bhatia_exercise_VII_1_11
      bhatia_theorem_VII_3_1 (hband s hs) (hB s hs) (hε s hs)
  refine ⟨fun s hs ↦ ⟨
    -- The eigenvalues of `H(s)` outside the band lie at distance at least `Γ_s` from `I_s`.
    fun μ hμ ↦ truncated_endpoints_original_separation (hband s hs) hμ,
    -- `P'_s` and `P_s` have equal rank.
    (hend s hs).1,
    -- The other eigenvalues of `H^{(k)}(s)` lie at distance at least `Γ_s - ε_s` from `I_s`.
    fun μ hμ ↦ truncated_endpoints_perturbed_separation bhatia_corollary_III_2_6
      (hband s hs) (hB s hs) (hε s hs) hμ,
    -- `ε_s < Γ_s/2` gives `ε_s < Γ_s - ε_s`.
    by simp only [ε, Γ]; linarith [hε s hs],
    -- `‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖ ≤ ε_s/(Γ_s - ε_s)`.
    (hend s hs).2.1, (hend s hs).2.2⟩, ?_⟩
  -- Third paragraph: Proposition 2.4 with `A = B = 1`, and `‖U(T)‖ = 1`.
  have htransfer := transfer (d := d) (P := P 0) (Q := P 1) (P' := P' 0) (Q' := P' 1)
    (U := evolution H T T) (W := W) (A := 1) (B := 1)
    (spectralProjector_isOrthogonal _ _)
    (spectralProjector_isOrthogonal _ _) (spectralProjector_isOrthogonal _ _)
    (by simp [IsUnitary]) (by simp [IsUnitary])
    (Commute.one_left _) (Commute.one_left _)
  rw [norm_evolution_end H hT.le] at htransfer
  simp only [one_mul, mul_one] at htransfer
  calc
    _ ≤ ‖W - evolution H T T‖ + (‖P' 0 - P 0‖ + ‖P' 1 - P 1‖) := htransfer
    _ = ‖W - evolution H T T‖ + ‖P 0 - P' 0‖ + ‖P 1 - P' 1‖ := by
      rw [norm_sub_rev (P' 0), norm_sub_rev (P' 1)]
      ring
    _ ≤ ‖W - evolution H T T‖ + ε 0 / (Γ 0 - ε 0) + ε 1 / (Γ 1 - ε 1) := by
      -- `‖P_s - P'_s‖ = ‖(1 - P'_s) P_s‖ ≤ ε_s/(Γ_s - ε_s)` at `s = 0` and `s = 1`.
      have h0 := hend 0 (by simp)
      have h1 := hend 1 (by simp)
      exact add_le_add (add_le_add le_rfl (h0.2.1.trans_le h0.2.2)) (h1.2.1.trans_le h1.2.2)

end RoundedClocks
