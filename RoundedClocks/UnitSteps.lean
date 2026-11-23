/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions
public import RoundedClocks.Preliminaries
public import RoundedClocks.FineSteps
public import RoundedClocks.Appendix
public import RoundedClocks.UnitSteps.Basic
public import RoundedClocks.UnitSteps.RoundedClockComparison
public import RoundedClocks.UnitSteps.UnitSharp
public import RoundedClocks.UnitSteps.RoundedClockBound
public import RoundedClocks.UnitSteps.UnitTransferDuhamel
public import RoundedClocks.UnitSteps.OrderedEigenvalueContinuity
public import RoundedClocks.UnitSteps.ExponentialSpectrum
public import RoundedClocks.UnitSteps.UnitaryProducts
public import RoundedClocks.UnitSteps.WalkLeakage.Band
public import RoundedClocks.UnitSteps.WalkLeakage.EigenphaseGap
public import RoundedClocks.UnitSteps.WalkLeakage.HermitianLogarithm
public import RoundedClocks.UnitSteps.WalkLeakage.LogarithmUniqueness
public import RoundedClocks.UnitSteps.WalkLeakage.LogarithmWidth
public import RoundedClocks.UnitSteps.WalkLeakage.AgreeingFamilies
public import RoundedClocks.UnitSteps.WalkLeakage.EndpointProjectors

/-!
# Section 4: Products as evolutions

The rounded-clock comparison (Theorems 4.2 and 4.4), its examples (Examples 4.3 and 4.5), and
products of given unitaries (Theorems 4.6 and 4.7). Each proof takes the paper's steps in the
paper's order, and the files of `RoundedClocks/UnitSteps/` prove the steps:

* Section 4.1, Unit-step products. Theorem 4.2, `rounded_clock_comparison`:
  `RoundedClockComparison`. Example 4.3, `unit_sharp`: `UnitSharp`.
* Section 4.2, The jumps. Theorem 4.4, `rounded_clock_bound`: `RoundedClockBound`.
* Section 4.3, Transfer of continuous bounds. Example 4.5, `unit_transfer`:
  `UnitTransferDuhamel`.
* Section 4.4, Products of given unitaries. Theorem 4.6, `unitary_products`: `UnitaryProducts`,
  with `OrderedEigenvalueContinuity` (the least eigenvalue is continuous) and
  `ExponentialSpectrum` (the eigenvalues of `e^{-iH}`).
* Theorem 4.7, `walk_leakage`: the files of `WalkLeakage/`, in the order of the proof.
  `EigenphaseGap` (the least eigenphase gap is positive), `HermitianLogarithm` and
  `LogarithmUniqueness` (the continuous logarithm), `LogarithmWidth` (its spectrum lies in
  `[ℓ, ℓ + w]`), `AgreeingFamilies` (Theorem 4.6 applies to `W`), and `EndpointProjectors` (the
  projectors `P` and `Q`), with `Band` (Definition 2.5(ii) by parts) and
  `ExponentialCoordinates` (`e^{-iH}` in an eigenbasis of `H`).

`Basic` holds facts about unitaries, regulated families, and eigenvectors used throughout.
Definition 4.1 and the constants of Appendix B are in `Definitions.lean`.
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

/-! ## Section 4.1: Unit-step products -/

/-- **Theorem 4.2.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with the
remark (10.4.6), let `T ≥ 1` be an integer, and let `H(s)` for `s ∈ [0,1]` be a
differentiable time-dependent Hamiltonian with one-sided derivatives at `s = 0` and `s = 1`, with
`‖H'(s₁) - H'(s₂)‖ ≤ L |s₁ - s₂|` for `s₁, s₂ ∈ [0,1]`, and with samples `H(j/T)` for `0 ≤ j ≤ T`
whose eigenvalue differences have modulus at most a width `w < 2π`. Then the evolutions `U` of
`H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy
`‖V(T) - U(T)‖ ≤ (c₀ (‖H'(0)‖ + ‖H'(1)‖) + L/24 + c₁ ‖H'‖∞²)/T + Σ_{j=1}^T ‖Δ_j‖`,
where `c₀` and `c₁` are the constants of Appendix B at width `w`, and
`Δ_j = (1/T) (𝒩([H(j/T),·])H'(j/T) - 𝒩([H((j-1)/T),·])H'((j-1)/T))`, which is `Δ H T j`. -/
theorem rounded_clock_comparison (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hw0 : 0 ≤ w := width_nonneg hH hwidth
  have hsample : ∀ j : ℕ, j ≤ T → (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := fun j hj ↦
    unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T) (by exact_mod_cast hj)
  /- "Let `Y` be the correction that Lemma A.1 gives for every `j`": Lemma A.1 for `Ω = H(j/T)`
  and `H'(j/T)` gives `Z_j`, and the correction for `|t - j| < 1/2` is `Y_j(t) = Z_j(t - j)/T`,
  which solves (4.2) with `D = H'(j/T)/T`. -/
  obtain ⟨Z, hZode, hZleft, hZright, hZzero, hZgrowth⟩ :=
    exists_sample_corrections hH hw hwidth
  /- The two families `K(t) = H(t/T)` and `G(t) = H(⌊t+1/2⌋/T)`, their evolutions `U` and `V`, the
  pieces `Y_j` of the correction with their derivatives `Y_j'`, and the residual `R` of the piece
  `n(t) = ⌊t + 1/2⌋`. The points are `p_j = clockPoint T j`: `p_0 = 0`, `p_j = j - 1/2` for
  `1 ≤ j ≤ T`, and `p_{T+1} = T`. -/
  let K : ℝ → 𝕄 := fun t ↦ H (t / T)
  let G : ℝ → 𝕄 := fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)
  let U := evolution H T
  let V := roundedEvolution H T
  let Y : ℕ → ℝ → 𝕄 := fun j t ↦ (1 / T : ℝ) • Z j (t - j)
  let Y' : ℕ → ℝ → 𝕄 := fun j t ↦ (1 / T : ℝ) • ((t - j) • ∂H (j / T) -
    I • (H (j / T) * Z j (t - j) - Z j (t - j) * H (j / T)))
  let n : ℝ → ℕ := fun t ↦ (⌊t + 1 / 2⌋).toNat
  let R : ℝ → 𝕄 := fun t ↦ K t - G t - Y' (n t) t - I • (K t * Y (n t) t - Y (n t) t * G t)
  -- For `t ∈ [0,T]`, `n(t)` is the rounded clock `⌊t + 1/2⌋`, at most `T`.
  have hn : ∀ t ∈ Icc (0 : ℝ) T, ((n t : ℕ) : ℝ) = ⌊t + 1 / 2⌋ ∧ n t ≤ T := by
    intro t ht
    have h0 : 0 ≤ ⌊t + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith [ht.1])
    have hlt : ⌊t + 1 / 2⌋ < (T : ℤ) + 1 := Int.floor_lt.mpr (by push_cast; linarith [ht.2])
    refine ⟨by exact_mod_cast Int.toNat_of_nonneg h0, ?_⟩
    change (⌊t + 1 / 2⌋).toNat ≤ T
    omega
  have hround : ∀ t ∈ Icc (0 : ℝ) T, G t = H ((n t : ℝ) / T) := by
    intro t ht
    simp only [G, (hn t ht).1]
  -- For `t ∈ [p_j, p_{j+1}]`, `τ = t - j` lies in `[-1/2, 1/2]`.
  have hpiece : ∀ j : ℕ, j ≤ T → ∀ t ∈ Icc (clockPoint T j) (clockPoint T (j + 1)),
      t - j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j hj t ht
    constructor <;> linarith [sub_half_le_clockPoint hj, clockPoint_succ_le T j, ht.1, ht.2]
  /- The hypotheses of Theorem 2.2 on the two families: `K` is continuous, hence regulated; `G`
  is a function of the rounded clock, hence regulated; both are Hermitian for `t ∈ [0,T]` and
  generate `U` and `V`, which are unitary. -/
  obtain ⟨hKreg, hKh, hU⟩ :
      IsRegulated K 0 T ∧ IsHermitianFamily K 0 T ∧ Generates K U 0 T :=
    generates_evolution dieudonne_10_5_4 dieudonne_10_6_3 hT hH hL.1.continuousOn
  obtain ⟨hGreg, -, hV⟩ :
      IsRegulated G 0 T ∧ IsHermitianFamily G 0 T ∧ Generates G V 0 T :=
    generates_roundedEvolution dieudonne_10_5_4 dieudonne_10_6_3 hT hH
  have hUunit : ∀ t ∈ Icc (0 : ℝ) T, IsUnitary (U t) := hU.2.2.1
  have hVunit : ∀ t ∈ Icc (0 : ℝ) T, IsUnitary (V t) := hV.2.2.1
  /- The hypotheses of Theorem 2.2 on the correction: each piece `Y_j` is continuous for
  `t ∈ [p_j, p_{j+1}]` and has the regulated derivative `Y_j'` at every `t` with
  `p_j < t < p_{j+1}`, where `R` is its residual. -/
  have hZcont : ∀ j ≤ T, ContinuousOn (fun t ↦ Z j (t - j))
      (Icc (clockPoint T j) (clockPoint T (j + 1))) := by
    intro j hj
    have hc : ContinuousOn (Z j) (Icc (-1 / 2) (1 / 2)) :=
      fun τ hτ ↦ (hZode j hj τ hτ).continuousWithinAt
    exact hc.comp (continuousOn_id.sub continuousOn_const) (hpiece j hj)
  have hYc : ∀ j ≤ T, ContinuousOn (Y j) (Icc (clockPoint T j) (clockPoint T (j + 1))) :=
    fun j hj ↦ (hZcont j hj).const_smul _
  have hY' : ∀ j ≤ T, IsRegulated (Y' j) (clockPoint T j) (clockPoint T (j + 1)) := by
    intro j hj
    apply ContinuousOn.isRegulated
    have hc := hZcont j hj
    have hlin : ContinuousOn (fun t : ℝ ↦ (t - j) • ∂H (j / T))
        (Icc (clockPoint T j) (clockPoint T (j + 1))) :=
      (continuousOn_id.sub continuousOn_const).smul continuousOn_const
    exact (hlin.sub (((continuousOn_const.mul hc).sub
      (hc.mul continuousOn_const)).const_smul I)).const_smul _
  have hYd : ∀ j ≤ T, ∀ t ∈ Ioo (clockPoint T j) (clockPoint T (j + 1)), t ∉ (∅ : Set ℝ) →
      HasDerivAt (Y j) (Y' j t) t := by
    intro j hj t ht _
    have hτj : t - j ∈ Ioo (-1 / 2 : ℝ) (1 / 2) :=
      ⟨by linarith [sub_half_le_clockPoint hj, ht.1], by linarith [clockPoint_succ_le T j, ht.2]⟩
    have h := (hZode j hj (t - j) (Ioo_subset_Icc_self hτj)).hasDerivAt
      (Icc_mem_nhds hτj.1 hτj.2)
    exact (h.comp_sub_const t j).const_smul (1 / T : ℝ)
  have hR : ∀ j ≤ T, ∀ t ∈ Ioo (clockPoint T j) (clockPoint T (j + 1)), t ∉ (∅ : Set ℝ) →
      R t = K t - G t - Y' j t - I • (K t * Y j t - Y j t * G t) := by
    intro j hj t ht _
    have hfl : ⌊t + 1 / 2⌋ = (j : ℤ) :=
      floor_add_half_eq (by push_cast; linarith [sub_half_le_clockPoint hj, ht.1])
        (by push_cast; linarith [clockPoint_succ_le T j, ht.2])
    simp only [R, n, hfl, Int.toNat_natCast]
  -- **Theorem 2.2** with endpoints `0` and `T`.
  have hcomp := comparison dieudonne_7_6_1 K G U V hKreg hKh
    hGreg hU hV T (clockPoint T) (fun j _ ↦ clockPoint_mono T j) (clockPoint_zero T)
    clockPoint_last Y (fun _ ↦ ∅) (fun _ _ ↦ countable_empty)
    hYc Y' hY' hYd R hR
  -- The jump of `Y` at `p_j = j - 1/2` is `Δ_j`, as both pieces have end values `𝒩([Ω,·])D`.
  have hjump : ∀ j ∈ Finset.Icc 1 T,
      Y j (clockPoint T j) - Y (j - 1) (clockPoint T j) = Δ H T j := by
    intro j hj
    obtain ⟨h1, hjT⟩ := Finset.mem_Icc.mp hj
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
    have hleft : (j : ℝ) - 1 / 2 - j = -1 / 2 := by ring
    have hright : (j : ℝ) - 1 / 2 - ((j - 1 : ℕ) : ℝ) = 1 / 2 := by rw [hcast]; ring
    rw [clockPoint_eq h1 hjT]
    simp only [Y]
    rw [hleft, hright, hZleft j hjT, hZright (j - 1) (by omega), hcast, ← smul_sub]
    rfl
  /- **Equation (4.5).** `‖V(T) - U(T)‖ = ‖U(T)† V(T) - 1‖`, and Theorem 2.2 with the triangle
  inequality bounds this by `‖∫_0^T i U† R V dt‖ + ‖Y(T)‖ + ‖Y(0)‖ + Σ_j ‖Δ_j‖`. The first term is
  at most the `∫_0^T ‖R‖ dt` of (4.5); `hint` below bounds it without forming that integral. -/
  have hUT := hUunit T ⟨hT0.le, le_rfl⟩
  have hVT := hVunit T ⟨hT0.le, le_rfl⟩
  have h45 : ‖V T - U T‖ ≤ ‖∫ t in (0 : ℝ)..T, I • ((U t)† * R t * V t)‖ + ‖Y T T‖ + ‖Y 0 0‖ +
      ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
    have hsum : ‖I • ∑ j ∈ Finset.Icc 1 T, (U (clockPoint T j))† *
        (Y j (clockPoint T j) - Y (j - 1) (clockPoint T j)) * V (clockPoint T j)‖ ≤
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
      rw [hjump j hj]
      exact norm_conj_le (hUunit _ (clockPoint_mem T j)) (hVunit _ (clockPoint_mem T j)) _
    have hend : ‖I • ((U T)† * Y T T * V T)‖ ≤ ‖Y T T‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
      exact norm_conj_le hUT hVT _
    have hstart : ‖I • Y 0 0‖ = ‖Y 0 0‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have htri : ∀ A B C E : 𝕄, ‖A + B - C - E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖E‖ := fun A B C E ↦
      by simpa [sub_eq_add_neg] using norm_add₄_le (a := A) (b := B) (c := -C) (d := -E)
    rw [norm_sub_eq_norm_star_mul_sub_one hUT, hcomp]
    exact (htri _ _ _ _).trans (add_le_add (add_le_add (add_le_add le_rfl hend) hstart.le) hsum)
  -- Lemma A.1(ii) at `τ = 0` bounds the boundary values `Y(0)` and `Y(T)`.
  have hY0 : ‖Y 0 0‖ ≤ c₀ w * ‖∂H 0‖ / T := by
    have h := hZzero 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, zero_div] at h
    simp only [Y, Nat.cast_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hT0)]
    calc
      1 / T * ‖Z 0 0‖ ≤ 1 / T * (c₀ w * ‖∂H 0‖) := by gcongr
      _ = _ := by ring
  have hYT : ‖Y T T‖ ≤ c₀ w * ‖∂H 1‖ / T := by
    have h := hZzero T le_rfl
    rw [div_self hT0.ne'] at h
    simp only [Y, sub_self, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hT0)]
    calc
      1 / T * ‖Z T 0‖ ≤ 1 / T * (c₀ w * ‖∂H 1‖) := by gcongr
      _ = _ := by ring
  /- The residual display, first and second lines. By (4.1), whose bracket vanishes as `Y` solves
  (4.2), `‖R‖ ≤ Lτ²/(2T²) + (‖H'‖∞|τ|/T)(c₀ + τ²/2)‖H'‖∞/T` with `τ = t - ⌊t + 1/2⌋`. -/
  have hc₀ := c₀_nonneg_of_width hw0 hw
  let g : ℝ → ℝ := fun τ ↦
    1 / T ^ 2 * (L / 2 * τ ^ 2 + ‖∂H‖∞ ^ 2 * |τ| * (c₀ w + τ ^ 2 / 2))
  have hRle : ∀ t ∈ Icc (0 : ℝ) T, ‖R t‖ ≤ g (t - ⌊t + 1 / 2⌋) := by
    intro t ht
    obtain ⟨hnt, hnT⟩ := hn t ht
    have hτj : t - (n t : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      rw [hnt]
      exact sub_round_mem_Icc t
    have hjs := hsample (n t) hnT
    have hts : t / T ∈ Icc (0 : ℝ) 1 := unitInterval.div_mem ht.1 hT0.le ht.2
    -- Lemma A.1(ii) with `‖D‖ ≤ ‖H'‖∞/T`: `‖Z(τ)‖ ≤ (c₀ + τ²/2) ‖H'(j/T)‖ ≤ (c₀ + τ²/2) ‖H'‖∞`.
    have hZb : ‖Z (n t) (t - n t)‖ ≤ (c₀ w + (t - n t) ^ 2 / 2) * ‖∂H‖∞ := by
      have h1 := hZgrowth (n t) hnT (t - n t) hτj
      have h0 := hZzero (n t) hnT
      have hD := norm_deriv_le_supNorm hL hjs
      calc
        _ ≤ c₀ w * ‖∂H (n t / T)‖ + (t - n t) ^ 2 * ‖∂H (n t / T)‖ / 2 := by linarith
        _ = (c₀ w + (t - n t) ^ 2 / 2) * ‖∂H (n t / T)‖ := by ring
        _ ≤ _ := by gcongr
    -- (4.1) without its bracket.
    have hRt : R t = (K t - H (n t / T) - (1 / T * (t - n t)) • ∂H (n t / T)) -
        I • ((K t - H (n t / T)) * ((1 / T : ℝ) • Z (n t) (t - n t))) := by
      simp only [R, hround t ht, Y, Y']
      exact residual_eq _ _ _ _ _ _
    rw [hRt, ← hnt]
    exact norm_residual_le hL hT0 hjs hts hZb
  -- Third line (`integral_round`) and fourth line (`integral_residual_bound`) of the display.
  have hgcont : Continuous g := by fun_prop
  have hint : ‖∫ t in (0 : ℝ)..T, I • ((U t)† * R t * V t)‖ ≤
      ∫ t in (0 : ℝ)..T, g (t - ⌊t + 1 / 2⌋) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT0.le
    · refine Eventually.of_forall fun t ht ↦ ?_
      have ht' := Ioc_subset_Icc_self ht
      rw [norm_smul, Complex.norm_I, one_mul]
      exact (norm_conj_le (hUunit t ht') (hVunit t ht') _).trans (hRle t ht')
    · exact intervalIntegrable_round g hgcont _ _
  have hgint : ∫ t in (0 : ℝ)..T, g (t - ⌊t + 1 / 2⌋) =
      (L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T := by
    rw [integral_round g hgcont (fun τ ↦ by simp only [g, abs_neg, neg_sq]) T]
    simp only [g]
    rw [intervalIntegral.integral_const_mul, integral_residual_bound, c₁]
    field_simp
  -- Inserting the three bounds into (4.5) proves the theorem.
  calc ‖roundedEvolution H T T - evolution H T T‖
    _ ≤ ‖∫ t in (0 : ℝ)..T, I • ((U t)† * R t * V t)‖ + ‖Y T T‖ + ‖Y 0 0‖ +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := h45
    _ ≤ (L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T + c₀ w * ‖∂H 1‖ / T + c₀ w * ‖∂H 0‖ / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ :=
      add_le_add (add_le_add (add_le_add (hint.trans hgint.le) hYT) hY0) le_rfl
    _ = _ := by ring

/-- **Example 4.3.** Assuming Dieudonné (10.5.4) and (10.6.3) with the remark (10.4.6), for an
integer `T ≥ 2`, the time-dependent Hamiltonian `H(s) = s² Z` with `Z = diag(1,-1)` satisfies the
hypotheses of Theorem 4.2 with `L = 2` and `w = 2`, and its evolutions `U` and `V` satisfy
(i) `‖V(T) - U(T)‖ = 2 sin(1/(12T))`, asymptotic to `1/(6T)`, and
(ii) `‖W_T - U(T)‖ = 2 sin(1/4 - 1/(12T))`, with limit `2 sin(1/4)`. -/
theorem unit_sharp (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (T : ℕ) (hT : 2 ≤ T) :
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s ↦ (s ^ 2 : ℝ) • Matrix.diagonal ![1, -1]
    IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H 2 ∧ HasSampleWidth H T 2 ∧
      ‖roundedEvolution H T T - evolution H T T‖ = 2 * Real.sin (1 / (12 * T)) ∧
      (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * N))) ~[atTop] (fun N : ℕ ↦ 1 / (6 * N)) ∧
      ‖stepProduct H T - evolution H T T‖ = 2 * Real.sin (1 / 4 - 1 / (12 * T)) ∧
      Tendsto (fun N : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * N))) atTop
        (𝓝 (2 * Real.sin (1 / 4))) := by
  -- `UnitSharp.H` is the `H(s) = s²Z` of the statement, and `UnitSharp.E u` is `e^{-iuZ}`.
  change IsTimeDepHamiltonian UnitSharp.H ∧ _
  have hT1 : 1 ≤ T := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT1
  -- The hypotheses of Theorem 4.2 with `L = 2` and `w = 2`.
  obtain ⟨hH, hL, hwidth⟩ := UnitSharp.regularity T
  /- "The integral `∫_0^T H(t/T) dt = TZ/3`, the left-endpoint sum
  `Σ_{j=0}^{T-1} H(j/T) = (T-1)(2T-1)Z/(6T)`", which is `(T/3 - 1/2 + 1/(6T))Z`. -/
  have hintegral := UnitSharp.integral_H (T : ℝ) hTr
  have hleftSum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      ((T : ℝ) - 1) * (2 * T - 1) / (6 * T) := UnitSharp.left_sum T hT1
  have hsum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (T : ℝ) / 3 - 1 / 2 + 1 / (6 * T) := by
    rw [hleftSum]
    field_simp
    ring
  -- First line of the display: the values commute, so `U(T) = exp(-i∫_0^T H(t/T) dt) = e^{-iTZ/3}`.
  have hU : evolution UnitSharp.H T T =
      exp (-I • (∫ t in 0..(T : ℝ), UnitSharp.H (t / T))) :=
    UnitSharp.evolution_end dieudonne_10_5_4 dieudonne_10_6_3 T hT1
  have hevolution : evolution UnitSharp.H T T = UnitSharp.E ((T : ℝ) / 3) := by
    rw [hU, hintegral, smul_comm]
    rfl
  -- Second line: `W_T` is the exponential of `-i` times the left-endpoint sum.
  have hproduct := UnitSharp.sharp_stepProduct T hsum
  /- Third line: by (2.5), `V(T) = e^{-iH(1)/2} W_T e^{iH(0)/2}`, the exponential of the
  trapezoidal sum, which adds `(H(1) - H(0))/2 = Z/2` to the left-endpoint sum. -/
  have hrounded : roundedEvolution UnitSharp.H T T =
      UnitSharp.E ((T : ℝ) / 3 + 1 / (6 * T)) := by
    rw [roundedEvolution_end dieudonne_10_5_4 hH hT1, hproduct]
    have hleft : exp (-(I / 2) • UnitSharp.H 1) = UnitSharp.E (1 / 2) := by
      have hc : (1 / 2 : ℝ) • UnitSharp.H 1 = (1 / 2 : ℝ) • UnitSharp.Z := by
        simp [UnitSharp.H]
      rw [UnitSharp.E, smul_comm, ← hc]
      congr 1
      module
    have hright : exp ((I / 2) • UnitSharp.H 0) = 1 := by simp [UnitSharp.H]
    rw [hleft, hright, mul_one, ← UnitSharp.E_add]
    congr 1
    ring
  /- (i) and (ii): `‖A - B‖ = ‖AB† - 1‖` for unitaries `A` and `B` (`norm_reduction`), and
  `‖e^{iθZ} - 1‖ = 2|sin(θ/2)|` (`norm_phase`). -/
  have hcorrected :
      ‖roundedEvolution UnitSharp.H T T - evolution UnitSharp.H T T‖ =
        2 * Real.sin (1 / (12 * T)) := by
    rw [hrounded, hevolution, UnitSharp.norm_reduction, UnitSharp.norm_phase]
    have hx0 : 0 < 1 / (12 * (T : ℝ)) := by positivity
    have hxpi : 1 / (12 * (T : ℝ)) < π := by
      have := Real.pi_gt_three
      have hTreal : (2 : ℝ) ≤ T := by exact_mod_cast hT
      have hb := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 24)
        (show (24 : ℝ) ≤ 12 * T by linarith)
      linarith
    rw [show (((T : ℝ) / 3 + 1 / (6 * T)) - T / 3) / 2 =
      1 / (12 * T) by ring, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)]
  have huncorrected :
      ‖stepProduct UnitSharp.H T - evolution UnitSharp.H T T‖ =
        2 * Real.sin (1 / 4 - 1 / (12 * T)) := by
    rw [hproduct, hevolution, UnitSharp.norm_reduction, UnitSharp.norm_phase]
    have hx0 : 0 < 1 / 4 - 1 / (12 * (T : ℝ)) := by
      have hTreal : (2 : ℝ) ≤ T := by exact_mod_cast hT
      rw [sub_pos, div_lt_iff₀ (by positivity : 0 < 12 * (T : ℝ))]
      linarith [show (2 : ℝ) ≤ T by exact_mod_cast hT]
    have hxpi : 1 / 4 - 1 / (12 * (T : ℝ)) < π := by
      have hinv : 0 < 1 / (12 * (T : ℝ)) := by positivity
      linarith [Real.pi_gt_three]
    rw [show (((T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) - T / 3) / 2 =
      -(1 / 4 - 1 / (12 * T)) by ring, Real.sin_neg, abs_neg,
      abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)]
  exact ⟨hH, hL, hwidth, hcorrected, UnitSharp.asymptotic, huncorrected, UnitSharp.limit⟩

/-! ## Section 4.2: The jumps -/

/-- **Theorem 4.4.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), under the hypotheses of Theorem 4.2, with the `ℰ_w(H)` of
Appendix B, the evolutions `U` of `H(t/T)` and `V` of `H(⌊t+1/2⌋/T)` satisfy
`‖V(T) - U(T)‖ ≤ ℰ_w(H)/T`, which is equation (4.6). -/
theorem rounded_clock_bound (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤ ℰ w L H / T := by
  have hw0 : 0 ≤ w := width_nonneg hH hwidth
  -- First five lines of the display, summed over `1 ≤ j ≤ T`.
  have hjumps := sum_norm_Δ_le hT hH hL hw0 hw hwidth
  -- Sixth line: Theorem 4.2.
  have hcomparison := rounded_clock_comparison dieudonne_7_6_1
    dieudonne_10_5_4 dieudonne_10_6_3 hT hH hL hw hwidth
  calc
    _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := hcomparison
    _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        (𝒩 w * L + 2 * 𝒩' w * ‖∂H‖∞ ^ 2) / T := add_le_add_right hjumps _
    -- Last line: collect the coefficients of `ℰ_w(H)`.
    _ = ℰ w L H / T := by
      unfold ℰ
      ring

/-! ## Section 4.3: Transfer of continuous bounds -/

/-- **Example 4.5.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), let `H`, `T`, `L`, and `w` satisfy the hypotheses of
Theorem 4.2, with the `ℰ_w(H)` of Appendix B, let `P` and `Q` be orthogonal projectors commuting
with `H(0)` and `H(1)`, respectively, and let `C` be real. For a target leakage `δ > 0`, assume that
`‖(1 - Q) U(T) P‖ ≤ C/T` and `T ≥ 2(C + ℰ_w(H))/δ`, and choose an integer `k ≥ 0` with
`√2 σ_k 2^{-k} ≤ δ/(2T)`. The `T`-step product `W^{(k)}_T` of the truncation `H^{(k)}` of
Example 3.2 satisfies `‖(1 - Q) W^{(k)}_T P‖ ≤ δ`.

The statement holds for every real `C`; the paper takes `C ≥ 0`. -/
theorem unit_transfer (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) {P Q : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hPH : Commute P (H 0)) (hQH : Commute Q (H 1)) {C δ : ℝ}
    (hδ : 0 < δ) (hU : ‖(1 - Q) * evolution H T T * P‖ ≤ C / T)
    (hTδ : 2 * (C + ℰ w L H) / δ ≤ T) {k : ℕ}
    (hk : √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T)) :
    ‖(1 - Q) * stepProduct (truncation k H) T * P‖ ≤ δ := by
  let Hk : ℝ → 𝕄 := truncation k H
  let W := stepProduct H T
  let Wk := stepProduct Hk T
  let E := ℰ w L H
  let A := exp (-(I / 2) • H 1)
  let B := exp ((I / 2) • H 0)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  /- First line of the display: Proposition 2.4 with `A = e^{-iH(1)/2}` and `B = e^{iH(0)/2}`,
  which are unitary and commute with `Q` and `P`, and with `P̃ = P` and `Q̃ = Q`, so that its
  projector terms vanish. -/
  have hA : IsUnitary A := exp_neg_half_isUnitary (@hH 1 (by norm_num))
  have hB : IsUnitary B := exp_half_isUnitary (@hH 0 (by norm_num))
  have hAnorm : ‖A‖ ≤ 1 := unitary_norm_le_one hA
  have hBnorm : ‖B‖ ≤ 1 := unitary_norm_le_one hB
  have htransfer := transfer_end_phases (@hH 0 (by norm_num)) (@hH 1 (by norm_num))
    hP hQ hPH hQH (U := evolution H T T) (W := Wk)
  have hleak : ‖(1 - Q) * Wk * P‖ ≤ C / T + ‖A * Wk * B - evolution H T T‖ := by
    have hright := (abs_le.1 htransfer).2
    linarith
  -- Second line: the rounded-clock identity (2.5), and the triangle inequality.
  have hround : roundedEvolution H T T = A * W * B :=
    roundedEvolution_end dieudonne_10_5_4 hH hT
  have hsplit : ‖A * Wk * B - evolution H T T‖ ≤
      ‖Wk - W‖ + ‖roundedEvolution H T T - evolution H T T‖ := by
    calc
      _ = ‖A * (Wk - W) * B + (A * W * B - evolution H T T)‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖A * (Wk - W) * B‖ + ‖A * W * B - evolution H T T‖ :=
        norm_add_le _ _
      _ ≤ ‖Wk - W‖ + ‖A * W * B - evolution H T T‖ := by
        gcongr
        exact (norm_mul_le_of_le (norm_mul_le_of_le hAnorm le_rfl) hBnorm).trans_eq
          (by ring)
      _ = _ := by rw [hround]
  /- Third line: the bit truncation `[·]_k` is odd (Example 3.2), so `H^{(k)}` is Hermitian;
  Duhamel's bound (2.3) with Example 3.2 bounds `‖W^{(k)}_T - W_T‖` by `T √2 σ_k 2^{-k}`; and
  (4.6) bounds `‖V(T) - U(T)‖` by `ℰ_w(H)/T`. -/
  have hHk : IsTimeDepHamiltonian Hk := by
    intro s hs
    exact (Function.Odd.entrywise_and_sub_isHermitian
      (truncation_bits (d := d) k).1 (@hH s hs)).1
  have hsample : ‖Wk - W‖ ≤ T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
    calc
      _ ≤ ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - Hk ((j : ℝ) / T)‖ :=
        unit_transfer_stepProduct_error dieudonne_7_6_1 hT hH hHk
      _ ≤ ∑ _j ∈ Finset.range T, √2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (truncation_bits k).2 H hH
        exact unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T)
          (by exact_mod_cast (Finset.mem_range.1 hj).le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hclock : ‖roundedEvolution H T T - evolution H T T‖ ≤ E / T := by
    exact rounded_clock_bound dieudonne_7_6_1
      dieudonne_10_5_4 dieudonne_10_6_3 hT hH hL hw hwidth
  -- Fourth line: the choices of `T` and `k`.
  have htime : (C + E) / T ≤ δ / 2 := by
    have h := (div_le_iff₀ hδ).1 hTδ
    apply (div_le_iff₀ hTr).2
    linarith
  have hbits : T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) ≤ δ / 2 := by
    have h := mul_le_mul_of_nonneg_left hk hTr.le
    convert h using 1
    all_goals field_simp
  change ‖(1 - Q) * Wk * P‖ ≤ δ
  calc
    _ ≤ C / T + ‖A * Wk * B - evolution H T T‖ := hleak
    _ ≤ C / T + ‖Wk - W‖ +
        ‖roundedEvolution H T T - evolution H T T‖ := by linarith [hsplit]
    _ ≤ (C + E) / T + T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) := by
      calc
        _ ≤ C / T + T * (√2 * sparsity k H * ((2 : ℝ) ^ k)⁻¹) + E / T := by
          gcongr
        _ = _ := by ring
    _ ≤ δ / 2 + δ / 2 := add_le_add htime hbits
    _ = δ := by ring

/-! ## Section 4.4: Products of given unitaries -/

/-- **Theorem 4.6.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), let `T ≥ 1` be an integer and let `H` be a twice continuously differentiable
time-dependent Hamiltonian with sample width `w < 2π` and every `H(s)` with
eigenvalue differences of modulus at most `w`, and let `W = e^{-iH}`. Then the evolution `U` of
`H(t/T)` and `V(T) = e^{-iH(1)/2} W((T-1)/T) ⋯ W(0) e^{iH(0)/2}` satisfy
`‖V(T) - U(T)‖ ≤ ℰ̃_w(W)/T` for the constant `ℰ̃_w(W)` of Appendix B, which is equation (4.8).

The `C²` hypothesis supplies the Lipschitz constant `‖H''‖∞`; no separate Lipschitz
constant is assumed. -/
theorem unitary_products (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π)
    (hSampleWidth : HasSampleWidth H T w) (hC2 : IsC2Family H) (hwidth : HasWidth H w) :
    let W := fun s ↦ exp (-I • H s)
    ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) - evolution H T T‖ ≤
      ℰtilde w W / T := by
  let W : ℝ → 𝕄 := fun s ↦ exp (-I • H s)
  change ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) -
    evolution H T T‖ ≤ ℰtilde w W / T
  -- "By (2.5), `V(T)` is the evolution of `H(⌊t+1/2⌋/T)` at `T`."
  have hendpoint := roundedEvolution_end dieudonne_10_5_4 hH hT
  change roundedEvolution H T T =
    exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) at hendpoint
  rw [← hendpoint]
  -- The constants `κ`, `c₀`, `c₁`, `𝒩(w)`, `𝒩'(w)`, and `𝒩(w) - 𝒩(0)` are nonnegative.
  have hw0 : 0 ≤ w := width_nonneg hH hSampleWidth
  have hκ : 0 ≤ κ w := κ_nonneg_of_width hw0 hw
  have hc0 := c₀_nonneg_of_width hw0 hw
  have hc1 : 0 ≤ c₁ w := by unfold c₁; positivity
  have hN := 𝒩_nonneg_of_width hw0 hw
  have hN' : 0 ≤ 𝒩' w := deriv_𝒩_nonneg hw0 hw
  have htail : 0 ≤ 𝒩 w - 𝒩 0 := sub_nonneg.mpr (𝒩_zero_le hw0 hw)
  /- "As `W` is `C²` and satisfies (4.7) with `a` the least eigenvalue of `H`, `H` is the logarithm
  of Lemma A.2, so `‖H'‖ ≤ κ ‖W'‖` and `‖H''‖ ≤ κ ‖W''‖ + ‖W'‖²/cos²(w/4)`", and the same for the
  suprema over `[0,1]`. -/
  have hlog := log_derivative_bounds hH hw0 hw hC2 hwidth
  have hW1 : ContinuousOn (∂W) (Icc (0 : ℝ) 1) :=
    hC2.exp.deriv_contDiffOn.continuousOn
  have hW2 : ContinuousOn (∂∂W) (Icc (0 : ℝ) 1) := hC2.exp.continuousOn_deriv2
  have hH0 := supNorm_nonneg_of_continuousOn hC2.deriv_contDiffOn.continuousOn
  have hW0 := supNorm_nonneg_of_continuousOn hW1
  have hfirst : ‖∂H‖∞ ≤ κ w * ‖∂W‖∞ := by
    apply supNorm_le_of_forall
    intro s hs
    exact (hlog s hs).1.trans
      (mul_le_mul_of_nonneg_left (norm_le_supNorm_of_continuousOn hW1 hs) hκ)
  have hsecond : ‖∂∂H‖∞ ≤ κ w * ‖∂∂W‖∞ + ‖∂W‖∞ ^ 2 / Real.cos (w / 4) ^ 2 := by
    apply supNorm_le_of_forall
    intro s hs
    exact (hlog s hs).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (norm_le_supNorm_of_continuousOn hW2 hs) hκ)
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_le_supNorm_of_continuousOn hW1 hs) 2)
        (sq_nonneg _)))
  have hend : ‖∂H 0‖ + ‖∂H 1‖ ≤ κ w * (‖∂W 0‖ + ‖∂W 1‖) := by
    calc
      _ ≤ κ w * ‖∂W 0‖ + κ w * ‖∂W 1‖ :=
        add_le_add (hlog 0 (by norm_num)).1 (hlog 1 (by norm_num)).1
      _ = _ := by ring
  -- First two lines of the display, summed over `1 ≤ j ≤ T`: Lemma A.3(ii) for `Ω = H`.
  have hjump := jump_sum_le hT hH hw0 hw hwidth hC2
  -- Third line: Theorem 4.2 with `L = ‖H''‖∞`.
  have hclock := rounded_clock_comparison dieudonne_7_6_1 dieudonne_10_5_4 dieudonne_10_6_3 hT hH
    hC2.hasLipschitzDerivative hw hSampleWidth
  -- Fourth and fifth lines: the sum of the second line over `1 ≤ j ≤ T`.
  have hcombined : ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + (1 / 24 + 𝒩 w) * ‖∂∂H‖∞ +
        (c₁ w + (𝒩 w - 𝒩 0)) * ‖∂H‖∞ ^ 2 +
        2 * 𝒩' w * ‖∂W‖∞ * ‖∂H‖∞) / T := by
    calc
      _ ≤ (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + ‖∂∂H‖∞ / 24 +
          c₁ w * ‖∂H‖∞ ^ 2) / T +
          (𝒩 w * ‖∂∂H‖∞ + 2 * 𝒩' w * ‖∂W‖∞ * ‖∂H‖∞ +
            (𝒩 w - 𝒩 0) * ‖∂H‖∞ ^ 2) / T :=
        hclock.trans (add_le_add (le_refl _) hjump)
      _ = _ := by ring
  -- Last line: insert the two bounds of Lemma A.2 and collect the coefficient `c₂`.
  apply hcombined.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ c₀ w * (κ w * (‖∂W 0‖ + ‖∂W 1‖)) +
        (1 / 24 + 𝒩 w) * (κ w * ‖∂∂W‖∞ + ‖∂W‖∞ ^ 2 / Real.cos (w / 4) ^ 2) +
        (c₁ w + (𝒩 w - 𝒩 0)) * (κ w * ‖∂W‖∞) ^ 2 +
        2 * 𝒩' w * ‖∂W‖∞ * (κ w * ‖∂W‖∞) :=
      add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hend hc0)
          (mul_le_mul_of_nonneg_left hsecond (by positivity)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hfirst 2) (add_nonneg hc1 htail)))
        (mul_le_mul_of_nonneg_left hfirst (by positivity))
    _ = ℰtilde w W := by unfold ℰtilde c₂; ring

/-- **Theorem 4.7.** Assuming Dieudonné (7.6.1), (10.5.4), and (10.6.3) with
the remark (10.4.6), let `T ≥ 1` be an integer, let a
twice continuously differentiable unitary family `W` have a band of eigenvalues
`{e^{-iθ} : α(s) < θ < β(s)}` with `α < β < α + 2π`, eigenphase gap continuous in `s`, and endpoint
projectors `P` and `Q`, and let `ϑ` be the least eigenphase gap over `s ∈ [0,1]`. Let `U` be the
evolution of `H(t/T)` for the Hermitian `H(s)` with `e^{-iH(s)} = W(s)` and spectrum in
`(α(s), α(s) + 2π)`. Then, with `w = 2π - ϑ` and the `ℰ̃_w(W)` of Appendix B,
`‖(1 - Q) W((T-1)/T) ⋯ W(0) P‖ ≤ ‖(1 - Q) U(T) P‖ + ℰ̃_w(W)/T`.

The statement does not assume a constant number of eigenvalues in the band. -/
theorem walk_leakage (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_10_5_4 : Dieudonne_10_5_4) (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {W : ℝ → 𝕄} (hC2 : IsC2Family W) {α β : ℝ → ℝ}
    (hband : IsArcBandFamily W α β)
    (hgap : IsContinuousFamily (fun s ↦ eigenphaseGap (W s) (α s) (β s)))
    {H : ℝ → 𝕄} (hHlog : IsLogarithm W α H) :
    let ϑ := sInf ((fun s ↦ eigenphaseGap (W s) (α s) (β s)) '' Icc 0 1)
    let w := 2 * π - ϑ
    let P := arcBandProjector (W 0) (α 0) (β 0)
    let Q := arcBandProjector (W 1) (α 1) (β 1)
    ‖(1 - Q) * sampleProduct W T * P‖ ≤
      ‖(1 - Q) * evolution H T T * P‖ + ℰtilde w W / T := by
  intro ϑ w P Q
  have hH : IsTimeDepHamiltonian H := hHlog.isHermitian
  have hexp : ∀ s ∈ Icc (0 : ℝ) 1, exp (-I • H s) = W s := hHlog.exp_eq
  have hspec : ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Ioo (α s) (α s + 2 * π)) :=
    hHlog.spectrum_subset
  /- The least eigenphase gap `ϑ` over `s ∈ [0,1]` is attained and positive, as the gap is
  continuous, so `w = 2π - ϑ < 2π`. -/
  have hgapmin := WalkLeakage.gap_minimum hband hgap
  have hϑ : 0 < ϑ := hgapmin.1
  have hϑ_le : ∀ s ∈ Icc (0 : ℝ) 1, ϑ ≤ eigenphaseGap (W s) (α s) (β s) := hgapmin.2
  have hw : w < 2 * π := by
    change 2 * π - ϑ < 2 * π
    linarith
  /- "As `α` and `W` are continuous, `H = α + π + i Log(e^{i(α+π)} W)` is continuous": that
  formula gives a continuous logarithm `G` with spectrum in `(α, α + 2π)`, and `H = G`, as
  `θ ↦ e^{-iθ}` is injective for `θ ∈ (α(s), α(s) + 2π)`. -/
  obtain ⟨G, hGlog, hGcont⟩ :=
    WalkLeakage.exists_continuous_logarithm hband hC2.continuousOn
  have hHG : EqOn H G (Icc 0 1) := WalkLeakage.logarithms_eqOn hHlog hGlog
  have hHcont : IsContinuousFamily H := ContinuousOn.congr hGcont hHG
  -- "... and therefore so is its least eigenvalue `ℓ`".
  let ℓ := fun s ↦ sInf (spectrum ℝ (H s))
  have hℓ : IsContinuousFamily ℓ :=
    continuousOn_sInf_spectrum hH hHcont
  /- "An eigenvalue `θ` of `H(s)` lies in `(α(s), β(s))` exactly when `e^{-iθ}` lies in the band,
  and otherwise in `(β(s), α(s) + 2π)`. The band is nonempty and proper, so `ℓ(s)` lies in
  `(α(s), β(s))` and the greatest eigenvalue `φ` of `H(s)` in `(β(s), α(s) + 2π)`, and
  Definition 2.5(ii) gives `ϑ ≤ 2π - (φ - ℓ(s))`. Hence `H(s)` has spectrum in
  `[ℓ(s), ℓ(s) + w]`." -/
  have hspectrum : ∀ s ∈ Icc (0 : ℝ) 1,
      IsLeast (spectrum ℝ (H s)) (ℓ s) ∧ HasRealSpectrumIn (H s) (Icc (ℓ s) (ℓ s + w)) := by
    intro s hs
    apply WalkLeakage.spectrum_in_width (hband.isArcBand hs)
    · rw [← hexp s hs]
      exact spectrum_exp (@hH s hs)
    · exact hspec s hs
    · exact hϑ_le s hs
  -- The interval `[ℓ(0), ℓ(0) + w]` contains `ℓ(0)`, so `0 ≤ w`.
  have hw0 : 0 ≤ w := by
    have hs : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h := (hspectrum 0 hs).2 (hspectrum 0 hs).1.1
    change ℓ 0 ≤ ℓ 0 ∧ ℓ 0 ≤ ℓ 0 + w at h
    linarith [h.2]
  -- So `W` satisfies (4.7) with `a = ℓ`.
  have harc : HasSpectrumInPhaseInterval W ℓ w := by
    intro s hs z hz
    rw [← hexp s hs, spectrum_exp (@hH s hs)] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    exact ⟨θ, (hspectrum s hs).2 hθ, rfl⟩
  have hW : IsUnitaryFamily W 0 1 := by
    intro s hs
    exact (hband.isArcBand hs).isUnitary
  -- "... and `H` is `C²` by Lemma A.2": `H` is the logarithm of Lemma A.2, by its uniqueness.
  obtain ⟨K, -, -, hKunique, hKC2, -⟩ := walk_log hw0 hw hℓ hW harc hC2
  have hHK : EqOn H K (Icc 0 1) := by
    intro s hs
    exact hKunique s hs (H s) (@hH s hs) (hspectrum s hs).2 (hexp s hs)
  have hHC2 : IsC2Family H := ContDiffOn.congr hKC2 hHK
  /- The hypotheses of Theorem 4.6: every `H(s)` has eigenvalue differences of modulus at most
  `w`, in particular the samples. -/
  have hHwidth : HasWidth H w := by
    intro s hs x hx y hy
    have hx_bounds := (hspectrum s hs).2 hx
    have hy_bounds := (hspectrum s hs).2 hy
    simpa using abs_sub_le_of_le_of_le hx_bounds.1 hx_bounds.2 hy_bounds.1 hy_bounds.2
  have hHsample : HasSampleWidth H T w := by
    intro j hj
    have hs : (j : ℝ) / (T : ℝ) ∈ Icc (0 : ℝ) 1 :=
      unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T) (by exact_mod_cast hj)
    exact hHwidth _ hs
  /- "So Theorem 4.6 applies." It is stated for `e^{-iH}`, which agrees with `W` for `s ∈ [0,1]`,
  so the two have the same samples and the same `ℰ̃_w`. -/
  have hHexp : EqOn (fun s ↦ exp (-I • H s)) W (Icc 0 1) :=
    fun s hs ↦ hexp s hs
  have hproducts := WalkLeakage.sampleProduct_eq (T := T) hHexp
  have hℰ := WalkLeakage.ℰtilde_congr hHexp w
  have hcomparison :
      ‖exp (-(I / 2) • H 1) * sampleProduct W T * exp ((I / 2) • H 0) -
        evolution H T T‖ ≤ ℰtilde w W / T := by
    have h := unitary_products dieudonne_7_6_1 dieudonne_10_5_4 dieudonne_10_6_3
      hT hH hw hHsample hHC2 hHwidth
    dsimp only at h
    rw [hproducts, hℰ] at h
    exact h
  /- "As `W(s) = e^{-iH(s)}`, `P` and `Q` are the spectral projectors of `H(0)` and `H(1)` for
  their eigenvalues in `(α(0), β(0))` and `(α(1), β(1))` ..." -/
  have hprojectors : ∀ s ∈ Icc (0 : ℝ) 1,
      arcBandProjector (W s) (α s) (β s) = bandProjector (H s) (α s) (β s) := by
    intro s hs
    rw [← hexp s hs]
    apply walk_arcBandProjector_exp (@hH s hs) (hband.isArcBand hs).lt_add_two_pi
    intro j
    exact hspec s hs ((show (H s).IsHermitian from @hH s hs).eigenvalues_mem_spectrum_real j)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hPband : P = bandProjector (H 0) (α 0) (β 0) := hprojectors 0 h0
  have hQband : Q = bandProjector (H 1) (α 1) (β 1) := hprojectors 1 h1
  have hP : IsOrthogonalProjector P := spectralProjector_isOrthogonal (W 0) (arc (α 0) (β 0))
  have hQ : IsOrthogonalProjector Q := spectralProjector_isOrthogonal (W 1) (arc (α 1) (β 1))
  -- "... and they commute with `e^{iH(0)/2}` and `e^{-iH(1)/2}`."
  have hBP : Commute (exp ((I / 2) • H 0)) P := by
    rw [hPband]
    exact walk_phase_commute_bandProjector (@hH 0 h0) _ _ _
  have hAQ : Commute (exp (-(I / 2) • H 1)) Q := by
    rw [hQband]
    exact walk_phase_commute_bandProjector (@hH 1 h1) _ _ _
  /- Proposition 2.4 with these phases as `B` and `A`, with `P̃ = P` and `Q̃ = Q`, so that its
  projector terms vanish, gives `‖(1 - Q) W_T P‖ ≤ ‖(1 - Q) U(T) P‖ + ‖V(T) - U(T)‖`, and (4.8)
  bounds the last term. -/
  have htransfer := transfer (Q := Q) (U := evolution H T T) (W := sampleProduct W T)
    hP hP hQ (exp_neg_half_isUnitary (@hH 1 h1)) (exp_half_isUnitary (@hH 0 h0)) hAQ hBP
  simp only [sub_self, norm_zero, add_zero, mul_zero] at htransfer
  have hupper := (abs_le.mp htransfer).2
  exact sub_le_iff_le_add'.mp (hupper.trans hcomparison)

end RoundedClocks
