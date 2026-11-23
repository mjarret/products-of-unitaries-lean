/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.PiecewiseEvolution
public import RoundedClocks.Definitions
public import RoundedClocks.Citations
public import RoundedClocks.Preliminaries.ComparisonIdentity
public import RoundedClocks.Preliminaries.EvolutionUnitarity
public import RoundedClocks.Preliminaries.RegulatedIntegrability

/-!
# Section 2: preliminaries

The comparison of evolutions (Theorem 2.2), the rounded-clock identity (2.5), and the transfer of
leakage bounds (Proposition 2.4).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter MeasureTheory
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 2 (existence of evolutions). Assuming Dieudonné (10.5.4) and (10.6.3) with the remark
(10.4.6), a regulated Hermitian family `G(t)` with `t ∈ [a,b]` generates an evolution. -/
theorem generates_exists (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    {G : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b) (hreg : IsRegulated G a b)
    (hG : IsHermitianFamily G a b) : ∃ V, Generates G V a b := by
  rcases eq_or_lt_of_le hab with hzero | hpos
  · subst b
    refine ⟨fun _ ↦ 1, continuousOn_const, rfl, ?_, {a}, countable_singleton a, ?_⟩
    · intro t ht
      simp [IsUnitary]
    · intro t ht hn
      exact (hn (le_antisymm ht.2 ht.1)).elim
  · -- The linear coefficient and zero forcing term are regulated.
    let A : ℝ → 𝕄 := fun t ↦ -I • G t
    let B : ℝ → 𝕄 := fun _ ↦ 0
    have hA : IsRegulated A a b := by
      constructor
      · intro t ht
        obtain ⟨L, hL⟩ := hreg.1 t ht
        exact ⟨-I • L, hL.const_smul (-I)⟩
      · intro t ht
        obtain ⟨L, hL⟩ := hreg.2 t ht
        exact ⟨-I • L, hL.const_smul (-I)⟩
    have hB : IsRegulated B a b := by
      constructor <;> intro t _ <;> exact ⟨0, tendsto_const_nhds⟩
    -- The cited global solution has initial value 1 at the endpoint a.
    obtain ⟨V, hV, -⟩ :=
      dieudonne_10_6_3 d A B 1 a b a hpos ⟨le_rfl, hab⟩ hA hB
    -- Hermitian G gives V†V = 1 by the cited uniqueness theorem.
    exact ⟨V, generates_of_cited_linear_solution dieudonne_10_5_4 hab hG hV⟩

/-- The evolution `evolutionOf G T` that a regulated Hermitian family `G(t)` with `t ∈ [0,T]`
generates (`generates_exists` with `[a,b] = [0,T]`). -/
theorem generates_evolutionOf (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    {G : ℝ → 𝕄} {T : ℝ} (hT : 0 ≤ T) (hreg : IsRegulated G 0 T)
    (hG : IsHermitianFamily G 0 T) : Generates G (evolutionOf G T) 0 T := by
  have hexists := generates_exists dieudonne_10_5_4 dieudonne_10_6_3 hT hreg hG
  rw [evolutionOf, dif_pos hexists]
  exact Classical.choose_spec hexists

/-- Section 2 (uniqueness of evolutions). Assuming Dieudonné (10.5.4), a regulated family `G(t)`
with `t ∈ [a,b]` generates at most one evolution. -/
theorem generates_unique (dieudonne_10_5_4 : Dieudonne_10_5_4) {G V V' : ℝ → 𝕄}
    {a b : ℝ} (hreg : IsRegulated G a b) (hV : Generates G V a b)
    (hV' : Generates G V' a b) : EqOn V V' (Icc a b) := by
  by_cases hab : a ≤ b
  · let A : ℝ → 𝕄 := fun t ↦ (-I) • G t
    -- The linear coefficient and the zero forcing term are regulated.
    have hA : IsRegulated A a b := by
      constructor
      · intro t ht
        obtain ⟨L, hL⟩ := hreg.1 t ht
        exact ⟨(-I) • L, hL.const_smul (-I)⟩
      · intro t ht
        obtain ⟨L, hL⟩ := hreg.2 t ht
        exact ⟨(-I) • L, hL.const_smul (-I)⟩
    have hB : IsRegulated (fun _ : ℝ ↦ (0 : 𝕄)) a b := by
      constructor
      · intro t ht
        exact ⟨0, tendsto_const_nhds⟩
      · intro t ht
        exact ⟨0, tendsto_const_nhds⟩
    -- Each generated evolution solves the cited linear equation.
    have hsolve : ∀ W : ℝ → 𝕄, Generates G W a b →
        SolvesLinearMatrixODE A (fun _ ↦ 0) 1 W a a b := by
      intro W hW
      obtain ⟨hc, h0, _hu, S, hS, hd⟩ := hW
      refine ⟨hc, h0, S, hS, ?_⟩
      intro t ht hn
      simpa only [A, add_zero, Matrix.smul_mul] using hd t ht hn
    -- Dieudonné gives uniqueness for the common initial value.
    exact dieudonne_10_5_4 d A (fun _ ↦ 0) 1 V V' a b hab hA hB
      (hsolve V hV) (hsolve V' hV')
  · intro t ht
    exact (hab (ht.1.trans ht.2)).elim

/-- **Theorem 2.2.** Assuming Dieudonné (7.6.1) and Section 8.7, let regulated Hermitian families
`K(t)` and `G(t)` with `t ∈ [a,b]` generate `U` and `V`, respectively, let `m ≥ 0` be an integer,
and let `a = p₀ ≤ p₁ ≤ ⋯ ≤ pₘ₊₁ = b`. For `0 ≤ j ≤ m`, let the pieces `Yⱼ(t)` for
`t ∈ [pⱼ,pⱼ₊₁]` be continuous and matrix-valued, with a derivative that, for all but countably many
`t`, exists and agrees with a regulated function. Let `R(t)` be the residual
`R = K - G - Yⱼ' - i(K Yⱼ - Yⱼ G)` wherever `pⱼ < t < pⱼ₊₁` and `Yⱼ'(t)` exists, with arbitrary
values at the remaining countably many `t`. Let `Δⱼ = Yⱼ(pⱼ) - Yⱼ₋₁(pⱼ)` for `1 ≤ j ≤ m`. Then
`U(b)† V(b) - 1 = ∫_a^b i U† R V dt + i U(b)† Y_m(b) V(b) - i Y_0(a)
- i Σ_{j=1}^m U(p_j)† Δ_j V(p_j)`. -/
theorem comparison (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7) {a b : ℝ}
    [NeZero d] (K G U V : ℝ → 𝕄) (hK : IsRegulated K a b)
    (hKh : IsHermitianFamily K a b)
    (hG : IsRegulated G a b) (hGh : IsHermitianFamily G a b) (hU : Generates K U a b)
    (hV : Generates G V a b) (m : ℕ) (p : ℕ → ℝ)
    (hp : ∀ j ≤ m, p j ≤ p (j + 1)) (ha : p 0 = a) (hb : p (m + 1) = b)
    (Y : ℕ → ℝ → 𝕄) (S : ℕ → Set ℝ) (hS : ∀ j ≤ m, (S j).Countable)
    (hYc : ∀ j ≤ m, ContinuousOn (Y j) (Icc (p j) (p (j + 1))))
    (Y' : ℕ → ℝ → 𝕄) (hY' : ∀ j ≤ m, IsRegulated (Y' j) (p j) (p (j + 1)))
    (hYd : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S j →
      HasDerivAt (Y j) (Y' j t) t)
    (R : ℝ → 𝕄)
    (hR : ∀ j ≤ m, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ S j →
      R t = K t - G t - Y' j t - I • (K t * Y j t - Y j t * G t)) :
    (U b)† * V b - 1 = (∫ t in a..b, I • ((U t)† * R t * V t)) +
      I • ((U b)† * Y m b * V b) - I • Y 0 a -
      I • ∑ j ∈ Finset.Icc 1 m, (U (p j))† * (Y j (p j) - Y (j - 1) (p j)) * V (p j) := by
  classical
  let P := fun t ↦ (U t)† * V t
  let Q := fun j t ↦ (U t)† * Y j t * V t
  let A := fun t ↦ I • ((U t)† * (K t - G t) * V t)
  let B := fun j t ↦ (U t)† *
    (Y' j t + I • (K t * Y j t - Y j t * G t)) * V t
  let C := fun t ↦ I • ((U t)† * R t * V t)
  have hleft (j : ℕ) (hj : j ≤ m) : a ≤ p j :=
    ha ▸ comparison_partition_mono hp (Nat.zero_le j) (by omega)
  have hright (j : ℕ) (hj : j ≤ m) : p (j + 1) ≤ b :=
    hb ▸ comparison_partition_mono hp (Nat.add_le_add_right hj 1) le_rfl
  have hcell (j : ℕ) (hj : j ≤ m) : Icc (p j) (p (j + 1)) ⊆ Icc a b :=
    Icc_subset_Icc (hleft j hj) (hright j hj)
  -- Dieudonné gives the two primitives separately on each closed cell.
  have hprim (j : ℕ) (hj : j ≤ m) :
      IsRegulated A (p j) (p (j + 1)) ∧ IsRegulated (B j) (p j) (p (j + 1)) ∧
      (P (p (j + 1)) - P (p j) = ∫ t in p j..p (j + 1), A t) ∧
      (Q j (p (j + 1)) - Q j (p j) = ∫ t in p j..p (j + 1), B j t) := by
    exact comparison_piece_primitives dieudonne_section_8_7 K G U V (Y j) (Y' j)
      (p j) (p (j + 1)) (hp j hj)
      (comparison_regulated_restrict hK (hleft j hj) (hright j hj))
      (comparison_regulated_restrict hG (hleft j hj) (hright j hj)) (hY' j hj)
      (fun t ht ↦ hKh t (hcell j hj ht)) (hU.1.mono (hcell j hj))
      (hV.1.mono (hcell j hj)) (hYc j hj)
      (comparison_derivative_restrict hU.2.2.2 (hcell j hj))
      (comparison_derivative_restrict hV.2.2.2 (hcell j hj))
      (comparison_correction_derivative (hS j hj) (hYd j hj))
  -- The residual agrees almost everywhere with A - iB, including degenerate cells.
  have hres (j : ℕ) (hj : j ≤ m) :
      IntervalIntegrable C MeasureTheory.volume (p j) (p (j + 1)) ∧
      (∫ t in p j..p (j + 1), A t) =
        (∫ t in p j..p (j + 1), C t) + I • (∫ t in p j..p (j + 1), B j t) :=
    comparison_cited_integrate_residual dieudonne_7_6_1
      (hp j hj) (hprim j hj).1 (hprim j hj).2.1
      (comparison_residual_ae K G U V (Y j) (Y' j) R (hp j hj) (hS j hj) (hR j hj))
  have hsum : (∑ j ∈ Finset.range (m + 1), ∫ t in p j..p (j + 1), C t) =
      ∫ t in a..b, C t := by
    simpa only [ha, hb] using intervalIntegral.sum_integral_adjacent_intervals (n := m + 1)
      (fun j hj ↦ (hres j (by omega)).1)
  have hjump : (∑ j ∈ Finset.range m,
      (Q (j + 1) (p (j + 1)) - Q j (p (j + 1)))) =
      ∑ j ∈ Finset.Icc 1 m, (U (p j))† *
        (Y j (p j) - Y (j - 1) (p j)) * V (p j) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    simp only [Nat.one_add, Nat.succ_sub_one]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Q, mul_sub, sub_mul]
  calc
    (U b)† * V b - 1 = ∑ j ∈ Finset.range (m + 1),
        ∫ t in p j..p (j + 1), A t := by
      have ht := comparison_telescope P p m
      have he : (∑ j ∈ Finset.range (m + 1),
          (P (p (j + 1)) - P (p j))) =
          ∑ j ∈ Finset.range (m + 1), ∫ t in p j..p (j + 1), A t :=
        Finset.sum_congr rfl fun j hj ↦ (hprim j (by
          have := Finset.mem_range.mp hj; omega)).2.2.1
      rw [ht] at he
      simpa only [P, ha, hb, hU.2.1, hV.2.1, star_one, one_mul] using he
    _ = ∑ j ∈ Finset.range (m + 1),
        ((∫ t in p j..p (j + 1), C t) +
          I • (∫ t in p j..p (j + 1), B j t)) := by
      exact Finset.sum_congr rfl fun j hj ↦ (hres j (by
        have := Finset.mem_range.mp hj; omega)).2
    _ = (∫ t in a..b, C t) + I • ∑ j ∈ Finset.range (m + 1),
        (Q j (p (j + 1)) - Q j (p j)) := by
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hsum]
      congr 1
      congr 1
      exact Finset.sum_congr rfl fun j hj ↦ (hprim j (by
        have := Finset.mem_range.mp hj; omega)).2.2.2.symm
    _ = _ := by
      rw [comparison_boundaries Q p m, hjump]
      simp only [Q, C, ha, hb, hU.2.1, hV.2.1, star_one, one_mul, mul_one,
        smul_sub]
      abel

/-- **Equation (2.3)** (Duhamel's bound). Assuming Dieudonné (7.6.1) and Section 8.7, if regulated
Hermitian families `K(t)` and `G(t)` with `t ∈ [a,b]` generate `U` and `V`, then
`‖V(b) - U(b)‖ ≤ ∫_a^b ‖K - G‖ dt`. -/
theorem duhamel (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7) {K G U V : ℝ → 𝕄}
    {a b : ℝ} (hab : a ≤ b) (hK : IsRegulated K a b) (hKh : IsHermitianFamily K a b)
    (hG : IsRegulated G a b) (hGh : IsHermitianFamily G a b) (hU : Generates K U a b)
    (hV : Generates G V a b) :
    ‖V b - U b‖ ≤ ∫ t in a..b, ‖K t - G t‖ := by
  classical
  by_cases hd : d = 0
  · subst d
    -- Every matrix on Fin 0 is zero, so both sides vanish.
    have hzero (A : Matrix (Fin 0) (Fin 0) ℂ) : A = 0 := Subsingleton.elim _ _
    simp only [hzero (V b - U b), hzero (K _ - G _), norm_zero,
      intervalIntegral.integral_zero, le_refl]
  letI : NeZero d := ⟨hd⟩
  -- Use the single interval partition with no correction.
  let p : ℕ → ℝ := fun j ↦ if j = 0 then a else b
  -- The partition is increasing because a ≤ b.
  have hp : ∀ j ≤ 0, p j ≤ p (j + 1) := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa [p] using hab
  -- Theorem 2.2 with Y = 0 and R = K - G gives the integral identity.
  have hidentity :
      (U b)† * V b - 1 = ∫ t in a..b, I • ((U t)† * (K t - G t) * V t) := by
    have h := RoundedClocks.comparison dieudonne_7_6_1 dieudonne_section_8_7 K G U V
      hK hKh hG hGh hU hV 0 p hp
      (by simp [p]) (by simp [p]) (fun _ _ ↦ 0) (fun _ ↦ ∅)
      (fun _ _ ↦ countable_empty)
      (fun _ _ ↦ continuousOn_const) (fun _ _ ↦ 0)
      (fun _ _ ↦ by
        constructor <;> intro t ht <;> exact ⟨0, tendsto_const_nhds⟩)
      (fun _ _ t _ _ ↦ hasDerivAt_const t 0) (fun t ↦ K t - G t)
      (fun _ _ _ _ _ ↦ by simp)
    simpa only [smul_zero, mul_zero, zero_mul, add_zero, sub_zero,
      Finset.sum_const_zero] using h
  -- Convert the evolution identities into unitary group membership.
  have mem (W : 𝕄) := (Matrix.mem_unitaryGroup_iff' (A := W)).mpr
  -- Unitary invariance and the integral norm bound give Equation (2.3).
  calc
    ‖V b - U b‖ = ‖(U b)† * (V b - U b)‖ := by
      rw [CStarRing.norm_mem_unitary_mul _
        (Unitary.star_mem (mem (U b) (hU.2.2.1 b ⟨hab, le_rfl⟩)))]
    _ = ‖(U b)† * V b - 1‖ := by
      rw [mul_sub, hU.2.2.1 b ⟨hab, le_rfl⟩]
    _ = ‖∫ t in a..b, I • ((U t)† * (K t - G t) * V t)‖ :=
      congrArg norm hidentity
    _ ≤ ∫ t in a..b, ‖I • ((U t)† * (K t - G t) * V t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, ‖K t - G t‖ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      change ‖I • ((U t)† * (K t - G t) * V t)‖ = ‖K t - G t‖
      rw [norm_smul, Complex.norm_I, one_mul,
        CStarRing.norm_mul_mem_unitary _ (mem (V t) (hV.2.2.1 t ht)),
        CStarRing.norm_mem_unitary_mul _
          (Unitary.star_mem (mem (U t) (hU.2.2.1 t ht)))]

/-- **Equation (2.4)** (the evolution of a piecewise-constant family). Let
`t_0 ≤ t_1 ≤ ⋯ ≤ t_n`, and let `G(t) = G_j` for `t_j < t < t_{j+1}` with Hermitian `G_j`. Then
`G` generates an evolution `V` with
`V(t_n) = e^{-i(t_n - t_{n-1})G_{n-1}} ⋯ e^{-i(t_1 - t_0)G_0}`. -/
theorem piecewise_product {n : ℕ} {t : ℕ → ℝ} (ht : ∀ j < n, t j ≤ t (j + 1)) {G : ℝ → 𝕄}
    {A : ℕ → 𝕄} (hA : ∀ j < n, IsHermitian (A j))
    (hG : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = A j) :
    ∃ V, Generates G V (t 0) (t n) ∧
      V (t n) = ((List.range n).reverse.map fun j ↦
        exp ((-I * (t (j + 1) - t j : ℝ)) • A j)).prod := by
  exact exists_piecewise_evolution_list ht hA hG

/-- **Equation (2.5)** (the rounded-clock identity). Assuming Dieudonné (10.5.4), for an integer
`T ≥ 1`, the evolution of `H(⌊t+1/2⌋/T)` ends at `e^{-iH(1)/2} W_T e^{iH(0)/2}`, where `W_T` is
the `T`-step product. -/
theorem roundedEvolution_end (dieudonne_10_5_4 : Dieudonne_10_5_4) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {T : ℕ} (hT : 1 ≤ T) :
    roundedEvolution H T T = exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) := by
  let G : ℝ → 𝕄 := fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)
  let A : ℕ → 𝕄 := fun j ↦ H (j / T)
  let σ := roundedClockDuration T
  let t := switchTime σ
  obtain ⟨htT, hpiece⟩ := rounded_clock_partition H T hT
  have hσ : ∀ j, 0 ≤ σ j := by
    intro j
    simp only [σ, roundedClockDuration]
    split_ifs <;> norm_num
  have ht : ∀ j < T + 1, t j ≤ t (j + 1) := by
    intro j _
    change switchTime σ j ≤ switchTime σ j + σ j
    exact le_add_of_nonneg_right (hσ j)
  have hA : ∀ j < T + 1, IsHermitian (A j) := by
    intro j hj
    apply hH (j / T)
    have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
    constructor
    · positivity
    · exact (div_le_one hT0).mpr (by exact_mod_cast (show j ≤ T by omega))
  have hG : ∀ j < T + 1, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = A j := by
    simpa only [G, A, t, σ] using hpiece
  obtain ⟨V, hV, hVT⟩ := exists_piecewise_evolution ht hA hG
  have ht0 : t 0 = 0 := by simp [t, switchTime]
  have htend : t (T + 1) = T := by simpa only [t, σ] using htT
  have hreg : IsRegulated G 0 T := by
    have := piecewise_regulated G t A (T + 1) hG
    simpa only [ht0, htend] using this
  have hV' : Generates G V 0 T := by simpa only [ht0, htend] using hV
  have hexists : ∃ W, Generates G W 0 T := ⟨V, hV'⟩
  have hevolution : Generates G (evolutionOf G T) 0 T := by
    rw [evolutionOf, dif_pos hexists]
    exact Classical.choose_spec hexists
  have hend : evolutionOf G T T = V T := by
    exact generates_unique dieudonne_10_5_4 hreg hevolution hV' ⟨by positivity, le_rfl⟩
  have hproduct : V T = durationProduct σ A (T + 1) := by
    calc
      V T = recursiveProduct t A (T + 1) := by simpa only [htend] using hVT
      _ = durationProduct σ A (T + 1) := recursiveProduct_switchTime σ A (T + 1)
  calc
    roundedEvolution H T T = durationProduct σ A (T + 1) := by
      rw [roundedEvolution]
      change evolutionOf G T T = _
      exact hend.trans hproduct
    _ = frozenEvolution (H 1) (1 / 2) * stepProduct H T *
        frozenEvolution (H 0) (-1 / 2) := by
      rw [show σ = roundedClockDuration T from rfl,
        show A = fun j : ℕ ↦ H (j / T) from rfl,
        rounded_durationProduct_split H T hT,
        durationProduct_one_eq_stepProduct]
    _ = exp (-(I / 2) • H 1) * stepProduct H T * exp ((I / 2) • H 0) := by
      have hleft : frozenEvolution (H 1) (1 / 2) = exp (-(I / 2) • H 1) := by
        rw [frozenEvolution_eq]
        congr 1
        norm_num
        ring_nf
      have hright : frozenEvolution (H 0) (-1 / 2) = exp ((I / 2) • H 0) := by
        rw [frozenEvolution_eq]
        congr 1
        norm_num
        ring_nf
      rw [hleft, hright]

/-- Orthogonal projectors are contractions in the operator norm. -/
private theorem projector_norm_le_one {P : 𝕄} (hP : IsOrthogonalProjector P) : ‖P‖ ≤ 1 := by
  have hnorm : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, hP.isSelfAdjoint.star_eq,
      hP.isIdempotentElem.eq]
  by_contra h
  linarith [mul_lt_mul_of_pos_left (not_le.mp h) (zero_lt_one.trans (not_le.mp h))]

/-- The three-term identity in Proposition 2.4. -/
private theorem transfer_identity (P Q P' Q' U W A B : 𝕄) :
    (1 - Q') * A * W * B * P' - (1 - Q) * U * P =
      (1 - Q') * (A * W * B - U) * P' +
        (Q - Q') * U * P + (1 - Q') * U * (P' - P) := by
  noncomm_ring

/-- Commuting unitary endpoint phases do not change the leakage norm. -/
private theorem transfer_phase_norm {P' Q' A B : 𝕄} (W : 𝕄)
    (hA : IsUnitary A) (hB : IsUnitary B) (hAQ' : Commute A Q')
    (hBP' : Commute B P') :
    ‖(1 - Q') * A * W * B * P'‖ = ‖(1 - Q') * W * P'‖ := by
  have hleft : (1 - Q') * A = A * (1 - Q') := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAQ'.eq]
  have hmove : (1 - Q') * A * W * B * P' = A * ((1 - Q') * W * P') * B := by
    rw [hleft]
    simp only [mul_assoc, hBP'.eq]
  have hAu : A ∈ unitary 𝕄 := Matrix.mem_unitaryGroup_iff'.mpr hA
  have hBu : B ∈ unitary 𝕄 := Matrix.mem_unitaryGroup_iff'.mpr hB
  rw [hmove, CStarRing.norm_mul_mem_unitary _ hBu,
    CStarRing.norm_mem_unitary_mul _ hAu]

/-- **Proposition 2.4.** Let `P`, `Q`, `P'`, and `Q'` be orthogonal projectors, let `U` and `W` be
matrices, and let `A` and `B` be unitary matrices that commute with `Q'` and `P'`, respectively.
Then
`|‖(1 - Q') W P'‖ - ‖(1 - Q) U P‖| ≤ ‖A W B - U‖ + ‖U‖ (‖P' - P‖ + ‖Q' - Q‖)`. -/
theorem transfer [NeZero d] {P Q P' Q' U W A B : 𝕄} (hP : IsOrthogonalProjector P)
    (hQ : IsOrthogonalProjector Q) (hP' : IsOrthogonalProjector P')
    (hQ' : IsOrthogonalProjector Q') (hA : IsUnitary A) (hB : IsUnitary B)
    (hAQ' : Commute A Q') (hBP' : Commute B P') :
    |‖(1 - Q') * W * P'‖ - ‖(1 - Q) * U * P‖| ≤
      ‖A * W * B - U‖ + ‖U‖ * (‖P' - P‖ + ‖Q' - Q‖) := by
  have hphase := transfer_phase_norm W hA hB hAQ' hBP'
  have hPc := projector_norm_le_one hP
  have hP'c := projector_norm_le_one hP'
  have hQ'c := projector_norm_le_one hQ'.one_sub
  have herror : ‖(1 - Q') * (A * W * B - U) * P'‖ ≤ ‖A * W * B - U‖ := by
    simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le hQ'c (le_refl ‖A * W * B - U‖)) hP'c
  have hfinal : ‖(Q - Q') * U * P‖ ≤ ‖Q' - Q‖ * ‖U‖ := by
    simpa only [mul_one, norm_sub_rev] using
      norm_mul_le_of_le (norm_mul_le (Q - Q') U) hPc
  have hinitial : ‖(1 - Q') * U * (P' - P)‖ ≤ ‖U‖ * ‖P' - P‖ := by
    simpa only [one_mul] using
      norm_mul_le_of_le (norm_mul_le_of_le hQ'c (le_refl ‖U‖)) (le_refl ‖P' - P‖)
  calc
    _ = |‖(1 - Q') * A * W * B * P'‖ - ‖(1 - Q) * U * P‖| := by rw [hphase]
    _ ≤ ‖(1 - Q') * A * W * B * P' - (1 - Q) * U * P‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(1 - Q') * (A * W * B - U) * P' +
          (Q - Q') * U * P + (1 - Q') * U * (P' - P)‖ := by
      rw [transfer_identity]
    _ ≤ ‖A * W * B - U‖ + ‖Q' - Q‖ * ‖U‖ + ‖U‖ * ‖P' - P‖ :=
      norm_add_le_of_le (norm_add_le_of_le herror hfinal) hinitial
    _ = _ := by ring

end RoundedClocks
