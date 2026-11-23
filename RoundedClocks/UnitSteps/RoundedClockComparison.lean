/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries
public import RoundedClocks.Appendix
public import RoundedClocks.UnitSteps.TruncatedProductBounds

/-! # Rounded-clock comparison

Theorem 4.2 differentiates the relative evolution on each unit cell, bounds the jump correctors,
and sums the cell errors.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A family continuous on `[a,b]` is regulated there. -/
theorem isRegulated_of_continuousOn {G : ℝ → 𝕄} {a b : ℝ} (hG : ContinuousOn G (Icc a b)) :
    IsRegulated G a b := by
  constructor
  · intro t ht
    refine ⟨G t, (hG t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Ioo_mem_nhdsGT ht.2) (Ioo_subset_Icc_self.trans
      (Icc_subset_Icc ht.1 le_rfl))
  · intro t ht
    refine ⟨G t, (hG t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Ioo_mem_nhdsLT ht.1) (Ioo_subset_Icc_self.trans
      (Icc_subset_Icc le_rfl ht.2))

/-- On the rounded-clock cell `(j - 1/2, j + 1/2)`, the rounded clock `⌊t + 1/2⌋` equals `j`. -/
theorem floor_add_half_eq {t : ℝ} {j : ℤ} (h₁ : (j : ℝ) - 1 / 2 ≤ t) (h₂ : t < j + 1 / 2) :
    ⌊t + 1 / 2⌋ = j := by
  rw [Int.floor_eq_iff]
  constructor <;> linarith

/-- A function of the rounded clock `⌊t + 1/2⌋` is regulated on every interval. -/
theorem isRegulated_round (F : ℝ → 𝕄) (a b : ℝ) :
    IsRegulated (fun t ↦ F (⌊t + 1 / 2⌋ : ℝ)) a b := by
  constructor
  · intro t _
    refine ⟨F (⌊t + 1 / 2⌋ : ℝ), tendsto_const_nhds.congr' ?_⟩
    have hlt : t < ⌊t + 1 / 2⌋ + 1 / 2 := by linarith [Int.lt_floor_add_one (t + 1 / 2)]
    filter_upwards [Ioo_mem_nhdsGT hlt] with x hx
    rw [floor_add_half_eq (by linarith [Int.floor_le (t + 1 / 2), hx.1]) hx.2]
  · intro t _
    let n : ℤ := ⌈t + 1 / 2⌉ - 1
    refine ⟨F (n : ℝ), tendsto_const_nhds.congr' ?_⟩
    have hn : (n : ℝ) = ⌈t + 1 / 2⌉ - 1 := by push_cast [n]; ring
    have hlt : (n : ℝ) - 1 / 2 < t := by linarith [Int.ceil_lt_add_one (t + 1 / 2)]
    filter_upwards [Ioo_mem_nhdsLT hlt] with x hx
    rw [floor_add_half_eq hx.1.le (by linarith [Int.le_ceil (t + 1 / 2), hx.2])]

/-- One-sided first-order Taylor bound: if `f' ` is `L`-Lipschitz on `[a,b]` and `s₀ ≤ s`, then
`‖f s - f s₀ - (s - s₀) f' s₀‖ ≤ (L/2)(s - s₀)²`. -/
theorem taylor_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {a b L : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hL : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f' x - f' y‖ ≤ L * |x - y|) {s₀ s : ℝ}
    (hs₀ : s₀ ∈ Icc a b) (hs : s ∈ Icc a b) (hle : s₀ ≤ s) :
    ‖f s - f s₀ - (s - s₀) • f' s₀‖ ≤ L / 2 * (s - s₀) ^ 2 := by
  have hsub : Icc s₀ s ⊆ Icc a b := Icc_subset_Icc hs₀.1 hs.2
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun x ↦ f x - f s₀ - (x - s₀) • f' s₀) (f' := fun x ↦ f' x - f' s₀)
    (B := fun x ↦ L / 2 * (x - s₀) ^ 2) (B' := fun x ↦ L * (x - s₀)) ?_ ?_ ?_ ?_ ?_
    ⟨hle, le_rfl⟩
  · intro x hx
    exact (((hf x (hsub hx)).continuousWithinAt.mono hsub).sub continuousWithinAt_const).sub
      (((continuousWithinAt_id.sub continuousWithinAt_const).smul continuousWithinAt_const))
  · intro x hx
    have hmem : Icc a b ∈ 𝓝[≥] x :=
      Icc_mem_nhdsGE_of_mem ⟨(hsub (Ico_subset_Icc_self hx)).1, hx.2.trans_le hs.2⟩
    have h := ((hf x (hsub (Ico_subset_Icc_self hx))).mono_of_mem_nhdsWithin hmem).sub_const
      (f s₀)
    have h' := ((hasDerivWithinAt_id x (Ici x)).sub_const s₀).smul_const (f' s₀)
    simpa using h.sub h'
  · simp
  · intro x
    have h := (((hasDerivAt_id x).sub_const s₀).pow 2).const_mul (L / 2)
    convert h using 1
    simp only [id, Nat.cast_ofNat]
    ring
  · intro x hx
    have h := hL x (hsub (Ico_subset_Icc_self hx)) s₀ hs₀
    rwa [abs_of_nonneg (by linarith [hx.1])] at h

/-- First-order Taylor bound: if `f'` is `L`-Lipschitz on `[a,b]`, then for `s₀, s ∈ [a,b]`,
`‖f s - f s₀ - (s - s₀) f' s₀‖ ≤ (L/2)(s - s₀)²`. -/
theorem taylor_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {a b L : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hL : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f' x - f' y‖ ≤ L * |x - y|) {s₀ s : ℝ}
    (hs₀ : s₀ ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖f s - f s₀ - (s - s₀) • f' s₀‖ ≤ L / 2 * (s - s₀) ^ 2 := by
  rcases le_total s₀ s with hle | hle
  · exact taylor_right hf hL hs₀ hs hle
  -- Reflect: `f̃ u = f (-u)` on `[-b,-a]` has derivative `-f'(-u)`.
  have hneg : ∀ u ∈ Icc (-b) (-a), -u ∈ Icc a b := fun u hu ↦ ⟨by linarith [hu.2], by
    linarith [hu.1]⟩
  have hf' : ∀ u ∈ Icc (-b) (-a),
      HasDerivWithinAt (fun u ↦ f (-u)) (-f' (-u)) (Icc (-b) (-a)) u := by
    intro u hu
    have h := (hf (-u) (hneg u hu)).scomp u (hasDerivWithinAt_neg u (Icc (-b) (-a)))
      (fun v hv ↦ hneg v hv)
    simpa using h
  have hL' : ∀ x ∈ Icc (-b) (-a), ∀ y ∈ Icc (-b) (-a),
      ‖-f' (-x) - -f' (-y)‖ ≤ L * |x - y| := by
    intro x hx y hy
    have h := hL (-y) (hneg y hy) (-x) (hneg x hx)
    rw [neg_sub_neg]
    rwa [neg_sub_neg] at h
  have h := taylor_right hf' hL' (s₀ := -s₀) (s := -s) ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩
    ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
  simp only [neg_neg] at h
  convert h using 2
  · module
  · ring

/-- The cell integral `∫_{-1/2}^{1/2} ((L/2)τ² + S²|τ|(c + τ²/2)) dτ = L/24 + S²(c/4 + 1/64)`,
from `∫_{-1/2}^{1/2} (τ², |τ|, |τ|³) dτ = (1/12, 1/4, 1/32)`. -/
theorem cell_integral (L S c : ℝ) :
    ∫ τ in (-1 / 2 : ℝ)..1 / 2, (L / 2 * τ ^ 2 + S ^ 2 * |τ| * (c + τ ^ 2 / 2)) =
      L / 24 + S ^ 2 * (c / 4 + 1 / 64) := by
  set g : ℝ → ℝ := fun τ ↦ L / 2 * τ ^ 2 + S ^ 2 * |τ| * (c + τ ^ 2 / 2) with hg
  have hcont : Continuous g := by fun_prop
  have hhalf : ∫ τ in (0 : ℝ)..1 / 2, g τ = L / 48 + S ^ 2 * (c / 8 + 1 / 128) := by
    have hcongr : ∫ τ in (0 : ℝ)..1 / 2, g τ =
        ∫ τ in (0 : ℝ)..1 / 2, (L / 2 * τ ^ 2 + S ^ 2 * c * τ + S ^ 2 / 2 * τ ^ 3) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      rw [uIcc_of_le (by norm_num)] at hτ
      simp only [hg, abs_of_nonneg hτ.1]
      ring
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun τ ↦ L / 6 * τ ^ 3 + S ^ 2 * c / 2 * τ ^ 2 + S ^ 2 / 8 * τ ^ 4)]
    · norm_num
      ring
    · intro τ _
      have h := (((hasDerivAt_pow 3 τ).const_mul (L / 6)).add
        ((hasDerivAt_pow 2 τ).const_mul (S ^ 2 * c / 2))).add
        ((hasDerivAt_pow 4 τ).const_mul (S ^ 2 / 8))
      convert h using 1
      push_cast
      ring
    · exact (by fun_prop : Continuous fun τ : ℝ ↦
        L / 2 * τ ^ 2 + S ^ 2 * c * τ + S ^ 2 / 2 * τ ^ 3).intervalIntegrable _ _
  have hleft : ∫ τ in (-1 / 2 : ℝ)..0, g τ = ∫ τ in (0 : ℝ)..1 / 2, g τ := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1 / 2) g
    have heven : (fun τ ↦ g (-τ)) = g := by
      funext τ
      simp [hg, abs_neg]
    rw [heven] at h
    rw [h]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hleft, hhalf]
  ring

/-- A continuous `g`, read on the rounded clock `t - ⌊t + 1/2⌋`, is interval integrable. -/
theorem intervalIntegrable_round (g : ℝ → ℝ) (hg : Continuous g) (t₁ t₂ : ℝ) :
    IntervalIntegrable (fun t ↦ g (t - ⌊t + 1 / 2⌋)) volume t₁ t₂ := by
  have hτ : ∀ t : ℝ, t - (⌊t + 1 / 2⌋ : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro t
    constructor <;> linarith [Int.floor_le (t + 1 / 2), Int.lt_floor_add_one (t + 1 / 2)]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hg.continuousOn
  have hmeas : Measurable fun t : ℝ ↦ g (t - ⌊t + 1 / 2⌋) := by
    apply hg.measurable.comp
    exact measurable_id.sub ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.add_const _)))
  refine (intervalIntegrable_const (c := C)).mono_fun' hmeas.aestronglyMeasurable ?_
  exact Eventually.of_forall fun t ↦ hC _ (hτ t)

/-- A continuous even `g`, read on the rounded clock `t - ⌊t + 1/2⌋`, integrates over `[0,n]`
to `n` times its integral over `[-1/2,1/2]`: in the third line of the paper's display, `τ` runs
over `[-1/2,1/2)` as `t` runs over each `[k,k+1)`. -/
theorem integral_round (g : ℝ → ℝ) (hg : Continuous g) (heven : ∀ τ, g (-τ) = g τ) (n : ℕ) :
    ∫ t in (0 : ℝ)..n, g (t - ⌊t + 1 / 2⌋) = n * ∫ τ in (-1 / 2 : ℝ)..1 / 2, g τ := by
  set ρ : ℝ → ℝ := fun t ↦ g (t - ⌊t + 1 / 2⌋) with hρ
  have hper : Function.Periodic ρ 1 := by
    intro t
    simp only [hρ, show t + 1 + 1 / 2 = t + 1 / 2 + 1 by ring, Int.floor_add_one]
    push_cast
    ring_nf
  have hint : ∀ t₁ t₂, IntervalIntegrable ρ volume t₁ t₂ := intervalIntegrable_round g hg
  have h1 := hper.intervalIntegral_add_zsmul_eq (n : ℤ) 0 hint
  have h2 := hper.intervalIntegral_add_eq 0 (-1 / 2)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at h1 h2
  rw [h1, h2, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num)] at hx
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have h0 : ⌊x + 1 / 2⌋ = 0 :=
      floor_add_half_eq (by push_cast; linarith [hx.1]) (by push_cast; linarith)
    simp only [hρ, h0, Int.cast_zero, sub_zero]
  · subst heq
    simp only [hρ]
    norm_num
    rw [← heven]
    norm_num

/-- Conjugating by unitaries does not increase the norm: `‖A† X B‖ ≤ ‖X‖`. -/
theorem norm_conj_le [NeZero d] {A B : 𝕄} (hA : IsUnitary A) (hB : IsUnitary B) (X : 𝕄) :
    ‖A† * X * B‖ ≤ ‖X‖ := by
  have hA' : IsUnitary A† := by
    change A†† * A† = 1
    rw [star_star]
    exact mul_eq_one_comm.mp hA
  calc
    ‖A† * X * B‖ ≤ ‖A†‖ * ‖X‖ * ‖B‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖X‖ * 1 := by
      gcongr
      · exact unitary_norm_le_one hA'
      · exact unitary_norm_le_one hB
    _ = ‖X‖ := by ring

/-- Equation (4.1) with its bracket removed: when `Y = cZ` and `Y' = c(τD - i[Ω,Z])`,
`K - Ω - Y' - i(KY - YΩ) = (K - Ω - cτ D) - i(K - Ω)Y`. -/
theorem residual_eq (K Ω D Z : 𝕄) (c τ : ℝ) :
    K - Ω - c • (τ • D - I • (Ω * Z - Z * Ω)) - I • (K * (c • Z) - c • Z * Ω) =
      (K - Ω - (c * τ) • D) - I • ((K - Ω) * (c • Z)) := by
  simp only [sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc]
  module

/-- **Theorem 4.2**, proof. See `RoundedClocks.rounded_clock_comparison`. -/
theorem rounded_clock_comparison_main (dieudonne_7_6_1 : Dieudonne_7_6_1)
    (dieudonne_section_8_7 : Dieudonne_Section_8_7)
    (dlmf_4_22_5 : DLMF_4_22_5) (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    [NeZero d] {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H)
    {L w : ℝ} (hL : HasLipschitzDerivative H L) (hw : w < 2 * π)
    (hwidth : HasSampleWidth H T w) :
    ‖roundedEvolution H T T - evolution H T T‖ ≤
      (c₀ w * (‖∂H 0‖ + ‖∂H 1‖) + L / 24 + c₁ w * ‖∂H‖∞ ^ 2) / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  set S := ‖∂H‖∞ with hSdef
  /- Standing facts about `H`: it has derivative `∂H` on `[0,1]` (from `hL`), `∂H` is bounded by
  `S = ‖∂H‖∞`, the samples `j/T` lie in `[0,1]`, and the width `w` is nonnegative. -/
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (∂H s) (Icc 0 1) s :=
    fun s hs ↦ (hL.1 s hs).hasDerivWithinAt
  have hbdd : BddAbove ((fun s ↦ ‖∂H s‖) '' Icc (0 : ℝ) 1) := by
    refine ⟨‖∂H 0‖ + |L|, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have h := hL.2 s hs 0 ⟨le_rfl, zero_le_one⟩
    have hs1 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs.1]; exact hs.2
    have hLs : L * |s - 0| ≤ |L| :=
      (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)).trans
        (mul_le_of_le_one_right (abs_nonneg L) hs1)
    linarith [norm_le_norm_add_norm_sub' (∂H s) (∂H 0), norm_sub_rev (∂H s) (∂H 0)]
  have hS : ∀ s ∈ Icc (0 : ℝ) 1, ‖∂H s‖ ≤ S := fun s hs ↦ le_csSup hbdd ⟨s, hs, rfl⟩
  have hsample : ∀ j : ℕ, j ≤ T → (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := fun j hj ↦
    ⟨by positivity, div_le_one_of_le₀ (by exact_mod_cast hj) hT0.le⟩
  have hw0 : 0 ≤ w := by
    have h := hwidth 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div] at h
    have hx := (hH 0 ⟨le_rfl, zero_le_one⟩).eigenvalues_mem_spectrum_real 0
    simpa using h _ hx _ hx
  /- Lemma A.1 for `Ω = H(j/T)` and `H'(j/T)`, for every `0 ≤ j ≤ T`. The correction on cell `j`
  is `Y_j(t) = Z_j(t - j)/T`, which solves (4.2) with `D = H'(j/T)/T`. -/
  have hcell : ∀ j : ℕ, ∃ Z : ℝ → 𝕄, j ≤ T →
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), HasDerivWithinAt Z
        (τ • ∂H (j / T) - I • (H (j / T) * Z τ - Z τ * H (j / T))) (Icc (-1 / 2) (1 / 2)) τ) ∧
      Z (-1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T)) ∧ Z (1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T)) ∧
      ‖Z 0‖ ≤ c₀ w * ‖∂H (j / T)‖ ∧
      ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Z τ‖ ≤ ‖Z 0‖ + τ ^ 2 * ‖∂H (j / T)‖ / 2 := by
    intro j
    by_cases hj : j ≤ T
    · obtain ⟨Z, -, hZ⟩ :=
        cell dlmf_4_22_5 hw0 hw (hH _ (hsample j hj)) (hwidth j hj) (∂H (j / T))
      exact ⟨Z, fun _ ↦ hZ⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  choose Z hZ using hcell
  /- The two families `K(t) = H(t/T)` and `G(t) = H(⌊t+1/2⌋/T)`, their evolutions `U` and `V`,
  the points `p_0 = 0`, `p_j = j - 1/2` for `1 ≤ j ≤ T`, `p_{T+1} = T`, the pieces `Y_j`, their
  derivatives `Y_j'`, and the residual `R` on the cell `n(t) = ⌊t + 1/2⌋` containing `t`. -/
  let K : ℝ → 𝕄 := fun t ↦ H (t / T)
  let G : ℝ → 𝕄 := fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)
  let U := evolution H T
  let V := roundedEvolution H T
  let p : ℕ → ℝ := fun j ↦ max 0 (min ((j : ℝ) - 1 / 2) T)
  let Y : ℕ → ℝ → 𝕄 := fun j t ↦ (1 / T : ℝ) • Z j (t - j)
  let Y' : ℕ → ℝ → 𝕄 := fun j t ↦ (1 / T : ℝ) • ((t - j) • ∂H (j / T) -
    I • (H (j / T) * Z j (t - j) - Z j (t - j) * H (j / T)))
  let n : ℝ → ℕ := fun t ↦ (⌊t + 1 / 2⌋).toNat
  let R : ℝ → 𝕄 := fun t ↦ K t - G t - Y' (n t) t - I • (K t * Y (n t) t - Y (n t) t * G t)
  -- On `[0,T]`, the cell index `n(t)` is the rounded clock, at most `T`.
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
  have hτ : ∀ t : ℝ, t - (⌊t + 1 / 2⌋ : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro t
    constructor <;> linarith [Int.floor_le (t + 1 / 2), Int.lt_floor_add_one (t + 1 / 2)]
  -- The pieces: `t - j ∈ [-1/2,1/2]` on `[p_j, p_{j+1}]`.
  have hp_ge : ∀ j : ℕ, j ≤ T → (j : ℝ) - 1 / 2 ≤ p j := by
    intro j hj
    have : (j : ℝ) ≤ T := by exact_mod_cast hj
    exact le_max_of_le_right (le_min le_rfl (by linarith))
  have hp_le : ∀ j : ℕ, p (j + 1) ≤ (j : ℝ) + 1 / 2 := by
    intro j
    refine max_le (by positivity) (min_le_left _ _ |>.trans (by push_cast; linarith))
  have hpiece : ∀ j : ℕ, j ≤ T → ∀ t ∈ Icc (p j) (p (j + 1)),
      t - j ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro j hj t ht
    constructor <;> linarith [hp_ge j hj, hp_le j, ht.1, ht.2]
  have hpIcc : ∀ j : ℕ, p j ∈ Icc (0 : ℝ) T :=
    fun j ↦ ⟨le_max_left _ _, max_le hT0.le (min_le_right _ _)⟩
  /- The hypotheses of Theorem 2.2: `K` is continuous, hence regulated; `G` is a function of the
  rounded clock, hence regulated; both are Hermitian on `[0,T]` and generate `U` and `V`. -/
  have hKcont : ContinuousOn K (Icc 0 T) := by
    refine hL.1.continuousOn.comp (continuousOn_id.div_const _) ?_
    intro t ht
    exact ⟨div_nonneg ht.1 hT0.le, div_le_one_of_le₀ ht.2 hT0.le⟩
  have hKreg : IsRegulated K 0 T := isRegulated_of_continuousOn hKcont
  have hKh : IsHermitianFamily K 0 T := fun t ht ↦
    hH _ ⟨div_nonneg ht.1 hT0.le, div_le_one_of_le₀ ht.2 hT0.le⟩
  have hGreg : IsRegulated G 0 T := isRegulated_round (fun x ↦ H (x / T)) 0 T
  have hGh : IsHermitianFamily G 0 T := by
    intro t ht
    rw [hround t ht]
    exact hH _ (hsample _ (hn t ht).2)
  have hU : Generates K U 0 T :=
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3 hT0.le hKreg hKh
  have hV : Generates G V 0 T :=
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3 hT0.le hGreg hGh
  have hp : ∀ j ≤ T, p j ≤ p (j + 1) := by
    intro j _
    exact max_le_max le_rfl (min_le_min (by push_cast; linarith) le_rfl)
  have hp0 : p 0 = 0 := max_eq_left (min_le_left _ _ |>.trans (by norm_num))
  have hpT : p (T + 1) = T := by
    simp only [p]
    rw [min_eq_right (by push_cast; linarith), max_eq_right hT0.le]
  have hZcont : ∀ j ≤ T, ContinuousOn (fun t ↦ Z j (t - j)) (Icc (p j) (p (j + 1))) := by
    intro j hj
    have hc : ContinuousOn (Z j) (Icc (-1 / 2) (1 / 2)) :=
      fun τ hτ ↦ ((hZ j hj).1 τ hτ).continuousWithinAt
    exact hc.comp (continuousOn_id.sub continuousOn_const) (hpiece j hj)
  have hYc : ∀ j ≤ T, ContinuousOn (Y j) (Icc (p j) (p (j + 1))) :=
    fun j hj ↦ (hZcont j hj).const_smul _
  have hY' : ∀ j ≤ T, IsRegulated (Y' j) (p j) (p (j + 1)) := by
    intro j hj
    apply isRegulated_of_continuousOn
    have hc := hZcont j hj
    have hlin : ContinuousOn (fun t : ℝ ↦ (t - j) • ∂H (j / T)) (Icc (p j) (p (j + 1))) :=
      (continuousOn_id.sub continuousOn_const).smul continuousOn_const
    exact (hlin.sub (((continuousOn_const.mul hc).sub
      (hc.mul continuousOn_const)).const_smul I)).const_smul _
  have hYd : ∀ j ≤ T, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ (∅ : Set ℝ) →
      HasDerivAt (Y j) (Y' j t) t := by
    intro j hj t ht _
    have hτj : t - j ∈ Ioo (-1 / 2 : ℝ) (1 / 2) :=
      ⟨by linarith [hp_ge j hj, ht.1], by linarith [hp_le j, ht.2]⟩
    have h := ((hZ j hj).1 (t - j) (Ioo_subset_Icc_self hτj)).hasDerivAt
      (Icc_mem_nhds hτj.1 hτj.2)
    exact (h.comp_sub_const t j).const_smul (1 / T : ℝ)
  have hR : ∀ j ≤ T, ∀ t ∈ Ioo (p j) (p (j + 1)), t ∉ (∅ : Set ℝ) →
      R t = K t - G t - Y' j t - I • (K t * Y j t - Y j t * G t) := by
    intro j hj t ht _
    have hfl : ⌊t + 1 / 2⌋ = (j : ℤ) :=
      floor_add_half_eq (by push_cast; linarith [hp_ge j hj, ht.1])
        (by push_cast; linarith [hp_le j, ht.2])
    simp only [R, n, hfl, Int.toNat_natCast]
  -- **Theorem 2.2** with endpoints `0` and `T`.
  have hcomp := comparison dieudonne_7_6_1 dieudonne_section_8_7 K G U V hKreg hKh
    hGreg hGh hU hV T p hp hp0 hpT Y (fun _ ↦ ∅) (fun _ _ ↦ countable_empty)
    hYc Y' hY' hYd R hR
  -- The jump of `Y` at `p_j = j - 1/2` is `Δ_j`, as both cells have end values `𝒩([Ω,·])D`.
  have hjump : ∀ j ∈ Finset.Icc 1 T, Y j (p j) - Y (j - 1) (p j) = Δ H T j := by
    intro j hj
    obtain ⟨h1, hjT⟩ := Finset.mem_Icc.mp hj
    have h1' : (1 : ℝ) ≤ j := by exact_mod_cast h1
    have hjT' : (j : ℝ) ≤ T := by exact_mod_cast hjT
    have hpj : p j = (j : ℝ) - 1 / 2 := by
      simp only [p]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
    have hleft : (j : ℝ) - 1 / 2 - j = -1 / 2 := by ring
    have hright : (j : ℝ) - 1 / 2 - ((j - 1 : ℕ) : ℝ) = 1 / 2 := by rw [hcast]; ring
    rw [hpj]
    simp only [Y]
    rw [hleft, hright, (hZ j hjT).2.1, (hZ (j - 1) (by omega)).2.2.1, hcast, ← smul_sub]
    rfl
  -- Lemma A.1(ii) at `τ = 0` bounds the boundary values `Y(0)` and `Y(T)`.
  have hY0 : ‖Y 0 0‖ ≤ c₀ w * ‖∂H 0‖ / T := by
    have h := (hZ 0 (Nat.zero_le _)).2.2.2.1
    simp only [Nat.cast_zero, zero_div] at h
    simp only [Y, Nat.cast_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hT0)]
    calc
      1 / T * ‖Z 0 0‖ ≤ 1 / T * (c₀ w * ‖∂H 0‖) := by gcongr
      _ = _ := by ring
  have hYT : ‖Y T T‖ ≤ c₀ w * ‖∂H 1‖ / T := by
    have h := (hZ T le_rfl).2.2.2.1
    rw [div_self hT0.ne'] at h
    simp only [Y, sub_self, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hT0)]
    calc
      1 / T * ‖Z T 0‖ ≤ 1 / T * (c₀ w * ‖∂H 1‖) := by gcongr
      _ = _ := by ring
  /- The residual: by (4.1) with its bracket removed (as `Y` solves (4.2)),
  `‖R‖ ≤ Lτ²/(2T²) + (‖H'‖∞|τ|/T)(c₀ + τ²/2)‖H'‖∞/T` with `τ = t - ⌊t + 1/2⌋`. -/
  have hc₀ := c₀_nonneg_of_width dlmf_4_22_5 hw0 hw
  let g : ℝ → ℝ := fun τ ↦ 1 / T ^ 2 * (L / 2 * τ ^ 2 + S ^ 2 * |τ| * (c₀ w + τ ^ 2 / 2))
  have hRle : ∀ t ∈ Icc (0 : ℝ) T, ‖R t‖ ≤ g (t - ⌊t + 1 / 2⌋) := by
    intro t ht
    obtain ⟨hnt, hnT⟩ := hn t ht
    have hτj : t - (n t : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by rw [hnt]; exact hτ t
    have hRt : R t = (K t - H (n t / T) - (1 / T * (t - n t)) • ∂H (n t / T)) -
        I • ((K t - H (n t / T)) * ((1 / T : ℝ) • Z (n t) (t - n t))) := by
      simp only [R, hround t ht, Y, Y']
      exact residual_eq _ _ _ _ _ _
    have hjs := hsample (n t) hnT
    have hts : t / T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hT0.le, div_le_one_of_le₀ ht.2 hT0.le⟩
    -- Taylor: `‖K'(σ) - K'(⌊t+1/2⌋)‖ ≤ L|σ - ⌊t+1/2⌋|/T²`, integrated.
    have htaylor := taylor_lipschitz hderiv hL.2 hjs hts
    rw [show t / T - n t / T = 1 / T * (t - n t) by ring] at htaylor
    -- `‖K(t) - G(t)‖ ≤ ‖H'‖∞ |τ|/T`.
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hS
      hjs hts
    rw [Real.norm_eq_abs, show t / T - n t / T = (t - n t) / T by ring, abs_div,
      abs_of_pos hT0] at hmvt
    -- Lemma A.1(ii): `‖Z(τ)‖ ≤ (c₀ + τ²/2) ‖H'(j/T)‖ ≤ (c₀ + τ²/2) ‖H'‖∞`.
    have hZb : ‖Z (n t) (t - n t)‖ ≤ (c₀ w + (t - n t) ^ 2 / 2) * S := by
      have h1 := (hZ (n t) hnT).2.2.2.2 (t - n t) hτj
      have h0 := (hZ (n t) hnT).2.2.2.1
      have hD := hS _ hjs
      calc
        _ ≤ c₀ w * ‖∂H (n t / T)‖ + (t - n t) ^ 2 * ‖∂H (n t / T)‖ / 2 := by linarith
        _ = (c₀ w + (t - n t) ^ 2 / 2) * ‖∂H (n t / T)‖ := by ring
        _ ≤ _ := by gcongr
    rw [hRt]
    calc
      _ ≤ ‖K t - H (n t / T) - (1 / T * (t - n t)) • ∂H (n t / T)‖ +
          ‖(K t - H (n t / T)) * ((1 / T : ℝ) • Z (n t) (t - n t))‖ := by
        refine (norm_sub_le _ _).trans_eq ?_
        rw [norm_smul, Complex.norm_I, one_mul]
      _ ≤ L / 2 * (1 / T * (t - n t)) ^ 2 +
          S * |t - n t| / T * (1 / T * ((c₀ w + (t - n t) ^ 2 / 2) * S)) := by
        refine add_le_add htaylor ((norm_mul_le _ _).trans ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hT0)]
        have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 ⟨le_rfl, zero_le_one⟩)
        exact mul_le_mul (hmvt.trans_eq (by ring)) (mul_le_mul_of_nonneg_left hZb (by positivity))
          (by positivity) (div_nonneg (mul_nonneg hS0 (abs_nonneg _)) hT0.le)
      _ = g (t - ⌊t + 1 / 2⌋) := by
        rw [← hnt]
        simp only [g]
        field_simp
  -- `‖∫_0^T i U† R V dt‖ ≤ ∫_0^T ‖R‖ ≤ (L/24 + c₁ ‖H'‖∞²)/T`.
  have hgcont : Continuous g := by fun_prop
  have hint : ‖∫ t in (0 : ℝ)..T, I • ((U t)† * R t * V t)‖ ≤
      ∫ t in (0 : ℝ)..T, g (t - ⌊t + 1 / 2⌋) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT0.le
    · refine Eventually.of_forall fun t ht ↦ ?_
      have ht' := Ioc_subset_Icc_self ht
      rw [norm_smul, Complex.norm_I, one_mul]
      exact (norm_conj_le (hU.2.2.1 t ht') (hV.2.2.1 t ht') _).trans (hRle t ht')
    · exact intervalIntegrable_round g hgcont _ _
  have hgint : ∫ t in (0 : ℝ)..T, g (t - ⌊t + 1 / 2⌋) = (L / 24 + c₁ w * S ^ 2) / T := by
    rw [integral_round g hgcont (fun τ ↦ by simp only [g, abs_neg, neg_sq]) T]
    simp only [g]
    rw [intervalIntegral.integral_const_mul, cell_integral, c₁]
    field_simp
  -- `‖V(T) - U(T)‖ = ‖U(T)† V(T) - 1‖`, and the three bounds into Theorem 2.2.
  have hUT := hU.2.2.1 T ⟨hT0.le, le_rfl⟩
  have hVT := hV.2.2.1 T ⟨hT0.le, le_rfl⟩
  have hunit : ‖V T - U T‖ ≤ ‖(U T)† * V T - 1‖ := by
    have hUU : U T * (U T)† = 1 := mul_eq_one_comm.mp hUT
    calc
      ‖V T - U T‖ = ‖U T * ((U T)† * V T - 1)‖ := by
        rw [mul_sub, ← mul_assoc, hUU, one_mul, mul_one]
      _ ≤ ‖U T‖ * ‖(U T)† * V T - 1‖ := norm_mul_le _ _
      _ ≤ 1 * ‖(U T)† * V T - 1‖ := by gcongr; exact unitary_norm_le_one hUT
      _ = _ := one_mul _
  have hsum : ‖I • ∑ j ∈ Finset.Icc 1 T, (U (p j))† * (Y j (p j) - Y (j - 1) (p j)) * V (p j)‖ ≤
      ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
    rw [hjump j hj]
    exact norm_conj_le (hU.2.2.1 _ (hpIcc j)) (hV.2.2.1 _ (hpIcc j)) _
  have hend : ‖I • ((U T)† * Y T T * V T)‖ ≤ c₀ w * ‖∂H 1‖ / T := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (norm_conj_le hUT hVT _).trans hYT
  have hstart : ‖I • Y 0 0‖ ≤ c₀ w * ‖∂H 0‖ / T := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact hY0
  have htri : ∀ A B C E : 𝕄, ‖A + B - C - E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖E‖ := fun A B C E ↦
    (norm_sub_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
      (add_le_add_left (norm_add_le _ _) _)) _)
  change ‖V T - U T‖ ≤ _
  rw [hcomp] at hunit
  calc
    _ ≤ _ := hunit
    _ ≤ _ := htri _ _ _ _
    _ ≤ (L / 24 + c₁ w * S ^ 2) / T + c₀ w * ‖∂H 1‖ / T + c₀ w * ‖∂H 0‖ / T +
        ∑ j ∈ Finset.Icc 1 T, ‖Δ H T j‖ :=
      add_le_add (add_le_add (add_le_add (hint.trans hgint.le) hend) hstart) hsum
    _ = _ := by ring

end RoundedClocks
