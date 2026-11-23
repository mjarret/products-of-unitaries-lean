/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries
public import RoundedClocks.Appendix
public import RoundedClocks.UnitSteps.Basic

/-! # The steps of the proof of Theorem 4.2

The proof of Theorem 4.2 (`rounded_clock_comparison`) applies Theorem 2.2 to `K(t) = H(t/T)` and
`G(t) = H(⌊t+1/2⌋/T)` for `t ∈ [0,T]`, with the correction of Lemma A.1 for every sample `H(j/T)`.
This gives (4.5). Lemma A.1(ii) bounds its boundary values `Y(0)` and `Y(T)`, and the display
after (4.5) bounds its residual. The jumps `Δ_j` remain. This file proves the steps:

* the rounded clock `⌊t + 1/2⌋` equals `j` for `j - 1/2 ≤ t < j + 1/2` (`floor_add_half_eq`), so
  `τ = t - ⌊t + 1/2⌋` lies in `[-1/2, 1/2]` (`sub_round_mem_Icc`) and a function of the rounded
  clock is regulated (`isRegulated_round`);
* `K` and `G` are regulated and Hermitian, and they generate the evolutions `U` and `V`
  (`generates_evolution`, `generates_roundedEvolution`);
* the points `p_0 = 0`, `p_j = j - 1/2` for `1 ≤ j ≤ T`, and `p_{T+1} = T` (`clockPoint`);
* the consequences of the hypotheses on `H`: `0 ≤ w` (`width_nonneg`), `‖H'(s)‖ ≤ ‖H'‖∞`
  (`norm_deriv_le_supNorm`), `‖H(b) - H(a)‖ ≤ ‖H'‖∞ |b - a|` (`norm_sub_le_supNorm_mul`), and
  `‖H(s) - H(s₀) - (s - s₀) H'(s₀)‖ ≤ L (s - s₀)²/2` (`taylor_lipschitz`);
* Lemma A.1 at every sample (`exists_sample_corrections`);
* the residual (4.1) without its bracket (`residual_eq`) and the second, third, and fourth lines
  of the residual display (`norm_residual_le`, `integral_round`, `integral_residual_bound`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter MeasureTheory
open Complex (I)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-! ### The rounded clock -/

/-- For `j - 1/2 ≤ t < j + 1/2`, the rounded clock `⌊t + 1/2⌋` equals `j`. -/
theorem floor_add_half_eq {t : ℝ} {j : ℤ} (h₁ : (j : ℝ) - 1 / 2 ≤ t) (h₂ : t < j + 1 / 2) :
    ⌊t + 1 / 2⌋ = j := by
  exact round_eq t ▸ round_eq_iff.mpr ⟨h₁, h₂⟩

/-- `τ = t - ⌊t + 1/2⌋` lies in `[-1/2, 1/2]`. -/
theorem sub_round_mem_Icc (t : ℝ) : t - (⌊t + 1 / 2⌋ : ℝ) ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  rw [← round_eq, neg_div]
  exact abs_le.mp (abs_sub_round t)

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

/-! ### The two evolutions -/

/-- For a continuous time-dependent Hamiltonian `H` and an integer `T ≥ 1`, the family
`K(t) = H(t/T)` for `t ∈ [0,T]` is regulated and Hermitian, and it generates the evolution `U` of
`H` over time `T`. -/
theorem generates_evolution (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3) {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) (hHc : ContinuousOn H (Icc 0 1)) :
    IsRegulated (fun t ↦ H (t / T)) 0 T ∧ IsHermitianFamily (fun t ↦ H (t / T)) 0 T ∧
      Generates (fun t ↦ H (t / T)) (evolution H T) 0 T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hKcont : ContinuousOn (fun t : ℝ ↦ H (t / T)) (Icc 0 T) := by
    refine hHc.comp (continuousOn_id.div_const _) ?_
    intro t ht
    exact (unitInterval.div_mem ht.1 hT0.le ht.2)
  have hKreg : IsRegulated (fun t : ℝ ↦ H (t / T)) 0 T := ContinuousOn.isRegulated hKcont
  have hKh : IsHermitianFamily (fun t : ℝ ↦ H (t / T)) 0 T := fun {t} ht ↦
    @hH _ (unitInterval.div_mem ht.1 hT0.le ht.2)
  exact ⟨hKreg, hKh,
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3 hT0.le hKreg hKh⟩

/-- For a time-dependent Hamiltonian `H` and an integer `T ≥ 1`, the family
`G(t) = H(⌊t+1/2⌋/T)` for `t ∈ [0,T]`, which is `H` run on the rounded clock, is regulated and
Hermitian, and it generates the evolution `V`. -/
theorem generates_roundedEvolution (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3) {T : ℕ} (hT : 1 ≤ T) {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) :
    IsRegulated (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) 0 T ∧
      IsHermitianFamily (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) 0 T ∧
      Generates (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) (roundedEvolution H T) 0 T := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hGreg : IsRegulated (fun t : ℝ ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) 0 T :=
    isRegulated_round (fun x ↦ H (x / T)) 0 T
  have hGh : IsHermitianFamily (fun t : ℝ ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) 0 T := by
    intro t ht
    have h0 : (0 : ℝ) ≤ (⌊t + 1 / 2⌋ : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr (by linarith [ht.1])
    have hlt : ⌊t + 1 / 2⌋ < (T : ℤ) + 1 := Int.floor_lt.mpr (by push_cast; linarith [ht.2])
    have hle : (⌊t + 1 / 2⌋ : ℝ) ≤ T := by exact_mod_cast Int.lt_add_one_iff.mp hlt
    exact @hH _ (unitInterval.div_mem h0 hT0.le hle)
  exact ⟨hGreg, hGh,
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3 hT0.le hGreg hGh⟩

/-! ### The points `p_j` -/

/-- The points of the proof of Theorem 4.2: `p_0 = 0`, `p_j = j - 1/2` for `1 ≤ j ≤ T`, and
`p_{T+1} = T`. Theorem 2.2 is applied with these points, and the correction jumps at `p_j` for
`1 ≤ j ≤ T`. -/
def clockPoint (T j : ℕ) : ℝ := max 0 (min ((j : ℝ) - 1 / 2) T)

/-- `p_0 = 0`. -/
theorem clockPoint_zero (T : ℕ) : clockPoint T 0 = 0 := by
  unfold clockPoint
  exact max_eq_left (min_le_left _ _ |>.trans (by norm_num))

/-- `p_{T+1} = T`. -/
theorem clockPoint_last {T : ℕ} : clockPoint T (T + 1) = T := by
  unfold clockPoint
  rw [min_eq_right (by push_cast; linarith), max_eq_right (Nat.cast_nonneg T)]

/-- `p_j = j - 1/2` for `1 ≤ j ≤ T`. -/
theorem clockPoint_eq {T j : ℕ} (h1 : 1 ≤ j) (hjT : j ≤ T) :
    clockPoint T j = (j : ℝ) - 1 / 2 := by
  have h1' : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have hjT' : (j : ℝ) ≤ T := by exact_mod_cast hjT
  unfold clockPoint
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- `p_j ≤ p_{j+1}`. -/
theorem clockPoint_mono (T j : ℕ) : clockPoint T j ≤ clockPoint T (j + 1) := by
  unfold clockPoint
  exact max_le_max le_rfl (min_le_min (by push_cast; linarith) le_rfl)

/-- `0 ≤ p_j ≤ T`. -/
theorem clockPoint_mem (T j : ℕ) : clockPoint T j ∈ Icc (0 : ℝ) T := by
  unfold clockPoint
  exact ⟨le_max_left _ _, max_le (Nat.cast_nonneg T) (min_le_right _ _)⟩

/-- `j - 1/2 ≤ p_j` for `j ≤ T`. -/
theorem sub_half_le_clockPoint {T j : ℕ} (hj : j ≤ T) : (j : ℝ) - 1 / 2 ≤ clockPoint T j := by
  have hjT : (j : ℝ) ≤ T := by exact_mod_cast hj
  unfold clockPoint
  exact le_max_of_le_right (le_min le_rfl (by linarith))

/-- `p_{j+1} ≤ j + 1/2`. -/
theorem clockPoint_succ_le (T j : ℕ) : clockPoint T (j + 1) ≤ (j : ℝ) + 1 / 2 := by
  unfold clockPoint
  exact max_le (by positivity) (min_le_left _ _ |>.trans (by push_cast; linarith))

/-! ### Consequences of the hypotheses on `H` -/

/-- The bound `‖f(s) - f(s₀) - (s - s₀) f'(s₀)‖ ≤ (L/2)(s - s₀)²` for `s₀ ≤ s`, when `f'` is
`L`-Lipschitz on `[a,b]`. -/
theorem taylor_lipschitz_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
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

/-- If `f'` is `L`-Lipschitz on `[a,b]`, then for `s₀, s ∈ [a,b]`,
`‖f(s) - f(s₀) - (s - s₀) f'(s₀)‖ ≤ (L/2)(s - s₀)²`. The left side is the norm of
`∫_{s₀}^s (f'(σ) - f'(s₀)) dσ`, and the bound integrates `‖f'(σ) - f'(s₀)‖ ≤ L|σ - s₀|`. The
proofs of Theorems 4.2 and 4.4 use it in this form, without the integral. -/
theorem taylor_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {a b L : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hL : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f' x - f' y‖ ≤ L * |x - y|) {s₀ s : ℝ}
    (hs₀ : s₀ ∈ Icc a b) (hs : s ∈ Icc a b) :
    ‖f s - f s₀ - (s - s₀) • f' s₀‖ ≤ L / 2 * (s - s₀) ^ 2 := by
  rcases le_total s₀ s with hle | hle
  · exact taylor_lipschitz_of_le hf hL hs₀ hs hle
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
  have h := taylor_lipschitz_of_le hf' hL' (s₀ := -s₀) (s := -s)
    ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩ ⟨by linarith [hs.2], by linarith [hs.1]⟩
    (by linarith)
  simp only [neg_neg] at h
  convert h using 2
  · module
  · ring

/-- The width is nonnegative: `H(0)` has an eigenvalue, whose difference with itself is `0`. -/
theorem width_nonneg [NeZero d] {T : ℕ} {H : ℝ → 𝕄} (hH : IsTimeDepHamiltonian H) {w : ℝ}
    (hwidth : HasSampleWidth H T w) : 0 ≤ w := by
  have h0 := hwidth 0 (Nat.zero_le T)
  have hH0 : IsHermitian (H (((0 : ℕ) : ℝ) / T)) := @hH _ ⟨by simp, by simp⟩
  have hx := hH0.eigenvalues_mem_spectrum_real 0
  simpa using h0 _ hx _ hx

/-- `‖H'(s)‖ ≤ ‖H'‖∞` for `s ∈ [0,1]`; the supremum is finite as `H'` is Lipschitz. -/
theorem norm_deriv_le_supNorm {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖∂H s‖ ≤ ‖∂H‖∞ := by
  refine le_csSup ⟨‖∂H 0‖ + |L|, ?_⟩ (mem_image_of_mem (fun t ↦ ‖∂H t‖) hs)
  rintro y ⟨t, ht, rfl⟩
  have h := hL.2 t ht 0 (left_mem_Icc.2 zero_le_one)
  have h1 : L * |t - 0| ≤ |L| := by
    rw [sub_zero, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right (le_abs_self L) ht.1).trans
      (mul_le_of_le_one_right (abs_nonneg L) ht.2)
  have h2 := norm_sub_norm_le (∂H t) (∂H 0)
  dsimp only
  linarith

/-- The mean value bound `‖H(b) - H(a)‖ ≤ ‖H'‖∞ |b - a|` for `a, b ∈ [0,1]`. -/
theorem norm_sub_le_supNorm_mul {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖H b - H a‖ ≤ ‖∂H‖∞ * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_derivWithin_le hL.1 (fun _ hx ↦ norm_deriv_le_supNorm hL hx)
    (convex_Icc 0 1) ha hb

/-! ### The correction of Lemma A.1 at every sample -/

/-- Lemma A.1 at every sample. For `0 ≤ j ≤ T` there is `Z_j(τ)` for `|τ| ≤ 1/2` that solves
`Z_j' + i[H(j/T), Z_j] = τ H'(j/T)`, with end values `𝒩([H(j/T),·])H'(j/T)`,
`‖Z_j(0)‖ ≤ c₀ ‖H'(j/T)‖`, and `‖Z_j(τ)‖ ≤ ‖Z_j(0)‖ + τ² ‖H'(j/T)‖/2`. The correction of the proof
of Theorem 4.2 for `|t - j| < 1/2` is `Y(t) = Z_j(t - j)/T`, which solves (4.2) with
`Ω = H(j/T)` and `D = H'(j/T)/T`. -/
theorem exists_sample_corrections [NeZero d] {T : ℕ} {H : ℝ → 𝕄}
    (hH : IsTimeDepHamiltonian H) {w : ℝ} (hw : w < 2 * π) (hwidth : HasSampleWidth H T w) :
    ∃ Z : ℕ → ℝ → 𝕄,
      (∀ j ≤ T, ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), HasDerivWithinAt (Z j)
        (τ • ∂H (j / T) - I • (H (j / T) * Z j τ - Z j τ * H (j / T)))
        (Icc (-1 / 2) (1 / 2)) τ) ∧
      (∀ j ≤ T, Z j (-1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T))) ∧
      (∀ j ≤ T, Z j (1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T))) ∧
      (∀ j ≤ T, ‖Z j 0‖ ≤ c₀ w * ‖∂H (j / T)‖) ∧
      ∀ j ≤ T, ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        ‖Z j τ‖ ≤ ‖Z j 0‖ + τ ^ 2 * ‖∂H (j / T)‖ / 2 := by
  have hw0 : 0 ≤ w := width_nonneg hH hwidth
  have hcell : ∀ j : ℕ, ∃ Z : ℝ → 𝕄, j ≤ T →
      (∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), HasDerivWithinAt Z
        (τ • ∂H (j / T) - I • (H (j / T) * Z τ - Z τ * H (j / T))) (Icc (-1 / 2) (1 / 2)) τ) ∧
      Z (-1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T)) ∧ Z (1 / 2) = 𝒩ad (H (j / T)) (∂H (j / T)) ∧
      ‖Z 0‖ ≤ c₀ w * ‖∂H (j / T)‖ ∧
      ∀ τ ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖Z τ‖ ≤ ‖Z 0‖ + τ ^ 2 * ‖∂H (j / T)‖ / 2 := by
    intro j
    by_cases hj : j ≤ T
    · have hjs : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 :=
        unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T) (by exact_mod_cast hj)
      obtain ⟨Z, -, hZ⟩ := cell hw0 hw (@hH _ hjs) (hwidth j hj) (∂H (j / T))
      exact ⟨Z, fun _ ↦ hZ⟩
    · exact ⟨0, fun h ↦ absurd h hj⟩
  -- `choose` gives a `Z j` for every natural `j`; for `j > T` it is `0` and is never used.
  choose Z hZ using hcell
  exact ⟨Z, fun j hj ↦ (hZ j hj).1, fun j hj ↦ (hZ j hj).2.1, fun j hj ↦ (hZ j hj).2.2.1,
    fun j hj ↦ (hZ j hj).2.2.2.1, fun j hj ↦ (hZ j hj).2.2.2.2⟩

/-! ### The residual -/

/-- Equation (4.1) without its bracket: when `Y = cZ` and `Y' = c(τD - i[Ω,Z])`,
`K - Ω - Y' - i(KY - YΩ) = (K - Ω - cτ D) - i(K - Ω)Y`. In the proof of Theorem 4.2,
`K - Ω - cτD` is the term `∫_{⌊t+1/2⌋}^t (K'(σ) - K'(⌊t+1/2⌋)) dσ` of (4.1), written without the
integral. -/
theorem residual_eq (K Ω D Z : 𝕄) (c τ : ℝ) :
    K - Ω - c • (τ • D - I • (Ω * Z - Z * Ω)) - I • (K * (c • Z) - c • Z * Ω) =
      (K - Ω - (c * τ) • D) - I • ((K - Ω) * (c • Z)) := by
  simp only [sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc]
  module

/-- Second line of the residual display in the proof of Theorem 4.2. With `τ = t - j`, the
residual (4.1) without its bracket has norm at most
`Lτ²/(2T²) + (‖H'‖∞ |τ|/T) (c + τ²/2) ‖H'‖∞/T` when `‖Z‖ ≤ (c + τ²/2) ‖H'‖∞`. The first term
uses `‖K'(σ) - K'(j)‖ ≤ L|σ - j|/T²`, and the second uses `‖K(t) - K(j)‖ ≤ ‖H'‖∞ |τ|/T`. -/
theorem norm_residual_le {H : ℝ → 𝕄} {L : ℝ} (hL : HasLipschitzDerivative H L) {T t j c : ℝ}
    (hT : 0 < T) (hj : j / T ∈ Icc (0 : ℝ) 1) (ht : t / T ∈ Icc (0 : ℝ) 1) {Z : 𝕄}
    (hZ : ‖Z‖ ≤ (c + (t - j) ^ 2 / 2) * ‖∂H‖∞) :
    ‖H (t / T) - H (j / T) - (1 / T * (t - j)) • ∂H (j / T) -
        I • ((H (t / T) - H (j / T)) * ((1 / T : ℝ) • Z))‖ ≤
      1 / T ^ 2 * (L / 2 * (t - j) ^ 2 + ‖∂H‖∞ ^ 2 * |t - j| * (c + (t - j) ^ 2 / 2)) := by
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (∂H s) (Icc 0 1) s :=
    fun s hs ↦ (hL.1 s hs).hasDerivWithinAt
  have hS0 : 0 ≤ ‖∂H‖∞ := (norm_nonneg _).trans (norm_deriv_le_supNorm hL hj)
  -- `‖K'(σ) - K'(j)‖ ≤ L|σ - j|/T²`, integrated.
  have htaylor := taylor_lipschitz hderiv hL.2 hj ht
  rw [show t / T - j / T = 1 / T * (t - j) by ring] at htaylor
  -- `‖K(t) - K(j)‖ ≤ ‖H'‖∞ |τ|/T`.
  have hmvt := norm_sub_le_supNorm_mul hL hj ht
  rw [Real.norm_eq_abs, show t / T - j / T = (t - j) / T by ring, abs_div,
    abs_of_pos hT] at hmvt
  calc
    _ ≤ ‖H (t / T) - H (j / T) - (1 / T * (t - j)) • ∂H (j / T)‖ +
        ‖(H (t / T) - H (j / T)) * ((1 / T : ℝ) • Z)‖ := by
      refine (norm_sub_le _ _).trans_eq ?_
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ L / 2 * (1 / T * (t - j)) ^ 2 +
        ‖∂H‖∞ * |t - j| / T * (1 / T * ((c + (t - j) ^ 2 / 2) * ‖∂H‖∞)) := by
      refine add_le_add htaylor ((norm_mul_le _ _).trans ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hT)]
      exact mul_le_mul (hmvt.trans_eq (by ring))
        (mul_le_mul_of_nonneg_left hZ (one_div_pos.mpr hT).le)
        (mul_nonneg (one_div_pos.mpr hT).le (norm_nonneg _))
        (div_nonneg (mul_nonneg hS0 (abs_nonneg _)) hT.le)
    _ = _ := by field_simp

/-- A continuous `g` of `τ = t - ⌊t + 1/2⌋` is interval integrable in `t`. -/
theorem intervalIntegrable_round (g : ℝ → ℝ) (hg : Continuous g) (t₁ t₂ : ℝ) :
    IntervalIntegrable (fun t ↦ g (t - ⌊t + 1 / 2⌋)) volume t₁ t₂ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hg.continuousOn
  have hmeas : Measurable fun t : ℝ ↦ g (t - ⌊t + 1 / 2⌋) := by
    apply hg.measurable.comp
    exact measurable_id.sub ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.add_const _)))
  refine (intervalIntegrable_const (c := C)).mono_fun' hmeas.aestronglyMeasurable ?_
  exact Eventually.of_forall fun t ↦ hC _ (sub_round_mem_Icc t)

/-- Third line of the residual display in the proof of Theorem 4.2: a continuous even `g` of
`τ = t - ⌊t + 1/2⌋` integrates over `t ∈ [0,n]` to `n` times its integral over `τ ∈ [-1/2,1/2]`,
as `τ` runs over `[-1/2,1/2)` when `t` runs over each `[k,k+1)`. -/
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
  · -- At the single point `x = 1/2` the rounded clock is `1`, and `g(-1/2) = g(1/2)`.
    subst heq
    simp only [hρ]
    norm_num
    rw [← heven]
    norm_num

/-- Fourth line of the residual display in the proof of Theorem 4.2:
`∫_{-1/2}^{1/2} ((L/2)τ² + S²|τ|(c + τ²/2)) dτ = L/24 + S²(c/4 + 1/64)`,
from `∫_{-1/2}^{1/2} (τ², |τ|, |τ|³) dτ = (1/12, 1/4, 1/32)`. -/
theorem integral_residual_bound (L S c : ℝ) :
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

end RoundedClocks
