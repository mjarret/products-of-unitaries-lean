/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.PartitionIndependent

/-!
# Evolutions of regulated families

## Declarations

- `aestronglyMeasurable`
- `countable_not_continuousWithinAt`
- `exists_norm_le`
- `intervalIntegrable`
- `checkpoint_or_mem_piece`
- `evolution_eq_of_solves_off_countable`
- `exists_approximate_evolution_of_regulated`
- `exists_evolution_of_regulated`
- `exists_integral_evolution_of_regulated`
- `exists_uniform_limit_of_regulated`
- `hasDerivWithinAt_integral_evolution`
- `intervalIntegrable_of_hasDerivAt_off_countable`
- `norm_sub_evolutions_le`
- `piece_index_unique`
- `regulatedEvolution`
- `regulatedEvolution_hasDerivWithinAt`
- `star_mul_self_of_solves_off_countable`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set Filter MeasureTheory
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A point of $[0, t_n]$ is either a switch time $t_j$ or lies inside an open piece
$(t_j, t_{j+1})$. -/
theorem checkpoint_or_mem_piece {τ : ℕ → ℝ} (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (switchTime τ n)) :
    (∃ j ≤ n, t = switchTime τ j) ∨
      ∃ j < n, t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)) := by
  induction n with
  | zero => exact Or.inl ⟨0, le_rfl, le_antisymm ht.2 (by simpa using ht.1)⟩
  | succ n ih =>
    rcases le_or_gt t (switchTime τ n) with hle | hgt
    · rcases ih ⟨ht.1, hle⟩ with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
      · exact Or.inl ⟨j, hj.trans (Nat.le_succ n), he⟩
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, he⟩
    · rcases ht.2.eq_or_lt with he | hlt
      · exact Or.inl ⟨n + 1, le_rfl, he⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hgt, hlt⟩

namespace Regulated

/-- A regulated family on $[0,T]$ is bounded (§2, after Definition 2.1), including at the switch
times of its step-function approximation. -/
theorem exists_norm_le {H : ℝ → 𝕄} {T : ℝ}
    (hreg : Regulated H 0 T) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ‖H t‖ ≤ B := by
  obtain ⟨m, τ, c, hτ, hsw, hc, happ⟩ := exists_pieces_of_regulated hT hreg zero_lt_one
  let B := 1 + (∑ j ∈ Finset.range (m + 1), ‖H (switchTime τ j)‖) +
    ∑ j ∈ Finset.range m, ‖H (c j)‖
  have hs₁ : 0 ≤ ∑ j ∈ Finset.range (m + 1), ‖H (switchTime τ j)‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hs₂ : 0 ≤ ∑ j ∈ Finset.range m, ‖H (c j)‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  refine ⟨B, by dsimp [B]; linarith, fun t ht ↦ ?_⟩
  rcases checkpoint_or_mem_piece (τ := τ) (t := t) m (by simpa only [hsw] using ht) with
    ⟨j, hj, rfl⟩ | ⟨j, hj, htj⟩
  · dsimp [B]
    linarith [Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) ↦
      norm_nonneg (H (switchTime τ i))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
  · have hb := Finset.single_le_sum (fun i (_ : i ∈ Finset.range m) ↦
        norm_nonneg (H (c i))) (Finset.mem_range.mpr hj)
    have hn : ‖H t‖ ≤ ‖H t - H (c j)‖ + ‖H (c j)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (H t - H (c j)) (H (c j))
    dsimp [B]
    linarith [happ j hj t htj]

end Regulated

/-- Open pieces of a partition with nonnegative durations are disjoint, so a point lies in at most
one of them. -/
theorem piece_index_unique {τ : ℕ → ℝ} (hτ : ∀ j, 0 ≤ τ j) {j k : ℕ} {t : ℝ}
    (hj : t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)))
    (hk : t ∈ Ioo (switchTime τ k) (switchTime τ (k + 1))) : j = k :=
  le_antisymm (not_lt.mp fun hgt ↦ absurd (hj.1.trans hk.2)
      (not_lt_of_ge (switchTime_mono hτ (Nat.succ_le_of_lt hgt))))
    (not_lt.mp fun hlt ↦ absurd (hk.1.trans hj.2)
      (not_lt_of_ge (switchTime_mono hτ (Nat.succ_le_of_lt hlt))))

/-- Existence, step (a): a step function $K$ within $\varepsilon$ of $H$ on $[0,T]$, with a
continuous contraction $U$ solving $iU' = KU$ off a finite set. $K$ holds a sample of $H$ on each
open piece and agrees with $H$ at the switch times, so the error bound holds everywhere. -/
theorem exists_approximate_evolution_of_regulated {H : ℝ → 𝕄} {T ε : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) (hε : 0 < ε) :
    ∃ (K U : ℝ → 𝕄) (S : Finset ℝ),
      (∀ t ∈ Icc 0 T, (K t).IsHermitian) ∧
      (∀ t ∈ Icc 0 T, ‖H t - K t‖ ≤ ε) ∧
      Continuous U ∧ U 0 = 1 ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ 1) ∧
      ∀ t ∈ Icc 0 T, t ∉ S → HasDerivAt U (-I • (K t * U t)) t := by
  classical
  obtain ⟨m, τ, c, hτ, hsw, hc, he⟩ := exists_pieces_of_regulated hT hreg hε
  let P := fun t j ↦ j < m ∧ t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1))
  -- K holds H(c_j) on the open piece j, found by `h.choose`; `piece_index_unique` shows that the
  -- index is determined, so K is a well-defined step function.
  let K : ℝ → 𝕄 := fun t ↦ if h : ∃ j, P t j then H (c h.choose) else H t
  have hKpiece : ∀ j < m, ∀ t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)),
      K t = H (c j) := by
    intro j hj t ht
    have hp : ∃ i, P t i := ⟨j, hj, ht⟩
    have hi : hp.choose = j := piece_index_unique (fun i ↦ (hτ i).le) hp.choose_spec.2 ht
    simp only [K, dif_pos hp, hi]
  have hK : ∀ t ∈ Icc 0 T, (K t).IsHermitian ∧ ‖H t - K t‖ ≤ ε := fun t ht ↦ by
    by_cases hp : ∃ j, P t j
    · rw [show K t = H (c hp.choose) from dif_pos hp]
      exact ⟨hH _ (hc _ hp.choose_spec.1), he _ hp.choose_spec.1 t hp.choose_spec.2⟩
    · rw [show K t = H t from dif_neg hp, sub_self, norm_zero]
      exact ⟨hH t ht, hε.le⟩
  -- The glued evolution of the step function K, a contraction because K is Hermitian.
  obtain ⟨U, S, hUc, hU0, _, hd⟩ := exists_piecewise_evolution hτ m hKpiece
  have hdT : ∀ t ∈ Icc 0 T, t ∉ S → HasDerivAt U (-I • (K t * U t)) t := by
    simpa only [hsw] using hd
  refine ⟨K, U, S, fun t ht ↦ (hK t ht).1, fun t ht ↦ (hK t ht).2, hUc, hU0, ?_, hdT⟩
  exact norm_le_one_of_hermitian_off_countable (S : Set ℝ) S.countable_toSet
    (fun t ht _ ↦ (hK t ht).1)
    hUc.continuousOn (fun t ht hn ↦ (hdT t ht hn).hasDerivWithinAt)
    (by rw [hU0]; exact norm_le_one_of_star_mul_self (by simp))

namespace Regulated

/-- The discontinuities of a regulated matrix family form a countable set.
Endpoints are included in the exceptional set, so this also bounds the set of
failures of relative continuity on the closed interval. -/
theorem countable_not_continuousWithinAt {H : ℝ → 𝕄} {T : ℝ}
    (hreg : Regulated H 0 T) (hT : 0 ≤ T) :
    {t ∈ Icc 0 T | ¬ ContinuousWithinAt H (Icc 0 T) t}.Countable := by
  classical
  choose m τ c hτ hsw hc he using fun n : ℕ ↦
    exists_pieces_of_regulated hT hreg (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
  let S : Set ℝ := ⋃ n : ℕ, Set.range (switchTime (τ n))
  have hS : S.Countable := Set.countable_iUnion (fun _ ↦ Set.countable_range _)
  refine hS.mono fun t ht ↦ Classical.byContradiction fun hn ↦ ht.2
    (ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.mpr fun ε hε ↦ ?_))
  obtain ⟨n, hnε⟩ := exists_nat_one_div_lt (half_pos hε)
  have hno : ∀ j, t ≠ switchTime (τ n) j := fun j hj ↦ hn (Set.mem_iUnion.mpr ⟨n, j, hj.symm⟩)
  obtain ⟨j, hj, htj⟩ := (checkpoint_or_mem_piece (τ := τ n) (t := t) (m n)
    (by simpa only [hsw] using ht.1)).resolve_left fun ⟨j, _, heq⟩ ↦ hno j heq
  filter_upwards [Ioo_mem_nhds htj.1 htj.2] with x hx
  rw [dist_eq_norm]
  linarith [he n j hj x hx, he n j hj t htj, norm_sub_rev (H (c n j)) (H t),
    norm_sub_le_norm_sub_add_norm_sub (H x) (H (c n j)) (H t)]

/-- Regulated families are almost everywhere strongly measurable on their interval. -/
theorem aestronglyMeasurable {H : ℝ → 𝕄} {T : ℝ}
    (hreg : Regulated H 0 T) (hT : 0 ≤ T) :
    AEStronglyMeasurable H (volume.restrict (Icc 0 T)) := by
  let S := {t ∈ Icc 0 T | ¬ ContinuousWithinAt H (Icc 0 T) t}
  have hS : S.Countable := hreg.countable_not_continuousWithinAt hT
  have hc : ContinuousOn H (Icc 0 T \ S) := fun x hx ↦
    ContinuousWithinAt.mono (not_not.mp fun hn ↦ hx.2 ⟨hx.1, hn⟩) Set.diff_subset
  have hm := hc.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff hS.measurableSet)
  rwa [Measure.restrict_congr_set (diff_null_ae_eq_self (hS.measure_zero volume))] at hm

/-- A regulated family is Bochner integrable on its compact interval. -/
theorem intervalIntegrable {H : ℝ → 𝕄} {T : ℝ}
    (hreg : Regulated H 0 T) (hT : 0 ≤ T) :
    IntervalIntegrable H volume 0 T := by
  obtain ⟨B, _, hB⟩ := hreg.exists_norm_le hT
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  exact Integrable.of_bound (hreg.aestronglyMeasurable hT) B
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hB t ht)

end Regulated

/-- A bounded derivative specified outside a countable set is integrable. -/
theorem intervalIntegrable_of_hasDerivAt_off_countable {U F : ℝ → 𝕄} {T B : ℝ}
    (hT : 0 ≤ T) (S : Set ℝ) (hS : S.Countable)
    (hF : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivAt U (F t) t)
    (hB : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ B) : IntervalIntegrable F volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  have he : (fun t ↦ deriv U t) =ᵐ[volume.restrict (Icc 0 T)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      (hS.insert 0 |>.insert T).ae_notMem (volume.restrict (Icc 0 T))] with t ht hn
    exact (hF t ⟨lt_of_le_of_ne ht.1 fun hh ↦ hn (Or.inr (Or.inl hh.symm)),
      lt_of_le_of_ne ht.2 fun hh ↦ hn (Or.inl hh)⟩ fun hh ↦ hn (Or.inr (Or.inr hh))).deriv
  exact Integrable.of_bound ((stronglyMeasurable_deriv U).aestronglyMeasurable.congr he) B
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hB t ht)

/-- **Stability estimate.** Continuous solutions of $iU' = HU$ and $iV' = KV$ from $1$, with $H$,
$K$ Hermitian and $\|H - K\| \le \eta$ off the countable exceptional sets, satisfy
$\|U(t) - V(t)\| \le \eta t$ on $[0,T]$. It gives uniqueness ($K = H$, $\eta = 0$) and the Cauchy
step of existence. -/
theorem norm_sub_evolutions_le {H K U V : ℝ → 𝕄} {T η : ℝ}
    (S R : Set ℝ) (hS : S.Countable) (hR : R.Countable)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hK : ∀ t ∈ Icc 0 T, (K t).IsHermitian)
    (hUc : ContinuousOn U (Icc 0 T)) (hVc : ContinuousOn V (Icc 0 T))
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Ioo 0 T, t ∉ R → HasDerivWithinAt V (-I • (K t * V t)) (Icc 0 T) t)
    (hη : ∀ t ∈ Icc 0 T, t ∉ S ∪ R → ‖H t - K t‖ ≤ η) :
    ∀ t ∈ Icc 0 T, ‖U t - V t‖ ≤ η * t := by
  intro t ht
  -- Restrict to [0, t] and collect the endpoints and both exceptional sets into one countable E.
  let E : Set ℝ := insert 0 (insert T (S ∪ R))
  have hE : E.Countable := (hS.union hR).insert T |>.insert 0
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hmem : ∀ x ∈ Icc 0 t, x ∉ E → x ∈ Ioo 0 T ∧ x ∉ S ∪ R := fun x hx hn ↦ by
    simp only [E, Set.mem_insert_iff, Set.mem_union, not_or] at hn
    exact ⟨⟨lt_of_le_of_ne hx.1 (Ne.symm hn.1), lt_of_le_of_ne (hsub hx).2 hn.2.1⟩,
      not_or.mpr hn.2.2⟩
  -- The energy estimate off E, started from the contraction U(0) = 1.
  have hb := norm_sub_le_of_norm_sub_le_off_countable E hE ht.1
    (fun x hx _ ↦ hH x (hsub hx)) (fun x hx _ ↦ hK x (hsub hx))
    (hUc.mono hsub) (hVc.mono hsub)
    (fun x hx hn ↦ (hU x (hmem x hx hn).1
      (fun he ↦ (hmem x hx hn).2 (Or.inl he))).mono hsub)
    (fun x hx hn ↦ (hV x (hmem x hx hn).1
      (fun he ↦ (hmem x hx hn).2 (Or.inr he))).mono hsub)
    (by rw [hU0]; exact norm_le_one_of_star_mul_self (by simp))
    (fun x hx hn ↦ hη x (hsub hx) (hmem x hx hn).2)
  simpa only [hU0, hV0, sub_self, norm_zero, zero_add, sub_zero] using hb

/-- Supports the uniqueness half of the existence-and-uniqueness claim of §2.1 ("by that
uniqueness, only $V$"): two
continuous solutions of $iU' = HU$ from $1$, each off its own countable set, agree on $[0,T]$.

Reading the statement against the paper:
* The two candidates need not be unitary: only continuity on $[0,T]$, $U(0) = V(0) = 1$, and the
  equation on $(0,T)$ outside the countable sets `S`, `R`, one-sided within $[0,T]$, are assumed.
* $H$ is only assumed Hermitian on $[0,T]$, with no regularity: this is stronger than the
  uniqueness that §2.1 needs.

The proof takes a different route from the paper's, which cites Dieudonné's uniqueness theorem for
linear equations: (1) `norm_sub_evolutions_le` with $K = H$ and $\eta = 0$ gives
$\|U(t) - V(t)\| \le 0$; (2) behind it, for each vector $v$, $y = (U - V)v$ has
$\operatorname{Re}\langle y, -iHy\rangle = 0$ because $H$ is Hermitian, and a mean-value inequality
off a countable set bounds $\|y\|$ (`norm_sub_le_of_norm_sub_le_off_countable`). -/
theorem evolution_eq_of_solves_off_countable {H U V : ℝ → 𝕄} {T : ℝ}
    (S R : Set ℝ) (hS : S.Countable) (hR : R.Countable)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hUc : ContinuousOn U (Icc 0 T)) (hVc : ContinuousOn V (Icc 0 T))
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t)
    (hV : ∀ t ∈ Ioo 0 T, t ∉ R → HasDerivWithinAt V (-I • (H t * V t)) (Icc 0 T) t) :
    Set.EqOn U V (Icc 0 T) := fun t ht ↦ by
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using
    norm_sub_evolutions_le (η := 0) S R hS hR hH hH hUc hVc hU0 hV0 hU hV
      (fun _ _ _ ↦ by rw [sub_self, norm_zero]) t ht

/-- Existence, step (b): the evolutions $U_n$ of step functions $K_n$ within $1/(n+1)$ of $H$
converge uniformly on $[0,T]$ to a continuous contraction $V$ with $V(0) = 1$. This is only the
limit stage; the differential equation is not asserted here. -/
theorem exists_uniform_limit_of_regulated {H : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) :
    ∃ (K U : ℕ → ℝ → 𝕄) (S : ℕ → Finset ℝ) (V : ℝ → 𝕄),
      (∀ n, (∀ t ∈ Icc 0 T, (K n t).IsHermitian) ∧
        (∀ t ∈ Icc 0 T, ‖H t - K n t‖ ≤ 1 / ((n : ℝ) + 1)) ∧
        Continuous (U n) ∧ U n 0 = 1 ∧ (∀ t ∈ Icc 0 T, ‖U n t‖ ≤ 1) ∧
        ∀ t ∈ Icc 0 T, t ∉ S n → HasDerivAt (U n) (-I • (K n t * U n t)) t) ∧
      TendstoUniformlyOn U V atTop (Icc 0 T) ∧ ContinuousOn V (Icc 0 T) ∧
      V 0 = 1 ∧ ∀ t ∈ Icc 0 T, ‖V t‖ ≤ 1 := by
  classical
  have hex := fun n : ℕ ↦ exists_approximate_evolution_of_regulated hT hreg hH
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose K U S hKh hKe hUc hU0 hUb hUd using hex
  -- Step 1: by the stability estimate, ‖U_n(t) - U_m(t)‖ ≤ (1/(n+1) + 1/(m+1)) t.
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Antitone e := fun n m hnm ↦
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
  have hpair : ∀ n m t, t ∈ Icc 0 T → ‖U n t - U m t‖ ≤ (e n + e m) * t := by
    intro n m t ht
    exact norm_sub_evolutions_le (S n : Set ℝ) (S m : Set ℝ)
      (S n).countable_toSet (S m).countable_toSet (hKh n) (hKh m)
      (hUc n).continuousOn (hUc m).continuousOn (hU0 n) (hU0 m)
      (fun x hx hn ↦ (hUd n x (Ioo_subset_Icc_self hx) hn).hasDerivWithinAt)
      (fun x hx hn ↦ (hUd m x (Ioo_subset_Icc_self hx) hn).hasDerivWithinAt)
      (fun x hx _ ↦ (norm_sub_le_norm_sub_add_norm_sub _ (H x) _).trans
        (add_le_add ((norm_sub_rev _ _).le.trans (hKe n x hx)) (hKe m x hx))) t ht
  -- Step 2: so (U_n) is uniformly Cauchy on [0, T] and converges pointwise to some V.
  let b := fun n ↦ (e n + e n) * T
  have hb0 : Tendsto b atTop (𝓝 0) := by
    simpa only [zero_add, zero_mul] using (tendsto_one_div_add_atTop_nhds_zero_nat.add
      tendsto_one_div_add_atTop_nhds_zero_nat).mul_const T
  have hb : ∀ n m N, N ≤ n → N ≤ m → ∀ t ∈ Icc 0 T, dist (U n t) (U m t) ≤ b N :=
    fun n m N hn hm t ht ↦ (dist_eq_norm _ _).trans_le ((hpair n m t ht).trans (mul_le_mul
      (add_le_add (he hn) (he hm)) ht.2 ht.1
      (add_nonneg (by dsimp [e]; positivity) (by dsimp [e]; positivity))))
  have hC : UniformCauchySeqOn U atTop (Icc 0 T) := by
    refine Metric.uniformCauchySeqOn_iff.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hb0.eventually (gt_mem_nhds hε))
    exact ⟨N, fun n hn m hm t ht ↦ (hb n m N hn hm t ht).trans_lt (hN N le_rfl)⟩
  have hpoint : ∀ t ∈ Icc 0 T, ∃ v, Tendsto (fun n ↦ U n t) atTop (𝓝 v) := fun t ht ↦
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0 b
      (fun n m N hn hm ↦ hb n m N hn hm t ht) hb0)
  choose! V hV using hpoint
  -- Step 3: the convergence is uniform, so V is continuous, V(0) = 1 and ‖V‖ ≤ 1.
  have hconv := hC.tendstoUniformlyOn_of_tendsto hV
  refine ⟨K, U, S, V, fun n ↦ ⟨hKh n, hKe n, hUc n, hU0 n, hUb n, hUd n⟩,
    hconv, hconv.continuousOn (Filter.Eventually.of_forall fun n ↦ (hUc
      n).continuousOn).frequently, ?_, ?_⟩
  · exact tendsto_nhds_unique (hV 0 ⟨le_rfl, hT⟩) (tendsto_const_nhds.congr fun n ↦ (hU0 n).symm)
  · exact fun t ht ↦ le_of_tendsto (hV t ht).norm (Filter.Eventually.of_forall fun n ↦ hUb n t ht)

/-- Existence, step (c): the uniform limit $V$ satisfies the integral equation
$\int_0^t -iH V = V(t) - 1$ for every $t \in [0,T]$. -/
theorem exists_integral_evolution_of_regulated {H : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) :
    ∃ V : ℝ → 𝕄, ContinuousOn V (Icc 0 T) ∧ V 0 = 1 ∧
      (∀ t ∈ Icc 0 T, ‖V t‖ ≤ 1) ∧
      ∀ t ∈ Icc 0 T, (∫ x in 0..t, -I • (H x * V x)) = V t - 1 := by
  obtain ⟨K, U, S, V, hdata, hconv, hVc, hV0, hVb⟩ :=
    exists_uniform_limit_of_regulated hT hreg hH
  obtain ⟨B, hB0, hB⟩ := hreg.exists_norm_le hT
  -- Step 1: the integrands F_n = -iK_nU_n are bounded by B + 1, with B a bound for H, and
  -- converge pointwise to -iHV.
  let F := fun n t ↦ -I • (K n t * U n t)
  have hFb : ∀ n t, t ∈ Icc 0 T → ‖F n t‖ ≤ B + 1 := by
    intro n t ht
    have he1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hKb : ‖K n t‖ ≤ B + 1 := by
      linarith [norm_sub_norm_le (K n t) (H t), norm_sub_rev (K n t) (H t), (hdata n).2.1 t ht,
        hB t ht]
    simp only [F, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact (norm_mul_le_of_le hKb ((hdata n).2.2.2.2.1 t ht)).trans_eq (mul_one _)
  have hKd : ∀ t ∈ Icc 0 T, Tendsto (fun n ↦ K n t) atTop (𝓝 (H t)) := fun t ht ↦
    tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n ↦ norm_nonneg _)
      (fun n ↦ (norm_sub_rev _ _).le.trans ((hdata n).2.1 t ht))
      tendsto_one_div_add_atTop_nhds_zero_nat)
  refine ⟨V, hVc, hV0, hVb, ?_⟩
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hFi : ∀ n, IntervalIntegrable (F n) volume 0 t := fun n ↦
    intervalIntegrable_of_hasDerivAt_off_countable ht.1 (S n : Set ℝ)
      (S n).countable_toSet
      (fun x hx hn ↦ (hdata n).2.2.2.2.2 x (hsub (Ioo_subset_Icc_self hx)) hn)
      (fun x hx ↦ hFb n x (hsub hx))
  -- Step 2: each U_n satisfies its integral equation, by the fundamental theorem of calculus off
  -- its finite exceptional set.
  have hint : ∀ n, (∫ x in 0..t, F n x) = U n t - 1 := fun n ↦ by
    simpa only [(hdata n).2.2.2.1] using integral_eq_of_hasDerivAt_off_countable_of_le (U n) (F n)
      ht.1 (S n).countable_toSet (hdata n).2.2.1.continuousOn
      (fun x hx ↦ (hdata n).2.2.2.2.2 x (hsub (Ioo_subset_Icc_self hx.1)) hx.2) (hFi n)
  -- Step 3: dominated convergence passes the integrals to the limit; the right sides converge to
  -- V(t) - 1, and limits are unique.
  have hlim : Tendsto (fun n ↦ ∫ x in 0..t, F n x) atTop
      (𝓝 (∫ x in 0..t, -I • (H x * V x))) := by
    simp only [intervalIntegral.integral_of_le ht.1]
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ ↦ B + 1)
      (fun n ↦ (hFi n).1.aestronglyMeasurable) (integrable_const _)
    · exact fun n ↦ (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦
        hFb n x (hsub ⟨hx.1.le, hx.2⟩)
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ ((hKd x (hsub ⟨hx.1.le, hx.2⟩)).mul
        (hconv.tendsto_at (hsub ⟨hx.1.le, hx.2⟩))).const_smul (-I)
  have hlim' : Tendsto (fun n ↦ ∫ x in 0..t, F n x) atTop (𝓝 (V t - 1)) := by
    simpa only [hint] using (hconv.tendsto_at ht).sub_const 1
  exact tendsto_nhds_unique hlim hlim'

/-- Existence, step (d): a solution of the integral equation solves $iV' = HV$, relative to
$[0,T]$ (so one-sided at the ends), at every point where $H$ is continuous relative to $[0,T]$. -/
theorem hasDerivWithinAt_integral_evolution {H V : ℝ → 𝕄} {T : ℝ}
    (hreg : Regulated H 0 T)
    (hVc : ContinuousOn V (Icc 0 T))
    (hint : ∀ t ∈ Icc 0 T, (∫ x in 0..t, -I • (H x * V x)) = V t - 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hHt : ContinuousWithinAt H (Icc 0 T) t) :
    HasDerivWithinAt V (-I • (H t * V t)) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  let F := fun x ↦ -I • (H x * V x)
  -- This `Fact` lets Mathlib's instance `intervalIntegral.FTCFilter.nhdsIcc` treat 𝓝[Icc 0 T] t
  -- as a filter for the fundamental theorem of calculus.
  letI : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hd := (intervalIntegral.integral_hasDerivWithinAt_right (f := F) (s := Icc 0 T)
    ((((hreg.intervalIntegrable hT).mul_continuousOn (by rwa [uIcc_of_le hT])).smul (-I)).mono_set
      (by rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))
    ⟨Icc 0 T, self_mem_nhdsWithin, ((hreg.aestronglyMeasurable hT).mul
      (hVc.aestronglyMeasurable measurableSet_Icc)).const_smul (-I)⟩
    ((hHt.mul (hVc t ht)).const_smul (-I))).add_const 1
  exact hd.congr (fun x hx ↦ sub_eq_iff_eq_add.mp (hint x hx).symm)
    (sub_eq_iff_eq_add.mp (hint t ht).symm)

/-- Existence, step (e), as in the paper's argument for the existence-and-uniqueness claim of
§2.1: off a countable set
$(U^\dagger U)' = 0$ because $H$ is Hermitian, so $U^\dagger U = 1$ on $[0,T]$. -/
theorem star_mul_self_of_solves_off_countable {H U : ℝ → 𝕄} {T : ℝ}
    (S : Set ℝ) (hS : S.Countable)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hUc : ContinuousOn U (Icc 0 T)) (hU0 : U 0 = 1)
    (hU : ∀ t ∈ Ioo 0 T, t ∉ S → HasDerivAt U (-I • (H t * U t)) t) :
    ∀ t ∈ Icc 0 T, star (U t) * U t = 1 := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hd : ∀ x ∈ Ioo 0 t \ S,
      HasDerivAt (fun y ↦ star (U y) * U y) (0 : 𝕄) x := by
    intro x hx
    have hh := hU x ⟨hx.1.1, hx.1.2.trans_le ht.2⟩ hx.2
    convert hh.star.mul hh using 1
    simp only [star_neg, star_smul, star_mul, show star (H x) = H x from
      (hH x (hsub (Ioo_subset_Icc_self hx.1))).eq, Complex.star_def, conj_I, neg_neg,
      smul_mul_assoc, mul_smul_comm, mul_assoc, neg_smul, mul_neg, add_neg_cancel]
  have hh := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun y ↦ star (U y) * U y) (fun _ ↦ (0 : 𝕄)) ht.1 hS
    ((hUc.mono hsub).star.mul (hUc.mono hsub)) hd (intervalIntegrable_const)
  exact sub_eq_zero.mp (by
    simpa only [intervalIntegral.integral_zero, hU0, star_one, one_mul] using hh.symm)

/-- Existence in the existence-and-uniqueness claim of §2.1: every regulated Hermitian family on
$[0,T]$ has a continuous
unitary evolution from $1$, satisfying the integral equation, and the equation $iU' = HU$ at every
interior point where $H$ is continuous relative to $[0,T]$; the other points are countable
(`Regulated.countable_not_continuousWithinAt`). -/
theorem exists_evolution_of_regulated {H : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) :
    ∃ U : ℝ → 𝕄, ContinuousOn U (Icc 0 T) ∧ U 0 = 1 ∧
      (∀ t ∈ Icc 0 T, star (U t) * U t = 1 ∧ U t * star (U t) = 1) ∧
      (∀ t ∈ Icc 0 T, (∫ x in 0..t, -I • (H x * U x)) = U t - 1) ∧
      ∀ t ∈ Ioo 0 T, ContinuousWithinAt H (Icc 0 T) t →
        HasDerivAt U (-I • (H t * U t)) t := by
  obtain ⟨U, hc, h0, _, hi⟩ := exists_integral_evolution_of_regulated hT hreg hH
  have hd : ∀ t ∈ Ioo 0 T, ContinuousWithinAt H (Icc 0 T) t →
      HasDerivAt U (-I • (H t * U t)) t := fun t ht hh ↦
    (hasDerivWithinAt_integral_evolution hreg hc hi (Ioo_subset_Icc_self ht) hh).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  let S := {t ∈ Icc 0 T | ¬ ContinuousWithinAt H (Icc 0 T) t}
  have hS : S.Countable := hreg.countable_not_continuousWithinAt hT
  have hu := star_mul_self_of_solves_off_countable S hS hH hc h0
    (fun t ht hn ↦ hd t ht (not_not.mp fun hh ↦ hn ⟨Ioo_subset_Icc_self ht, hh⟩))
  exact ⟨U, hc, h0, fun t ht ↦ ⟨hu t ht, mul_eq_one_comm.mp (hu t ht)⟩, hi, hd⟩

/-- The evolution $U$ generated by a regulated Hermitian $H$ on $[0,T]$ (the
existence-and-uniqueness claim of §2.1), chosen
with `Exists.choose` from `exists_evolution_of_regulated`. The choice is determined on $[0,T]$:
every $V$ that $H$ generates agrees with it there, by the uniqueness clause of
`Paper.regulated_evolution` (the existence-and-uniqueness claim of §2.1 as
`Paper.exists_unique_evolution`), or directly by
`evolution_eq_of_solves_off_countable`.
Outside $[0,T]$ the definition says nothing about its values. -/
noncomputable def regulatedEvolution {H : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) : ℝ → 𝕄 :=
  (exists_evolution_of_regulated hT hreg hH).choose

/-- `regulatedEvolution` solves $iU' = HU$ at every point where $H$ is continuous relative to
$[0,T]$, one-sided at the endpoints. -/
theorem regulatedEvolution_hasDerivWithinAt {H : ℝ → 𝕄} {T : ℝ}
    (hT : 0 ≤ T) (hreg : Regulated H 0 T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hc : ContinuousWithinAt H (Icc 0 T) t) :
    HasDerivWithinAt (regulatedEvolution hT hreg hH)
      (-I • (H t * regulatedEvolution hT hreg hH t)) (Icc 0 T) t :=
  hasDerivWithinAt_integral_evolution hreg (exists_evolution_of_regulated hT hreg hH).choose_spec.1
    (exists_evolution_of_regulated hT hreg hH).choose_spec.2.2.2.1 ht hc

end UnitaryProducts
