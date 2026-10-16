/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.LevelPartitions
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Walks.LogarithmSmoothness

/-!
# Regulated families

## Declarations

- `Regulated`
- `exists_local_osc_of_regulated`
- `exists_pieces_of_regulated`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator Topology
open Complex Set Filter MeasureTheory

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Regulated family** (Definition 2.1; `Paper.IsRegulated` is this predicate). $H$ has a right
limit at every point of $[a,b)$ and a left limit at every point of $(a,b]$. The limits are in the
operator-norm topology, which is the topology of every norm on matrices. Hermiticity is not part of
the definition; every use assumes it separately. For $b \le a$ both conditions hold vacuously. -/
def Regulated (H : ℝ → 𝕄) (a b : ℝ) : Prop :=
  (∀ t ∈ Ico a b, ∃ L, Tendsto H (𝓝[>] t) (𝓝 L)) ∧
    (∀ t ∈ Ioc a b, ∃ L, Tendsto H (𝓝[<] t) (𝓝 L))

/-- Near a point of $[0,T]$, a regulated family oscillates by at most $\varepsilon$ on a one-sided
neighbourhood on each side where a one-sided limit exists. -/
theorem exists_local_osc_of_regulated {H : ℝ → 𝕄} {T : ℝ} (hH : Regulated H 0 T) {ε : ℝ}
    (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ δ > 0, (t < T → ∀ x ∈ Ioo t (t + δ), ∀ y ∈ Ioo t (t + δ), ‖H x - H y‖ ≤ ε) ∧
      (0 < t → ∀ x ∈ Ioo (t - δ) t, ∀ y ∈ Ioo (t - δ) t, ‖H x - H y‖ ≤ ε) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  have hclose : ∀ (L : 𝕄) (x y : ℝ), dist (H x) L < ε / 2 → dist (H y) L < ε / 2 →
      ‖H x - H y‖ ≤ ε := fun L x y hx hy ↦ by
    rw [← dist_eq_norm]; linarith [dist_triangle_right (H x) (H y) L]
  obtain ⟨δ₁, hδ₁, hR⟩ : ∃ δ > 0,
      t < T → ∀ x ∈ Ioo t (t + δ), ∀ y ∈ Ioo t (t + δ), ‖H x - H y‖ ≤ ε := by
    by_cases htT : t < T
    · obtain ⟨L, hL⟩ := hH.1 t ⟨ht.1, htT⟩
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
        (hL (Metric.ball_mem_nhds L hε2))
      refine ⟨u - t, sub_pos.mpr hu, fun _ x hx y hy ↦ hclose L x y ?_ ?_⟩
      exacts [hsub (by simpa using hx), hsub (by simpa using hy)]
    · exact ⟨1, one_pos, fun h ↦ absurd h htT⟩
  obtain ⟨δ₂, hδ₂, hL⟩ : ∃ δ > 0,
      0 < t → ∀ x ∈ Ioo (t - δ) t, ∀ y ∈ Ioo (t - δ) t, ‖H x - H y‖ ≤ ε := by
    by_cases ht0 : 0 < t
    · obtain ⟨L, hL⟩ := hH.2 t ⟨ht0, ht.2⟩
      obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
        (hL (Metric.ball_mem_nhds L hε2))
      refine ⟨t - l, sub_pos.mpr hl, fun _ x hx y hy ↦ hclose L x y ?_ ?_⟩
      exacts [hsub (by simpa using hx), hsub (by simpa using hy)]
    · exact ⟨1, one_pos, fun h ↦ absurd h ht0⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h x hx y hy ↦ hR h x ?_ y ?_,
    fun h x hx y hy ↦ hL h x ?_ y ?_⟩
  · exact ⟨hx.1, hx.2.trans_le (by linarith [min_le_left δ₁ δ₂])⟩
  · exact ⟨hy.1, hy.2.trans_le (by linarith [min_le_left δ₁ δ₂])⟩
  · exact ⟨lt_of_le_of_lt (by linarith [min_le_right δ₁ δ₂]) hx.1, hx.2⟩
  · exact ⟨lt_of_le_of_lt (by linarith [min_le_right δ₁ δ₂]) hy.1, hy.2⟩

/-- **A regulated family is uniformly close to a step function** (Dieudonné (7.6.1), cited after
Definition 2.1). For every $\varepsilon > 0$ there is a partition of $[0,T]$ into finitely many
pieces of positive length and a sample point $c_j \in [0,T]$ for each piece such that $H$ stays
within $\varepsilon$ of $H(c_j)$ on the open interior of the piece. Same output shape as
`exists_pieces_of_gauge_eps`, without a bound on the number of pieces. -/
theorem exists_pieces_of_regulated {H : ℝ → 𝕄} {T : ℝ} (hT : 0 ≤ T) (hH : Regulated H 0 T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (τ : ℕ → ℝ) (c : ℕ → ℝ), (∀ j, 0 < τ j) ∧ switchTime τ m = T ∧
      (∀ j < m, c j ∈ Icc 0 T) ∧
      (∀ j < m, ∀ t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)), ‖H t - H (c j)‖ ≤ ε) := by
  classical
  -- Step 1: every t ∈ [0, T] has one-sided neighbourhoods of radius δ(t) where H oscillates by
  -- at most ε; finitely many of the intervals (t - δ(t), t + δ(t)) cover [0, T].
  choose! δ hδpos hδ using fun t (ht : t ∈ Icc 0 T) ↦ exists_local_osc_of_regulated hH hε ht
  obtain ⟨F, hFsub, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).elim_nhds_subcover
    (fun t ↦ Ioo (t - δ t) (t + δ t))
    (fun t ht ↦ Ioo_mem_nhds (by linarith [hδpos t ht]) (by linarith [hδpos t ht]))
  -- Step 2: cut [0, T] at 0, T, the cover's centres and the ends of its intervals.
  set S : Finset ℝ := insert 0 (insert T (F ∪ F.image (fun t ↦ min (t + δ t) T)
    ∪ F.image (fun t ↦ max (t - δ t) 0))) with hSdef
  have hS : ∀ x ∈ S, x ≤ T := by
    intro x hx
    simp only [hSdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with rfl | rfl | (hx | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    exacts [hT, le_rfl, (hFsub x hx).2, min_le_right _ _,
      max_le (by linarith [(hFsub t ht).2, hδpos t (hFsub t ht)]) hT]
  obtain ⟨n, τ, hτ, hsw, hgap, -⟩ := exists_switchTime_of_finset hT
    (by simp [hSdef]) (by simp [hSdef]) hS
  have hmono := switchTime_mono fun j ↦ (hτ j).le
  have hlt : ∀ j, switchTime τ j < switchTime τ (j + 1) := fun j ↦ by
    rw [switchTime_succ]; linarith [hτ j]
  have hlo : ∀ j, 0 ≤ switchTime τ j := fun j ↦ by
    simpa [switchTime_zero] using hmono (Nat.zero_le j)
  have hhi : ∀ j < n, switchTime τ (j + 1) ≤ T := fun j hj ↦ hsw ▸ hmono hj
  -- Step 3: sample each piece at its midpoint p. The centre x of a cover interval containing p
  -- is not inside the piece, so the piece lies in one one-sided neighbourhood of x.
  refine ⟨n, τ, fun j ↦ (switchTime τ j + switchTime τ (j + 1)) / 2, hτ, hsw, fun j hj ↦
    ⟨by linarith [hlo j, hlt j], by linarith [hhi j hj, hlt j]⟩, fun j hj t ht ↦ ?_⟩
  set a := switchTime τ j
  set b := switchTime τ (j + 1)
  set p := (a + b) / 2
  have hab := hlt j
  have hp : p ∈ Ioo a b := ⟨by simp only [p]; linarith, by simp only [p]; linarith⟩
  have hpT : p ∈ Icc 0 T := ⟨by linarith [hlo j, hp.1], by linarith [hhi j hj, hp.2]⟩
  have hbT := hhi j hj
  have ha0 := hlo j
  obtain ⟨x, hxF, hpx⟩ := mem_iUnion₂.mp (hcover hpT)
  have hxI := hFsub x hxF
  have hxS : x ∈ S := by simp [hSdef, hxF]
  have hxab := hgap j hj x hxS
  rcases le_or_gt x a with hxa | hxa
  · -- the piece lies to the right of `x`
    have hmS : min (x + δ x) T ∈ S := by
      simp only [hSdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inl (Or.inr ⟨x, hxF, rfl⟩)))
    have hmab := hgap j hj _ hmS
    have hma : a < min (x + δ x) T := lt_min (by linarith [hpx.2, hp.1]) (by linarith)
    have hbm : b ≤ min (x + δ x) T := le_of_not_gt fun hcon ↦ hmab ⟨hma, hcon⟩
    have hbx : b ≤ x + δ x := hbm.trans (min_le_left _ _)
    have hsub : ∀ y ∈ Ioo a b, y ∈ Ioo x (x + δ x) := fun y hy ↦
      ⟨lt_of_le_of_lt hxa hy.1, lt_of_lt_of_le hy.2 hbx⟩
    exact (hδ x hxI).1 (by linarith) t (hsub t ht) p (hsub p hp)
  · -- the piece lies to the left of `x`
    have hbx : b ≤ x := le_of_not_gt fun hcon ↦ hxab ⟨hxa, hcon⟩
    have hmS : max (x - δ x) 0 ∈ S := by
      simp only [hSdef, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inr ⟨x, hxF, rfl⟩))
    have hmab := hgap j hj _ hmS
    have hmb : max (x - δ x) 0 < b := max_lt (by linarith [hpx.1, hp.2]) (by linarith)
    have ham : max (x - δ x) 0 ≤ a := le_of_not_gt fun hcon ↦ hmab ⟨hcon, hmb⟩
    have hax : x - δ x ≤ a := (le_max_left _ _).trans ham
    have hsub : ∀ y ∈ Ioo a b, y ∈ Ioo (x - δ x) x := fun y hy ↦
      ⟨lt_of_le_of_lt hax hy.1, lt_of_lt_of_le hy.2 hbx⟩
    exact (hδ x hxI).2 (by linarith) t (hsub t ht) p (hsub p hp)

end UnitaryProducts
