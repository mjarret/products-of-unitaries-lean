/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.SimulationError

/-!
# Equal-variation checkpoints and midpoint products

## Declarations

- `inverseLevelTime_norm_sub_le`
- `heldProduct`
- `inverseLevelTime`
- `inverseLevelTime_band`
- `inverseLevelTime_last`
- `inverseLevelTime_mem`
- `inverseLevelTime_mono`
- `inverseLevelTime_osc`
- `inverseLevelTime_zero`
- `level_bdd`
- `level_nonempty`
- `scheduleDuration`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator Topology
open Complex Set MeasureTheory

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The equal-variation checkpoints of §3.2 for a gauge $\varphi$ (the paper takes the total
variation $\ell$): $t_0 = 0$, $t_j = \inf\{x \in [0,T] : j(\varphi(T) - \varphi(0))/n \le
\varphi(x) - \varphi(0)\}$ for $0 < j < n$, and $t_j = T$ for $j \ge n$. If the set is empty, which
happens only when $\varphi(T) < \varphi(0)$, `sInf` returns the junk value $0$; the lemmas below
assume $\varphi(T) \ge \varphi(0)$. -/
noncomputable def inverseLevelTime (φ : ℝ → ℝ) (T : ℝ) (n j : ℕ) : ℝ :=
  if j = 0 then 0 else if n ≤ j then T else
    sInf {x ∈ Icc 0 T | (j : ℝ) * (φ T - φ 0) / n ≤ φ x - φ 0}

/-- The durations $t_{j+1} - t_j$ of the checkpoints $t_0, \dots, t_n$, and $0$ for $j \ge n$. -/
noncomputable def scheduleDuration (t : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if j < n then t (j + 1) - t j else 0

/-- The midpoint product (Definition 3.5) of the family $\Theta \circ H$ on checkpoints
$t_0, \dots, t_n$: the product (2.5) of the family equal to $\Theta(H(t_{j+1/2}))$,
$t_{j+1/2} = (t_j + t_{j+1})/2$, on each piece; Definition 3.5 is the case $\Theta = \mathrm{id}$.
A piece with $t_{j+1} = t_j$ contributes the factor $1$, matching the paper's "coinciding
checkpoints give the factor $1$" (proof of Theorem 3.6). -/
noncomputable def heldProduct (Θ : 𝕄 → 𝕄) (H : ℝ → 𝕄) (n : ℕ) (t : ℕ → ℝ) : 𝕄 :=
  pieceProduct (scheduleDuration t n) (fun j ↦ Θ (H ((t j + t (j + 1)) / 2))) n

/-- The set defining $t_j$ contains $T$ when $\varphi(T) \ge \varphi(0)$ and $j \le n$. -/
theorem level_nonempty {φ : ℝ → ℝ} {T : ℝ} {n j : ℕ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ φ T - φ 0) (hj : j ≤ n) :
    {x ∈ Icc 0 T | (j : ℝ) * (φ T - φ 0) / n ≤ φ x - φ 0}.Nonempty := by
  refine ⟨T, ⟨hT, le_rfl⟩, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hℓ
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hℓ

/-- The set defining $t_j$ is bounded below by $0$. -/
theorem level_bdd (φ : ℝ → ℝ) (T : ℝ) (n j : ℕ) :
    BddBelow {x ∈ Icc 0 T | (j : ℝ) * (φ T - φ 0) / n ≤ φ x - φ 0} :=
  ⟨0, fun _ hx ↦ hx.1.1⟩

/-- $t_0 = 0$. -/
@[simp] theorem inverseLevelTime_zero (φ : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    inverseLevelTime φ T n 0 = 0 := by simp [inverseLevelTime]

/-- $t_n = T$ for $n > 0$. -/
@[simp] theorem inverseLevelTime_last (φ : ℝ → ℝ) (T : ℝ) {n : ℕ} (hn : 0 < n) :
    inverseLevelTime φ T n n = T := by simp [inverseLevelTime, hn.ne']

/-- Every cut lies in the closed time interval, even when the gauge jumps. -/
theorem inverseLevelTime_mem {φ : ℝ → ℝ} {T : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ φ T - φ 0) (j : ℕ) :
    inverseLevelTime φ T n j ∈ Icc 0 T := by
  unfold inverseLevelTime
  split_ifs with hj0 hj
  · exact ⟨le_rfl, hT⟩
  · exact ⟨hT, le_rfl⟩
  · have hne := level_nonempty hT hℓ (le_of_lt (not_le.mp hj))
    exact ⟨le_csInf hne (fun _ hx ↦ hx.1.1),
      (csInf_le (level_bdd φ T n j) hne.choose_spec).trans hne.choose_spec.1.2⟩

/-- **the monotonicity in Remark 3.9**: the checkpoints are nondecreasing, since the sets defining
them contain $T$
and shrink as $j$ increases. -/
theorem inverseLevelTime_mono {φ : ℝ → ℝ} {T : ℝ} {n : ℕ}
    (hT : 0 ≤ T) (hℓ : 0 ≤ φ T - φ 0) :
    Monotone (inverseLevelTime φ T n) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    simpa using (inverseLevelTime_mem hT hℓ j).1
  by_cases hj : n ≤ j
  · simpa [inverseLevelTime, show j ≠ 0 by omega, hj] using
      (inverseLevelTime_mem hT hℓ i).2
  have hi' : ¬n ≤ i := by omega
  rw [inverseLevelTime, if_neg hi, if_neg hi', inverseLevelTime,
    if_neg (show j ≠ 0 by omega), if_neg hj]
  exact csInf_le_csInf (level_bdd φ T n i) (level_nonempty hT hℓ (by omega)) fun x hx ↦
    ⟨hx.1, (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hℓ)
      (Nat.cast_nonneg n)).trans hx.2⟩

/-- **The level band of a piece.**  For `t_j < x ≤ y < t_{j+1}` at the inverse levels of a
nondecreasing `φ`, the increase of `φ` stays between two consecutive levels:
`jℓ/n ≤ φ(x) - φ(0) ≤ φ(y) - φ(0) ≤ (j+1)ℓ/n`, `ℓ = φ(T) - φ(0)`. -/
theorem inverseLevelTime_band {φ : ℝ → ℝ} {T : ℝ} {n j : ℕ}
    (hT : 0 ≤ T) (hφ : MonotoneOn φ (Icc 0 T)) (hj : j < n)
    {x y : ℝ} (hx : inverseLevelTime φ T n j < x) (hxy : x ≤ y)
    (hy : y < inverseLevelTime φ T n (j + 1)) :
    (j : ℝ) * (φ T - φ 0) / n ≤ φ x - φ 0 ∧ φ x - φ 0 ≤ φ y - φ 0 ∧
      φ y - φ 0 ≤ ((j : ℝ) + 1) * (φ T - φ 0) / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt hj
  have hℓ : 0 ≤ φ T - φ 0 := sub_nonneg.mpr (hφ ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT)
  have hxI : x ∈ Icc 0 T := ⟨(inverseLevelTime_mem hT hℓ j).1.trans hx.le,
    hxy.trans (hy.le.trans (inverseLevelTime_mem hT hℓ (j + 1)).2)⟩
  have hyI : y ∈ Icc 0 T := ⟨hxI.1.trans hxy,
    hy.le.trans (inverseLevelTime_mem hT hℓ (j + 1)).2⟩
  refine ⟨?_, sub_le_sub_right (hφ hxI hyI hxy) _, ?_⟩
  · by_cases hj0 : j = 0
    · simp only [hj0, Nat.cast_zero, zero_mul, zero_div]
      exact sub_nonneg.mpr (hφ ⟨le_rfl, hT⟩ hxI hxI.1)
    · rw [inverseLevelTime, if_neg hj0, if_neg (not_le.mpr hj)] at hx
      obtain ⟨z, hz, hzx⟩ := exists_lt_of_csInf_lt (level_nonempty hT hℓ hj.le) hx
      exact hz.2.trans (sub_le_sub_right (hφ hz.1 hxI hzx.le) _)
  · by_cases hjn : j + 1 = n
    · rw [← Nat.cast_add_one, hjn, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]
      exact sub_le_sub_right (hφ hyI ⟨hT, le_rfl⟩ hyI.2) _
    · have hnot : ¬ ((j + 1 : ℕ) : ℝ) * (φ T - φ 0) / n ≤ φ y - φ 0 := fun h ↦ by
        rw [inverseLevelTime, if_neg (by omega), if_neg (by omega)] at hy
        exact (not_le.mpr hy) (csInf_le (level_bdd φ T n (j + 1)) ⟨hyI, h⟩)
      simpa only [Nat.cast_add_one] using (lt_of_not_ge hnot).le

/-- the variation bound of Remark 3.9 for the gauge: between consecutive checkpoints it increases
by at most
$(\varphi(T) - \varphi(0))/n$. No infimum is assumed attained: a point strictly to its right has
a superlevel witness to its left. The endpoint levels use monotonicity instead. -/
theorem inverseLevelTime_osc {φ : ℝ → ℝ} {T : ℝ} {n j : ℕ}
    (hT : 0 ≤ T) (hφ : MonotoneOn φ (Icc 0 T)) (hj : j < n)
    {x y : ℝ} (hx : inverseLevelTime φ T n j < x) (hxy : x ≤ y)
    (hy : y < inverseLevelTime φ T n (j + 1)) :
    φ y - φ x ≤ (φ T - φ 0) / n := by
  obtain ⟨hlo, _, hhi⟩ := inverseLevelTime_band hT hφ hj hx hxy hy
  have h := sub_le_sub hhi hlo
  rwa [sub_sub_sub_cancel_right, show ((j : ℝ) + 1) * (φ T - φ 0) / n - (j : ℝ) * (φ T - φ 0) / n
    = (φ T - φ 0) / n by ring] at h

/-- **the variation bound of Remark 3.9**: on each open piece $(t_j, t_{j+1})$, $\|H(x) - H(y)\| \le
(\varphi(T) - \varphi(0))/n$, for a gauge $\varphi$ of $H$ such as its total variation. -/
theorem Gauge.inverseLevelTime_norm_sub_le {H : ℝ → 𝕄} {φ : ℝ → ℝ} {T : ℝ}
    (hg : Gauge H φ 0 T) (hT : 0 ≤ T) {n j : ℕ} (hj : j < n)
    {x y : ℝ} (hx : x ∈ Ioo (inverseLevelTime φ T n j) (inverseLevelTime φ T n (j + 1)))
    (hy : y ∈ Ioo (inverseLevelTime φ T n j) (inverseLevelTime φ T n (j + 1))) :
    ‖H x - H y‖ ≤ (φ T - φ 0) / n := by
  have hℓ : 0 ≤ φ T - φ 0 := sub_nonneg.mpr (hg.mono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT)
  have hxI : x ∈ Icc 0 T := ⟨(inverseLevelTime_mem hT hℓ j).1.trans hx.1.le,
    hx.2.le.trans (inverseLevelTime_mem hT hℓ (j + 1)).2⟩
  have hyI : y ∈ Icc 0 T := ⟨(inverseLevelTime_mem hT hℓ j).1.trans hy.1.le,
    hy.2.le.trans (inverseLevelTime_mem hT hℓ (j + 1)).2⟩
  rcases le_total y x with hyx | hxy
  · exact (hg.dominates y hyI x hxI hyx).trans (inverseLevelTime_osc hT hg.mono hj hy.1 hyx hx.2)
  · rw [norm_sub_rev]
    exact (hg.dominates x hxI y hyI hxy).trans (inverseLevelTime_osc hT hg.mono hj hx.1 hxy hy.2)

end UnitaryProducts
