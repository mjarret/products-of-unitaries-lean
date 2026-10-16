/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.BandTransfer

/-!
# Midpoint approximation and continuous leakage bounds

## Declarations

- `fine_steps_split`
- `UnitaryProducts.Prose.localSteps_norm_integrable`
- `checkpoints_split`
- `checkpoints_sum_const`
- `midpoint_mem_Ioo`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Complex Set MeasureTheory Filter
noncomputable section
namespace UnitaryProducts.Prose
open UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 3.2: the norm integrands on checkpoint intervals are integrable. -/
theorem localSteps_norm_integrable {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) {n : ℕ} {t : ℕ → ℝ}
    (ht : (variationCheckpoints H T n).2.1 t) {j : ℕ} (hj : j < n) (c : 𝕄) :
    IntervalIntegrable (fun x ↦ ‖H x - c‖) volume (t j) (t (j + 1)) :=
  (((hreg.intervalIntegrable_on hT.le).mono_set (by
    rw [uIcc_of_le (ht.1 (Nat.le_succ j)), uIcc_of_le hT.le]
    exact Icc_subset_Icc (ht.2.1 ▸ ht.1 (Nat.zero_le j)) (ht.2.2 ▸ ht.1 hj))).sub
    (intervalIntegrable_const (c := c))).norm

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- Constants integrate over checkpoints to `T` times the constant: the factor $T$ in front of the
maximum in the auxiliary integrated midpoint estimate. -/
private theorem checkpoints_sum_const {H : ℝ → 𝕄} {T : ℝ} {n : ℕ} {t : ℕ → ℝ}
    (ht : (variationCheckpoints H T n).2.1 t) (β : ℝ) :
    ∑ j ∈ Finset.range n, ∫ _x in t j..t (j+1), β = T*β := by
  simp only [intervalIntegral.integral_const, smul_eq_mul, ← Finset.sum_mul,
    Finset.sum_range_sub, ht.2.1, ht.2.2, sub_zero]

omit [NeZero d] in
/-- Splitting the value $G_j$ off at the midpoint sample: the second inequality in the proof of
the auxiliary integrated midpoint estimate,
$\|H(t)-G_j\|\le\|H(t)-H(t_{j+1/2})\|+\|H(t_{j+1/2})-G_j\|$, integrated. -/
private theorem checkpoints_split {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) (n : ℕ) (t : ℕ → ℝ)
    (ht : (variationCheckpoints H T n).2.1 t) (G : ℕ → 𝕄) (β : ℝ)
    (hβ : ∀ j < n, ‖H ((t j + t (j + 1)) / 2) - G j‖ ≤ β) :
    ∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-G j‖ ≤
      (∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-H ((t j + t (j + 1)) / 2)‖)+T*β := by
  rw [← checkpoints_sum_const ht β, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  rw [← intervalIntegral.integral_add
    (Prose.localSteps_norm_integrable hT hreg ht hj' (H ((t j + t (j + 1)) / 2)))
    intervalIntegrable_const]
  exact intervalIntegral.integral_mono_on (ht.1 (Nat.le_succ j))
    (Prose.localSteps_norm_integrable hT hreg ht hj' (G j))
    ((Prose.localSteps_norm_integrable hT hreg ht hj' (H ((t j + t (j + 1)) / 2))).add
      intervalIntegrable_const) fun x _ ↦
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add le_rfl (hβ j hj'))

/-- The midpoint lies inside its interval (used in the claim after the auxiliary integrated
midpoint estimate, and to apply
the variation bound of Remark 3.9 at $t_{j+1/2}$ in the auxiliary variation bound). -/
private theorem midpoint_mem_Ioo {a b x : ℝ} (hx : x ∈ Ioo a b) : (a+b)/2 ∈ Ioo a b :=
  ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩

omit [NeZero d] in
/-- Supports the auxiliary integrated midpoint estimate (fine steps) and the variation bit bound,
$\|W-U(T)\|\le T\ell/n+\sqrt2\,s\,2^{-k}T$ (§3.2, the display after the auxiliary integrated
midpoint estimate), in their form
for a family on $[0,T]$. The three conjuncts are the auxiliary integrated midpoint estimate, the
claim after it, and the auxiliary variation bound
on $[0,T]$; the paper's forms for a path over time $T$ follow by $t=Ts$
(`path_midpoint_product_error_and_infimum`, `path_midpoint_product_error_le`).

Reading the statement against the paper:
* `osc n t` is the first term of the auxiliary integrated midpoint estimate,
  $\sum_j\int_{t_j}^{t_{j+1}}\|H(t)-H(t_{j+1/2})\|\,dt$, with $t_{j+1/2}$ written
  `(t j + t (j + 1)) / 2`.
* Oddness of $F$ is `∀ x, F (-x) = -F x`. `(levelFunctionData F).2 H` is the family $H^{(F)}$, and
  `(levelFunctionData F).1` is the entrywise map on one matrix.
* Checkpoints $t_0,\dots,t_n$ are `(variationCheckpoints H T n).2.1 t`: `t` is monotone, with
  `t 0 = 0` and `t n = T`.
* $\max_j$ is `⨆ j : Fin n`, a supremum over a finite index set.
* The claim after the auxiliary integrated midpoint estimate is `sInf {…} = 0`, the infimum over
all `n` and all checkpoints `t`.
* Eq. (3.1): $\sigma_k\le s$ is `∀ t ∈ Icc 0 T, RowSparse s (H t - H^{(k)}(t))`, at most $s$
  entries changed by bit truncation in each row of each $H(t)$; $s=0$ is allowed. $\ell<\infty$
  is `(variationCheckpoints H T 0).1 T < ⊤`, so `ℓ`, its `toReal`, is the paper's $\ell$. The
  equal-variation checkpoints are `inverseLevelTime … T n`, and `(truncation k).2.2.2 H` is
  $H^{(k)}$.
* Part (i) uses only the oddness of `F`. The regulated
  hypothesis is redundant for the auxiliary variation bound, where it follows from $\ell<\infty$.
* Stronger than the paper's setting: no $d\ge1$.
* The form of the auxiliary variation bound for $s$-sparse $H$ is `fine_steps_split_of_sparse`,
derived from
  this one.

The proof follows the paper's: (i) the error of the piecewise-constant family $G$ against $U$ (eq.
(2.5)) is split at
the midpoint sample; (ii) the switch times of a step family within $\eta$ of $H$ are checkpoints
with oscillation term at most $2\eta T$; (3.1) the variation bound of Remark 3.9 bounds the
oscillation term by
$T\ell/n$ and Example 3.2(ii) bounds the truncation term. In (i), the paper applies eq. (2.4) once
to the evolution of $G$; the Lean applies it on each interval and telescopes
(`piecewise_product_error_le_integral`), which is equivalent and avoids building the piecewise
evolution. -/
theorem fine_steps_split {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hU : IsEvolution H U 0 T) :
    let osc := fun (n : ℕ) (t : ℕ → ℝ) ↦
      ∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-H ((t j + t (j + 1)) / 2)‖
    let ℓ := ((variationCheckpoints H T 0).1 T).toReal
    (∀ F : ℝ → ℝ, (∀ x, F (-x) = -F x) →
      ∀ (n : ℕ) (t : ℕ → ℝ), (variationCheckpoints H T n).2.1 t →
      ‖midpointProduct ((levelFunctionData F).2 H) n t-U T‖ ≤
        osc n t+T*⨆ j : Fin n, ‖H ((t j + t (j + 1)) / 2)-
          (levelFunctionData F).1 (H ((t j + t (j + 1)) / 2))‖) ∧
    sInf {x : ℝ | ∃ (n : ℕ) (t : ℕ → ℝ), (variationCheckpoints H T n).2.1 t ∧
      x = osc n t} = 0 ∧
    (∀ s k : ℕ, (∀ t ∈ Icc 0 T, UnitaryProducts.RowSparse s (H t - (truncation k).2.2.1 (H t))) →
      (variationCheckpoints H T 0).1 T < ⊤ → ∀ n : ℕ, 1 ≤ n →
      ‖midpointProduct ((truncation k).2.2.2 H) n
          (UnitaryProducts.inverseLevelTime (fun x ↦ ((variationCheckpoints H T 0).1 x).toReal)
            T n)-U T‖ ≤
        T*ℓ/n+Real.sqrt 2 * s * ((2 : ℝ) ^ k)⁻¹*T) := by
  dsimp only
  have hT0 : T ≠ 0 := hT.ne'
  -- The midpoint samples t_{j+1/2} lie in [0,T], where H is Hermitian.
  have hmid : ∀ {n : ℕ} {t : ℕ → ℝ}, (variationCheckpoints H T n).2.1 t →
      ∀ j < n, (t j + t (j + 1))/2 ∈ Icc 0 T := fun ht j hj ↦
    ⟨by linarith [ht.2.1 ▸ ht.1 (Nat.zero_le j), ht.1 (Nat.le_succ j)],
      by linarith [ht.2.2 ▸ ht.1 hj, ht.1 (Nat.le_succ j)]⟩
  refine ⟨?_, ?_, ?_⟩
  -- Part (i) (paper, eq. (2.4)): Duhamel on each interval against the held sample
  -- H^{(F)}(t_{j+1/2}), which is Hermitian because F is odd.
  · intro F hodd n t ht
    let G := fun j ↦ UnitaryProducts.scalarEntryMap F (H ((t j + t (j + 1)) / 2))
    have hb := piecewise_product_error_le_integral hT hreg hU n t ht G
      (fun j hj ↦ UnitaryProducts.scalarEntryMap_isHermitian F hodd (hH _ (hmid ht j hj)))
    -- Split at the midpoint sample; each truncation error is at most the max over `Fin n`.
    refine hb.trans (checkpoints_split hT hreg n t ht G _ fun j hj ↦ ?_)
    exact le_ciSup (f := fun i : Fin n ↦ ‖H ((t i+t (i+1)) / 2)-
      (levelFunctionData F).1 (H ((t i+t (i+1)) / 2))‖) (Set.finite_range _).bddAbove ⟨j, hj⟩
  -- Part (ii): the infimum of the oscillation term over all checkpoints is 0.
  · apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    -- The set is nonempty: the switch times of any step approximation of H are checkpoints.
    · obtain ⟨m, τ, c, hτ, hsw, _, _⟩ := UnitaryProducts.exists_pieces_of_regulated hT.le hreg
        one_pos
      exact ⟨_, m, UnitaryProducts.switchTime τ, ⟨UnitaryProducts.switchTime_mono fun j ↦ (hτ j).le,
        UnitaryProducts.switchTime_zero τ, hsw⟩, rfl⟩
    -- Every value is a sum of integrals of norms, so it is nonnegative.
    · rintro x ⟨n, t, ht, rfl⟩
      exact Finset.sum_nonneg fun j _ ↦
        intervalIntegral.integral_nonneg (ht.1 (Nat.le_succ j)) fun _ _ ↦ norm_nonneg _
    -- For w > 0, take a step family within η = w/(4T) of H (the paper's piecewise-constant
    -- family, values c_j). On each piece, ‖H(x) - H(t_{j+1/2})‖ ≤ ‖H(x) - c_j‖ + ‖c_j -
    -- H(t_{j+1/2})‖ ≤ 2η, so the oscillation term is at most 2ηT = w/2 < w.
    · intro w hw
      have hη : 0 < w/(4*T) := div_pos hw (by linarith)
      obtain ⟨m, τ, c, hτ, hsw, _, hb⟩ := UnitaryProducts.exists_pieces_of_regulated hT.le hreg hη
      have ht : (variationCheckpoints H T m).2.1 (UnitaryProducts.switchTime τ) :=
        ⟨UnitaryProducts.switchTime_mono fun j ↦ (hτ j).le, UnitaryProducts.switchTime_zero τ, hsw⟩
      refine ⟨_, ⟨m, UnitaryProducts.switchTime τ, ht, rfl⟩, ?_⟩
      have hle : ∀ j < m, ∀ x ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ
        (j + 1)),
          ‖H x-H ((UnitaryProducts.switchTime τ j+UnitaryProducts.switchTime τ (j + 1)) / 2)‖ ≤
            w/(4*T)+w/(4*T) := by
        intro j hj x hx
        calc _ ≤ ‖H x-H (c j)‖+‖H (c j)-H ((UnitaryProducts.switchTime τ j+
              UnitaryProducts.switchTime τ (j + 1)) / 2)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ w/(4*T)+w/(4*T) := add_le_add (hb j hj x hx) (by
              rw [norm_sub_rev]; exact hb j hj _ (midpoint_mem_Ioo hx))
      calc _ ≤ ∑ j ∈ Finset.range m, ∫ _x in
          UnitaryProducts.switchTime τ j..UnitaryProducts.switchTime τ (j+1),
              (w/(4*T)+w/(4*T)) :=
            Finset.sum_le_sum fun j hj ↦ intervalIntegral.integral_mono_on_of_le_Ioo
              (ht.1 (Nat.le_succ j)) (Prose.localSteps_norm_integrable hT hreg ht
                (Finset.mem_range.mp hj) _) intervalIntegrable_const
              (hle j (Finset.mem_range.mp hj))
        _ = T*(w/(4*T)+w/(4*T)) := checkpoints_sum_const ht _
        _ = w/2 := by field_simp; ring
        _ < w := half_lt_self hw
  -- Eq. (3.1): bit truncation on the equal-variation checkpoints.
  · intro s k hsp hfin n hn
    -- Remark 3.9: the equal-variation checkpoints are checkpoints, and H moves by at most ℓ/n
    -- inside each open interval.
    obtain ⟨ht, -, hosc⟩ := inverse_level_variation_bound hT hfin n hn
    set t := UnitaryProducts.inverseLevelTime
      (fun x ↦ ((variationCheckpoints H T 0).1 x).toReal) T n with htdef
    -- Part (i) for the held samples H^{(k)}(t_{j+1/2}).
    let G := fun j ↦ UnitaryProducts.truncHerm k (H ((t j + t (j + 1)) / 2))
    have hb := piecewise_product_error_le_integral hT hreg hU n t ht G
      (fun j hj ↦ UnitaryProducts.isHermitian_truncHerm k (hH _ (hmid ht j hj)))
    -- Example 3.2(ii): each truncation error is at most √2 s 2^{-k}, as truncation changes at
    -- most s entries in each row.
    have hsplit := checkpoints_split hT hreg n t ht G (Real.sqrt 2 * s * ((2 : ℝ) ^ k)⁻¹)
      (fun j hj ↦ (entry_truncation_bounds k).2.2.2 _ s (hH _ (hmid ht j hj))
        (hsp _ (hmid ht j hj)))
    -- the variation bound of Remark 3.9 at the midpoint, which lies in the same open interval:
    -- the oscillation
    -- term is at most Tℓ/n.
    have hosc' : (∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-H ((t j + t (j + 1)) / 2)‖) ≤
        T*(((variationCheckpoints H T 0).1 T).toReal/n) := by
      rw [← checkpoints_sum_const ht]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hj' := Finset.mem_range.mp hj
      apply intervalIntegral.integral_mono_on_of_le_Ioo (ht.1 (Nat.le_succ j))
        (Prose.localSteps_norm_integrable hT hreg ht hj' _) intervalIntegrable_const
      intro x hx
      have hm := midpoint_mem_Ioo hx
      rcases le_total ((t j + t (j + 1)) / 2) x with h | h
      · exact hosc j hj' _ x hm.1 h hx.2
      · rw [norm_sub_rev]; exact hosc j hj' x _ hx.1 h hm.2
    -- Combine: ‖W - U(T)‖ ≤ Tℓ/n + √2 s 2^{-k} T.
    exact (hb.trans hsplit).trans ((add_le_add hosc' le_rfl).trans_eq (by ring))

end UnitaryProducts.Paper
