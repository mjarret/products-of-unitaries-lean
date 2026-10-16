/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.OneVariable
public import UnitaryProducts.Approximation.JRSComparison

/-!
# Prose steps in Section 3

## Declarations

- `truncation_path_rowSparse`
- `bounded_truncation_error_tendsto`
- `distinct_band_card_le`
- `endpoint_projector_eq_directed_and_le`
- `exists_midpointProductOver_truncation_close`
- `jrsFunctional_mono_band_size`
- `jrs_bound_of_distinct_band_count`
- `midpointProductOver_eq_evolution_of_pieces`
- `norm_sub_eq_directed_of_lt_one`
- `pieceProduct_eq_evolution_of_pieces`
- `truncBits_mem_uIcc`
- `truncBits_nonneg_le`
- `truncHerm_entry_zero`
- `truncation_changed_count_le`
- `truncation_error_sparsity_eq_zero`
- `truncation_error_sparsity_le_dim`
- `truncation_error_sparsity_le_nonzero`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Set MeasureTheory Filter

namespace UnitaryProducts.Prose

/-- Section 3, proof of Example 3.2: rounding a nonnegative scalar toward zero stays between
zero and that scalar. -/
theorem truncBits_nonneg_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ truncBits k x ∧ truncBits k x ≤ x := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  simp only [truncBits, level, if_pos hx]
  exact ⟨div_nonneg (Int.cast_nonneg (Int.floor_nonneg.mpr (mul_nonneg hp.le hx))) hp.le,
    (div_le_iff₀ hp).mpr (by simpa [mul_comm] using Int.floor_le ((2 : ℝ)^k*x))⟩

/-- Section 3, proof of Example 3.2, before the real error display: the scalar error
is that `[x]ₖ` lies between `0` and `x`. Literal equality of signs fails when truncation
rounds a nonzero input to zero; see `truncBits_sign_counterexample`. -/
theorem truncBits_mem_uIcc (k : ℕ) (x : ℝ) : truncBits k x ∈ uIcc 0 x := by
  rw [mem_uIcc]
  rcases le_total 0 x with hx | hx
  · exact Or.inl (truncBits_nonneg_le k hx)
  · obtain ⟨h0, hle⟩ := truncBits_nonneg_le k (neg_nonneg.mpr hx)
    rw [truncBits_neg] at h0 hle
    exact Or.inr ⟨by linarith, by linarith⟩

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 3: the largest changed-entry count along the path is at most `d`. -/
theorem truncation_error_sparsity_le_dim (H : ℝ → 𝕄) (k : ℕ) :
    (⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card) ≤ d := by
  classical
  haveI : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  exact ciSup_le fun s ↦ ciSup_le' fun i ↦ (Finset.card_filter_le _ _).trans (by simp)

/-- Example 3.2: the largest changed-entry count along the path bounds the
number of nonzero entries in every row of every truncation error. -/
theorem truncation_path_rowSparse (H : ℝ → 𝕄) (k : ℕ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    RowSparse (⨆ t : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H t) i j ≠ H t i j).card)
      (H s - truncHerm k (H s)) := by
  classical
  have hb (t : Icc (0 : ℝ) 1) : BddAbove (Set.range fun i : Fin d ↦
      (Finset.univ.filter fun j ↦ truncHerm k (H t) i j ≠ H t i j).card) :=
    (Set.finite_range _).bddAbove
  have hbpath : BddAbove (Set.range fun t : Icc (0 : ℝ) 1 ↦
      ⨆ i : Fin d, (Finset.univ.filter fun j ↦ truncHerm k (H t) i j ≠ H t i j).card) := by
    exact ⟨d, Set.forall_mem_range.mpr fun t ↦ ciSup_le' fun i ↦
      (Finset.card_filter_le _ _).trans (by simp)⟩
  intro i
  change (Finset.univ.filter fun j ↦ H s i j - truncHerm k (H s) i j ≠ 0).card ≤ _
  simp only [sub_ne_zero]
  simpa only [ne_comm] using
    (le_ciSup (hb ⟨s, hs⟩) i).trans (le_ciSup hbpath ⟨s, hs⟩)

/-- Following Example 3.2: bit truncation preserves every zero matrix entry. -/
theorem truncHerm_entry_zero (k : ℕ) (A : 𝕄) (i j : Fin d) (hz : A i j = 0) :
    truncHerm k A i j = 0 := by
  have hzero : truncBits k 0 = 0 := Function.Odd.map_zero (truncBits_neg k)
  change (⟨truncBits k (A i j).re, truncBits k (A i j).im⟩ : ℂ) = 0
  simp only [hz, Complex.zero_re, Complex.zero_im, hzero]; rfl

/-- Following Example 3.2: a row has no more changed entries than nonzero entries. -/
theorem truncation_changed_count_le (k : ℕ) (A : 𝕄) (i : Fin d) :
    (Finset.univ.filter fun j ↦ truncHerm k A i j ≠ A i j).card ≤
      (Finset.univ.filter fun j ↦ A i j ≠ 0).card := by
  classical
  refine Finset.card_le_card fun j hj ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact fun hz ↦ hj ((truncHerm_entry_zero k A i j hz).trans hz.symm)

/-- Following Example 3.2: the maximal changed-entry count is bounded by maximal row sparsity. -/
theorem truncation_error_sparsity_le_nonzero (H : ℝ → 𝕄) (k : ℕ) :
    (⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card) ≤
    (⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ H s i j ≠ 0).card) := by
  classical
  have hb (s : Icc (0 : ℝ) 1) : BddAbove (Set.range fun i : Fin d ↦
      (Finset.univ.filter fun j ↦ H s i j ≠ 0).card) := (Set.finite_range _).bddAbove
  have hbpath : BddAbove (Set.range fun s : Icc (0 : ℝ) 1 ↦
      ⨆ i : Fin d, (Finset.univ.filter fun j ↦ H s i j ≠ 0).card) := by
    refine ⟨d, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact ciSup_le' fun i ↦ (Finset.card_filter_le _ _).trans (by simp)
  exact ciSup_mono hbpath fun s ↦
    ciSup_mono (hb s) (fun i ↦ truncation_changed_count_le k (H s) i)

/-- Following Example 3.2: a path fixed by truncation has zero changed-entry count, regardless
of its density. Only equality on the path's parameter interval is needed. -/
theorem truncation_error_sparsity_eq_zero (H : ℝ → 𝕄) (k : ℕ)
    (hfix : ∀ s ∈ Icc (0 : ℝ) 1, truncHerm k (H s) = H s) :
    (⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin d,
      (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  exact ciSup_le' fun s ↦ ciSup_le' fun i ↦ by simp [hfix _ s.property]

/-- Section 3, after Theorem 3.6 and in the unnumbered bit-transfer estimate: bounded changed-entry
counts
make the bit-error bound tend to zero, even when the count depends on the precision. -/
theorem bounded_truncation_error_tendsto (σ : ℕ → ℕ) (S : ℕ) (hσ : ∀ k, σ k ≤ S) :
    Tendsto (fun k : ℕ ↦ Real.sqrt 2 * σ k * ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun k : ℕ ↦ Real.sqrt 2 * S * ((2 : ℝ) ^ k)⁻¹)
    (fun _ ↦ by positivity)
    (fun k ↦ mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hσ k) (Real.sqrt_nonneg 2))
      (by positivity))
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))).const_mul
      (Real.sqrt 2 * S)

/-- Section 3, proof of the unnumbered endpoint projector estimate: the directed projector distance
equals the full
projector distance whenever that distance is below one. -/
theorem norm_sub_eq_directed_of_lt_one {P Q : 𝕄}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hclose : ‖P - Q‖ < 1) :
    ‖P - Q‖ = ‖(1 - Q) * P‖ := by
  apply le_antisymm (norm_sub_le_directed_of_lt_one hP hQ hclose)
  rw [show (1 - Q) * P = (P - Q) * P by rw [sub_mul, one_mul, sub_mul, hP.isIdempotentElem.eq]]
  exact (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_left (norm_le_one_of_isStarProjection hP) (norm_nonneg _)).trans_eq
      (mul_one _))

/-- Section 3, the parenthesis after the JRS citation: the number of distinct band
 eigenvalues is at most the number counted with multiplicity. -/
theorem distinct_band_card_le {A : 𝕄} (hA : A.IsHermitian) (S : Finset (Fin d)) :
    (S.image hA.eigenvalues).card ≤ S.card := by
  classical exact Finset.card_image_le

/-- Section 3, opening paragraph: checkpoints and a bit precision approximate the evolution
of any regulated Hermitian path to any positive tolerance, including paths with jumps. -/
theorem exists_midpointProductOver_truncation_close {H U : ℝ → 𝕄} {T ε : ℝ}
    (hT : 0 < T) (hreg : Paper.IsRegulated H 0 1)
    (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hU : Paper.IsEvolution (fun t ↦ H (t / T)) U 0 T) (hε : 0 < ε) :
    ∃ (k n : ℕ) (s : ℕ → ℝ), (Paper.variationCheckpoints H 1 n).2.1 s ∧
      ‖Paper.midpointProductOver (fun x ↦ truncHerm k (H x)) T n s - U T‖ < ε := by
  classical
  let osc := fun (n : ℕ) (s : ℕ → ℝ) ↦
    ∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1), ‖H x - H ((s j + s (j + 1)) / 2)‖
  let E := {x : ℝ | ∃ (n : ℕ) (s : ℕ → ℝ),
    (Paper.variationCheckpoints H 1 n).2.1 s ∧ x = osc n s}
  obtain ⟨hb, hinf⟩ := Paper.path_midpoint_product_error_and_infimum hT hreg hH hU
  have hne : E.Nonempty := by
    obtain ⟨n, τ, c, hτ, hsw, _, _⟩ :=
      exists_pieces_of_regulated zero_le_one hreg one_pos
    exact ⟨_, n, switchTime τ,
      ⟨switchTime_mono fun j ↦ (hτ j).le, switchTime_zero τ, hsw⟩, rfl⟩
  have htol : 0 < ε / (2 * T) := div_pos hε (by positivity)
  obtain ⟨_, ⟨n, s, hs, rfl⟩, hosc⟩ :=
    exists_lt_of_csInf_lt hne (show sInf E < ε / (2 * T) by rw [hinf]; exact htol)
  have htend : Tendsto (fun k : ℕ ↦ Real.sqrt 2 * d * ((2 : ℝ)^k)⁻¹) atTop (𝓝 0) :=
    bounded_truncation_error_tendsto (fun _ ↦ d) d fun _ ↦ le_rfl
  obtain ⟨k, hk⟩ := ((tendsto_order.mp htend).2 _ htol).exists
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn ↦ by simpa [hn, hs.2.1] using hs.2.2
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsamp : ∀ j : Fin n, (s j + s (j + 1)) / 2 ∈ Icc (0 : ℝ) 1 := by
    intro j
    have h0 := hs.2.1 ▸ hs.1 (Nat.zero_le j.val)
    have h1 := hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt j.isLt)
    have hj := hs.1 (Nat.le_succ j.val)
    constructor <;> linarith
  have he : (⨆ j : Fin n,
      ‖H ((s j + s (j + 1)) / 2) - truncHerm k (H ((s j + s (j + 1)) / 2))‖) ≤
      Real.sqrt 2 * d * ((2 : ℝ)^k)⁻¹ := by
    refine ciSup_le fun j ↦ ?_
    apply (Paper.entry_truncation_bounds (d := d) k).2.2.2 _ d (hH _ (hsamp j))
    intro i
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hbound := hb (truncBits k) (Paper.entry_truncation_bounds (d := d) k).1.1 n s hs
  refine ⟨k, n, s, hs, hbound.trans_lt ?_⟩
  change T * (osc n s + _) < ε
  have hsum := add_lt_add hosc (he.trans_lt hk)
  have hmul := mul_lt_mul_of_pos_left hsum hT
  have hid : T * (ε / (2 * T) + ε / (2 * T)) = ε := by field_simp; ring
  rwa [hid] at hmul

/-- Section 3, the parenthesis after the JRS citation: increasing the eigenvalue count
increases `J_m`. The continuity and sign hypotheses hold for the derivative norms and the
positive continuous gap in the paper. -/
theorem jrsFunctional_mono_band_size {m n : ℝ} (hm : 0 ≤ m) (hmn : m ≤ n)
    {u v g : ℝ → ℝ} (hu : ContinuousOn u (Icc 0 1))
    (hv : ContinuousOn v (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hu0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ u s)
    (hv0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ v s)
    (hg0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s) :
    jrsFunctional m u v g ≤ jrsFunctional n u v g := by
  have hn : 0 ≤ n := hm.trans hmn
  have hc : ∀ a : ℝ, ContinuousOn
      (fun s ↦ a * v s / g s ^ 2 + 7 * a * Real.sqrt a * u s ^ 2 / g s ^ 3)
      (Icc 0 1) := fun a ↦
    ((continuousOn_const.mul hv).div (hg.pow 2)
      (fun s hs ↦ pow_ne_zero _ (hg0 s hs).ne')).add
      ((continuousOn_const.mul (hu.pow 2)).div (hg.pow 3)
        (fun s hs ↦ pow_ne_zero _ (hg0 s hs).ne'))
  have hcoef : 7 * m * Real.sqrt m ≤ 7 * n * Real.sqrt n :=
    mul_le_mul (mul_le_mul_of_nonneg_left hmn (by norm_num))
      (Real.sqrt_le_sqrt hmn) (Real.sqrt_nonneg _) (by positivity)
  unfold jrsFunctional
  apply add_le_add
  · apply add_le_add
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmn (hu0 0 ⟨le_rfl, zero_le_one⟩)) (sq_nonneg _)
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmn (hu0 1 ⟨zero_le_one, le_rfl⟩)) (sq_nonneg _)
  · refine intervalIntegral.integral_mono_on zero_le_one
      (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (hc m))
      (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (hc n)) fun s hs ↦ add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmn (hv0 s hs))
        (sq_nonneg _))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
        (pow_nonneg (hg0 s hs).le _))

/-- Section 3, proof of Theorem 3.6: the product on a nondecreasing sequence of checkpoints
is the final evolution value of the corresponding piecewise constant family, even when
checkpoints coincide. -/
theorem pieceProduct_eq_evolution_of_pieces {K : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hK : ∀ x ∈ Icc 0 T, (K x).IsHermitian) (n : ℕ) (t : ℕ → ℝ)
    (ht : Monotone t ∧ t 0 = 0 ∧ t n = T) (G : ℕ → 𝕄)
    (hG : ∀ j < n, (G j).IsHermitian)
    (hpieces : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), K x = G j) :
    ∃ U : ℝ → 𝕄, Paper.IsEvolution K U 0 T ∧
      pieceProduct (scheduleDuration t n) G n = U T := by
  have hr : Paper.IsRegulated K 0 T := by
    simpa only [ht.2.1, ht.2.2] using Paper.piecewise_regulated K t G n hpieces
  obtain ⟨U, hU, _⟩ := Paper.regulated_evolution hT hK hr
  refine ⟨U, hU, sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _)))⟩
  have hb := Paper.piecewise_product_error_le_integral hT hr hU n t ht G hG
  have hi : ∀ j < n, (∫ x in t j..t (j + 1), ‖K x - G j‖) = 0 := by
    intro j hj
    calc _ = ∫ _x in t j..t (j + 1), (0 : ℝ) := by
           apply intervalIntegral.integral_congr_ae
           have hn : ∀ᵐ x : ℝ ∂volume, x ≠ t (j + 1) := ae_iff.mpr (by simp)
           filter_upwards [hn] with x hx hmem
           rw [uIoc_of_le (ht.1 (Nat.le_succ j))] at hmem
           rw [hpieces j hj x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩, sub_self, norm_zero]
         _ = 0 := intervalIntegral.integral_zero
  simpa only [Finset.sum_eq_zero (fun j hj ↦ hi j (Finset.mem_range.mp hj))] using hb

/-- Section 3, proof of Theorem 3.6: specifically, the midpoint product of `A` over time `T`
is the final evolution of the family equal to its midpoint samples on open checkpoint cells.
The checkpoints need only be nondecreasing. -/
theorem midpointProductOver_eq_evolution_of_pieces {A K : ℝ → 𝕄} {T : ℝ}
    (hT : 0 < T) (hA : ∀ x ∈ Icc (0 : ℝ) 1, (A x).IsHermitian)
    (hK : ∀ x ∈ Icc (0 : ℝ) 1, (K x).IsHermitian) (n : ℕ) (s : ℕ → ℝ)
    (hs : Monotone s ∧ s 0 = 0 ∧ s n = 1)
    (hpieces : ∀ j < n, ∀ x ∈ Ioo (s j) (s (j + 1)),
      K x = A ((s j + s (j + 1)) / 2)) :
    ∃ U : ℝ → 𝕄, Paper.IsEvolution (fun t ↦ K (t / T)) U 0 T ∧
      Paper.midpointProductOver A T n s = U T := by
  have ht : Monotone (fun j ↦ T * s j) ∧ T * s 0 = 0 ∧ T * s n = T :=
    ⟨fun i j hij ↦ mul_le_mul_of_nonneg_left (hs.1 hij) hT.le,
      by rw [hs.2.1, mul_zero], by rw [hs.2.2, mul_one]⟩
  obtain ⟨U, hU, he⟩ := pieceProduct_eq_evolution_of_pieces hT
    (fun x hx ↦ hK (x / T) ⟨div_nonneg hx.1 hT.le, (div_le_one hT).mpr hx.2⟩)
    n (fun j ↦ T * s j) ht (fun j ↦ A ((s j + s (j + 1)) / 2))
    (fun j hj ↦ hA _ ⟨by linarith [hs.2.1 ▸ hs.1 (Nat.zero_le j), hs.1 (Nat.le_succ j)],
      by linarith [hs.2.2 ▸ hs.1 (Nat.succ_le_of_lt hj), hs.1 (Nat.le_succ j)]⟩)
    (fun j hj x hx ↦ hpieces j hj (x / T)
      ⟨(lt_div_iff₀ hT).mpr (by simpa [mul_comm] using hx.1),
        (div_lt_iff₀ hT).mpr (by simpa [mul_comm] using hx.2)⟩)
  exact ⟨U, hU, (Paper.midpointProductOver_eq A T n s).trans he⟩

/-- Section 3, proof of the unnumbered endpoint projector estimate: at either endpoint, the full
projector error equals
the directed error and is at most `ε / (Γ - ε)`. The index projectors are the paper's hull
and enlarged-hull projectors by `Paper.hull_windowProj_eq_bandProj`. -/
theorem endpoint_projector_eq_directed_and_le {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {S : Finset (Fin d)}
    (hS : Paper.IsBand hA S) (he : ‖A - D‖ < Paper.bandGap hA hS / 2) :
    ‖Paper.bandProj S A - Paper.bandProj S D‖ =
      ‖(1 - Paper.bandProj S D) * Paper.bandProj S A‖ ∧
    ‖(1 - Paper.bandProj S D) * Paper.bandProj S A‖ ≤
      ‖A - D‖ / (Paper.bandGap hA hS - ‖A - D‖) := by
  have hU : Paper.IsEvolution (fun _ ↦ A) (evol A) 0 1 := by
    refine ⟨(continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_evol A t).continuousAt).continuousOn, evol_zero A,
      fun t _ ↦ star_evol_mul_self hA t, ∅, Set.countable_empty,
      fun t ht _ ↦ solvesSchrodinger_evol A 0 1 t ht⟩
  have hb := (Paper.leakage_le_of_endpoint_approximation_sharp one_pos
    (fun _ _ ↦ hA) hU hS hS hD hD he he (1 : 𝕄)).2.1
  have hgap : 0 < Paper.bandGap hA hS := by linarith [norm_nonneg (A - D)]
  have hclose : ‖Paper.bandProj S A - Paper.bandProj S D‖ < 1 :=
    hb.trans_lt ((div_lt_one (by linarith)).mpr (by linarith))
  obtain ⟨hP, hQ⟩ := Paper.hull_windowProj_eq_bandProj hA hD hS he
  have hprojP : IsStarProjection (Paper.bandProj S A) :=
    hP ▸ isStarProjection_windowProj _ _ A
  have hprojQ : IsStarProjection (Paper.bandProj S D) :=
    hQ ▸ isStarProjection_windowProj _ _ D
  have heq := norm_sub_eq_directed_of_lt_one hprojP hprojQ hclose
  exact ⟨heq, heq ▸ hb⟩

/-- Section 3, the parenthesis after the JRS citation: a bound with the count of distinct
band eigenvalues implies the same bound with multiplicities counted. -/
theorem jrs_bound_of_distinct_band_count {A W P Q : 𝕄} (hA : A.IsHermitian)
    (S : Finset (Fin d)) {T : ℝ} (hT : 0 < T) {u v g : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (hu0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ u s)
    (hv0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ v s) (hg0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s)
    (hJRS : ‖(1 - Q) * W * P‖ ≤ jrsFunctional (S.image hA.eigenvalues).card u v g / T) :
    ‖(1 - Q) * W * P‖ ≤ jrsFunctional S.card u v g / T := by
  classical
  exact hJRS.trans (div_le_div_of_nonneg_right (jrsFunctional_mono_band_size (Nat.cast_nonneg _)
    (by exact_mod_cast distinct_band_card_le hA S) hu hv hg hu0 hv0 hg0) hT.le)

end UnitaryProducts.Prose
