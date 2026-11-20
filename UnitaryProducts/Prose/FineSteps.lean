/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.OneVariable
public import Mathlib

/-!
# Prose steps in Section 3

## Declarations

- `endpoint_projector_eq_directed_and_le`
- `midpointProductOver_eq_evolution_of_pieces`
- `norm_sub_eq_directed_of_lt_one`
- `pieceProduct_eq_evolution_of_pieces`
- `truncBits_mem_uIcc`
- `truncBits_nonneg_le`
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

end UnitaryProducts.Prose
