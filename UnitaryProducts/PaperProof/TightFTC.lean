/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import Mathlib

/-! # Exact integral identities in the affine jump bound in Theorem 4.4

These statements record the equalities before the norm inequalities in the
paper. The fundamental theorem is Mathlib's Banach-valued interval-integral FTC.
-/
@[expose] public section
open Set MeasureTheory Real
open scoped Topology BigOperators
noncomputable section
namespace UnitaryProducts.PaperProof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "J" => Icc (0 : ℝ) 1

/-- the affine jump bound in Theorem 4.4: an increment of a C1 curve is exactly the integral of its
within derivative, including subintervals meeting the endpoints of `[0,1]`. -/
theorem unified_increment_eq_integral {F : ℝ → E}
    (hF : ContDiffOn ℝ 1 F J) {a b : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≤ b) :
    F b - F a = ∫ s in a..b, derivWithin F J s := by
  have hsub : Icc a b ⊆ J := Icc_subset_Icc ha.1 hb.2
  have hderiv_cont : ContinuousOn (derivWithin F J) J :=
    hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hint : IntervalIntegrable (derivWithin F J) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hderiv_cont.mono hsub
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hF.continuousOn.mono hsub) _ hint
  intro s hs
  have hsJ : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt hs.1, hs.2.trans_le hb.2⟩
  exact ((hF.differentiableOn (by norm_num) s
    (Ioo_subset_Icc_self hsJ)).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hsJ.1 hsJ.2)

/-- the affine jump bound in Theorem 4.4: take norms after the exact fundamental-theorem identity,
then move the norm inside the integral. -/
theorem unified_increment_norm_integral_chain {F : ℝ → E}
    (hF : ContDiffOn ℝ 1 F J) {a b : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≤ b) :
    ‖F b - F a‖ = ‖∫ s in a..b, derivWithin F J s‖ ∧
      ‖∫ s in a..b, derivWithin F J s‖ ≤
        ∫ s in a..b, ‖derivWithin F J s‖ := by
  exact ⟨congrArg norm (unified_increment_eq_integral hF ha hb hab),
    intervalIntegral.norm_integral_le_integral_norm hab⟩

/-- Theorem 4.4's common computation: express each increment as its
FTC integral and move the norm inside, then sum. Affine pieces use `a=0,b=1`
in their normalized coordinate; the smooth curve uses the physical mesh.
Both parts of the jump theorem instantiate this one finite calculation. -/
theorem unified_finite_integral_chain (T : ℕ) (F : ℕ → ℝ → E) (a b : ℕ → ℝ)
    (hF : ∀ j < T, ContDiffOn ℝ 1 (F j) J)
    (ha : ∀ j < T, a j ∈ J) (hb : ∀ j < T, b j ∈ J)
    (hab : ∀ j < T, a j ≤ b j) :
    (∑ j ∈ Finset.range T, ‖F j (b j) - F j (a j)‖) =
      (∑ j ∈ Finset.range T, ‖∫ s in a j..b j, derivWithin (F j) J s‖) ∧
    (∑ j ∈ Finset.range T, ‖∫ s in a j..b j, derivWithin (F j) J s‖) ≤
      ∑ j ∈ Finset.range T, ∫ s in a j..b j, ‖derivWithin (F j) J s‖ := by
  have hcell (j : ℕ) (hj : j < T) :=
    unified_increment_norm_integral_chain (hF j hj) (ha j hj) (hb j hj) (hab j hj)
  exact ⟨Finset.sum_congr rfl (fun j hj ↦ (hcell j (Finset.mem_range.mp hj)).1),
    Finset.sum_le_sum (fun j hj ↦ (hcell j (Finset.mem_range.mp hj)).2)⟩

/-- the C² jump bound in Theorem 4.6: the sum of increment norms is exactly the sum of norms
of the derivative integrals on the adjacent sampling intervals. -/
theorem unified_mesh_norm_eq_integrals {F : ℝ → E}
    (hF : ContDiffOn ℝ 1 F J) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.range T, ‖F (((j : ℝ) + 1) / T) - F (j / T)‖) =
      ∑ j ∈ Finset.range T,
        ‖∫ s in (j : ℝ) / T..((j : ℝ) + 1) / T, derivWithin F J s‖ := by
  have htr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hmem (j : ℕ) (hj : j ≤ T) : (j : ℝ) / T ∈ J :=
    ⟨by positivity, (div_le_one htr).mpr (by exact_mod_cast hj)⟩
  have hchain := unified_finite_integral_chain T (fun _ ↦ F)
    (fun j ↦ (j : ℝ) / T) (fun j ↦ ((j + 1 : ℕ) : ℝ) / T)
    (fun _ _ ↦ hF) (fun j hj ↦ hmem j hj.le) (fun j hj ↦ hmem (j + 1) hj)
    (fun j _ ↦ div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) htr.le)
  simpa only [Nat.cast_add, Nat.cast_one] using hchain.1

/-- the C² jump bound in Theorem 4.6: move each norm inside its cell integral and join the
adjacent cells, obtaining one integral of the derivative norm. -/
theorem unified_mesh_norm_integrals_le {F : ℝ → E}
    (hF : ContDiffOn ℝ 1 F J) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.range T,
      ‖∫ s in (j : ℝ) / T..((j : ℝ) + 1) / T, derivWithin F J s‖) ≤
      ∫ s in (0 : ℝ)..1, ‖derivWithin F J s‖ := by
  have htr : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hc : ContinuousOn (fun s ↦ ‖derivWithin F J s‖) J :=
    (hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).norm
  have hmem (j : ℕ) (hj : j ≤ T) : (j : ℝ) / T ∈ J :=
    ⟨by positivity, (div_le_one htr).mpr (by exact_mod_cast hj)⟩
  have hcell (j : ℕ) (hj : j < T) :
      IntervalIntegrable (fun s ↦ ‖derivWithin F J s‖) volume
        (j / T) ((j + 1 : ℕ) / T) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.le_succ j) htr.le)]
    exact hc.mono (Icc_subset_Icc (hmem j hj.le).1 (hmem (j + 1) hj).2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ (j : ℝ) / T) hcell
  calc
    _ ≤ ∑ j ∈ Finset.range T,
        ∫ s in (j : ℝ) / T..((j + 1 : ℕ) : ℝ) / T,
          ‖derivWithin F J s‖ := by
      have hchain := unified_finite_integral_chain T (fun _ ↦ F)
        (fun j ↦ (j : ℝ) / T) (fun j ↦ ((j + 1 : ℕ) : ℝ) / T)
        (fun _ _ ↦ hF) (fun j hj ↦ hmem j hj.le) (fun j hj ↦ hmem (j + 1) hj)
        (fun j _ ↦ div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.le_succ j) htr.le)
      simpa only [Nat.cast_add, Nat.cast_one] using hchain.2
    _ = _ := by simpa only [Nat.cast_zero, zero_div, div_self htr.ne'] using hsum

/-- Integrate a continuous majorant after the exact increment identity and the
norm-integral inequality. This is the route displayed in the affine jump bound in Theorem 4.4. -/
theorem unified_increment_integral_via_ftc {F : ℝ → E} {g : ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F J)
    (hbound : ∀ s ∈ J, ‖derivWithin F J s‖ ≤ g s)
    (hi : IntervalIntegrable g volume 0 1) {a b : ℝ}
    (ha : a ∈ J) (hb : b ∈ J) (hab : a ≤ b) :
    ‖F b - F a‖ ≤ ∫ s in a..b, g s := by
  have hsub : Icc a b ⊆ J := Icc_subset_Icc ha.1 hb.2
  have hc : ContinuousOn (fun s ↦ ‖derivWithin F J s‖) J :=
    (hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).norm
  have hiF : IntervalIntegrable (fun s ↦ ‖derivWithin F J s‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.mono hsub
  have hig : IntervalIntegrable g volume a b := hi.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact hsub)
  obtain ⟨heq, hnorm⟩ := unified_increment_norm_integral_chain hF ha hb hab
  rw [heq]
  exact hnorm.trans (intervalIntegral.integral_mono_on (μ := volume)
    hab hiF hig (fun s hs ↦ hbound s (hsub hs)))

/-- the C² jump bound in Theorem 4.6's full mesh route: replace increments by exact derivative
integrals, move norms inside, join cells, and insert the pointwise majorant. -/
theorem unified_mesh_integral_via_ftc {F : ℝ → E} {g : ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F J)
    (hbound : ∀ s ∈ J, ‖derivWithin F J s‖ ≤ g s)
    (hi : IntervalIntegrable g volume 0 1) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.range T, ‖F (((j : ℝ) + 1) / T) - F (j / T)‖) ≤
      ∫ s in (0 : ℝ)..1, g s := by
  have hc : ContinuousOn (fun s ↦ ‖derivWithin F J s‖) J :=
    (hF.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).norm
  have hiF := hc.intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [unified_mesh_norm_eq_integrals hF hT]
  exact (unified_mesh_norm_integrals_le hF hT).trans
    (intervalIntegral.integral_mono_on (μ := volume) zero_le_one hiF hi hbound)


end UnitaryProducts.PaperProof
