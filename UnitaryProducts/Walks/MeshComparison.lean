/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.CorrectorData

/-!
# Mesh bounds for the walk comparison

## Declarations

- `walkCubic_interval_bound`
- `walkCubic_interval_nonneg`
- `walk_cubic_data_nonneg`
- `walk_cubic_jump_of_derivative`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Real Set MeasureTheory Filter UnitaryProducts.Corrector UnitaryProducts

noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Sup norms over an interval are nonnegative. -/
theorem walkCubic_interval_nonneg (F : ℝ → 𝕄) (a b : ℝ) :
    0 ≤ intervalSupNorm F a b :=
  Real.sSup_nonneg (by rintro y ⟨s, _, rfl⟩; exact norm_nonneg _)

/-- A value of a continuous $F$ on $[0,1]$ is at most its sup over an interval containing the
point. -/
theorem walkCubic_interval_bound {F : ℝ → 𝕄}
    (hc : ContinuousOn F (Icc (0 : ℝ) 1)) {a b s : ℝ}
    (hsub : Icc a b ⊆ Icc (0 : ℝ) 1) (hs : s ∈ Icc a b) :
    ‖F s‖ ≤ intervalSupNorm F a b :=
  le_csSup (isCompact_Icc.bddAbove_image (hc.mono hsub).norm) ⟨s, hs, rfl⟩

/-- One corrector jump from a derivative bound, by the mean-value inequality: if the end value
$F = $ `frameOp H Hd` has derivative of norm at most `frameBound w`$\,\|H''\|$ +
`dcoef`$\,\|W'\|^2$ on $(0,1)$ and $\|H''\| \le S\|W''\| + R\|W'\|^2$, then
$\|F((j+2)/T) - F((j+1)/T)\|$ is at most
(`frameBound w`$\,(Sm_2 + Rm_1^2)$ + `dcoef`$\,m_1^2)/T$, with $m_1$ and $m_2$ the maxima of
$\|W'\|$ and $\|W''\|$ on mesh cell $j + 1$, respectively. The proof of the walk comparison uses
it with
the spectral comparison's `dcoef` $= \eta$. -/
theorem walk_cubic_jump_of_derivative
    (H Hd Hdd Wd Wdd : ℝ → 𝕄) (T j : ℕ) (w S R dcoef : ℝ)
    (hj : j + 2 < T) (hw0 : 0 ≤ w)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hdcoef : 0 ≤ dcoef)
    (hWd : ContinuousOn Wd (Icc (0 : ℝ) 1)) (hWdd : ContinuousOn Wdd (Icc (0 : ℝ) 1))
    (hsecond : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hdd s‖ ≤ S * ‖Wdd s‖ + R * ‖Wd s‖ ^ 2)
    (hframe : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ Fd : 𝕄,
      HasDerivAt (fun t ↦ frameOp (H t) (Hd t)) Fd s ∧
        ‖Fd‖ ≤ frameBound w * ‖Hdd s‖ + dcoef * ‖Wd s‖ ^ 2) :
    ‖frameOp (H ((j + 2 : ℕ) / T)) (Hd ((j + 2 : ℕ) / T)) -
      frameOp (H ((j + 1 : ℕ) / T)) (Hd ((j + 1 : ℕ) / T))‖ ≤
      (frameBound w*(S*meshSupNorm Wdd T (j + 1)+R*(meshSupNorm Wd T (j + 1)) ^ 2)+
        dcoef*(meshSupNorm Wd T (j + 1)) ^ 2)/T := by
  let a : ℝ := (j+1 : ℕ)/T
  let b : ℝ := (j + 2 : ℕ)/T
  let J : ℝ := frameBound w*(S*meshSupNorm Wdd T (j + 1)+R*(meshSupNorm Wd T (j + 1)) ^ 2)+
    dcoef*(meshSupNorm Wd T (j + 1))^2
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hab : a ≤ b := div_le_div_of_nonneg_right (Nat.cast_le.mpr (by omega)) hTR.le
  have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun t ht ↦
    ⟨(div_pos (Nat.cast_pos.mpr (by omega)) hTR).trans_le ht.1,
      ht.2.trans_lt ((div_lt_one hTR).mpr (Nat.cast_lt.mpr hj))⟩
  have hmesh : Icc a b ⊆ meshInterval T (j + 1) := Icc_subset_Icc
    (div_le_div_of_nonneg_right (max_le (Nat.cast_nonneg _) (by linarith)) hTR.le)
    (div_le_div_of_nonneg_right (le_min (Nat.cast_le.mpr hj.le) (by push_cast; linarith)) hTR.le)
  choose! Fd hdF hFd using hframe
  have hbound : ∀ t ∈ Icc a b, ‖Fd t‖ ≤ J := by
    intro t ht
    have hWsq : ‖Wd t‖^2 ≤ (meshSupNorm Wd T (j + 1))^2 := pow_le_pow_left₀ (norm_nonneg _)
      (walkCubic_interval_bound hWd cubic_mesh_subset (hmesh ht)) 2
    have hM : ‖Hdd t‖ ≤ S*meshSupNorm Wdd T (j + 1)+R*(meshSupNorm Wd T (j + 1))^2 :=
      (hsecond t (Ioo_subset_Icc_self (hsub ht))).trans (add_le_add (mul_le_mul_of_nonneg_left
        (walkCubic_interval_bound hWdd cubic_mesh_subset (hmesh ht)) hS)
        (mul_le_mul_of_nonneg_left hWsq hR))
    exact (hFd t (hsub ht)).trans (add_le_add (mul_le_mul_of_nonneg_left hM (frameBound_nonneg hw0))
      (mul_le_mul_of_nonneg_left hWsq hdcoef))
  have hba : b-a = 1/(T:ℝ) := by dsimp [a,b]; push_cast; ring
  simpa only [hba, abs_of_nonneg (div_nonneg zero_le_one hTR.le), mul_one_div] using
    norm_sub_le_of_derivWithin_le (fun t ht ↦ (hdF t (hsub ht)).hasDerivWithinAt) hbound a
      ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩

/-- The three walk data of `walk_unit_comparison_sharp`, the mean of the end-cell maxima of
$\|W'\|$ and the mesh moments $\|W''\|_{1,T}$, $\|W'\|_{2,T}^2$, are nonnegative. -/
theorem walk_cubic_data_nonneg (Wd Wdd : ℝ → 𝕄) (T : ℕ) :
    0 ≤ endSupMean Wd T ∧ 0 ≤ meshMoment Wdd T 1 ∧ 0 ≤ meshMoment Wd T 2 := by
  have hm (F : ℝ → 𝕄) (p : ℕ) : 0 ≤ meshMoment F T p :=
    div_nonneg (Finset.sum_nonneg (fun i _ ↦
      pow_nonneg (walkCubic_interval_nonneg F _ _) p)) (Nat.cast_nonneg T)
  exact ⟨div_nonneg (add_nonneg (walkCubic_interval_nonneg Wd _ _)
    (walkCubic_interval_nonneg Wd _ _)) zero_le_two, hm Wdd 1, hm Wd 2⟩

end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.unitSupNorm
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.intervalSupNorm
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.endSupMean
