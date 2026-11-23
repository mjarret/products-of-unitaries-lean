/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import RoundedClocks.Definitions

/-! The Weyl and calculus facts used by the gap-adapted schedule. -/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace Topology
open Finset Matrix Module Real Set MeasureTheory

noncomputable section

namespace RoundedClocks

variable {n : ℕ}

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
local notation "Tmat" => Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)
local notation "Euc" => EuclideanSpace ℂ (Fin (n + 1))

/-- The re-indexing from sorted eigenvalue positions to matrix indices. -/
private noncomputable def sortIdx (m : ℕ) : Fin (Fintype.card (Fin m)) ≃ Fin m :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- Mathlib's indexed eigenvalue at `sortIdx` is the corresponding sorted eigenvalue. -/
private theorem eigenvalues_sortIdx {A : Mat} (hA : IsHermitian A)
    (j : Fin (Fintype.card (Fin (n + 1)))) :
    hA.eigenvalues (sortIdx (n + 1) j) = hA.eigenvalues₀ j :=
  congrArg hA.eigenvalues₀ ((sortIdx (n + 1)).symm_apply_apply j)

/-- The affine Hamiltonian path used in Example 5.1. -/
def gapInterp (H₀ H₁ : Mat) (x : ℝ) : Mat := (1 - x) • H₀ + x • H₁

/-- Real affine combinations of Hermitian matrices are Hermitian. -/
theorem gapInterp_hermitian {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (x : ℝ) : IsHermitian (gapInterp H₀ H₁ x) := by
  exact (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _)) h₀).add
    (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _)) h₁)

/-- The difference of affine samples is the parameter difference times `H₁-H₀`. -/
theorem gapInterp_sub (H₀ H₁ : Mat) (x y : ℝ) :
    gapInterp H₀ H₁ x - gapInterp H₀ H₁ y = (x - y) • (H₁ - H₀) := by
  unfold gapInterp
  module

/-- The affine interpolation of two contractions is a contraction. -/
theorem gapInterp_norm_le {H₀ H₁ : Mat} (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖gapInterp H₀ H₁ x‖ ≤ 1 := by
  calc
    _ ≤ ‖(1 - x) • H₀‖ + ‖x • H₁‖ := norm_add_le _ _
    _ = (1 - x) * ‖H₀‖ + x * ‖H₁‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hx.2), abs_of_nonneg hx.1]
    _ ≤ (1 - x) * 1 + x * 1 := add_le_add
      (mul_le_mul_of_nonneg_left hn₀ (sub_nonneg.mpr hx.2))
      (mul_le_mul_of_nonneg_left hn₁ hx.1)
    _ = 1 := by ring

/-- The sorted eigenvalues along the affine path. -/
def gapEigen (H₀ H₁ : Mat) (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (k : Fin (n + 1)) (x : ℝ) : ℝ :=
  (gapInterp_hermitian h₀ h₁ x).eigenvalues₀ ⟨k, by simpa using k.isLt⟩

/-- The last decreasing eigenvalue is the least one. -/
theorem gapEigen_least {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (k : Fin (n + 1)) (x : ℝ) :
    gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x ≤ gapEigen H₀ H₁ h₀ h₁ k x := by
  apply (gapInterp_hermitian h₀ h₁ x).eigenvalues₀_antitone
  exact k.le_last

/-- The least positive difference from the least eigenvalue, in sorted coordinates. -/
def IsLeastGap (H₀ H₁ : Mat) (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (x Gamma : ℝ) : Prop :=
  (∃ k, 0 < gapEigen H₀ H₁ h₀ h₁ k x -
      gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x ∧
    Gamma = gapEigen H₀ H₁ h₀ h₁ k x -
      gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x) ∧
  ∀ k, gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x <
      gapEigen H₀ H₁ h₀ h₁ k x →
    Gamma ≤ gapEigen H₀ H₁ h₀ h₁ k x -
      gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x

/-- A real number is a Hermitian eigenvalue exactly when it is a sorted eigenvalue. -/
private theorem ofReal_mem_spectrum_iff {A : Mat} (hA : IsHermitian A) (x : ℝ) :
    (x : ℂ) ∈ spectrum ℂ A ↔
      ∃ j : Fin (Fintype.card (Fin (n + 1))), hA.eigenvalues₀ j = x := by
  rw [show (x : ℂ) = algebraMap ℝ ℂ x from rfl, spectrum.algebraMap_mem_iff,
    hA.spectrum_real_eq_range_eigenvalues]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(sortIdx (n + 1)).symm i, ?_⟩
    rw [← eigenvalues_sortIdx hA, Equiv.apply_symm_apply]
  · rintro ⟨j, rfl⟩
    exact ⟨sortIdx (n + 1) j, eigenvalues_sortIdx hA j⟩

/-- The least eigenvalue is the final sorted eigenvalue. -/
theorem leastEigenvalue_eq {A : Mat} (hA : IsHermitian A) :
    leastEigenvalue A = hA.eigenvalues₀ ⟨Fin.last n, by simp⟩ := by
  have hset : {x : ℝ | (x : ℂ) ∈ spectrum ℂ A} = Set.range hA.eigenvalues₀ := by
    ext x
    exact ofReal_mem_spectrum_iff hA x
  rw [leastEigenvalue, hset]
  apply le_antisymm
  · exact csInf_le (Set.finite_range _).bddBelow ⟨_, rfl⟩
  · refine le_csInf (Set.range_nonempty _) ?_
    rintro _ ⟨j, rfl⟩
    apply hA.eigenvalues₀_antitone
    rw [Fin.le_iff_val_le_val]
    have hj := j.isLt
    simp only [Fintype.card_fin] at hj
    simp only [Fin.val_last]
    omega

/-- A least-eigenvalue gap is nonnegative, including when the defining set is empty. -/
theorem gap_leastEigenvalueGap_nonneg (A : Mat) : 0 ≤ leastEigenvalueGap A := by
  let S := {r : ℝ | ∃ y : ℝ, (y : ℂ) ∈ spectrum ℂ A ∧ leastEigenvalue A < y ∧
    r = y - leastEigenvalue A}
  change 0 ≤ sInf S
  by_cases hS : S.Nonempty
  · refine le_csInf hS ?_
    rintro r ⟨y, _, hy, rfl⟩
    exact sub_nonneg.mpr hy.le
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]

/-- A positive least-eigenvalue gap is attained and bounds every larger eigenvalue. -/
theorem leastGap_of_pos {A : Mat} (hA : IsHermitian A) (hpos : 0 < leastEigenvalueGap A) :
    let e : Fin (n + 1) → ℝ := fun k ↦ hA.eigenvalues₀ ⟨k, by simpa using k.isLt⟩
    (∃ k, 0 < e k - e (Fin.last n) ∧ leastEigenvalueGap A = e k - e (Fin.last n)) ∧
      ∀ k, e (Fin.last n) < e k → leastEigenvalueGap A ≤ e k - e (Fin.last n) := by
  intro e
  have hm : leastEigenvalue A = e (Fin.last n) := leastEigenvalue_eq hA
  have hmem : ∀ y : ℝ, (y : ℂ) ∈ spectrum ℂ A ↔ ∃ k : Fin (n + 1), e k = y := by
    intro y
    rw [ofReal_mem_spectrum_iff hA]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j, by simpa using j.isLt⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  let S := {r : ℝ | ∃ y : ℝ, (y : ℂ) ∈ spectrum ℂ A ∧
    leastEigenvalue A < y ∧ r = y - leastEigenvalue A}
  have hgap : leastEigenvalueGap A = sInf S := rfl
  have hSfin : S.Finite := by
    apply (Set.finite_range fun k : Fin (n + 1) ↦ e k - leastEigenvalue A).subset
    rintro _ ⟨y, hy, -, rfl⟩
    obtain ⟨k, rfl⟩ := (hmem y).1 hy
    exact ⟨k, rfl⟩
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hgap, h, Real.sInf_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨y, hy, hlt, hg⟩ := hne.csInf_mem hSfin
  obtain ⟨k, rfl⟩ := (hmem y).1 hy
  rw [hm] at hlt hg
  refine ⟨⟨k, sub_pos.mpr hlt, hgap.trans hg⟩, fun j hj ↦ ?_⟩
  rw [hgap]
  refine csInf_le hSfin.bddBelow ⟨e j, (hmem _).2 ⟨j, rfl⟩, ?_, ?_⟩
  · rwa [hm]
  · rw [hm]

/-- Every eigenvalue of an affine sample lies in `[-1,1]`. -/
private theorem gapInterp_eigenvalue_bounds {H₀ H₁ : Mat}
    (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁) (hn₀ : ‖H₀‖ ≤ 1)
    (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (i : Fin (n + 1)) :
    (gapInterp_hermitian h₀ h₁ x).eigenvalues i ∈ Icc (-1 : ℝ) 1 := by
  have hi := spectrum.norm_le_norm_of_mem
    ((gapInterp_hermitian h₀ h₁ x).eigenvalues_mem_spectrum_real i)
  have hn := gapInterp_norm_le hn₀ hn₁ hx
  have hiabs : |(gapInterp_hermitian h₀ h₁ x).eigenvalues i| ≤ ‖gapInterp H₀ H₁ x‖ := by
    simpa only [Real.norm_eq_abs] using hi
  exact abs_le.mp (hiabs.trans hn)

/-- Every affine sample has eigenvalue differences at most two. -/
theorem gapInterp_width {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (i j : Fin (n + 1)) :
    |(gapInterp_hermitian h₀ h₁ x).eigenvalues i -
      (gapInterp_hermitian h₀ h₁ x).eigenvalues j| ≤ 2 := by
  have hi := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx i
  have hj := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx j
  exact abs_sub_le_iff.mpr ⟨by linarith [hi.2, hj.1], by linarith [hi.1, hj.2]⟩

/-- The least spectral gap is at most two. -/
theorem interp_gap_le_two {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x Gamma : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hGamma : IsLeastGap H₀ H₁ h₀ h₁ x Gamma) : Gamma ≤ 2 := by
  obtain ⟨k, hk, rfl⟩ := hGamma.1
  have hw := gapInterp_width h₀ h₁ hn₀ hn₁ hx (sortIdx (n + 1) ⟨k, by simpa using k.isLt⟩)
    (sortIdx (n + 1) ⟨Fin.last n, by simp⟩)
  rw [eigenvalues_sortIdx, eigenvalues_sortIdx] at hw
  exact (le_abs_self _).trans hw

/-- The power function has the Lipschitz constant used in the manuscript. -/
private theorem rpow_lipschitz_two {p x y : ℝ} (hp : 1 ≤ p)
    (hx : x ∈ Icc (0 : ℝ) 2) (hy : y ∈ Icc (0 : ℝ) 2) :
    |x ^ p - y ^ p| ≤ p * 2 ^ (p - 1) * |x - y| := by
  have hd : ∀ z ∈ Icc (0 : ℝ) 2,
      HasDerivWithinAt (fun z : ℝ ↦ z ^ p) (p * z ^ (p - 1)) (Icc 0 2) z :=
    fun z _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt
  have hb : ∀ z ∈ Icc (0 : ℝ) 2, ‖p * z ^ (p - 1)‖ ≤ p * 2 ^ (p - 1) := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg hz.1 _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1 hz.2 (by linarith)) (by linarith)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

/-- The normalizing inverse-gap integral is positive. -/
theorem gap_normalization_pos {Gamma : ℝ → ℝ}
    (hGamma : ContinuousOn Gamma (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Gamma x) (p : ℝ) :
    0 < ∫ x in (0 : ℝ)..1, Gamma x ^ (-p) := by
  have hc : ContinuousOn (fun x ↦ Gamma x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hGamma.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  exact intervalIntegral.integral_pos (by norm_num) hc
    (fun x hx ↦ (Real.rpow_pos_of_pos (hpos x ⟨hx.1.le, hx.2⟩) _).le)
    ⟨0, by norm_num, Real.rpow_pos_of_pos (hpos 0 (by norm_num)) _⟩

/-- Integrating the schedule ODE gives the normalized inverse-gap primitive. -/
private theorem gap_schedule_integral {Gamma u : ℝ → ℝ} {p : ℝ}
    (hGamma : ContinuousOn Gamma (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Gamma x) (hu0 : u 0 = 0)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Gamma x ^ (-p)) * Gamma (u s) ^ p)
        (Icc 0 1) s) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..u s, Gamma x ^ (-p) =
      (∫ x in (0 : ℝ)..1, Gamma x ^ (-p)) * s := by
  let cp := ∫ x in (0 : ℝ)..1, Gamma x ^ (-p)
  have huc : ContinuousOn u (Icc (0 : ℝ) 1) := fun x hx ↦ (hu x hx).continuousWithinAt
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hs.2
  have hpow : ContinuousOn (fun x ↦ Gamma x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hGamma.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hud : ContinuousOn (fun x ↦ cp * Gamma (u x) ^ p) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((hGamma.comp huc hurange).rpow_const
      (fun x hx ↦ Or.inl (ne_of_gt (hpos (u x) (hurange hx)))))
  have hchange := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := s) (f := u) (f' := fun x ↦ cp * Gamma (u x) ^ p)
    (g := fun x ↦ Gamma x ^ (-p))
    (by simpa only [uIcc_of_le hs.1] using huc.mono hsub)
    (fun x hx ↦ ((hu x ⟨by simpa only [min_eq_left hs.1] using hx.1.le,
      (by simpa only [max_eq_right hs.1] using hx.2.le : x ≤ s).trans hs.2⟩).hasDerivAt
        (Icc_mem_nhds (by simpa only [min_eq_left hs.1] using hx.1)
          (lt_of_lt_of_le (by simpa only [max_eq_right hs.1] using hx.2) hs.2))).hasDerivWithinAt)
    (by simpa only [uIcc_of_le hs.1] using hud.mono hsub)
    (hpow.mono (by rintro z ⟨x, hx, rfl⟩; exact hurange (hsub (by
      simpa only [uIcc_of_le hs.1] using hx))))
  have hint : (∫ x in (0 : ℝ)..s, ((fun x ↦ Gamma x ^ (-p)) ∘ u) x *
      (cp * Gamma (u x) ^ p)) = cp * s := by
    have heq : ∀ x ∈ uIcc (0 : ℝ) s,
        ((fun x ↦ Gamma x ^ (-p)) ∘ u) x * (cp * Gamma (u x) ^ p) = cp := by
      intro x hx
      have hx' := hsub (show x ∈ Icc (0 : ℝ) s by simpa only [uIcc_of_le hs.1] using hx)
      have hr := Real.rpow_add (hpos (u x) (hurange hx')) (-p) p
      simp only [neg_add_cancel, Real.rpow_zero] at hr
      dsimp only [Function.comp_apply]
      calc
        _ = cp * (Gamma (u x) ^ (-p) * Gamma (u x) ^ p) := by ring
        _ = cp := by rw [← hr, mul_one]
    rw [intervalIntegral.integral_congr heq]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hu0] at hchange
  exact hchange.symm.trans hint

/-- The normalizing integral makes the schedule reach `u(1)=1`. -/
theorem gap_schedule_endpoint {Gamma u : ℝ → ℝ} {p : ℝ}
    (hGamma : ContinuousOn Gamma (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Gamma x) (hu0 : u 0 = 0)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Gamma x ^ (-p)) * Gamma (u s) ^ p)
        (Icc 0 1) s) : u 1 = 1 := by
  have hone := gap_schedule_integral hGamma hpos hu0 hurange hu (s := 1) (by norm_num)
  rw [mul_one] at hone
  have hrange := hurange (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  by_contra hne
  have hlt : u 1 < 1 := lt_of_le_of_ne hrange.2 hne
  have hpow : ContinuousOn (fun x ↦ Gamma x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hGamma.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hsmall : Icc (u 1) 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hrange.1 le_rfl
  have hpositive : 0 < ∫ x in u 1..1, Gamma x ^ (-p) :=
    intervalIntegral.integral_pos hlt (hpow.mono hsmall)
      (fun x hx ↦ (Real.rpow_pos_of_pos (hpos x (hsmall ⟨hx.1.le, hx.2⟩)) _).le)
      ⟨1, ⟨hlt.le, le_rfl⟩, Real.rpow_pos_of_pos (hpos 1 (by norm_num)) _⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hpow.mono (Icc_subset_Icc le_rfl hrange.2)).intervalIntegrable_of_Icc hrange.1)
    ((hpow.mono hsmall).intervalIntegrable_of_Icc hlt.le)
  linarith

/-- The ODE and `Gamma ≤ 2` give the schedule's Lipschitz bound. -/
private theorem gap_schedule_lipschitz {Gamma u : ℝ → ℝ} {p cp : ℝ} (hp : 0 ≤ p)
    (hcp : 0 ≤ cp) (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, Gamma x ∈ Icc (0 : ℝ) 2)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u (cp * Gamma (u s) ^ p) (Icc 0 1) s)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |u t - u s| ≤ 2 ^ p * cp * |t - s| := by
  have hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖cp * Gamma (u x) ^ p‖ ≤ 2 ^ p * cp := by
    intro x hx
    have hg := hGamma (u x) (hurange hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hg.1 _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hg.1 hg.2 hp) hcp
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hu hb hs ht

/-- Differentiating the scheduled affine Hamiltonian. -/
theorem gap_schedule_derivative (H₀ H₁ : Mat) {u : ℝ → ℝ} {s v : ℝ}
    (hu : HasDerivWithinAt u v (Icc 0 1) s) :
    HasDerivWithinAt (fun s ↦ gapInterp H₀ H₁ (u s)) (v • (H₁ - H₀))
      (Icc 0 1) s := by
  have heq : (fun s ↦ gapInterp H₀ H₁ (u s)) =
      (fun s ↦ H₀ + u s • (H₁ - H₀)) := by
    funext x
    unfold gapInterp
    module
  rw [heq]
  simpa using (hu.smul_const (H₁ - H₀)).const_add H₀

/-- The derivative supremum bound in Example 5.1. -/
theorem gap_derivative_supNorm_le (D : Mat) {Gamma u : ℝ → ℝ} {p cp : ℝ}
    (hp : 0 ≤ p) (hcp : 0 ≤ cp)
    (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, Gamma x ∈ Icc (0 : ℝ) 2)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    supNorm (fun s ↦ (cp * Gamma (u s) ^ p) • D) ≤ 2 ^ p * cp * ‖D‖ := by
  unfold supNorm
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨0, by norm_num, rfl⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hg := hGamma (u s) (hurange hs)
    dsimp only
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hg.1 _))]
    calc
      _ ≤ (cp * 2 ^ p) * ‖D‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg.1 hg.2 hp) hcp) (norm_nonneg _)
      _ = _ := by ring

/-- Multiplying the manuscript's three Lipschitz constants. -/
theorem gap_derivative_lipschitz (D : Mat) {Gamma u : ℝ → ℝ} {p cp : ℝ}
    (hp : 1 ≤ p) (hcp : 0 ≤ cp)
    (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, Gamma x ∈ Icc (0 : ℝ) 2)
    (hGammalip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |Gamma x - Gamma y| ≤ 2 * ‖D‖ * |x - y|)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u (cp * Gamma (u s) ^ p) (Icc 0 1) s)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(cp * Gamma (u t) ^ p) • D - (cp * Gamma (u s) ^ p) • D‖ ≤
      p * 4 ^ p * cp ^ 2 * ‖D‖ ^ 2 * |t - s| := by
  have hpzero : 0 ≤ p := by linarith
  have hpconst : 0 ≤ p * 2 ^ (p - 1) :=
    mul_nonneg hpzero (Real.rpow_nonneg (by norm_num) _)
  have hup := gap_schedule_lipschitz hpzero hcp hGamma hurange hu hs ht
  have hgap := hGammalip (u t) (hurange ht) (u s) (hurange hs)
  have hpower := rpow_lipschitz_two hp (hGamma (u t) (hurange ht))
    (hGamma (u s) (hurange hs))
  have hfour : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
  calc
    _ = cp * |Gamma (u t) ^ p - Gamma (u s) ^ p| * ‖D‖ := by
      rw [← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hcp]
    _ ≤ cp * (p * 2 ^ (p - 1) * |Gamma (u t) - Gamma (u s)|) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hcp) (norm_nonneg _)
    _ ≤ cp * (p * 2 ^ (p - 1) * (2 * ‖D‖ * |u t - u s|)) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgap hpconst) hcp) (norm_nonneg _)
    _ ≤ cp * (p * 2 ^ (p - 1) * (2 * ‖D‖ * (2 ^ p * cp * |t - s|))) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup (by positivity)) hpconst)
        hcp) (norm_nonneg _)
    _ = _ := by rw [Real.rpow_sub_one (by norm_num), hfour]; ring

/-- The endpoint derivative identity in Example 5.1. -/
theorem gap_derivative_endpoints (D : Mat) {Gamma u : ℝ → ℝ} {p cp : ℝ}
    (hcp : 0 ≤ cp) (hGamma0 : 0 ≤ Gamma 0) (hGamma1 : 0 ≤ Gamma 1)
    (hu0 : u 0 = 0) (hu1 : u 1 = 1) :
    ‖(cp * Gamma (u 0) ^ p) • D‖ + ‖(cp * Gamma (u 1) ^ p) • D‖ =
      cp * ‖D‖ * (Gamma 0 ^ p + Gamma 1 ^ p) := by
  rw [hu0, hu1, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hGamma0 _)),
    abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hGamma1 _))]
  ring

end RoundedClocks
