/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import RoundedClocks.Preliminaries.Basic

/-! # Example 5.1: the gap-adapted schedule

For the affine path `(1-x)H₀ + xH₁` with `‖H₀‖ ≤ 1` and `‖H₁‖ ≤ 1`, every eigenvalue lies in
`[-1,1]`, so `Γ ≤ 2` and every sample has eigenvalue differences of modulus at most `2`.
Integrating `Γ(u)^{-p} u' = c_p` gives `u(1) = 1`, and `H' = c_p Γ(u)^p (H₁ - H₀)` gives the three
displayed lines. Here `gapInterp H₀ H₁ x` is `(1-x)H₀ + xH₁`, and `Γ(x)` is
`leastEigenvalueGap (gapInterp H₀ H₁ x)`. The Lipschitz constant of `Γ` is in
`GapAdaptedSpectralGap.lean`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace Topology
open Finset Matrix Module Real Set MeasureTheory

noncomputable section

namespace RoundedClocks

variable {n : ℕ}

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ

/-- The affine path `(1-x)H₀ + xH₁` of Example 5.1. -/
def gapInterp (H₀ H₁ : Mat) (x : ℝ) : Mat := (1 - x) • H₀ + x • H₁

/-- `(1-x)H₀ + xH₁` is Hermitian. -/
theorem gapInterp_hermitian {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (x : ℝ) : IsHermitian (gapInterp H₀ H₁ x) := by
  exact ((IsSelfAdjoint.all (1 - x)).smul h₀).add ((IsSelfAdjoint.all x).smul h₁)

/-- `((1-x)H₀ + xH₁) - ((1-y)H₀ + yH₁) = (x - y)(H₁ - H₀)`. -/
theorem gapInterp_sub (H₀ H₁ : Mat) (x y : ℝ) :
    gapInterp H₀ H₁ x - gapInterp H₀ H₁ y = (x - y) • (H₁ - H₀) := by
  have h := (AffineMap.lineMap (k := ℝ) H₀ H₁).linearMap_vsub x y
  simpa [gapInterp, AffineMap.lineMap_apply_module] using h.symm

/-- `‖(1-x)H₀ + xH₁‖ ≤ 1` for `x ∈ [0,1]`, when `‖H₀‖ ≤ 1` and `‖H₁‖ ≤ 1`. -/
theorem gapInterp_norm_le {H₀ H₁ : Mat} (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : ‖gapInterp H₀ H₁ x‖ ≤ 1 := by
  exact mem_closedBall_zero_iff.mp <| convex_closedBall 0 1 (mem_closedBall_zero_iff.mpr hn₀)
    (mem_closedBall_zero_iff.mpr hn₁) (sub_nonneg.mpr hx.2) hx.1 (sub_add_cancel 1 x)

/-- The eigenvalues of `(1-x)H₀ + xH₁` in decreasing order; index `Fin.last n` is the least
eigenvalue. -/
def gapEigen (H₀ H₁ : Mat) (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (k : Fin (n + 1)) (x : ℝ) : ℝ :=
  (gapInterp_hermitian h₀ h₁ x).eigenvalues₀ ⟨k, by simpa using k.isLt⟩

/-- The last eigenvalue in decreasing order is the least one. -/
theorem gapEigen_least {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (k : Fin (n + 1)) (x : ℝ) :
    gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x ≤ gapEigen H₀ H₁ h₀ h₁ k x := by
  apply (gapInterp_hermitian h₀ h₁ x).eigenvalues₀_antitone
  exact k.le_last

/-- `Gamma` is the least positive difference between an eigenvalue of `(1-x)H₀ + xH₁` and its least
eigenvalue: the spectral gap `Γ(x)` of the least eigenvalue, in terms of the eigenvalues in
decreasing order. -/
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

/-- A real number is an eigenvalue of a Hermitian matrix exactly when it occurs in the decreasing
list of its eigenvalues. -/
private theorem ofReal_mem_spectrum_iff {A : Mat} (hA : IsHermitian A) (x : ℝ) :
    (x : ℂ) ∈ spectrum ℂ A ↔
      ∃ j : Fin (Fintype.card (Fin (n + 1))), hA.eigenvalues₀ j = x := by
  have h : Set.range hA.eigenvalues = Set.range hA.eigenvalues₀ :=
    EquivLike.range_comp hA.eigenvalues₀ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  simpa [hA.spectrum_eq_image_range] using Set.ext_iff.mp h x

/-- The least eigenvalue is the last one in decreasing order. -/
theorem leastEigenvalue_eq {A : Mat} (hA : IsHermitian A) :
    leastEigenvalue A = hA.eigenvalues₀ ⟨Fin.last n, by simp⟩ := by
  simpa only [Function.comp_apply, Fintype.card_fin, finCongr_apply, Nat.add_sub_cancel,
    Fin.val_last] using (sorted_eigenvalues hA).2.csInf_eq

/-- `leastEigenvalueGap A ≥ 0`, also when `A` has only one eigenvalue. -/
theorem leastEigenvalueGap_nonneg (A : Mat) : 0 ≤ leastEigenvalueGap A := by
  exact Real.sInf_nonneg (by rintro r ⟨y, -, hy, rfl⟩; exact sub_nonneg.mpr hy.le)

/-- A positive `leastEigenvalueGap A` is the least positive difference between an eigenvalue of `A`
and its least eigenvalue. -/
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

/-- When `Γ(x) > 0`, `Γ(x) = leastEigenvalueGap ((1-x)H₀ + xH₁)` is the least positive difference
between an eigenvalue and the least eigenvalue. -/
theorem isLeastGap_leastEigenvalueGap {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    {x : ℝ} (hpos : 0 < leastEigenvalueGap (gapInterp H₀ H₁ x)) :
    IsLeastGap H₀ H₁ h₀ h₁ x (leastEigenvalueGap (gapInterp H₀ H₁ x)) :=
  leastGap_of_pos (gapInterp_hermitian h₀ h₁ x) hpos

/-- `Γ(x) ≥ Γ_*` for `x ∈ [0,1]`, where `Γ_* = inf_{x ∈ [0,1]} Γ(x)`. -/
theorem sInf_leastEigenvalueGap_le (H₀ H₁ : Mat) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sInf ((fun x : ℝ ↦ leastEigenvalueGap (gapInterp H₀ H₁ x)) '' Icc 0 1) ≤
      leastEigenvalueGap (gapInterp H₀ H₁ x) := by
  refine csInf_le ⟨0, ?_⟩ ⟨x, hx, rfl⟩
  rintro _ ⟨z, -, rfl⟩
  exact leastEigenvalueGap_nonneg (gapInterp H₀ H₁ z)

/-- Weyl: every eigenvalue of `(1-x)H₀ + xH₁` lies in `[-1,1]`. -/
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

/-- Every sample `(1-x)H₀ + xH₁` has eigenvalue differences of modulus at most `2`. -/
theorem gapInterp_width {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (i j : Fin (n + 1)) :
    |(gapInterp_hermitian h₀ h₁ x).eigenvalues i -
      (gapInterp_hermitian h₀ h₁ x).eigenvalues j| ≤ 2 := by
  have hi := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx i
  have hj := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx j
  exact abs_sub_le_iff.mpr ⟨by linarith [hi.2, hj.1], by linarith [hi.1, hj.2]⟩

/-- `Γ ≤ 2`, for `Γ` given as the least positive difference from the least eigenvalue. -/
theorem gap_le_two {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x Gamma : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hGamma : IsLeastGap H₀ H₁ h₀ h₁ x Gamma) : Gamma ≤ 2 := by
  obtain ⟨k, hk, rfl⟩ := hGamma.1
  have hw := gapInterp_width h₀ h₁ hn₀ hn₁ hx
    (eigenvalueIndexEquiv (n + 1) ⟨k, by simpa using k.isLt⟩)
    (eigenvalueIndexEquiv (n + 1) ⟨Fin.last n, by simp⟩)
  rw [eigenvalues_eigenvalueIndexEquiv, eigenvalues_eigenvalueIndexEquiv] at hw
  exact (le_abs_self _).trans hw

/-- Example 5.1: `Γ ≤ 2`, as the eigenvalues of `(1-x)H₀ + xH₁` lie in `[-1,1]`. -/
theorem leastEigenvalueGap_le_two {H₀ H₁ : Mat} (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hpos : 0 < leastEigenvalueGap (gapInterp H₀ H₁ x)) :
    leastEigenvalueGap (gapInterp H₀ H₁ x) ≤ 2 :=
  gap_le_two h₀ h₁ hn₀ hn₁ hx (isLeastGap_leastEigenvalueGap h₀ h₁ hpos)

/-- `y ↦ y^p` has Lipschitz constant `p 2^{p-1}` for `0 ≤ y ≤ 2`. -/
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

/-- `c_p = ∫₀¹ Γ(x)^{-p} dx > 0`. -/
theorem gap_normalization_pos {Gamma : ℝ → ℝ}
    (hGamma : ContinuousOn Gamma (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Gamma x) (p : ℝ) :
    0 < ∫ x in (0 : ℝ)..1, Gamma x ^ (-p) := by
  have hc : ContinuousOn (fun x ↦ Gamma x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hGamma.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  exact intervalIntegral.integral_pos (by norm_num) hc
    (fun x hx ↦ (Real.rpow_pos_of_pos (hpos x ⟨hx.1.le, hx.2⟩) _).le)
    ⟨0, by norm_num, Real.rpow_pos_of_pos (hpos 0 (by norm_num)) _⟩

/-- Integrating `Γ(u)^{-p} u' = c_p` from `0` to `s`: `∫₀^{u(s)} Γ(x)^{-p} dx = c_p s`. -/
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

/-- Integrating `Γ(u)^{-p} u' = c_p` gives `u(1) = 1`. -/
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

/-- `u` has Lipschitz constant `2^p c_p`, as `u' = c_p Γ(u)^p` and `Γ ≤ 2`. -/
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

/-- `H' = u' (H₁ - H₀)` for `H = (1-u)H₀ + uH₁`. -/
theorem gap_schedule_derivative (H₀ H₁ : Mat) {u : ℝ → ℝ} {s v : ℝ}
    (hu : HasDerivWithinAt u v (Icc 0 1) s) :
    HasDerivWithinAt (fun s ↦ gapInterp H₀ H₁ (u s)) (v • (H₁ - H₀))
      (Icc 0 1) s := by
  have h := (AffineMap.hasDerivAt_lineMap (a := H₀) (b := H₁)
    (x := u s)).scomp_hasDerivWithinAt s hu
  simpa [Function.comp_def, gapInterp, AffineMap.lineMap_apply_module] using h

/-- The second displayed line of Example 5.1: `‖H'‖∞ ≤ 2^p c_p ‖H₁ - H₀‖`, as `Γ ≤ 2`. -/
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

/-- The third displayed line of Example 5.1: `H'` has Lipschitz constant `p 4^p c_p² ‖H₁ - H₀‖²`,
the product of the Lipschitz constants `p 2^{p-1}` of `y ↦ y^p`, `2‖H₁ - H₀‖` of `Γ`, and `2^p c_p`
of `u`, times `c_p ‖H₁ - H₀‖`. -/
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

/-- The first displayed line of Example 5.1: `‖H'(0)‖ + ‖H'(1)‖ = c_p ‖H₁ - H₀‖ (Γ(0)^p + Γ(1)^p)`.
-/
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
