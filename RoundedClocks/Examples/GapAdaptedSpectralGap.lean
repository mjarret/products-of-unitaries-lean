/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.GapAdapted
public import RoundedClocks.UnitSteps.unitary_products

/-! # The spectral gap along an affine path

Ordered eigenvalues and the least spectral gap vary Lipschitz-continuously along the affine path.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace Topology
open Finset Matrix Module Real Set MeasureTheory

noncomputable section

namespace RoundedClocks.GapAdaptedSpectralGap

variable {n : ℕ}

local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ

/-- Bhatia's ordered-eigenvalue bound along the affine path. -/
theorem eigen_lipschitz (bhatia : Bhatia_Corollary_III_2_6)
    {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (k : Fin (n + 1)) (x y : ℝ) :
    |gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ k y| ≤
      ‖H₁ - H₀‖ * |x - y| := by
  have hA := gapInterp_hermitian h₀ h₁ x
  have hB := gapInterp_hermitian h₀ h₁ y
  have h := bhatia (n + 1) (gapInterp H₀ H₁ x) (gapInterp H₀ H₁ y)
    _ _ hA hB (RoundedClocks.sorted_eigenvalues hA).1
    (RoundedClocks.sorted_eigenvalues hB).1 k
  simpa only [gapEigen, Function.comp_apply, finCongr_apply, gapInterp_sub,
    norm_smul, Real.norm_eq_abs, mul_comm] using h

/-- Every ordered eigenvalue depends continuously on the path parameter. -/
theorem eigen_continuous (bhatia : Bhatia_Corollary_III_2_6)
    {H₀ H₁ : Mat} (h₀ : IsHermitian H₀)
    (h₁ : IsHermitian H₁) (k : Fin (n + 1)) :
    Continuous (gapEigen H₀ H₁ h₀ h₁ k) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨‖H₁ - H₀‖, norm_nonneg _⟩) ?_).continuous
  intro x y
  simpa only [Real.dist_eq] using eigen_lipschitz bhatia h₀ h₁ k x y

/-- A continuous nonnegative function uniformly separated from zero cannot cross zero. -/
theorem zero_iff {f : ℝ → ℝ} {g : ℝ} (hg : 0 < g)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hsep : ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 ∨ g ≤ f x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    f x = 0 ↔ f y = 0 := by
  suffices h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x = 0 → f y = 0 by
    exact ⟨h x hx y hy, h y hy x hx⟩
  intro a ha b hb hfa
  rcases hsep b hb with hfb | hfb
  · exact hfb
  · have hmid : g / 2 ∈ Icc (f a) (f b) := by constructor <;> linarith
    obtain ⟨z, hz, hzg⟩ := (convex_Icc (0 : ℝ) 1).isPreconnected.intermediate_value
      ha hb hf hmid
    rcases hsep z hz with heq | hge <;> linarith

/-- A uniform positive gap makes the ground-space multiplicity constant. -/
theorem ground_indices_constant (bhatia : Bhatia_Corollary_III_2_6)
    {H₀ H₁ : Mat}
    (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁) (Gamma : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Gamma x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Gamma x) (k : Fin (n + 1))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    gapEigen H₀ H₁ h₀ h₁ k x = gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x ↔
      gapEigen H₀ H₁ h₀ h₁ k y =
        gapEigen H₀ H₁ h₀ h₁ (Fin.last n) y := by
  have hcont : ContinuousOn (fun z ↦ gapEigen H₀ H₁ h₀ h₁ k z -
      gapEigen H₀ H₁ h₀ h₁ (Fin.last n) z) (Icc (0 : ℝ) 1) :=
    ((eigen_continuous bhatia h₀ h₁ k).sub
      (eigen_continuous bhatia h₀ h₁ (Fin.last n))).continuousOn
  have hsep : ∀ z ∈ Icc (0 : ℝ) 1,
      gapEigen H₀ H₁ h₀ h₁ k z -
        gapEigen H₀ H₁ h₀ h₁ (Fin.last n) z = 0 ∨
      g ≤ gapEigen H₀ H₁ h₀ h₁ k z -
        gapEigen H₀ H₁ h₀ h₁ (Fin.last n) z := by
    intro z hz
    rcases (gapEigen_least h₀ h₁ k z).eq_or_lt with heq | hlt
    · exact Or.inl (sub_eq_zero.mpr heq.symm)
    · exact Or.inr ((hlow z hz).trans ((hGamma z hz).2 k hlt))
  simpa only [sub_eq_zero] using zero_iff hg hcont hsep hx hy

/-- One fixed sorted position is the first excited level along a uniformly gapped path. -/
theorem first_excited_fixed (bhatia : Bhatia_Corollary_III_2_6)
    {H₀ H₁ : Mat}
    (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁) (Gamma : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Gamma x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Gamma x) :
    ∃ k : Fin (n + 1), ∀ x ∈ Icc (0 : ℝ) 1,
      Gamma x = gapEigen H₀ H₁ h₀ h₁ k x -
        gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x := by
  classical
  let S := Finset.univ.filter fun k ↦
    gapEigen H₀ H₁ h₀ h₁ (Fin.last n) 0 < gapEigen H₀ H₁ h₀ h₁ k 0
  have hS : S.Nonempty := by
    obtain ⟨k, hk, -⟩ := (hGamma 0 (by norm_num)).1
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_pos.mp hk⟩⟩
  let k := S.max' hS
  have hk : k ∈ S := S.max'_mem hS
  refine ⟨k, ?_⟩
  intro x hx
  have hpositive : ∀ j, j ∈ S ↔ gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x <
      gapEigen H₀ H₁ h₀ h₁ j x := by
    intro j
    have heq := ground_indices_constant bhatia h₀ h₁ Gamma hg hGamma hlow j
      (x := 0) (by norm_num) hx
    have hzero := gapEigen_least h₀ h₁ j 0
    have hxleast := gapEigen_least h₀ h₁ j x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hlt
      apply lt_of_le_of_ne hxleast
      intro he
      have := heq.mpr he.symm
      linarith
    · intro hlt
      apply lt_of_le_of_ne hzero
      intro he
      have := heq.mp he.symm
      linarith
  apply le_antisymm ((hGamma x hx).2 k ((hpositive k).mp hk))
  obtain ⟨j, hj, heq⟩ := (hGamma x hx).1
  have hjS := (hpositive j).mpr (sub_pos.mp hj)
  have hjk : j ≤ k := S.le_max' j hjS
  have heig : gapEigen H₀ H₁ h₀ h₁ k x ≤ gapEigen H₀ H₁ h₀ h₁ j x :=
    (gapInterp_hermitian h₀ h₁ x).eigenvalues₀_antitone hjk
  linarith

/-- The least spectral gap is Lipschitz with twice the path speed. -/
theorem interp_gap_lipschitz (bhatia : Bhatia_Corollary_III_2_6)
    {H₀ H₁ : Mat}
    (h₀ : IsHermitian H₀) (h₁ : IsHermitian H₁) (Gamma : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hGamma : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Gamma x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Gamma x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |Gamma x - Gamma y| ≤ 2 * ‖H₁ - H₀‖ * |x - y| := by
  obtain ⟨k, hk⟩ := first_excited_fixed bhatia h₀ h₁ Gamma hg hGamma hlow
  rw [hk x hx, hk y hy]
  have hfirst := eigen_lipschitz bhatia h₀ h₁ k x y
  have hlast := eigen_lipschitz bhatia h₀ h₁ (Fin.last n) x y
  calc
    _ = |(gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ k y) -
        (gapEigen H₀ H₁ h₀ h₁ (Fin.last n) x -
          gapEigen H₀ H₁ h₀ h₁ (Fin.last n) y)| := by
      congr 1
      ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

end RoundedClocks.GapAdaptedSpectralGap
