/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.PaperProof.UniformConsequences

/-! # Gap-adapted schedules

The regularity and comparison argument of Example 5.1 (`ex:gap-adapted`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Real Set Matrix MeasureTheory Filter
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin (d + 1)) (𝕜 := ℂ)

/-- The affine Hermitian path in Example 5.1. -/
def gapInterp (H₀ H₁ : 𝕄) (x : ℝ) : 𝕄 := (1 - x) • H₀ + x • H₁

/-- Real affine combinations of Hermitian matrices are Hermitian. -/
theorem gapInterp_hermitian {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (x : ℝ) :
    (gapInterp H₀ H₁ x).IsHermitian := by
  exact (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _)) h₀).add
    (IsSelfAdjoint.smul (isSelfAdjoint_iff.mpr (star_trivial _)) h₁)

/-- The difference of affine samples is the parameter difference times `H₁-H₀`. -/
theorem gapInterp_sub (H₀ H₁ : 𝕄) (x y : ℝ) :
    gapInterp H₀ H₁ x - gapInterp H₀ H₁ y = (x - y) • (H₁ - H₀) := by
  unfold gapInterp
  module

/-- The affine interpolation of two contractions is a contraction. -/
theorem gapInterp_norm_le {H₀ H₁ : 𝕄} (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
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

/-- The sorted eigenvalues in the proof of Example 5.1 (Mathlib orders them decreasingly). -/
def gapEigen (H₀ H₁ : 𝕄) (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (k : Fin (d + 1)) (x : ℝ) : ℝ :=
  (gapInterp_hermitian h₀ h₁ x).eigenvalues₀ ⟨k, by simpa using k.isLt⟩

/-- Weyl's perturbation theorem along the affine path, with the paper's constant. -/
theorem gapEigen_lipschitz {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (k : Fin (d + 1)) (x y : ℝ) :
    |gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ k y| ≤
      ‖H₁ - H₀‖ * |x - y| := by
  have h := abs_eigenvalues₀_sub_le (gapInterp_hermitian h₀ h₁ x)
    (gapInterp_hermitian h₀ h₁ y) ⟨k, by simpa using k.isLt⟩
  simpa only [gapEigen, gapInterp_sub, norm_smul, Real.norm_eq_abs, mul_comm] using h

/-- Every ordered eigenvalue depends continuously on the interpolation parameter. -/
theorem gapEigen_continuous {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (k : Fin (d + 1)) : Continuous (gapEigen H₀ H₁ h₀ h₁ k) := by
  apply (LipschitzWith.of_dist_le_mul (K := ⟨‖H₁ - H₀‖, norm_nonneg _⟩) ?_).continuous
  intro x y
  simpa only [Real.dist_eq] using gapEigen_lipschitz h₀ h₁ k x y

/-- The final entry of the decreasing list is its least eigenvalue. -/
theorem gapEigen_least {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (k : Fin (d + 1)) (x : ℝ) :
    gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x ≤ gapEigen H₀ H₁ h₀ h₁ k x := by
  apply (gapInterp_hermitian h₀ h₁ x).eigenvalues₀_antitone
  exact k.le_last

/-- `Γ` is the spectral gap above the least eigenvalue: it is the least strictly
positive difference from that eigenvalue. This allows ground-space multiplicity. -/
def IsLeastGap (H₀ H₁ : 𝕄) (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (x Γ : ℝ) : Prop :=
  (∃ k, 0 < gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x ∧
    Γ = gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x) ∧
  ∀ k, gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x < gapEigen H₀ H₁ h₀ h₁ k x →
    Γ ≤ gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x

/-- A continuous nonnegative function separated from zero by a uniform positive
constant cannot change whether it is zero on an interval. Applied to the ordered
eigenvalue differences, this is the constant-ground-multiplicity argument. -/
theorem gap_zero_iff {f : ℝ → ℝ} {g : ℝ} (hg : 0 < g)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hsep : ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 ∨ g ≤ f x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    f x = 0 ↔ f y = 0 := by
  suffices h : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      f x = 0 → f y = 0 by
    exact ⟨h x hx y hy, h y hy x hx⟩
  intro a ha b hb hfa
  rcases hsep b hb with hfb | hfb
  · exact hfb
  · have hmid : g / 2 ∈ Icc (f a) (f b) := by constructor <;> linarith
    obtain ⟨z, hz, hzg⟩ := (convex_Icc (0 : ℝ) 1).isPreconnected.intermediate_value
      ha hb hf hmid
    rcases hsep z hz with heq | hge <;> linarith

/-- Uniform positive gap forces every ordered eigenvalue to stay either in the
least eigenspace or outside it. -/
theorem gap_ground_indices_constant {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (Γ : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Γ x)
    (k : Fin (d + 1)) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    gapEigen H₀ H₁ h₀ h₁ k x = gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x ↔
    gapEigen H₀ H₁ h₀ h₁ k y = gapEigen H₀ H₁ h₀ h₁ (Fin.last d) y := by
  have hcont : ContinuousOn (fun z ↦ gapEigen H₀ H₁ h₀ h₁ k z -
      gapEigen H₀ H₁ h₀ h₁ (Fin.last d) z) (Icc (0 : ℝ) 1) :=
    ((gapEigen_continuous h₀ h₁ k).sub
    (gapEigen_continuous h₀ h₁ (Fin.last d))).continuousOn
  have hsep : ∀ z ∈ Icc (0 : ℝ) 1,
      gapEigen H₀ H₁ h₀ h₁ k z - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) z = 0 ∨
      g ≤ gapEigen H₀ H₁ h₀ h₁ k z - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) z := by
    intro z hz
    rcases (gapEigen_least h₀ h₁ k z).eq_or_lt with heq | hlt
    · exact Or.inl (sub_eq_zero.mpr heq.symm)
    · exact Or.inr ((hlow z hz).trans ((hΓ z hz).2 k hlt))
  simpa only [sub_eq_zero] using gap_zero_iff hg hcont hsep hx hy

/-- A fixed position in the ordered eigenvalue list describes the first excited
level throughout a uniformly gapped path, even when higher levels cross. -/
theorem gap_first_excited_fixed {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (Γ : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Γ x) :
    ∃ k : Fin (d + 1), ∀ x ∈ Icc (0 : ℝ) 1,
      Γ x = gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x := by
  classical
  let S := Finset.univ.filter fun k ↦
    gapEigen H₀ H₁ h₀ h₁ (Fin.last d) 0 < gapEigen H₀ H₁ h₀ h₁ k 0
  have hS : S.Nonempty := by
    obtain ⟨k, hk, _⟩ := (hΓ 0 (by norm_num)).1
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_pos.mp hk⟩⟩
  let k := S.max' hS
  have hk : k ∈ S := S.max'_mem hS
  refine ⟨k, ?_⟩
  intro x hx
  have hpositive : ∀ j, j ∈ S ↔ gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x <
      gapEigen H₀ H₁ h₀ h₁ j x := by
    intro j
    have heq := gap_ground_indices_constant h₀ h₁ Γ hg hΓ hlow j (x := 0) (by norm_num) hx
    have h0 := gapEigen_least h₀ h₁ j 0
    have hx' := gapEigen_least h₀ h₁ j x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hlt
      apply lt_of_le_of_ne hx'
      intro hzero
      have := heq.mpr hzero.symm
      linarith
    · intro hlt
      apply lt_of_le_of_ne h0
      intro hzero
      have := heq.mp hzero.symm
      linarith
  apply le_antisymm ((hΓ x hx).2 k ((hpositive k).mp hk))
  obtain ⟨j, hj, heq⟩ := (hΓ x hx).1
  have hjS := (hpositive j).mpr (sub_pos.mp hj)
  have hjk : j ≤ k := S.le_max' j hjS
  have heig : gapEigen H₀ H₁ h₀ h₁ k x ≤ gapEigen H₀ H₁ h₀ h₁ j x :=
    (gapInterp_hermitian h₀ h₁ x).eigenvalues₀_antitone hjk
  linarith

/-- The least spectral gap is Lipschitz with constant twice the speed of the
matrix interpolation. No differentiability of the gap is assumed. -/
theorem interp_gap_lipschitz {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (Γ : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Γ x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |Γ x - Γ y| ≤ 2 * ‖H₁ - H₀‖ * |x - y| := by
  obtain ⟨k, hk⟩ := gap_first_excited_fixed h₀ h₁ Γ hg hΓ hlow
  rw [hk x hx, hk y hy]
  have hfirst := gapEigen_lipschitz h₀ h₁ k x y
  have hlast := gapEigen_lipschitz h₀ h₁ (Fin.last d) x y
  calc
    _ = |(gapEigen H₀ H₁ h₀ h₁ k x - gapEigen H₀ H₁ h₀ h₁ k y) -
        (gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x - gapEigen H₀ H₁ h₀ h₁ (Fin.last d) y)| := by
      congr 1
      ring
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-- Every eigenvalue of an affine sample lies in `[-1,1]`. -/
theorem gapInterp_eigenvalue_bounds {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (i : Fin (d + 1)) : (gapInterp_hermitian h₀ h₁ x).eigenvalues i ∈ Icc (-1 : ℝ) 1 := by
  have hi := spectrum.norm_le_norm_of_mem
    ((gapInterp_hermitian h₀ h₁ x).eigenvalues_mem_spectrum_real i)
  have hn := gapInterp_norm_le hn₀ hn₁ hx
  have hi' : |(gapInterp_hermitian h₀ h₁ x).eigenvalues i| ≤ ‖gapInterp H₀ H₁ x‖ := by
    simpa only [Real.norm_eq_abs] using hi
  exact abs_le.mp (hi'.trans hn)

/-- The spectral width of every affine sample is at most two. -/
theorem gapInterp_width {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (i j : Fin (d + 1)) :
    |(gapInterp_hermitian h₀ h₁ x).eigenvalues i -
      (gapInterp_hermitian h₀ h₁ x).eigenvalues j| ≤ 2 := by
  have hi := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx i
  have hj := gapInterp_eigenvalue_bounds h₀ h₁ hn₀ hn₁ hx j
  exact abs_sub_le_iff.mpr ⟨by linarith [hi.2, hj.1], by linarith [hi.1, hj.2]⟩

/-- In particular the gap above the least eigenvalue is at most two. -/
theorem interp_gap_le_two {H₀ H₁ : 𝕄} (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1) {x Γ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hΓ : IsLeastGap H₀ H₁ h₀ h₁ x Γ) : Γ ≤ 2 := by
  obtain ⟨k, hk, rfl⟩ := hΓ.1
  have hw := gapInterp_width h₀ h₁ hn₀ hn₁ hx
    (sortIdx (d + 1) ⟨k, by simpa using k.isLt⟩)
    (sortIdx (d + 1) ⟨Fin.last d, by simp⟩)
  rw [eigenvalues_sortIdx, eigenvalues_sortIdx] at hw
  exact (le_abs_self _).trans hw

/-- The power function has the Lipschitz constant used in Example 5.1. -/
theorem rpow_lipschitz_two {p x y : ℝ} (hp : 1 ≤ p)
    (hx : x ∈ Icc (0 : ℝ) 2) (hy : y ∈ Icc (0 : ℝ) 2) :
    |x ^ p - y ^ p| ≤ p * 2 ^ (p - 1) * |x - y| := by
  have hd : ∀ z ∈ Icc (0 : ℝ) 2,
      HasDerivWithinAt (fun z : ℝ ↦ z ^ p) (p * z ^ (p - 1)) (Icc 0 2) z :=
    fun z _ ↦ (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt
  have hb : ∀ z ∈ Icc (0 : ℝ) 2, ‖p * z ^ (p - 1)‖ ≤ p * 2 ^ (p - 1) := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg hz.1 _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.1 hz.2 (by linarith))
      (by linarith)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

/-- The normalizing integral of a strictly positive continuous gap is positive. -/
theorem gap_normalization_pos {Γ : ℝ → ℝ} (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x) (p : ℝ) :
    0 < ∫ x in (0 : ℝ)..1, Γ x ^ (-p) := by
  have hc : ContinuousOn (fun x ↦ Γ x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hΓ.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  exact intervalIntegral.integral_pos (by norm_num) hc
    (fun x hx ↦ (Real.rpow_pos_of_pos (hpos x ⟨hx.1.le, hx.2⟩) _).le)
    ⟨0, by norm_num, Real.rpow_pos_of_pos (hpos 0 (by norm_num)) _⟩

/-- The schedule ODE integrates to the normalized inverse-gap primitive,
including both endpoints of the schedule interval. -/
theorem gap_schedule_integral {Γ u : ℝ → ℝ} {p : ℝ}
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x)
    (hu0 : u 0 = 0) (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Γ x ^ (-p)) * Γ (u s) ^ p) (Icc 0 1) s)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..u s, Γ x ^ (-p) = (∫ x in (0 : ℝ)..1, Γ x ^ (-p)) * s := by
  let cp := ∫ x in (0 : ℝ)..1, Γ x ^ (-p)
  have huc : ContinuousOn u (Icc (0 : ℝ) 1) := fun x hx ↦ (hu x hx).continuousWithinAt
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hs.2
  have hpow : ContinuousOn (fun x ↦ Γ x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hΓ.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hud : ContinuousOn (fun x ↦ cp * Γ (u x) ^ p) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul ((hΓ.comp huc hurange).rpow_const
      (fun x hx ↦ Or.inl (ne_of_gt (hpos (u x) (hurange hx)))))
  have hchange := intervalIntegral.integral_comp_mul_deriv''
    (a := 0) (b := s) (f := u) (f' := fun x ↦ cp * Γ (u x) ^ p)
    (g := fun x ↦ Γ x ^ (-p))
    (by simpa only [uIcc_of_le hs.1] using huc.mono hsub)
    (fun x hx ↦ ((hu x ⟨by simpa only [min_eq_left hs.1] using hx.1.le,
      (by simpa only [max_eq_right hs.1] using hx.2.le : x ≤ s).trans hs.2⟩).hasDerivAt
        (Icc_mem_nhds (by simpa only [min_eq_left hs.1] using hx.1)
          (lt_of_lt_of_le (by simpa only [max_eq_right hs.1] using hx.2) hs.2))).hasDerivWithinAt)
    (by simpa only [uIcc_of_le hs.1] using hud.mono hsub)
    (hpow.mono (by rintro z ⟨x, hx, rfl⟩; exact hurange (hsub (by
      simpa only [uIcc_of_le hs.1] using hx))))
  have hint : (∫ x in (0 : ℝ)..s, ((fun x ↦ Γ x ^ (-p)) ∘ u) x *
      (cp * Γ (u x) ^ p)) = cp * s := by
    have heq : ∀ x ∈ uIcc (0 : ℝ) s,
        ((fun x ↦ Γ x ^ (-p)) ∘ u) x * (cp * Γ (u x) ^ p) = cp := by
      intro x hx
      have hx' := hsub (show x ∈ Icc (0 : ℝ) s by simpa only [uIcc_of_le hs.1] using hx)
      have hr := Real.rpow_add (hpos (u x) (hurange hx')) (-p) p
      simp only [neg_add_cancel, Real.rpow_zero] at hr
      dsimp only [Function.comp_apply]
      calc
        _ = cp * (Γ (u x) ^ (-p) * Γ (u x) ^ p) := by ring
        _ = cp := by rw [← hr, mul_one]
    rw [intervalIntegral.integral_congr heq]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hu0] at hchange
  exact hchange.symm.trans hint

/-- The normalizing integral makes the schedule reach the right endpoint at
unit parameter time. -/
theorem gap_schedule_endpoint {Γ u : ℝ → ℝ} {p : ℝ}
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x)
    (hu0 : u 0 = 0) (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Γ x ^ (-p)) * Γ (u s) ^ p) (Icc 0 1) s) :
    u 1 = 1 := by
  have hone := gap_schedule_integral hΓ hpos hu0 hurange hu (s := 1) (by norm_num)
  rw [mul_one] at hone
  have hrange := hurange (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  by_contra hne
  have hlt : u 1 < 1 := lt_of_le_of_ne hrange.2 hne
  have hpow : ContinuousOn (fun x ↦ Γ x ^ (-p)) (Icc (0 : ℝ) 1) :=
    hΓ.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hsmall : Icc (u 1) 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hrange.1 le_rfl
  have hpositive : 0 < ∫ x in u 1..1, Γ x ^ (-p) :=
    intervalIntegral.integral_pos hlt (hpow.mono hsmall)
      (fun x hx ↦ (Real.rpow_pos_of_pos (hpos x (hsmall ⟨hx.1.le, hx.2⟩)) _).le)
      ⟨1, ⟨hlt.le, le_rfl⟩, Real.rpow_pos_of_pos (hpos 1 (by norm_num)) _⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hpow.mono (Icc_subset_Icc le_rfl hrange.2)).intervalIntegrable_of_Icc hrange.1)
    ((hpow.mono hsmall).intervalIntegrable_of_Icc hlt.le)
  linarith

/-- The ODE and `Γ ≤ 2` give the Lipschitz bound `2^p c_p` for the schedule. -/
theorem gap_schedule_lipschitz {Γ u : ℝ → ℝ} {p cp : ℝ} (hp : 0 ≤ p)
    (hcp : 0 ≤ cp) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u (cp * Γ (u s) ^ p) (Icc 0 1) s)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |u t - u s| ≤ 2 ^ p * cp * |t - s| := by
  have hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖cp * Γ (u x) ^ p‖ ≤ 2 ^ p * cp := by
    intro x hx
    have hg := hΓ (u x) (hurange hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hg.1 _))]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg.1 hg.2 hp) hcp
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hu hb hs ht

/-- The derivative of the scheduled Hamiltonian is the ODE speed times the
constant interpolation direction. -/
theorem gap_schedule_derivative (H₀ H₁ : 𝕄) {u : ℝ → ℝ} {s v : ℝ}
    (hu : HasDerivWithinAt u v (Icc 0 1) s) :
    HasDerivWithinAt (fun s ↦ gapInterp H₀ H₁ (u s)) (v • (H₁ - H₀)) (Icc 0 1) s := by
  have heq : (fun s ↦ gapInterp H₀ H₁ (u s)) = (fun s ↦ H₀ + u s • (H₁ - H₀)) := by
    funext x
    unfold gapInterp
    module
  rw [heq]
  simpa using (hu.smul_const (H₁ - H₀)).const_add H₀

/-- Pointwise derivative bound used for the supremum in Example 5.1. -/
theorem gap_derivative_norm_le (D : 𝕄) {Γ u : ℝ → ℝ} {p cp : ℝ}
    (hp : 0 ≤ p) (hcp : 0 ≤ cp)
    (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖(cp * Γ (u s) ^ p) • D‖ ≤ 2 ^ p * cp * ‖D‖ := by
  have hg := hΓ (u s) (hurange hs)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hg.1 _))]
  calc
    _ ≤ (cp * 2 ^ p) * ‖D‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg.1 hg.2 hp) hcp) (norm_nonneg _)
    _ = _ := by ring

/-- The derivative supremum bound displayed in Example 5.1. -/
theorem gap_derivative_supNorm_le (D : 𝕄) {Γ u : ℝ → ℝ} {p cp : ℝ}
    (hp : 0 ≤ p) (hcp : 0 ≤ cp)
    (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1)) :
    unitSupNorm (fun s ↦ (cp * Γ (u s) ^ p) • D) ≤ 2 ^ p * cp * ‖D‖ := by
  unfold unitSupNorm
  refine csSup_le ?_ ?_
  · exact ⟨_, 0, by norm_num, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact gap_derivative_norm_le D hp hcp hΓ hurange hs

/-- Multiplying the three Lipschitz constants in the paper gives precisely
`p 4^p c_p² ‖H₁-H₀‖²`. -/
theorem gap_derivative_lipschitz (D : 𝕄) {Γ u : ℝ → ℝ} {p cp : ℝ}
    (hp : 1 ≤ p) (hcp : 0 ≤ cp)
    (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2)
    (hΓlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |Γ x - Γ y| ≤ 2 * ‖D‖ * |x - y|)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u (cp * Γ (u s) ^ p) (Icc 0 1) s)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(cp * Γ (u t) ^ p) • D - (cp * Γ (u s) ^ p) • D‖ ≤
      p * 4 ^ p * cp ^ 2 * ‖D‖ ^ 2 * |t - s| := by
  have hp0 : 0 ≤ p := by linarith
  have hpconst : 0 ≤ p * 2 ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg (by norm_num) _)
  have hup := gap_schedule_lipschitz hp0 hcp hΓ hurange hu hs ht
  have hgap := hΓlip (u t) (hurange ht) (u s) (hurange hs)
  have hpower := rpow_lipschitz_two hp (hΓ (u t) (hurange ht)) (hΓ (u s) (hurange hs))
  have hfour : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
  calc
    _ = cp * |Γ (u t) ^ p - Γ (u s) ^ p| * ‖D‖ := by
      rw [← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcp]
    _ ≤ cp * (p * 2 ^ (p - 1) * |Γ (u t) - Γ (u s)|) * ‖D‖ :=
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
theorem gap_derivative_endpoints (D : 𝕄) {Γ u : ℝ → ℝ} {p cp : ℝ}
    (hcp : 0 ≤ cp) (hΓ0 : 0 ≤ Γ 0) (hΓ1 : 0 ≤ Γ 1)
    (hu0 : u 0 = 0) (hu1 : u 1 = 1) :
    ‖(cp * Γ (u 0) ^ p) • D‖ + ‖(cp * Γ (u 1) ^ p) • D‖ =
      cp * ‖D‖ * (Γ 0 ^ p + Γ 1 ^ p) := by
  rw [hu0, hu1, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hΓ0 _)),
    abs_of_nonneg (mul_nonneg hcp (Real.rpow_nonneg hΓ1 _))]
  ring

/-- **Example 5.1** (`ex:gap-adapted`): the gap-adapted path satisfies the
unit-step hypotheses at width two, with the three displayed derivative bounds.
The proof checks Weyl regularity, ODE normalization, and the derivative bounds;
The least-eigenvalue spectral projectors commute with the endpoint Hamiltonians;
Example 4.5 gives the truncated-product bound for every continuous leakage bound. -/
theorem ex_gap_adapted (H₀ H₁ : 𝕄) (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    (Γ : ℝ → ℝ) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (Γstar : ℝ) (hΓstar : 0 < Γstar) (hΓlow : ∀ x ∈ Icc (0 : ℝ) 1, Γstar ≤ Γ x)
    (p : ℝ) (hp : 1 < p) (u : ℝ → ℝ) (hu0 : u 0 = 0)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Γ x ^ (-p)) * Γ (u s) ^ p) (Icc 0 1) s) :
    let cp := ∫ x in (0 : ℝ)..1, Γ x ^ (-p)
    let H := fun s ↦ gapInterp H₀ H₁ (u s)
    let Hd := fun s ↦ (cp * Γ (u s) ^ p) • (H₁ - H₀)
    u 1 = 1 ∧ H 0 = H₀ ∧ H 1 = H₁ ∧
    (IsTimeDepHamiltonian H) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s) ∧
    DifferentiableOn ℝ H (Icc (0 : ℝ) 1) ∧
    ContinuousOn Hd (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, derivWithin H (Icc (0 : ℝ) 1) s = Hd s) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ i k,
      |(gapInterp_hermitian h₀ h₁ (u s)).eigenvalues i -
        (gapInterp_hermitian h₀ h₁ (u s)).eigenvalues k| ≤ 2) ∧
    (2 : ℝ) < 2 * π ∧
    ‖Hd 0‖ + ‖Hd 1‖ = cp * ‖H₁ - H₀‖ * (Γ 0 ^ p + Γ 1 ^ p) ∧
    unitSupNorm Hd ≤ 2 ^ p * cp * ‖H₁ - H₀‖ ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ p * 4 ^ p * cp ^ 2 * ‖H₁ - H₀‖ ^ 2 * |t - s|) ∧
    (let P := specProj h₀ {h₀.eigenvalues₀ ⟨Fin.last d, by simp⟩}
     let Q := specProj h₁ {h₁.eigenvalues₀ ⟨Fin.last d, by simp⟩}
     IsStarProjection P ∧ IsStarProjection Q ∧ Commute P (H 0) ∧ Commute Q (H 1) ∧
     ∀ (U : ℝ → 𝕄) (T k : ℕ), 0 < T →
       IsEvolution (fun t ↦ H (t / T)) U 0 T →
       ∀ (C : NNReal) (δ : ℝ), 0 < δ → ‖(1 - Q) * U T * P‖ ≤ (C : ℝ) / T →
       let σ := ⨆ s : Icc (0 : ℝ) 1, ⨆ i : Fin (d + 1),
         (Finset.univ.filter fun j ↦ truncHerm k (H s) i j ≠ H s i j).card
       2 * ((C : ℝ) + hamiltonianEnergy 2
         (p * 4 ^ p * cp ^ 2 * ‖H₁ - H₀‖ ^ 2) H) / δ ≤ T →
       Real.sqrt 2 * σ * ((2 : ℝ) ^ k)⁻¹ ≤ δ / (2 * T) →
       ‖(1 - Q) * (unitProduct (fun s ↦ scalarEntryMap (truncBits k) (H s)) T).1 * P‖ ≤ δ) := by
  intro cp H Hd
  let D := H₁ - H₀
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x := fun x hx ↦ hΓstar.trans_le (hΓlow x hx)
  have hbounds : ∀ x ∈ Icc (0 : ℝ) 1, Γ x ∈ Icc (0 : ℝ) 2 :=
    fun x hx ↦ ⟨(hpos x hx).le, interp_gap_le_two h₀ h₁ hn₀ hn₁ hx (hΓ x hx)⟩
  have hΓlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |Γ x - Γ y| ≤ 2 * ‖D‖ * |x - y| :=
    fun x hx y hy ↦ interp_gap_lipschitz h₀ h₁ Γ hΓstar hΓ hΓlow hx hy
  have hΓcont : ContinuousOn Γ (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le
    (fun x hx y hy ↦ by simpa only [Real.norm_eq_abs] using hΓlip y hy x hx)
  have hcp : 0 ≤ cp := (gap_normalization_pos hΓcont hpos p).le
  have hu1 : u 1 = 1 := gap_schedule_endpoint hΓcont hpos hu0 hurange hu
  have hH0 : H 0 = H₀ := by simp [H, gapInterp, hu0]
  have hH1 : H 1 = H₁ := by simp [H, gapInterp, hu1]
  have hH : IsTimeDepHamiltonian H :=
    fun s _ ↦ gapInterp_hermitian h₀ h₁ (u s)
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ gap_schedule_derivative H₀ H₁ (hu s hs)
  have hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ p * 4 ^ p * cp ^ 2 * ‖D‖ ^ 2 * |t - s| :=
    fun s hs t ht ↦ gap_derivative_lipschitz D hp.le hcp hbounds hΓlip hurange hu hs ht
  have hc : DifferentiableOn ℝ H (Icc (0 : ℝ) 1) :=
    fun s hs ↦ (hd s hs).differentiableWithinAt
  have hdc : ContinuousOn Hd (Icc (0 : ℝ) 1) := continuousOn_of_norm_sub_le hlip
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, derivWithin H (Icc (0 : ℝ) 1) s = Hd s :=
    fun s hs ↦ (hd s hs).derivWithin ((uniqueDiffOn_Icc (by norm_num)) s hs)
  have hwidth : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i k,
      |(gapInterp_hermitian h₀ h₁ (u s)).eigenvalues i -
        (gapInterp_hermitian h₀ h₁ (u s)).eigenvalues k| ≤ 2 :=
    fun s hs i k ↦ gapInterp_width h₀ h₁ hn₀ hn₁ (hurange hs) i k
  have hends : ‖Hd 0‖ + ‖Hd 1‖ = cp * ‖D‖ * (Γ 0 ^ p + Γ 1 ^ p) :=
    gap_derivative_endpoints D hcp (hpos 0 (by norm_num)).le (hpos 1 (by norm_num)).le hu0 hu1
  have hsup : unitSupNorm Hd ≤ 2 ^ p * cp * ‖D‖ :=
    gap_derivative_supNorm_le D (by linarith) hcp hbounds hurange
  have hnonresonant : (2 : ℝ) < 2 * π := by linarith [pi_gt_three]
  refine ⟨hu1, hH0, hH1, hH, hd, hc, hdc, hderiv, hwidth,
    hnonresonant, hends, hsup, hlip, ?_⟩
  let P := specProj h₀ {h₀.eigenvalues₀ ⟨Fin.last d, by simp⟩}
  let Q := specProj h₁ {h₁.eigenvalues₀ ⟨Fin.last d, by simp⟩}
  have hP : IsStarProjection P := isStarProjection_specProj h₀ _
  have hQ : IsStarProjection Q := isStarProjection_specProj h₁ _
  have hPc : Commute P (H 0) := by rw [hH0]; exact commute_specProj h₀ _
  have hQc : Commute Q (H 1) := by rw [hH1]; exact commute_specProj h₁ _
  refine ⟨hP, hQ, hPc, hQc, ?_⟩
  intro U T k hT hU C δ hδ hcont
  have hderivLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤
        p * 4 ^ p * cp ^ 2 * ‖H₁ - H₀‖ ^ 2 * |t - s| := by
    intro s hs t ht
    rw [hderiv s hs, hderiv t ht]
    exact hlip s hs t ht
  have hsampleWidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ i q,
      |(hH _ (walkCubic_sample hj)).eigenvalues i -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ 2 :=
    fun j hj i q ↦ hwidth _ (walkCubic_sample hj) i q
  exact ex_unit_transfer_bounds 2 hnonresonant H U T k hT hH
    (p * 4 ^ p * cp ^ 2 * ‖H₁ - H₀‖ ^ 2)
    ⟨fun s hs ↦ (hc s hs).hasDerivWithinAt, hderivLip⟩
    ((hasSampleWidth_iff hH).2 hsampleWidth) hU
    P Q hP hQ hPc hQc C δ hδ hcont

end UnitaryProducts.PaperProof
