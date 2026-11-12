/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.PaperProof.ExamplesPi
public import UnitaryProducts.PaperProof.Crossings

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

/-- The multiplicity of the ground eigenvalue is constant along the path. -/
theorem gap_ground_multiplicity_constant {H₀ H₁ : 𝕄}
    (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian) (Γ : ℝ → ℝ) {g : ℝ}
    (hg : 0 < g) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, g ≤ Γ x)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    (Finset.univ.filter fun k ↦ gapEigen H₀ H₁ h₀ h₁ k x =
      gapEigen H₀ H₁ h₀ h₁ (Fin.last d) x).card =
    (Finset.univ.filter fun k ↦ gapEigen H₀ H₁ h₀ h₁ k y =
      gapEigen H₀ H₁ h₀ h₁ (Fin.last d) y).card := by
  classical
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact gap_ground_indices_constant h₀ h₁ Γ hg hΓ hlow k hx hy

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

/-- The two coefficients used in Example 5.1 are nonnegative. -/
theorem gap_coefficients_nonneg :
    0 ≤ (1 / (2 * π) - 1 / π ^ 2 : ℝ) ∧
    0 ≤ (5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 : ℝ) := by
  have hc := UnitaryProducts.Paper.UnitStepsProse.center_bound_nonneg pi_pos.le
    (by linarith [pi_pos] : π < 2 * π)
  rw [frameBound_center_pi] at hc
  refine ⟨hc, ?_⟩
  have hf := UnitaryProducts.Corrector.frameLip_nonneg pi_pos.le
  calc
    0 ≤ (1 / (2 * π) - 1 / π ^ 2) / 4 + 1 / 64 + 2 * frameLip π := by positivity
    _ = _ := by rw [frameBound_frameLip_pi.2]; ring

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

/-- **Example 5.1** (`ex:gap-adapted`): the affine gap-adapted schedule transfers
its continuous leakage bound to the sampled product. The ground projectors may
be replaced by any commuting orthogonal endpoint projectors. The proof follows
the paper: Weyl regularity, ODE normalization, derivative bounds, equation (5.2),
and the width-pi specialization (5.1). -/
theorem ex_gap_adapted (H₀ H₁ : 𝕄) (h₀ : H₀.IsHermitian) (h₁ : H₁.IsHermitian)
    (hn₀ : ‖H₀‖ ≤ 1) (hn₁ : ‖H₁‖ ≤ 1)
    (Γ : ℝ → ℝ) (hΓ : ∀ x ∈ Icc (0 : ℝ) 1, IsLeastGap H₀ H₁ h₀ h₁ x (Γ x))
    (Γstar : ℝ) (hΓstar : 0 < Γstar) (hΓlow : ∀ x ∈ Icc (0 : ℝ) 1, Γstar ≤ Γ x)
    (p : ℝ) (hp : 1 < p) (u : ℝ → ℝ) (hu0 : u 0 = 0)
    (hurange : MapsTo u (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hu : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt u ((∫ x in (0 : ℝ)..1, Γ x ^ (-p)) * Γ (u s) ^ p) (Icc 0 1) s)
    (T : ℕ) (hT : 0 < T) (U : ℝ → 𝕄)
    (hU : IsEvolution (fun t ↦ gapInterp H₀ H₁ (u (t / T))) U 0 T)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P H₀) (hQc : Commute Q H₁) :
    let cp := ∫ x in (0 : ℝ)..1, Γ x ^ (-p)
    let H := fun s ↦ gapInterp H₀ H₁ (u s)
    let c₀ := 1 / (2 * π) - 1 / π ^ 2
    let b := 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64
    ‖(1 - Q) * (unitProduct H T).1 * P‖ ≤ ‖(1 - Q) * U T * P‖ +
      cp * ‖H₁ - H₀‖ / T * (c₀ * (Γ 0 ^ p + Γ 1 ^ p) +
        4 ^ p * (p / 24 + p / π ^ 2 + b) * cp * ‖H₁ - H₀‖) := by
  intro cp H c₀ b
  let D := H₁ - H₀
  let Hd := fun s ↦ (cp * Γ (u s) ^ p) • D
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
  have hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian :=
    fun s _ ↦ gapInterp_hermitian h₀ h₁ (u s)
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ gap_schedule_derivative H₀ H₁ (hu s hs)
  have hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ p * 4 ^ p * cp ^ 2 * ‖D‖ ^ 2 * |t - s| :=
    fun s hs t ht ↦ gap_derivative_lipschitz D hp.le hcp hbounds hΓlip hurange hu hs ht
  have hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ i k,
      |(hH _ (walkCubic_sample hj)).eigenvalues i -
        (hH _ (walkCubic_sample hj)).eigenvalues k| ≤ π := by
    intro j hj i k
    exact (gapInterp_width h₀ h₁ hn₀ hn₁ (hurange (walkCubic_sample hj)) i k).trans
      (by linarith [Real.pi_gt_three])
  have hcomparison := products_pi hT H Hd U hH hd hlip hwidth hU
  have htransfer := leak_transfer H T (U T) P Q
    (hH 0 (by norm_num)) (hH 1 (by norm_num)) hP hQ
    (show Commute P (H 0) by rw [hH0]; exact hPc)
    (show Commute Q (H 1) by rw [hH1]; exact hQc)
  have hends : ‖Hd 0‖ + ‖Hd 1‖ = cp * ‖D‖ * (Γ 0 ^ p + Γ 1 ^ p) :=
    gap_derivative_endpoints D hcp (hpos 0 (by norm_num)).le (hpos 1 (by norm_num)).le hu0 hu1
  have hsup : unitSupNorm Hd ≤ 2 ^ p * cp * ‖D‖ :=
    gap_derivative_supNorm_le D (by linarith) hcp hbounds hurange
  have hsup0 : 0 ≤ unitSupNorm Hd := (norm_nonneg (Hd 0)).trans
    (norm_le_unitSupNorm (continuousOn_of_norm_sub_le hlip) (by norm_num))
  have hsq := pow_le_pow_left₀ hsup0 hsup 2
  have hb : 0 ≤ b := gap_coefficients_nonneg.2
  have hfour : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
  have hcoarse :
      ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ ≤
      cp * ‖D‖ / T * (c₀ * (Γ 0 ^ p + Γ 1 ^ p) +
        4 ^ p * (p / 24 + p / π ^ 2 + b) * cp * ‖D‖) := by
    refine hcomparison.trans ?_
    rw [hends]
    calc
      _ ≤ (1 / T : ℝ) * (c₀ * (cp * ‖D‖ * (Γ 0 ^ p + Γ 1 ^ p)) +
        (1 / 24 + 1 / π ^ 2) * (p * 4 ^ p * cp ^ 2 * ‖D‖ ^ 2) +
        b * (2 ^ p * cp * ‖D‖) ^ 2) := mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left hsq hb) _) (by positivity)
      _ = _ := by rw [hfour]; ring
  linarith only [htransfer, hcoarse]

/-- The inverse-power threshold used in the layer-cake calculation following
Example 5.1. -/
theorem gap_inverse_power_threshold {a y p : ℝ} (ha : 0 < a) (hy : 0 < y)
    (hp : 0 < p) :
    (y < a ^ (-p) ↔ a < y ^ (-1 / p)) ∧
    (y ≤ a ^ (-p) ↔ a ≤ y ^ (-1 / p)) := by
  have ht : 0 < y ^ (-1 / p) := Real.rpow_pos_of_pos hy _
  have he : (y ^ (-1 / p)) ^ (-p) = y := by
    rw [← Real.rpow_mul hy.le, show (-1 / p) * (-p) = (1 : ℝ) by field_simp, Real.rpow_one]
  constructor
  · conv_lhs => rw [← he]
    exact Real.rpow_lt_rpow_iff_of_neg ht ha (neg_neg_of_pos hp)
  · conv_lhs => rw [← he]
    exact Real.rpow_le_rpow_iff_of_neg ht ha (neg_neg_of_pos hp)

/-- The layer-cake identity written in the paragraph following Example 5.1.
The spectral gap has a positive lower bound, so the tail integral stops at
`Γstar^(-p)`. -/
theorem gap_normalization_layercake {Γ : ℝ → ℝ} {p Γstar : ℝ}
    (hp : 0 < p) (hstar : 0 < Γstar)
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, Γstar ≤ Γ x) :
    ∫ x in (0 : ℝ)..1, Γ x ^ (-p) =
      ∫ y in (0 : ℝ)..Γstar ^ (-p),
        volume.real {x | x ∈ Icc (0 : ℝ) 1 ∧ Γ x < y ^ (-1 / p)} := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let f := fun x ↦ Γ x ^ (-p)
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x := fun x hx ↦ hstar.trans_le (hlow x hx)
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    hΓ.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hfi : Integrable f μ := hfc.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (Real.rpow_pos_of_pos (hpos x hx) _).le
  have hbound : f ≤ᵐ[μ] fun _ ↦ Γstar ^ (-p) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.rpow_le_rpow_of_nonpos hstar (hlow x hx) (neg_nonpos.mpr hp.le)
  have hfinite := hfi.integral_eq_integral_Ioc_meas_le hnonneg hbound
  have hae : (fun y ↦ μ.real {x | y ≤ f x}) =ᵐ[volume]
      (fun y ↦ μ.real {x | y < f x}) := by
    filter_upwards [meas_le_ae_eq_meas_lt μ volume f] with y hy
    exact congrArg ENNReal.toReal hy
  have hcut : 0 ≤ Γstar ^ (-p) := (Real.rpow_pos_of_pos hstar _).le
  calc
    _ = ∫ x, f x ∂μ := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact integral_Icc_eq_integral_Ioc.symm
    _ = ∫ y in Ioc (0 : ℝ) (Γstar ^ (-p)), μ.real {x | y ≤ f x} := hfinite
    _ = ∫ y in Ioc (0 : ℝ) (Γstar ^ (-p)), μ.real {x | y < f x} :=
      integral_congr_ae (ae_restrict_of_ae hae)
    _ = _ := by
      rw [intervalIntegral.integral_of_le hcut]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only [Measure.real, μ]
      rw [Measure.restrict_apply' measurableSet_Icc]
      congr 2
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, f]
      constructor
      · rintro ⟨hxy, hx⟩
        exact ⟨hx, (gap_inverse_power_threshold (hpos x hx) hy.1 hp).1.mp hxy⟩
      · rintro ⟨hx, hxy⟩
        exact ⟨(gap_inverse_power_threshold (hpos x hx) hy.1 hp).1.mpr hxy, hx⟩

/-- The normalization estimate following Example 5.1, proved from the paper's
sublevel-set length hypothesis by layer cake and integration of `y^(-1/p)`. -/
theorem gap_normalization_bound {Γ : ℝ → ℝ} {p Γstar C : ℝ}
    (hp : 1 < p) (hstar : 0 < Γstar)
    (hΓ : ContinuousOn Γ (Icc (0 : ℝ) 1))
    (hlow : ∀ x ∈ Icc (0 : ℝ) 1, Γstar ≤ Γ x)
    (hmeas : ∀ y > 0, volume.real {x | x ∈ Icc (0 : ℝ) 1 ∧ Γ x ≤ y} ≤ C * y) :
    ∫ x in (0 : ℝ)..1, Γ x ^ (-p) ≤ p * C * Γstar ^ (1 - p) / (p - 1) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let f := fun x ↦ Γ x ^ (-p)
  let M := Γstar ^ (-p)
  have hM : 0 < M := Real.rpow_pos_of_pos hstar _
  have hp0 : 0 < p := by linarith
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < Γ x := fun x hx ↦ hstar.trans_le (hlow x hx)
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    hΓ.rpow_const (fun x hx ↦ Or.inl (ne_of_gt (hpos x hx)))
  have hfi : Integrable f μ := hfc.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (Real.rpow_pos_of_pos (hpos x hx) _).le
  have hbound : f ≤ᵐ[μ] fun _ ↦ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact Real.rpow_le_rpow_of_nonpos hstar (hlow x hx) (neg_nonpos.mpr hp0.le)
  have hfinite := hfi.integral_eq_integral_Ioc_meas_le hnonneg hbound
  have hanti : Antitone (fun y ↦ μ.real {x | y ≤ f x}) := by
    intro a b hab
    exact measureReal_mono (fun x hx ↦ hab.trans hx)
  have hexp : -1 < -1 / p := by
    apply (lt_div_iff₀ hp0).mpr
    linarith
  have hrint : IntervalIntegrable (fun y : ℝ ↦ C * y ^ (-1 / p)) volume 0 M :=
    (intervalIntegral.intervalIntegrable_rpow' hexp).const_mul C
  have heval : (∫ y in (0 : ℝ)..M, C * y ^ (-1 / p)) =
      p * C * Γstar ^ (1 - p) / (p - 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hexp),
      Real.zero_rpow (by linarith : -1 / p + 1 ≠ 0), sub_zero]
    dsimp only [M]
    rw [← Real.rpow_mul hstar.le,
      show -p * (-1 / p + 1) = 1 - p by field_simp; ring]
    field_simp
    ring
  calc
    _ = ∫ y in Ioc (0 : ℝ) M, μ.real {x | y ≤ f x} := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      exact hfinite
    _ ≤ ∫ y in Ioc (0 : ℝ) M, C * y ^ (-1 / p) :=
      setIntegral_mono_on (hanti.intervalIntegrable (μ := volume) (a := 0) (b := M)).1
        hrint.1 measurableSet_Ioc (by
          intro y hy
          have heq : μ.real {x | y ≤ f x} =
              volume.real {x | x ∈ Icc (0 : ℝ) 1 ∧ Γ x ≤ y ^ (-1 / p)} := by
            dsimp only [Measure.real, μ]
            rw [Measure.restrict_apply' measurableSet_Icc]
            congr 2
            ext x
            simp only [mem_inter_iff, mem_setOf_eq, f]
            constructor
            · rintro ⟨hxy, hx⟩
              exact ⟨hx, (gap_inverse_power_threshold (hpos x hx) hy.1 hp0).2.mp hxy⟩
            · rintro ⟨hx, hxy⟩
              exact ⟨(gap_inverse_power_threshold (hpos x hx) hy.1 hp0).2.mpr hxy, hx⟩
          rw [heq]
          exact hmeas _ (Real.rpow_pos_of_pos hy.1 _))
    _ = _ := by rw [← intervalIntegral.integral_of_le hM.le]; exact heval

/-- Orthogonal projection decomposes the squared norm into success probability
and leakage probability, as used after Example 5.1. -/
theorem gap_projection_probability {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {Q : E →L[ℂ] E}
    (hQ : IsStarProjection Q) (v : E) :
    ‖(1 - Q) v‖ ^ 2 = ‖v‖ ^ 2 - ‖Q v‖ ^ 2 := by
  obtain ⟨K, hK, rfl⟩ := isStarProjection_iff_eq_starProjection.mp hQ
  letI := hK
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection v K
  rw [Submodule.starProjection_orthogonal'] at h
  linarith

/-- A bound on the failure probability for every ground-space unit vector is
an operator-norm leakage bound. This is the inference from Guo--An's cited
vector estimate in the paragraph after Example 5.1; the cited estimate is an
explicit hypothesis, not an axiom. -/
theorem gap_probability_to_operator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P Q U : E →L[ℂ] E}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hU : U ∈ unitary (E →L[ℂ] E)) {η : ℝ} (hη : 0 ≤ η)
    (hGA : ∀ ψ : E, ‖ψ‖ = 1 → P ψ = ψ → 1 - ‖Q (U ψ)‖ ^ 2 ≤ η ^ 2) :
    ‖(1 - Q) * U * P‖ ≤ η := by
  have hvbound : ∀ v : E, P v = v → ‖(1 - Q) (U v)‖ ≤ η * ‖v‖ := by
    intro v hPv
    by_cases hv : v = 0
    · simp [hv]
    let c : ℂ := (‖v‖ : ℂ)⁻¹
    let ψ := c • v
    have hψ : ‖ψ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hv
    have hPψ : P ψ = ψ := by simp only [ψ, map_smul, hPv]
    have hsq : ‖(1 - Q) (U ψ)‖ ^ 2 ≤ η ^ 2 := by
      rw [gap_projection_probability hQ, ContinuousLinearMap.norm_map_of_mem_unitary hU, hψ,
        one_pow]
      exact hGA ψ hψ hPψ
    have hle := (sq_le_sq₀ (norm_nonneg _) hη).mp hsq
    have hc : ‖c‖ = ‖v‖⁻¹ := by simp [c]
    have hscaled : ‖(1 - Q) (U ψ)‖ = ‖v‖⁻¹ * ‖(1 - Q) (U v)‖ := by
      rw [show ψ = c • v from rfl, map_smul, map_smul, norm_smul, hc]
    rw [hscaled] at hle
    calc
      _ = ‖v‖ * (‖v‖⁻¹ * ‖(1 - Q) (U v)‖) := by rw [← mul_assoc, mul_inv_cancel₀
        (norm_ne_zero_iff.mpr hv), one_mul]
      _ ≤ ‖v‖ * η := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = _ := mul_comm _ _
  obtain ⟨K, hK, hPK⟩ := isStarProjection_iff_eq_starProjection.mp hP
  letI := hK
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hη
  intro x hx
  have hPx : P (P x) = P x := congrArg (fun A : E →L[ℂ] E ↦ A x) hP.isIdempotentElem.eq
  have hcontract : ‖P x‖ ≤ 1 := by
    rw [hPK]
    exact (K.norm_starProjection_apply_le x).trans_eq hx
  exact (hvbound (P x) hPx).trans ((mul_le_mul_of_nonneg_left hcontract hη).trans_eq (mul_one _))

/-- A uniform coefficient for the order estimate following Example 5.1. The
constants depend only on the fixed `p,C`; the gap and runtime do not occur. -/
def gapOrderCoefficient (p C : ℝ) : ℝ :=
  let A := p * C / (p - 1)
  let c₀ := 1 / (2 * π) - 1 / π ^ 2
  let b := 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64
  4 * c₀ * 2 ^ p * A * 2 ^ (p - 1) + 4 * 4 ^ p * (p / 24 + p / π ^ 2 + b) * A ^ 2

/-- The added term in Example 5.1 is bounded by a constant depending only on
`p,C` times `Γstar^(2-2p)/T`. The scalar inputs are the endpoint gap powers,
the interpolation norm, and the normalization integral, already bounded above. -/
theorem gap_added_term_bound {p C Γstar cp D e₀ e₁ T : ℝ}
    (hp : 1 < p) (hC : 0 ≤ C) (hstar : 0 < Γstar) (hstar2 : Γstar ≤ 2)
    (hcp0 : 0 ≤ cp) (hcp : cp ≤ p * C * Γstar ^ (1 - p) / (p - 1))
    (hD0 : 0 ≤ D) (hD : D ≤ 2) (he₀ : e₀ ≤ 2 ^ p) (he₁ : e₁ ≤ 2 ^ p)
    (he0 : 0 ≤ e₀) (he1 : 0 ≤ e₁) (hT : 0 < T) :
    let c₀ := 1 / (2 * π) - 1 / π ^ 2
    let b := 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64
    cp * D / T * (c₀ * (e₀ + e₁) + 4 ^ p * (p / 24 + p / π ^ 2 + b) * cp * D) ≤
      gapOrderCoefficient p C * Γstar ^ (2 - 2 * p) / T := by
  intro c₀ b
  let A := p * C / (p - 1)
  let B := p / 24 + p / π ^ 2 + b
  have hp0 : 0 ≤ p := by linarith
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hp0 hC) (by linarith)
  have hc₀ : 0 ≤ c₀ := gap_coefficients_nonneg.1
  have hb : 0 ≤ b := gap_coefficients_nonneg.2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcp' : cp ≤ A * Γstar ^ (1 - p) := by simpa only [A, div_mul_eq_mul_div] using hcp
  have hpower : Γstar ^ (1 - p) ≤ 2 ^ (p - 1) * Γstar ^ (2 - 2 * p) := by
    calc
      _ = Γstar ^ (p - 1) * Γstar ^ (2 - 2 * p) := by
        rw [← Real.rpow_add hstar]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hstar.le hstar2 (by linarith)) (Real.rpow_nonneg hstar.le _)
  have hlinear : cp ≤ A * 2 ^ (p - 1) * Γstar ^ (2 - 2 * p) :=
    hcp'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hA)
  have hsquare : cp ^ 2 ≤ A ^ 2 * Γstar ^ (2 - 2 * p) := by
    have h := pow_le_pow_left₀ hcp0 hcp' 2
    rw [mul_pow] at h
    have he : (Γstar ^ (1 - p)) ^ 2 = Γstar ^ (2 - 2 * p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hstar.le]
      congr 1
      norm_num
      ring
    simpa only [he] using h
  calc
    _ ≤ cp * 2 / T * (c₀ * (2 ^ p + 2 ^ p) + 4 ^ p * B * cp * 2) := by
      dsimp only [B]
      gcongr
    _ = (4 * c₀ * 2 ^ p * cp + 4 * 4 ^ p * B * cp ^ 2) / T := by ring
    _ ≤ (4 * c₀ * 2 ^ p * (A * 2 ^ (p - 1) * Γstar ^ (2 - 2 * p)) +
        4 * 4 ^ p * B * (A ^ 2 * Γstar ^ (2 - 2 * p))) / T := by
      gcongr
    _ = _ := by dsimp only [gapOrderCoefficient, A, B, c₀, b]; ring

/-- The precise `O(Γstar^(2-2p)/T)` assertion in the paragraph after Example 5.1,
for any family of paths satisfying its uniform scalar bounds. -/
theorem gap_added_term_isBigO {ι : Type*} (l : Filter ι) {p C : ℝ}
    (hp : 1 < p) (hC : 0 ≤ C) (g cp D e₀ e₁ T : ι → ℝ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 2) (hT : ∀ i, 0 < T i)
    (hcp0 : ∀ i, 0 ≤ cp i)
    (hcp : ∀ i, cp i ≤ p * C * g i ^ (1 - p) / (p - 1))
    (hD : ∀ i, 0 ≤ D i ∧ D i ≤ 2)
    (he₀ : ∀ i, 0 ≤ e₀ i ∧ e₀ i ≤ 2 ^ p)
    (he₁ : ∀ i, 0 ≤ e₁ i ∧ e₁ i ≤ 2 ^ p) :
    let c₀ := 1 / (2 * π) - 1 / π ^ 2
    let b := 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64
    (fun i ↦ cp i * D i / T i * (c₀ * (e₀ i + e₁ i) +
      4 ^ p * (p / 24 + p / π ^ 2 + b) * cp i * D i)) =O[l]
      (fun i ↦ g i ^ (2 - 2 * p) / T i) := by
  intro c₀ b
  have hc₀ : 0 ≤ c₀ := gap_coefficients_nonneg.1
  have hb : 0 ≤ b := gap_coefficients_nonneg.2
  have hp0 : 0 ≤ p := by linarith
  apply Asymptotics.IsBigO.of_bound (gapOrderCoefficient p C)
  filter_upwards [] with i
  have hci := hcp0 i
  have hdi := (hD i).1
  have he0i := (he₀ i).1
  have he1i := (he₁ i).1
  have hgi := (hg i).1
  have hti := hT i
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using gap_added_term_bound hp hC (hg i).1
    (hg i).2 (hcp0 i) (hcp i) (hD i).1 (hD i).2 (he₀ i).2 (he₁ i).2 (he₀ i).1 (he₁ i).1 (hT i)

/-- At `p=3/2`, the gap power in the added term is exactly the inverse gap. -/
theorem gap_three_halves_order {g T : ℝ} :
    g ^ (2 - 2 * (3 / 2 : ℝ)) / T = 1 / (T * g) := by
  norm_num [Real.rpow_neg_one]
  ring

/-- Adding continuous and discrete inverse-gap errors needs a number of unit-time
factors proportional to `1/(ε Γstar)`. The continuous coefficient is an explicit
hypothesis supplied by the cited adiabatic theorem. -/
theorem gap_factor_count {Edis Econt Kcont Kdisc ε g T : ℝ}
    (hε : 0 < ε) (hg : 0 < g) (hT : 0 < T)
    (hcontinuous : Econt ≤ Kcont / (T * g))
    (htransfer : Edis ≤ Econt + Kdisc / (T * g))
    (hsteps : (Kcont + Kdisc) / (ε * g) ≤ T) : Edis ≤ ε := by
  have hbudget := (div_le_iff₀ (mul_pos hε hg)).mp hsteps
  have herr : (Kcont + Kdisc) / (T * g) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hT hg)).mpr
    calc
      Kcont + Kdisc ≤ T * (ε * g) := hbudget
      _ = ε * (T * g) := by ring
  calc
    Edis ≤ Econt + Kdisc / (T * g) := htransfer
    _ ≤ Kcont / (T * g) + Kdisc / (T * g) := add_le_add_left hcontinuous _
    _ = (Kcont + Kdisc) / (T * g) := by ring
    _ ≤ ε := herr

/-- The matrix form of the vector-to-operator inference after Example 5.1. -/
theorem gap_probability_to_matrix {P Q U : 𝕄}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hU : U ∈ unitary 𝕄)
    {η : ℝ} (hη : 0 ≤ η)
    (hGA : ∀ ψ : EuclideanSpace ℂ (Fin (d + 1)), ‖ψ‖ = 1 →
      𝒯 P ψ = ψ →
      1 - ‖𝒯 Q (𝒯 U ψ)‖ ^ 2 ≤ η ^ 2) :
    ‖(1 - Q) * U * P‖ ≤ η := by
  have h := gap_probability_to_operator
    ⟨hP.isIdempotentElem.map 𝒯, hP.isSelfAdjoint.map 𝒯⟩
    ⟨hQ.isIdempotentElem.map 𝒯, hQ.isSelfAdjoint.map 𝒯⟩
    (Unitary.map_mem 𝒯 hU) hη hGA
  rw [← Matrix.l2_opNorm_toEuclideanCLM ((1 - Q) * U * P)]
  simpa only [map_mul, map_sub, map_one] using h

/-- An integer number of unit-time factors realizes the inverse-gap accuracy
count. For `ε Γstar ≤ 1`, the count is at most `(K+2)/(ε Γstar)`, an explicit
uniform form of the `O(1/(ε Γstar))` assertion after Example 5.1. -/
theorem gap_factor_count_exists {error : ℕ → ℝ} {K ε g : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε) (hg : 0 < g) (hsmall : ε * g ≤ 1)
    (herror : ∀ T : ℕ, 0 < T → error T ≤ K / ((T : ℝ) * g)) :
    ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ (K + 2) / (ε * g) ∧ error T ≤ ε := by
  let T := ⌈K / (ε * g)⌉₊ + 1
  have hT : 0 < T := Nat.succ_pos _
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hratio : 0 ≤ K / (ε * g) := div_nonneg hK (mul_pos hε hg).le
  have hceil := Nat.le_ceil (K / (ε * g))
  have hceilupper := Nat.ceil_lt_add_one hratio
  have hbudget : K / (ε * g) ≤ T := by dsimp only [T]; push_cast; linarith
  have hcount : (T : ℝ) ≤ (K + 2) / (ε * g) := by
    have hcount' : (T : ℝ) ≤ K / (ε * g) + 2 := by dsimp only [T]; push_cast; linarith
    calc
      (T : ℝ) ≤ K / (ε * g) + 2 := hcount'
      _ ≤ (K + 2) / (ε * g) := by
        apply (le_div_iff₀ (mul_pos hε hg)).mpr
        have he : (K / (ε * g) + 2) * (ε * g) = K + 2 * (ε * g) := by
          field_simp
        rw [he]
        linarith
  refine ⟨T, hT, hcount, (herror T hT).trans ?_⟩
  apply (div_le_iff₀ (mul_pos hTr hg)).mpr
  have h := (div_le_iff₀ (mul_pos hε hg)).mp hbudget
  linarith [show (T : ℝ) * (ε * g) = ε * ((T : ℝ) * g) by ring]

end UnitaryProducts.PaperProof
