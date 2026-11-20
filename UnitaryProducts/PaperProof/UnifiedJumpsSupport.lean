/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.CommutatorTelescope
public import UnitaryProducts.PaperProof.TightFTC
public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.Comparison.EndpointFrame
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.LogarithmDerivative

/-! # Affine interpolation and integration for the unified jump estimate

Supports the two curve choices in the proof of Theorem 4.4. The unified derivative inequality is
an explicit input to the support theorem, supplied by Lemma A.3 in the paper head.
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology InnerProductSpace
open Complex Real Set Matrix Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "J" => Icc (0 : ℝ) 1
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- The affine segment used for both the Hamiltonian and its derivative data. -/
def jumpSegment (A B : 𝕄) (s : ℝ) : 𝕄 := (1 - s) • A + s • B

/-- Affine interpolation has the constant derivative `B-A`. -/
theorem hasDerivAt_jumpSegment (A B : 𝕄) (s : ℝ) :
    HasDerivAt (jumpSegment A B) (B - A) s := by
  convert (((hasDerivAt_id s).const_sub 1).smul_const A).add
    ((hasDerivAt_id s).smul_const B) using 1
  simp [sub_eq_add_neg, add_comm]

/-- The affine segment is smooth on the whole parameter line. -/
theorem contDiff_jumpSegment (A B : 𝕄) : ContDiff ℝ ⊤ (jumpSegment A B) := by
  unfold jumpSegment
  fun_prop

/-- Real affine combinations preserve Hermiticity. -/
theorem isHermitian_jumpSegment {A B : 𝕄} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (s : ℝ) : (jumpSegment A B s).IsHermitian :=
  (Separation.isHermitian_real_smul hA (1 - s)).add
    (Separation.isHermitian_real_smul hB s)

/-- Spectral interval bounds give the corresponding bounds for every Rayleigh
quadratic form, by expansion in a fixed eigenbasis. -/
theorem rayleigh_spectral_interval {A : 𝕄} (hA : A.IsHermitian) {a b : ℝ}
    (hev : ∀ p, hA.eigenvalues p ∈ Icc a b) (x : EuclideanSpace ℂ (Fin d)) :
    a * ‖x‖ ^ 2 ≤ (⟪x, 𝒯 A x⟫_ℂ).re ∧
    (⟪x, 𝒯 A x⟫_ℂ).re ≤ b * ‖x‖ ^ 2 := by
  classical
  let c := (hA.eigenvectorBasis.repr x).ofLp
  have hrep : ∑ p, c p • hA.eigenvectorBasis p = x := hA.eigenvectorBasis.sum_repr x
  have hnorm := norm_sq_sum_smul_eq hA.eigenvectorBasis.orthonormal c
  have hinner := re_inner_sum_smul_eq hA.eigenvectorBasis.orthonormal
    (toEuclideanCLM_eigenvectorBasis hA) c
  rw [hrep] at hnorm hinner
  simp only [RCLike.re_to_complex] at hinner
  rw [hinner, hnorm, Finset.mul_sum, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_right (hev p).1 (sq_nonneg _),
    Finset.sum_le_sum fun p _ ↦ mul_le_mul_of_nonneg_right (hev p).2 (sq_nonneg _)⟩

/-- Every interpolated eigenvalue lies between the affine combinations of the
endpoint spectral bounds. Choosing the largest and least bounds is precisely
convexity of the largest eigenvalue and concavity of the least. -/
theorem affine_eigenvalues_interval {A B : 𝕄}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a₀ a₁ b₀ b₁ s : ℝ}
    (hAw : ∀ p, hA.eigenvalues p ∈ Icc a₀ a₁)
    (hBw : ∀ p, hB.eigenvalues p ∈ Icc b₀ b₁)
    (hs : s ∈ J) (p : Fin d) :
    (isHermitian_jumpSegment hA hB s).eigenvalues p ∈
      Icc ((1 - s) * a₀ + s * b₀) ((1 - s) * a₁ + s * b₁) := by
  let hC := isHermitian_jumpSegment hA hB s
  let x := hC.eigenvectorBasis p
  have hx : ‖x‖ = 1 := hC.eigenvectorBasis.orthonormal.norm_eq_one p
  have hAx := rayleigh_spectral_interval hA hAw x
  have hBx := rayleigh_spectral_interval hB hBw x
  simp only [hx, one_pow, mul_one] at hAx hBx
  have hval : (⟪x, 𝒯 (jumpSegment A B s) x⟫_ℂ).re =
      hC.eigenvalues p := by
    rw [toEuclideanCLM_eigenvectorBasis hC]
    simp [x]
  have hsplit : (⟪x, 𝒯 (jumpSegment A B s) x⟫_ℂ).re =
      (1 - s) * (⟪x, 𝒯 A x⟫_ℂ).re +
        s * (⟪x, 𝒯 B x⟫_ℂ).re := by
    simp only [jumpSegment, RCLike.real_smul_eq_coe_smul (K := ℂ), map_add, map_smul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right,
      inner_smul_right, Complex.add_re, Complex.mul_re, RCLike.ofReal_eq_complex_ofReal,
        Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [← hval, hsplit]
  exact ⟨add_le_add (mul_le_mul_of_nonneg_left hAx.1 (sub_nonneg.mpr hs.2))
      (mul_le_mul_of_nonneg_left hBx.1 hs.1),
    add_le_add (mul_le_mul_of_nonneg_left hAx.2 (sub_nonneg.mpr hs.2))
      (mul_le_mul_of_nonneg_left hBx.2 hs.1)⟩

/-- The largest eigenvalue is convex and the least eigenvalue is concave,
as stated literally in the proof of the affine jump bound in Theorem 4.4. -/
theorem affine_spectral_extrema [NeZero d] {A B : 𝕄}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {s : ℝ} (hs : s ∈ J) :
    sSup (range (isHermitian_jumpSegment hA hB s).eigenvalues) ≤
      (1 - s) * sSup (range hA.eigenvalues) + s * sSup (range hB.eigenvalues) ∧
    (1 - s) * sInf (range hA.eigenvalues) + s * sInf (range hB.eigenvalues) ≤
      sInf (range (isHermitian_jumpSegment hA hB s).eigenvalues) := by
  have hbounds {C : 𝕄} (hC : C.IsHermitian) (p : Fin d) :
      hC.eigenvalues p ∈ Icc (sInf (range hC.eigenvalues)) (sSup (range hC.eigenvalues)) :=
    ⟨csInf_le (finite_range _).bddBelow ⟨p, rfl⟩,
      le_csSup (finite_range _).bddAbove ⟨p, rfl⟩⟩
  have hev := affine_eigenvalues_interval hA hB (hbounds hA) (hbounds hB) hs
  have hne : (range (isHermitian_jumpSegment hA hB s).eigenvalues).Nonempty :=
    ⟨_, 0, rfl⟩
  constructor
  · apply csSup_le hne
    rintro x ⟨p, rfl⟩
    exact (hev p).2
  · apply le_csInf hne
    rintro x ⟨p, rfl⟩
    exact (hev p).1

/-- Spectral width is preserved along the affine segment, by the convex
upper spectral bound and the concave lower spectral bound. -/
theorem width_jumpSegment {A B : 𝕄}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {w s : ℝ}
    (hAw : ∀ p q, |hA.eigenvalues p - hA.eigenvalues q| ≤ w)
    (hBw : ∀ p q, |hB.eigenvalues p - hB.eigenvalues q| ≤ w)
    (hs : s ∈ J) (p q : Fin d) :
    |(isHermitian_jumpSegment hA hB s).eigenvalues p -
      (isHermitian_jumpSegment hA hB s).eigenvalues q| ≤ w := by
  letI : NeZero d := ⟨Nat.ne_of_gt ((Nat.zero_le p.val).trans_lt p.isLt)⟩
  have hupperA : sSup (range hA.eigenvalues) ≤ sInf (range hA.eigenvalues) + w := by
    have hne : (range hA.eigenvalues).Nonempty := ⟨_, p, rfl⟩
    apply csSup_le hne
    rintro x ⟨r, rfl⟩
    exact (eigen_interval hA hAw r).2
  have hupperB : sSup (range hB.eigenvalues) ≤ sInf (range hB.eigenvalues) + w := by
    have hne : (range hB.eigenvalues).Nonempty := ⟨_, p, rfl⟩
    apply csSup_le hne
    rintro x ⟨r, rfl⟩
    exact (eigen_interval hB hBw r).2
  have hextrema := affine_spectral_extrema hA hB hs
  have hbounds (r : Fin d) : (isHermitian_jumpSegment hA hB s).eigenvalues r ∈
      Icc ((1 - s) * sInf (range hA.eigenvalues) + s * sInf (range hB.eigenvalues))
        ((1 - s) * (sInf (range hA.eigenvalues) + w) +
          s * (sInf (range hB.eigenvalues) + w)) := by
    constructor
    · exact hextrema.2.trans (csInf_le (finite_range _).bddBelow ⟨r, rfl⟩)
    · exact (le_csSup (finite_range _).bddAbove ⟨r, rfl⟩).trans
        (hextrema.1.trans (add_le_add
          (mul_le_mul_of_nonneg_left hupperA (sub_nonneg.mpr hs.2))
          (mul_le_mul_of_nonneg_left hupperB hs.1)))
  have hp := hbounds p
  have hq := hbounds q
  have hlength : ((1 - s) * (sInf (range hA.eigenvalues) + w) +
      s * (sInf (range hB.eigenvalues) + w)) -
      ((1 - s) * sInf (range hA.eigenvalues) + s * sInf (range hB.eigenvalues)) = w := by ring
  exact (abs_sub_le_of_le_of_le hp.1 hp.2 hq.1 hq.2).trans_eq hlength

/-- Mesh integration in the canonical derivative notation of Lemma A.3.
For the C² jump bound
in Theorem 4.6, `F(s)=frameOp (H s) (H' s)` and the majorant is
`N(w)||H''|| + eta(w)||W'|| ||H'||`. -/
theorem unified_mesh_integral_of_derivWithin {F : ℝ → 𝕄} {g : ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 F J)
    (hbound : ∀ s ∈ J, ‖derivWithin F J s‖ ≤ g s)
    (hi : IntervalIntegrable g volume 0 1) {T : ℕ} (hT : 0 < T) :
    (∑ j ∈ Finset.range T, ‖F (((j : ℝ) + 1) / T) - F (j / T)‖) ≤
      ∫ s in (0 : ℝ)..1, g s := by
  exact unified_mesh_integral_via_ftc hF hbound hi hT

end UnitaryProducts.PaperProof
