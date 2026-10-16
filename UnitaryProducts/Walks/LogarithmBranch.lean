/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# Hermitian logarithms of unitaries

## Declarations

- `argBranch`
- `argBranch_exp_mul_I`
- `argDomain`
- `cfc_argBranch_evol`
- `conj_argBranch`
- `continuousOn_argBranch`
- `continuous_evol_one`
- `eq_of_evol_eq`
- `evol_one_eq_cfc_exp`
- `exists_isHermitian_evol_eq`
- `exp_mul_I_mem_argDomain`
- `exp_mul_I_mul_exp`
- `exp_neg_I_mul_argBranch`
- `matrixCStarAlgebra`
- `toIocMod_eq_of_abs_lt`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Real UnitaryProducts.Corrector

/-- Matrices with the $\ell^2$ operator norm as a C⋆-algebra, so that the continuous functional
calculus `cfc` applies to normal matrices. This is a `def`, not a global instance; files install it
with `attribute [local instance]`. The `where` body is empty: every field (normed ring, normed
`ℂ`-algebra, star ring, C⋆-ring, completeness) is filled by the `Matrix.Norms.L2Operator`
instances in scope, so its norm is the $\ell^2$ operator norm of the statements. An adapter: the
pinned Mathlib has the fields but not this structure, which later Mathlib provides as the scoped
instance `Matrix.instCStarAlgebra`. -/
noncomputable def matrixCStarAlgebra (d : ℕ) : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

-- Installs `matrixCStarAlgebra` (above), built from the ℓ² operator-norm instances, for `cfc`.
attribute [local instance] matrixCStarAlgebra

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The branch of $-\arg$ centred at $-\alpha$: `argBranch α` $(e^{i\theta}) = -\theta$ for
$|\theta - \alpha| < \pi$. It is defined on all of `ℂ` through `Complex.arg` (value $-\alpha$ at
$0$), continuous on `argDomain α`, and used only on the unit circle. -/
noncomputable def argBranch (α : ℝ) (z : ℂ) : ℂ :=
  -((α : ℂ) + ((z * Complex.exp (-(α : ℝ) * I)).arg : ℂ))

/-- The set on which `argBranch α` is continuous: the plane slit along the ray `-ℝ₊ e^{iα}`. -/
def argDomain (α : ℝ) : Set ℂ := {z : ℂ | z * Complex.exp (-(α : ℝ) * I) ∈ Complex.slitPlane}

/-- `argBranch α` is continuous off its slit. -/
theorem continuousOn_argBranch (α : ℝ) : ContinuousOn (argBranch α) (argDomain α) := by
  intro z hz
  have h : ContinuousAt (fun w : ℂ ↦ (w * Complex.exp (-(α : ℝ) * I)).arg) z :=
    ContinuousAt.comp (g := Complex.arg) (f := fun w : ℂ ↦ w * Complex.exp (-(α : ℝ) * I))
      (Complex.continuousAt_arg hz) (continuous_id.mul continuous_const).continuousAt
  have h3 : ContinuousAt
      (fun w : ℂ ↦ -((α : ℂ) + (((w * Complex.exp (-(α : ℝ) * I)).arg : ℝ) : ℂ))) z :=
    (continuousAt_const.add (Complex.continuous_ofReal.continuousAt.comp h)).neg
  exact h3.continuousWithinAt

/-- `toIocMod` is the identity on `(-π, π)`. -/
theorem toIocMod_eq_of_abs_lt {ψ : ℝ} (h : |ψ| < π) :
    toIocMod Real.two_pi_pos (-π) ψ = ψ :=
  (toIocMod_eq_self _).2 ⟨(abs_lt.mp h).1, by linarith [(abs_lt.mp h).2]⟩

/-- $e^{i\theta}e^{-i\alpha} = e^{i(\theta - \alpha)}$. -/
theorem exp_mul_I_mul_exp {α θ : ℝ} :
    Complex.exp ((θ : ℂ) * I) * Complex.exp (-(α : ℝ) * I)
      = Complex.exp (((θ - α : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- $e^{i\theta}$ lies in `argDomain α` when $|\theta - \alpha| < \pi$. -/
theorem exp_mul_I_mem_argDomain {α θ : ℝ} (h : |θ - α| < π) :
    Complex.exp ((θ : ℂ) * I) ∈ argDomain α := by
  have him : (((θ - α : ℝ) : ℂ) * I).im = θ - α := by simp
  change _ ∈ Complex.slitPlane
  rw [exp_mul_I_mul_exp, Complex.exp_mem_slitPlane, him, toIocMod_eq_of_abs_lt h]
  exact ne_of_lt (abs_lt.mp h).2

/-- `argBranch α` $(e^{i\theta}) = -\theta$ when $|\theta - \alpha| < \pi$. -/
theorem argBranch_exp_mul_I {α θ : ℝ} (h : |θ - α| < π) :
    argBranch α (Complex.exp ((θ : ℂ) * I)) = -(θ : ℂ) := by
  rw [argBranch, exp_mul_I_mul_exp, Complex.arg_exp_mul_I, toIocMod_eq_of_abs_lt h]
  push_cast; ring

/-- `argBranch` is real-valued. -/
theorem conj_argBranch (α : ℝ) (z : ℂ) : (starRingEnd ℂ) (argBranch α z) = argBranch α z := by
  simp [argBranch]

/-- The branch inverts `z ↦ e^{-iz}` on the unit circle. -/
theorem exp_neg_I_mul_argBranch {α : ℝ} {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (-I * argBranch α z) = z := by
  set w : ℂ := z * Complex.exp (-(α : ℝ) * I) with hw
  have hexpn : ‖Complex.exp (-(α : ℝ) * I)‖ = 1 := by simp [Complex.norm_exp]
  have hwn : ‖w‖ = 1 := by rw [hw, norm_mul, hz, hexpn, one_mul]
  have key : Complex.exp ((w.arg : ℂ) * I) = w := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rwa [hwn, Complex.ofReal_one, one_mul] at h
  have hstep : -I * argBranch α z = (α : ℂ) * I + (w.arg : ℂ) * I := by
    rw [argBranch, ← hw]
    ring
  have hcancel : Complex.exp ((α : ℂ) * I) * Complex.exp (-(α : ℝ) * I) = 1 := by
    rw [← Complex.exp_add, show (α : ℂ) * I + -(α : ℝ) * I = 0 by ring,
      Complex.exp_zero]
  rw [hstep, Complex.exp_add, key, hw, mul_left_comm, hcancel, mul_one]

/-- **Existence of the Hermitian logarithm.**  A unitary whose spectrum lies in the closed arc of
half-width `r < π` about `e^{iα}` is `e^{-iA}` for a Hermitian `A` within `r` of `-α` (the
pointwise existence in Lemma A.2 (existence and uniqueness)). -/
theorem exists_isHermitian_evol_eq {U : 𝕄} {α r : ℝ} (hr0 : 0 ≤ r) (hr : r < π)
    (hU : star U * U = 1)
    (hspec : ∀ z ∈ spectrum ℂ U, ∃ θ ∈ Icc (α - r) (α + r), z = Complex.exp ((θ : ℂ) * I)) :
    ∃ A : 𝕄, A.IsHermitian ∧ ‖A - ((-α : ℝ) : ℂ) • 1‖ ≤ r ∧ evol A 1 = U := by
  have hnormal : IsStarNormal U :=
    ⟨by change star U * U = U * star U; rw [hU, mul_eq_one_comm.mp hU]⟩
  have hdom : ∀ z ∈ spectrum ℂ U, z ∈ argDomain α := by
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := hspec z hz
    exact exp_mul_I_mem_argDomain (abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
  have hcont : ContinuousOn (argBranch α) (spectrum ℂ U) :=
    (continuousOn_argBranch α).mono hdom
  refine ⟨cfc (argBranch α) U, ?_, ?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSelfAdjoint]
    exact (cfc_star (argBranch α) U).symm.trans (cfc_congr fun z _ ↦ conj_argBranch α z)
  · have hc : ((-α : ℝ) : ℂ) • (1 : 𝕄) = algebraMap ℂ 𝕄 ((-α : ℝ) : ℂ) :=
      (Algebra.algebraMap_eq_smul_one _).symm
    rw [hc, ← cfc_const ((-α : ℝ) : ℂ) U, ← cfc_sub _ _ _ hcont continuousOn_const]
    refine norm_cfc_le hr0 ?_
    intro z hz
    obtain ⟨θ, hθ, rfl⟩ := hspec z hz
    have habs : |θ - α| < π := abs_lt.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    rw [argBranch_exp_mul_I habs,
      show -(θ : ℂ) - ((-α : ℝ) : ℂ) = ((α - θ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  · have hsmul : cfc (fun z ↦ -I * argBranch α z) U = (-I) • cfc (argBranch α) U := by
      simpa [smul_eq_mul] using cfc_smul (S := ℂ) (-I) (argBranch α) U
    have hcomp : cfc (fun z ↦ Complex.exp (-I * argBranch α z)) U
        = cfc Complex.exp (cfc (fun z ↦ -I * argBranch α z) U) :=
      cfc_comp (R := ℂ) Complex.exp (fun z ↦ -I * argBranch α z) U hnormal
        Complex.continuous_exp.continuousOn (continuousOn_const.mul hcont)
    have hid : cfc (fun z ↦ Complex.exp (-I * argBranch α z)) U = U := by
      refine (cfc_congr fun z hz ↦ ?_).trans (cfc_id ℂ U)
      obtain ⟨θ, _, rfl⟩ := hspec z hz
      exact exp_neg_I_mul_argBranch (by simp [Complex.norm_exp])
    rw [evol, one_smul, ← hsmul, ← CFC.complex_exp_eq_normedSpace_exp, ← hcomp, hid]

/-- $e^{-iH}$ is the functional calculus of $z \mapsto e^{-iz}$ at a Hermitian $H$. -/
theorem evol_one_eq_cfc_exp (H : 𝕄) (hH : H.IsHermitian) :
    evol H 1 = cfc (fun z : ℂ ↦ Complex.exp (-I * z)) H := by
  have := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  rw [evol, one_smul, cfc_comp_const_mul (-I) Complex.exp H Complex.continuous_exp.continuousOn,
    CFC.complex_exp_eq_normedSpace_exp]

/-- Every Hermitian matrix in the window is recovered from its exponential by the branch. -/
theorem cfc_argBranch_evol [NeZero d] {A : 𝕄} {α r : ℝ} (hr : r < π)
    (hA : A.IsHermitian) (hAn : ‖A - ((-α : ℝ) : ℂ) • 1‖ ≤ r) :
    cfc (argBranch α) (evol A 1) = A := by
  have hsa : IsSelfAdjoint A := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hnormal : IsStarNormal A := hsa.isStarNormal
  have hspecA : ∀ z ∈ spectrum ℂ A, ∃ lam : ℝ, |lam + α| ≤ r ∧ z = (lam : ℂ) := by
    intro z hz
    obtain ⟨lam, rfl⟩ : ∃ lam : ℝ, z = (lam : ℂ) :=
      ⟨z.re, IsSelfAdjoint.mem_spectrum_eq_re hsa hz⟩
    refine ⟨lam, ?_, rfl⟩
    have hmem : (lam : ℂ) - ((-α : ℝ) : ℂ) ∈ spectrum ℂ (A - algebraMap ℂ 𝕄 ((-α : ℝ) : ℂ)) := by
      rw [← spectrum.sub_singleton_eq]
      exact Set.sub_mem_sub hz rfl
    have hnorm := spectrum.norm_le_norm_of_mem hmem
    rw [← Algebra.algebraMap_eq_smul_one] at hAn
    have h1 : ‖(lam : ℂ) - ((-α : ℝ) : ℂ)‖ = |lam + α| := by
      rw [show ((lam : ℂ) - ((-α : ℝ) : ℂ)) = ((lam + α : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h1] at hnorm
    exact hnorm.trans hAn
  have hcontg : ContinuousOn (fun z : ℂ ↦ Complex.exp (-I * z)) (spectrum ℂ A) :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hconv (lam : ℝ) : Complex.exp (-I * (lam : ℂ)) = Complex.exp (((-lam : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have himg : ∀ z ∈ (fun z : ℂ ↦ Complex.exp (-I * z)) '' spectrum ℂ A, z ∈ argDomain α := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨lam, hlam, rfl⟩ := hspecA y hy
    change Complex.exp (-I * (lam : ℂ)) ∈ argDomain α
    rw [hconv]
    refine exp_mul_I_mem_argDomain ?_
    have : |(-lam) - α| = |lam + α| := by
      rw [show (-lam) - α = -(lam + α) by ring, abs_neg]
    rw [this]
    exact lt_of_le_of_lt hlam hr
  have hcontf : ContinuousOn (argBranch α)
      ((fun z : ℂ ↦ Complex.exp (-I * z)) '' spectrum ℂ A) :=
    (continuousOn_argBranch α).mono himg
  rw [evol_one_eq_cfc_exp A hA,
    ← cfc_comp (R := ℂ) (argBranch α) (fun z ↦ Complex.exp (-I * z)) A hnormal hcontf hcontg]
  have hcongr : cfc (argBranch α ∘ fun z : ℂ ↦ Complex.exp (-I * z)) A = cfc (id : ℂ → ℂ) A := by
    refine cfc_congr fun z hz ↦ ?_
    obtain ⟨lam, hlam, rfl⟩ := hspecA z hz
    have habs : |(-lam) - α| < π := by
      rw [show (-lam) - α = -(lam + α) by ring, abs_neg]
      exact lt_of_le_of_lt hlam hr
    change argBranch α (Complex.exp (-I * (lam : ℂ))) = id (lam : ℂ)
    rw [hconv, argBranch_exp_mul_I habs]
    simp
  rw [hcongr, cfc_id ℂ A]

/-- **Uniqueness of the Hermitian logarithm** in a window of width `< 2π` (Lemma A.2 (existence
and uniqueness): both
logarithms are `argBranch` of the same exponential, as $\theta \mapsto e^{-i\theta}$ is one-to-one
on the window). -/
theorem eq_of_evol_eq [NeZero d] {A B : 𝕄} {α r : ℝ} (hr : r < π)
    (hA : A.IsHermitian) (hAn : ‖A - ((-α : ℝ) : ℂ) • 1‖ ≤ r)
    (hB : B.IsHermitian) (hBn : ‖B - ((-α : ℝ) : ℂ) • 1‖ ≤ r)
    (h : evol A 1 = evol B 1) : A = B := by
  rw [← cfc_argBranch_evol hr hA hAn, ← cfc_argBranch_evol hr hB hBn, h]

/-- `A ↦ e^{-iA}` is continuous. -/
theorem continuous_evol_one : Continuous (fun A : 𝕄 ↦ evol A 1) := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  exact NormedSpace.exp_continuous.comp (by fun_prop)

end UnitaryProducts
