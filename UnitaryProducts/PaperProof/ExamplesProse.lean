/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.PropJumps
public import UnitaryProducts.Prose.UnifiedQuadrature

/-! # Mathematical steps in the revised introduction and discussion -/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
open Set
open UnitaryProducts UnitaryProducts.Paper
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 6, QAOA: smooth angle schedules give a smooth unitary family of
layers. The free-arc hypothesis can therefore be supplied to the walk comparison. -/
theorem qaoa_smooth_unitary_family (B C : 𝕄) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (β γ : ℝ → ℝ) (hβ : ContDiffOn ℝ 2 β (Icc (0 : ℝ) 1))
    (hγ : ContDiffOn ℝ 2 γ (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (fun s ↦ evol ((β s) • B) 1 * evol ((γ s) • C) 1)
      (Icc (0 : ℝ) 1) ∧
    ∀ s : ℝ, evol ((β s) • B) 1 * evol ((γ s) • C) 1 ∈ unitary 𝕄 := by
  have hcB : ContDiffOn ℝ 2 (fun s ↦ (β s) • B) (Icc (0 : ℝ) 1) :=
    hβ.smul contDiffOn_const
  have hcC : ContDiffOn ℝ 2 (fun s ↦ (γ s) • C) (Icc (0 : ℝ) 1) :=
    hγ.smul contDiffOn_const
  have hleft : ContDiffOn ℝ 2 (fun s ↦ evol ((β s) • B) 1) (Icc (0 : ℝ) 1) := by
    intro s hs
    have he := (contDiffAt_evol_one ((β s) • B) (n := 2)).restrict_scalars ℝ
    have h := he.comp_contDiffWithinAt s (hcB s hs)
    exact h
  have hright : ContDiffOn ℝ 2 (fun s ↦ evol ((γ s) • C) 1) (Icc (0 : ℝ) 1) := by
    intro s hs
    have he := (contDiffAt_evol_one ((γ s) • C) (n := 2)).restrict_scalars ℝ
    have h := he.comp_contDiffWithinAt s (hcC s hs)
    exact h
  refine ⟨hleft.mul hright, fun s ↦ ?_⟩
  exact mul_mem (evol_mem_unitary (Separation.isHermitian_real_smul hB _) 1)
    (evol_mem_unitary (Separation.isHermitian_real_smul hC _) 1)

/-- Section 6, the resonance question: in a commuting differentiable family,
the derivative commutes with the sample. Thus it has no matrix entries between
distinct eigenspaces, in particular between resonant distinct eigenvalues. -/
theorem commuting_family_derivative (H Hd : ℝ → 𝕄)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hcomm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, Commute (H s) (H t))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Commute (H s) (Hd s) := by
  have hleft : HasDerivWithinAt (fun t ↦ H s * H t) (H s * Hd s) (Icc 0 1) s := by
    simpa using (hd s hs).const_mul (H s)
  have hright : HasDerivWithinAt (fun t ↦ H t * H s) (Hd s * H s) (Icc 0 1) s := by
    simpa using (hd s hs).mul_const (H s)
  have hright' : HasDerivWithinAt (fun t ↦ H s * H t) (Hd s * H s) (Icc 0 1) s :=
    hright.congr (fun t ht ↦ (hcomm s hs t ht).eq) rfl
  exact (hleft.derivWithin (uniqueDiffOn_Icc_zero_one s hs)).symm.trans
    (hright'.derivWithin (uniqueDiffOn_Icc_zero_one s hs))


/-- Section 6, the resonance question, in an eigenbasis: commutation kills
all entries between distinct eigenvalues, including nonzero resonances. -/
theorem commuting_diagonal_offdiagonal_zero (eig : Fin d → ℂ) (A : 𝕄)
    (hcomm : Commute (Matrix.diagonal eig) A) {p q : Fin d} (hne : eig p ≠ eig q) :
    A p q = 0 := by
  have hentry := congrFun (congrFun hcomm.eq p) q
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
  have hzero : (eig p - eig q) * A p q = 0 := by
    linear_combination hentry
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

/-- Section 6, eigenvector rotation: differentiating an eigenbasis equation
identifies the off-diagonal derivative with the spectral difference times the
rotation of that basis. The diagonal derivative has no off-diagonal entries. -/
theorem eigenbasis_derivative_entry (H W D : ℝ → 𝕄) (Hd Wd : 𝕄)
    (eig deig : Fin d → ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hH : HasDerivWithinAt H Hd (Icc 0 1) s)
    (hW : HasDerivWithinAt W Wd (Icc 0 1) s)
    (hD : HasDerivWithinAt D (Matrix.diagonal deig) (Icc 0 1) s)
    (heig : ∀ t ∈ Icc (0 : ℝ) 1, H t * W t = W t * D t)
    (hdiag : D s = Matrix.diagonal eig) (hunit : W s ∈ unitary 𝕄)
    {p q : Fin d} (hpq : p ≠ q) :
    (star (W s) * Hd * W s) p q =
      (eig q - eig p) * (star (W s) * Wd) p q := by
  have hl := hH.mul hW
  have hr := hW.mul hD
  have hr' : HasDerivWithinAt (fun t ↦ H t * W t)
      (Wd * D s + W s * Matrix.diagonal deig) (Icc 0 1) s :=
    hr.congr (fun t ht ↦ heig t ht) (heig s hs)
  have hder := (hl.derivWithin (uniqueDiffOn_Icc_zero_one s hs)).symm.trans
    (hr'.derivWithin (uniqueDiffOn_Icc_zero_one s hs))
  have hu := (Unitary.mem_iff.mp hunit)
  have hleft : star (W s) * H s = D s * star (W s) := by
    calc
      star (W s) * H s = star (W s) * H s * (W s * star (W s)) := by
        rw [hu.2, mul_one]
      _ = star (W s) * (H s * W s) * star (W s) := by simp only [mul_assoc]
      _ = D s * star (W s) := by rw [heig s hs]; simp only [← mul_assoc, hu.1, one_mul]
  have hmatrix := congrArg (fun A : 𝕄 ↦ star (W s) * A) hder
  simp only [mul_add, ← mul_assoc, hu.1, one_mul, hleft, hdiag] at hmatrix
  rw [mul_assoc (Matrix.diagonal eig) (star (W s)) Wd] at hmatrix
  have hentry := congrFun (congrFun hmatrix p) q
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply_ne _ hpq] at hentry
  linear_combination hentry

end UnitaryProducts.PaperProof
