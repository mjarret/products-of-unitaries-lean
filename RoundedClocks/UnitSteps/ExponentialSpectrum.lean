/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # The eigenvalues of `e^{-iH}`

"The unitary `W = e^{-iH}` has the eigenvalues of `H` read modulo `2π`" (Section 4.4): the
eigenvalues of `e^{-iH}` are the `e^{-iθ}` for the eigenvalues `θ` of a Hermitian `H`
(`spectrum_exp`). The proof of Theorem 4.6 uses this for (4.7). The proof of Theorem 4.7 also uses
that `θ ↦ e^{-iθ}` is injective for `θ ∈ (α, α + 2π)` (`phase_inj`), and that such a `θ` lies in
`(α, β)` exactly when `e^{-iθ}` lies in the arc `{e^{-iφ} : α < φ < β}` (`phase_mem_arc_iff`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section

namespace RoundedClocks

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}

/-- The eigenvalues of `e^{-iA}` are the `e^{-iθ}` for the eigenvalues `θ` of a Hermitian `A`. -/
theorem spectrum_exp {A : Matrix (Fin d) (Fin d) ℂ} (hA : IsHermitian A) :
    spectrum ℂ (NormedSpace.exp (-I • A)) =
      (fun θ : ℝ ↦ Complex.exp (-I * (θ : ℂ))) '' spectrum ℝ A := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  have hn : IsStarNormal A := hsa.isStarNormal
  have he : NormedSpace.exp (-I • A) =
      cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A := by
    have hh : cfc (fun z : ℂ ↦ Complex.exp (-I * z)) A =
        cfc Complex.exp (cfc (fun z : ℂ ↦ -I * z) A) :=
      cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I * z) A hn
        Complex.continuous_exp.continuousOn (continuousOn_const.mul continuousOn_id)
    rw [hh, cfc_const_mul_id (-I) A, CFC.complex_exp_eq_normedSpace_exp]
  rw [he, cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) A hn
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn]
  rw [← hsa.spectrumRestricts.algebraMap_image, Set.image_image]
  rfl

/-- `θ ↦ e^{-iθ}` is injective for `θ ∈ (α, α + 2π)`. -/
theorem phase_inj {α θ φ : ℝ}
    (hθ : θ ∈ Ioo α (α + 2 * π)) (hφ : φ ∈ Ioo α (α + 2 * π))
    (he : Complex.exp (-I * (θ : ℂ)) = Complex.exp (-I * (φ : ℂ))) : θ = φ := by
  haveI : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  refine (AddCircle.coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hθ)
    (Ioo_subset_Ico_self hφ)).mp ?_
  apply AddCircle.injective_toCircle Real.two_pi_pos.ne'
  apply Circle.ext
  have h := congrArg (·⁻¹) he
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_self Real.two_pi_pos.ne', one_mul]
  simpa [← Complex.exp_neg, mul_comm] using h

/-- Proof of Theorem 4.7: for `θ ∈ (α, α + 2π)` and `β < α + 2π`, `e^{-iθ}` lies in the arc
`{e^{-iφ} : α < φ < β}` exactly when `θ` lies in `(α, β)`. -/
theorem phase_mem_arc_iff {α β θ : ℝ} (hβ : β < α + 2 * π)
    (hθ : θ ∈ Ioo α (α + 2 * π)) :
    Complex.exp (-I * (θ : ℂ)) ∈ arc α β ↔ θ ∈ Ioo α β := by
  constructor
  · rintro ⟨φ, hφ, he⟩
    have heq := phase_inj ⟨hφ.1, hφ.2.trans hβ⟩ hθ he
    exact heq ▸ hφ
  · intro h
    exact ⟨θ, h, rfl⟩

end RoundedClocks
