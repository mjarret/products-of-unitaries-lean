/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Prose.GeneralSpectralSeries
public import UnitaryProducts.Corrector.PeriodicCharacterization
/-! # Entrywise spectral multipliers -/
@[expose] public section
open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.PaperProof UnitStepsProse

/-- Entries of the spectral multiplier in the Hermitian eigenbasis. This
internal calculus identity supports the closed cell formula in Appendix A. -/
theorem spectralMultiplier_eigenbasis_entry (Ω : 𝕄) (hΩ : Ω.IsHermitian)
    (f : ℝ → ℂ) (E : 𝕄) (p q : Fin d) :
    let V : 𝕄 := hΩ.eigenvectorUnitary
    (star V * complexSpectralMultiplier Ω hΩ f E * V) p q =
      f (hΩ.eigenvalues p - hΩ.eigenvalues q) * (star V * E * V) p q := by
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  change (e.symm (e (Matrix.of _))) p q = _
  rw [e.symm_apply_apply]
  rfl

end UnitaryProducts.Paper
