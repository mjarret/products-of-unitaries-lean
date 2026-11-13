/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PartialFractionMultiplier
public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.Corrector.FrameBounds
public import UnitaryProducts.Prose.GeneralSpectralSeries
public import UnitaryProducts.Walks.WalkScalarCut

/-! # The objects in the unit-step comparison -/
@[expose] public section

open scoped Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.Paper

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The domain of the complex multiplier in Definition 4.1 excludes its nonzero poles. -/
def unitMultiplierDomain (x : ℂ) : Prop :=
  ∀ m : ℤ, m ≠ 0 → x ≠ 2 * Real.pi * m

/-- **Definition 4.1** (`def:unit-objects`): the complex closed-form multiplier
on its stated domain, and its entrywise action for eigenvalue differences below `2π`. -/
def unitComparisonObjects :
    ({x : ℂ // unitMultiplierDomain x} → ℂ) ×
      ((Ω : 𝕄) → (hΩ : Ω.IsHermitian) →
        (∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * Real.pi) → 𝕄 → 𝕄) :=
  (fun x ↦ WalkCut.complexFrameMult x,
    fun Ω hΩ _ E ↦ UnitStepsProse.complexSpectralMultiplier Ω hΩ
      (fun x ↦ WalkCut.complexFrameMult (x : ℂ)) E)

/-- The matrix multiplier of Definition 4.1, extended by zero outside its domain.
Every comparison theorem evaluates it on a Hermitian matrix below width `2π`. -/
def paperFrameOp (Ω E : 𝕄) : 𝕄 :=
  if hΩ : Ω.IsHermitian then
    if hw : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * Real.pi then
      unitComparisonObjects.2 Ω hΩ hw E
    else 0
  else 0

/-- The closed scalar multiplier agrees with its absolutely convergent series. -/
theorem paperFrameMult_eq_series {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * Real.pi) :
    Corrector.frameMult w = Corrector.frameBound w := by
  exact Corrector.frameMult_eq_frameCoeff_series (by rwa [abs_of_nonneg hw0])

/-- The derivative of the closed scalar multiplier agrees with the derivative series. -/
theorem paperFrameMult_deriv_eq_series {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w < 2 * Real.pi) :
    deriv Corrector.frameMult w = Corrector.frameLip w := by
  exact (Corrector.hasDerivAt_frameMult (by rwa [abs_of_nonneg hw0])).deriv

/-- The matrix object in Definition 4.1 agrees with the operator series below width `2π`. -/
theorem paperFrameOp_eq_series {Ω : 𝕄} (hΩ : Ω.IsHermitian) {w : ℝ}
    (hw : w < 2 * Real.pi)
    (hwidth : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (E : 𝕄) :
    paperFrameOp Ω E = frameOp Ω E := by
  classical
  rw [paperFrameOp, dif_pos hΩ, dif_pos (fun p q ↦ (hwidth p q).trans_lt hw)]
  dsimp only [unitComparisonObjects]
  rw [frameOp_eq_eigenbasis hΩ hw (eigen_interval hΩ hwidth)]
  simp only [UnitStepsProse.complexSpectralMultiplier, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, WalkCut.complexFrameMult_ofReal]


end UnitaryProducts.Paper
