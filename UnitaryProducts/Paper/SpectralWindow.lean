/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.CircularBands

/-! # Bands, spectral gaps, multiplicities and endpoint projectors -/
@[expose] public section

open Complex Real Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Definition 2.5(i): the interval or arc used to select eigenvalues.
`circular = false` is the Hermitian case; `true` is the unitary case. -/
def spectralWindowSet (circular : Bool) (a b : ℝ) : Set ℂ :=
  (fun θ : ℝ ↦ if circular then Complex.exp (-I * (θ : ℂ)) else (θ : ℂ)) '' Ioo a b

/-- Definition 2.5(i): the selected eigenvalues form a nonempty proper subset,
and neither endpoint is an eigenvalue. In the unitary case these conditions
force `a < b < a + 2π`, as `spectralWindowBand_endpoint_order` proves. -/
def spectralWindowBand (circular : Bool) (A : 𝕄) (a b : ℝ) : Prop :=
  (if circular then star A * A = 1 else A.IsHermitian) ∧
  (spectrum ℂ A ∩ spectralWindowSet circular a b).Nonempty ∧
  (spectrum ℂ A \ spectralWindowSet circular a b).Nonempty ∧
  (if circular then Complex.exp (-I * (a : ℂ)) else (a : ℂ)) ∉ spectrum ℂ A ∧
  (if circular then Complex.exp (-I * (b : ℂ)) else (b : ℂ)) ∉ spectrum ℂ A

/-- Definition 2.5(i): orthogonal projection onto the span of the selected
eigenspaces. Mathlib's orthogonal projection handles the finite-dimensional span. -/
def spectralWindowProjector (circular : Bool) (A : 𝕄) (a b : ℝ) : 𝕄 :=
  let E : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
    ⨆ z ∈ spectralWindowSet circular a b,
      Module.End.eigenspace ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) A).toLinearMap z
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm E.starProjection

/-- Definition 2.5(ii): least distance between the band and its complement.
For the unitary case all phase representatives are included; their infimum is
the integer minimum in `angularDistance_isLeast`. On a genuine band both
spectral parts are nonempty. -/
def spectralWindowGap (circular : Bool) (A : 𝕄) (a b : ℝ) : ℝ :=
  if circular then
    sInf {r : ℝ | ∃ θ φ : ℝ,
      Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ A ∩ spectralWindowSet true a b ∧
      Complex.exp (-I * (φ : ℂ)) ∈ spectrum ℂ A \ spectralWindowSet true a b ∧
      r = angularDistance θ φ}
  else
    sInf {r : ℝ | ∃ x y : ℝ,
      (x : ℂ) ∈ spectrum ℂ A ∩ spectralWindowSet false a b ∧
      (y : ℂ) ∈ spectrum ℂ A \ spectralWindowSet false a b ∧ r = |x-y|}

/-- Definition 2.5(iii): multiplicities are those of the characteristic roots. -/
def spectralWindowCount (circular : Bool) (A : 𝕄) (a b : ℝ) : ℕ := by
  classical
  exact (A.charpoly.roots.filter (fun z ↦ z ∈ spectralWindowSet circular a b)).card

/-- Definition 2.5(iii): a band of a family has continuous endpoints on `[0,1]`.
Continuity of the family or of its gap is not silently included. -/
def spectralWindowFamily (circular : Bool) (A : ℝ → 𝕄) (a b : ℝ → ℝ) : Prop :=
  ContinuousOn a (Icc 0 1) ∧ ContinuousOn b (Icc 0 1) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, spectralWindowBand circular (A s) (a s) (b s)

/-- **Definition 2.5** (`def:spectral-window`), in paper order: band predicate,
spectral projector, spectral gap (Hermitian) or eigenphase gap (unitary),
family-band predicate, predicate of having
`m` eigenvalues counted with multiplicity, and the two endpoint projectors.
The Boolean selects Hermitian (`false`) or unitary (`true`) matrices. -/
def spectralWindowData (circular : Bool) :
    (𝕄 → ℝ → ℝ → Prop) × (𝕄 → ℝ → ℝ → 𝕄) × (𝕄 → ℝ → ℝ → ℝ) ×
    ((ℝ → 𝕄) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) ×
    ((ℝ → 𝕄) → (ℝ → ℝ) → (ℝ → ℝ) → ℕ → Prop) ×
    ((ℝ → 𝕄) → (ℝ → ℝ) → (ℝ → ℝ) → 𝕄 × 𝕄) :=
  (spectralWindowBand circular, spectralWindowProjector circular,
    spectralWindowGap circular, spectralWindowFamily circular,
    fun A a b m ↦ spectralWindowFamily circular A a b ∧
      ∀ s ∈ Icc (0 : ℝ) 1, spectralWindowCount circular (A s) (a s) (b s) = m,
    fun A a b ↦ (spectralWindowProjector circular (A 0) (a 0) (b 0),
      spectralWindowProjector circular (A 1) (a 1) (b 1)))

end UnitaryProducts.Paper
