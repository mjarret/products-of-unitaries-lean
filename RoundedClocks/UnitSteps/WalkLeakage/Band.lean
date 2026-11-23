/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Bands and logarithms by parts

The proof of Theorem 4.7 uses the parts of two definitions by name.

Definition 2.5(ii) and (iv): a band `{e^{-iθ} : a < θ < b}` of a unitary `A` has `b < a + 2π`,
contains an eigenvalue of `A`, does not contain every eigenvalue of `A`, and `e^{-ia}` and
`e^{-ib}` are not eigenvalues of `A`. A band of a unitary family `A(s)` is a band of each `A(s)`
for `s ∈ [0,1]`, with `a` and `b` continuous.

Theorem 4.7: the Hermitian `H(s)` with `e^{-iH(s)} = W(s)` and spectrum in `(α(s), α(s) + 2π)`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Real
open Set
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A matrix with a band `{e^{-iθ} : a < θ < b}` in the sense of Definition 2.5(ii) is unitary. -/
theorem IsArcBand.isUnitary {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) : IsUnitary A := h.1

/-- A band `{e^{-iθ} : a < θ < b}` of a unitary matrix has `b < a + 2π`. -/
theorem IsArcBand.lt_add_two_pi {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) : b < a + 2 * π :=
  h.2.2.1

/-- A band of a unitary matrix `A` contains an eigenvalue of `A`. -/
theorem IsArcBand.nonempty_inter {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) :
    (spectrum ℂ A ∩ arc a b).Nonempty :=
  h.2.2.2.1

/-- A band of a unitary matrix `A` does not contain every eigenvalue of `A`. -/
theorem IsArcBand.nonempty_diff {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) :
    (spectrum ℂ A \ arc a b).Nonempty :=
  h.2.2.2.2.1

/-- For a band `{e^{-iθ} : a < θ < b}` of a unitary `A`, `e^{-ia}` is not an eigenvalue of `A`. -/
theorem IsArcBand.left_notMem {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) :
    Complex.exp (-I * (a : ℂ)) ∉ spectrum ℂ A :=
  h.2.2.2.2.2.1

/-- For a band `{e^{-iθ} : a < θ < b}` of a unitary `A`, `e^{-ib}` is not an eigenvalue of `A`. -/
theorem IsArcBand.right_notMem {A : 𝕄} {a b : ℝ} (h : IsArcBand A a b) :
    Complex.exp (-I * (b : ℂ)) ∉ spectrum ℂ A :=
  h.2.2.2.2.2.2

/-- The lower endpoint `a(s)` of a band of a unitary family is continuous for `s ∈ [0,1]`. -/
theorem IsArcBandFamily.continuous_left {A : ℝ → 𝕄} {a b : ℝ → ℝ} (h : IsArcBandFamily A a b) :
    IsContinuousFamily a :=
  h.1

/-- A band of a unitary family `A(s)` is a band of each `A(s)` for `s ∈ [0,1]`. -/
theorem IsArcBandFamily.isArcBand {A : ℝ → 𝕄} {a b : ℝ → ℝ} (h : IsArcBandFamily A a b)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : IsArcBand (A s) (a s) (b s) :=
  h.2.2 s hs

/-- The logarithm `H` of Theorem 4.7 is a time-dependent Hamiltonian. -/
theorem IsLogarithm.isHermitian {W : ℝ → 𝕄} {α : ℝ → ℝ} {H : ℝ → 𝕄} (h : IsLogarithm W α H) :
    IsTimeDepHamiltonian H :=
  h.1

/-- The logarithm `H` of Theorem 4.7 satisfies `e^{-iH(s)} = W(s)` for `s ∈ [0,1]`. -/
theorem IsLogarithm.exp_eq {W : ℝ → 𝕄} {α : ℝ → ℝ} {H : ℝ → 𝕄} (h : IsLogarithm W α H) :
    ∀ s ∈ Icc (0 : ℝ) 1, exp (-I • H s) = W s :=
  h.2.1

/-- The logarithm `H(s)` of Theorem 4.7 has spectrum in `(α(s), α(s) + 2π)` for `s ∈ [0,1]`. -/
theorem IsLogarithm.spectrum_subset {W : ℝ → 𝕄} {α : ℝ → ℝ} {H : ℝ → 𝕄}
    (h : IsLogarithm W α H) :
    ∀ s ∈ Icc (0 : ℝ) 1, HasRealSpectrumIn (H s) (Ioo (α s) (α s + 2 * π)) :=
  h.2.2

end RoundedClocks
