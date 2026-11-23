/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.WalkLeakage.Band
public import RoundedClocks.UnitSteps.WalkLeakage.ExponentialCoordinates
public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-! # Uniqueness of the logarithm with spectrum in `(α, α + 2π)`

Theorem 4.7 takes "the Hermitian `H(s)` with `e^{-iH(s)} = W(s)` and spectrum in
`(α(s), α(s) + 2π)`". Hermitian `A` and `B` with spectra in `(α, α + 2π)` and
`e^{-iA} = e^{-iB}` are equal (`logarithm_unique`), as `θ ↦ e^{-iθ}` is injective for
`θ ∈ (α, α + 2π)`. The proof of Theorem 4.7 uses this to identify the `H` of the statement with
`α + π + i Log(e^{i(α+π)} W)`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace RoundedClocks.WalkLeakage

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝔼" => EuclideanSpace ℂ (Fin d)
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- Hermitian `A` and `B` with spectra in `(α, α + 2π)` and `e^{-iA} = e^{-iB}` are equal: in
eigenbases `ψ_i` of `A` and `φ_j` of `B`, `e^{-iλ_i} ψ_i† φ_j = e^{-iμ_j} ψ_i† φ_j`, so
`λ_i = μ_j` wherever `ψ_i† φ_j ≠ 0`. -/
theorem logarithm_unique {A B : 𝕄} {α : ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAspec : HasRealSpectrumIn A (Set.Ioo α (α + 2 * Real.pi)))
    (hBspec : HasRealSpectrumIn B (Set.Ioo α (α + 2 * Real.pi)))
    (hexp : NormedSpace.exp (-Complex.I • A) = NormedSpace.exp (-Complex.I • B)) :
    A = B := by
  classical
  have hphase (j : Fin d) :
      𝒯 (NormedSpace.exp (-Complex.I • B)) (hB.eigenvectorBasis j) =
        Complex.exp (-Complex.I * (hB.eigenvalues j : ℂ)) • hB.eigenvectorBasis j := by
    apply walk_ext_basis hB.eigenvectorBasis
    intro k
    rw [walk_inner_phase_eigenvectorBasis hB, inner_smul_right]
    simp only [orthonormal_iff_ite.mp hB.eigenvectorBasis.orthonormal]
    by_cases hkj : k = j <;> simp [hkj]
  have hvec (j : Fin d) : 𝒯 B (hB.eigenvectorBasis j) =
      (hB.eigenvalues j : ℂ) • hB.eigenvectorBasis j :=
    toEuclideanCLM_eigenvectorBasis hB j
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).injective
  apply ContinuousLinearMap.coe_injective
  apply hB.eigenvectorBasis.toBasis.ext
  intro j
  change 𝒯 A (hB.eigenvectorBasis j) = 𝒯 B (hB.eigenvectorBasis j)
  apply walk_ext_basis hA.eigenvectorBasis
  intro i
  rw [walk_inner_eigenvectorBasis hA, hvec, inner_smul_right]
  let c : ℂ := ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_ℂ
  change (hA.eigenvalues i : ℂ) * c = (hB.eigenvalues j : ℂ) * c
  by_cases hc : c = 0
  · rw [hc, mul_zero, mul_zero]
  · have he : Complex.exp (-Complex.I * (hA.eigenvalues i : ℂ)) * c =
        Complex.exp (-Complex.I * (hB.eigenvalues j : ℂ)) * c := by
      calc
        _ = ⟪hA.eigenvectorBasis i,
            𝒯 (NormedSpace.exp (-Complex.I • A)) (hB.eigenvectorBasis j)⟫_ℂ :=
          (walk_inner_phase_eigenvectorBasis hA i (hB.eigenvectorBasis j)).symm
        _ = _ := by rw [hexp, hphase, inner_smul_right]
    have hev : hA.eigenvalues i = hB.eigenvalues j :=
      phase_inj
        (hAspec (hA.eigenvalues_mem_spectrum_real i))
        (hBspec (hB.eigenvalues_mem_spectrum_real j)) (mul_right_cancel₀ hc he)
    rw [hev]

/-- Two logarithms of `W` with spectra in `(α(s), α(s) + 2π)` agree for `s ∈ [0,1]`. -/
theorem logarithms_eqOn {W : ℝ → 𝕄} {α : ℝ → ℝ} {H K : ℝ → 𝕄}
    (hH : IsLogarithm W α H) (hK : IsLogarithm W α K) :
    Set.EqOn H K (Set.Icc 0 1) := by
  intro s hs
  exact logarithm_unique (hH.isHermitian hs) (hK.isHermitian hs)
    (hH.spectrum_subset s hs) (hK.spectrum_subset s hs)
    ((hH.exp_eq s hs).trans (hK.exp_eq s hs).symm)

end RoundedClocks.WalkLeakage
