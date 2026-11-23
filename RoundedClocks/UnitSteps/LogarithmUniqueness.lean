/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.ExponentialCoordinates
public import RoundedClocks.UnitSteps.ExponentialSpectrum

/-! # Uniqueness of the Hermitian logarithm

Corollary 4.7 shows that two Hermitian logarithms with spectra in the same open turn agree whenever
their unitary exponentials agree.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace RoundedClocks.WalkLeakageUnique

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝔼" => EuclideanSpace ℂ (Fin d)
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

/-- The open-turn uniqueness step implicit in the first sentence of Theorem 4.7's proof. -/
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
      (hB.eigenvalues j : ℂ) • hB.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, hB.mulVec_eigenvectorBasis j,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
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
      WalkLeakageSpectrum.phase_inj
        (hAspec (hA.eigenvalues_mem_spectrum_real i))
        (hBspec (hB.eigenvalues_mem_spectrum_real j)) (mul_right_cancel₀ hc he)
    rw [hev]

/-- Two open-turn Hermitian logarithms agree on their defining time interval. -/
theorem logarithms_eqOn {W : ℝ → 𝕄} {α : ℝ → ℝ} {H K : ℝ → 𝕄}
    (hH : IsLogarithm W α H) (hK : IsLogarithm W α K) :
    Set.EqOn H K (Set.Icc 0 1) := by
  intro s hs
  exact logarithm_unique (hH.1 s hs) (hK.1 s hs)
    (hH.2.2 s hs) (hK.2.2 s hs) ((hH.2.1 s hs).trans (hK.2.1 s hs).symm)

end RoundedClocks.WalkLeakageUnique
