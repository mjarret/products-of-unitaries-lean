/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.ProjectionGeometry
public import UnitaryProducts.Spectral.Weyl

/-!
# Endpoint spectral windows under perturbation

## Declarations

- `endpointComplement`
- `endpointComplement_nonempty`
- `endpointSeparation`
- `endpoint_complement_separation`
- `endpoint_projector_bound`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator
open Finset
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The indices $i$ with $|\lambda_i(D)-m|>r+\gamma/2$: eigenvalues of $D$ outside the enlarged
window. (`Classical.decPred` only supplies decidability of the filter.) -/
noncomputable def endpointComplement {D : 𝕄} (hD : D.IsHermitian) (m r γ : ℝ) : Finset (Fin d) :=
  @Finset.filter _ (fun i ↦ r + γ/2 < |hD.eigenvalues i-m|) (Classical.decPred _) univ

/-- The minimum separation $\delta=\min(|\lambda_i(D)-m|-r)$ of the eigenvalues of $D$ outside the
enlarged window from the window of radius $r$. It takes a proof that this set of indices is
nonempty, so it has no junk value. -/
noncomputable def endpointSeparation {D : 𝕄} (hD : D.IsHermitian) (m r γ : ℝ)
    (hne : (endpointComplement hD m r γ).Nonempty) : ℝ :=
  (endpointComplement hD m r γ).inf' hne (fun i ↦ |hD.eigenvalues i-m|-r)

/-- Weyl gives the relative separation from the original interval to the continued complement. -/
theorem endpoint_complement_separation {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {m r γ : ℝ}
    (hg : HasGap hA m r γ) (hsmall : ‖A - D‖ < γ / 2)
    (i : Fin d) (hi : i ∈ endpointComplement hD m r γ) :
    r + (γ - ‖A-D‖) ≤ |hD.eigenvalues i-m| := by
  have hout : r+γ/2 < |hD.eigenvalues i-m| := (Finset.mem_filter.mp hi).2
  rcases hasGap_of_norm_sub_le hA hD hg (le_refl ‖A-D‖) i with hin | hex <;> linarith

/-- A proper continuous band has a nonempty continued complement under the half-gap condition. -/
theorem endpointComplement_nonempty {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {m r γ : ℝ}
    (hg : HasGap hA m r γ) (hsmall : ‖A - D‖ < γ / 2)
    (hproper : ∃ i, r < |hA.eigenvalues i - m|) :
    (endpointComplement hD m r γ).Nonempty := by
  obtain ⟨i, hi⟩ := hproper
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have ha : r+γ ≤ |hA.eigenvalues i-m| := (hg i).resolve_left (not_le_of_gt hi)
  have hw : |hA.eigenvalues i-m|-|hD.eigenvalues i-m| ≤ ‖A-D‖ := (abs_sub_abs_le_abs_sub _ _).trans
    (by rw [sub_sub_sub_cancel_right]; exact abs_eigenvalues_sub_le hA hD i)
  linarith

/-- Actual separation, relative Weyl comparison, and the factor-one projector estimate. -/
theorem endpoint_projector_bound {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {m r γ : ℝ}
    (hr : 0 ≤ r) (hg : HasGap hA m r γ)
    (hsmall : ‖A - D‖ < γ / 2) (hne : (endpointComplement hD m r γ).Nonempty) :
    let δ := endpointSeparation hD m r γ hne
    (1-‖A-D‖/γ)*γ ≤ δ ∧ γ/2 < δ ∧
      ‖windowProj m r A-windowProj m (r+γ/2) D‖ ≤ ‖A-D‖/δ := by
  have hγ : 0 < γ := by linarith [norm_nonneg (A - D)]
  dsimp only
  let δ := endpointSeparation hD m r γ hne
  have hrel : γ-‖A-D‖ ≤ δ := Finset.le_inf' hne _ fun i hi ↦ by
    linarith [endpoint_complement_separation hA hD hg hsmall i hi]
  have hδ : 0 < δ := (half_pos hγ).trans (by linarith)
  have hclose : ‖windowProj m r A-windowProj m (r+γ/2) D‖ < 1 := by
    simp only [windowProj, dif_pos hA, dif_pos hD]
    exact (norm_specProj_sub_le_widened hA hD hr hγ hg).trans_lt ((div_lt_iff₀ hγ).mpr (by
      linarith))
  have hdir : ‖(1-windowProj m (r+γ/2) D)*windowProj m r A‖ ≤ ‖A-D‖/δ := by
    simp only [windowProj, dif_pos hA, dif_pos hD]
    refine (norm_one_sub_specProj_mul_specProj_le hA hD hr hδ
      (fun i hi ↦ hi) (fun i hi ↦ ?_)).trans
      (div_le_div_of_nonneg_right (norm_leak_le_norm
        (isStarProjection_specProj hA _) (isStarProjection_specProj hD _) _) hδ.le)
    have hi' : i ∈ endpointComplement hD m r γ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hi⟩
    have hb : δ ≤ |hD.eigenvalues i-m|-r := Finset.inf'_le (fun j ↦ |hD.eigenvalues j-m|-r) hi'
    linarith
  refine ⟨?_, by linarith, ?_⟩
  · convert hrel using 1; field_simp
  · exact (norm_sub_le_directed_of_lt_one
      (by unfold windowProj; rw [dif_pos hA]; exact isStarProjection_specProj hA _)
      (by unfold windowProj; rw [dif_pos hD]; exact isStarProjection_specProj hD _) hclose).trans
        hdir

end UnitaryProducts
