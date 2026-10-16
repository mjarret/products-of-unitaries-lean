/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.EndpointGap

/-!
# Exact band gaps and Weyl's index preservation

## Declarations

- `finiteSpectralDistance`
- `finiteSpectralDistance_eq_margin`
- `finite_distance_to_tight_hull`
- `hasGap_of_exact_distance`
- `same_band_indices_of_small_perturbation`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator
open Finset
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Distance between two nonempty finite spectra, retaining multiplicity indices:
$\min_{i \in S,\, j \in R} |\lambda_i - \lambda'_j|$. With `ev = ev'` and `R = Sᶜ` it is the
spectral gap $\Gamma$ of the band `S` (`bandGap`, `exactGap`). The nonemptiness of `S` and `R`
are arguments, so there is no junk value. -/
noncomputable def finiteSpectralDistance (ev ev' : Fin d → ℝ)
    (S R : Finset (Fin d)) (hS : S.Nonempty) (hR : R.Nonempty) : ℝ :=
  S.inf' hS (fun i ↦ R.inf' hR (fun j ↦ |ev i-ev' j|))

/-- Distance from a finite band with attained extreme eigenvalues to an exterior point. -/
theorem finite_distance_to_tight_hull (ev : Fin d → ℝ)
    (S : Finset (Fin d)) (hS : S.Nonempty) {m r z : ℝ}
    (hin : ∀ i ∈ S, |ev i - m| ≤ r)
    (hleft : ∃ i ∈ S, ev i = m - r) (hright : ∃ i ∈ S, ev i = m + r)
    (hout : r ≤ |z - m|) :
    S.inf' hS (fun i ↦ |ev i-z|) = |z-m|-r := by
  apply le_antisymm
  · rcases le_total z m with hz | hz
    · obtain ⟨i, hi, he⟩ := hleft
      refine (Finset.inf'_le (fun i ↦ |ev i-z|) hi).trans_eq ?_
      rw [abs_of_nonpos (sub_nonpos.mpr hz)] at hout ⊢
      rw [he, abs_of_nonneg (by linarith)]; ring
    · obtain ⟨i, hi, he⟩ := hright
      refine (Finset.inf'_le (fun i ↦ |ev i-z|) hi).trans_eq ?_
      rw [abs_of_nonneg (sub_nonneg.mpr hz)] at hout ⊢
      rw [he, abs_of_nonpos (by linarith)]; ring
  · exact Finset.le_inf' hS _ fun i hi ↦ by
      linarith [abs_sub_le z (ev i) m, abs_sub_comm z (ev i), hin i hi]

/-- Finite set distance is exactly the margin from a tight hull when the other spectrum is exterior.
-/
theorem finiteSpectralDistance_eq_margin (ev ev' : Fin d → ℝ)
    (S R : Finset (Fin d)) (hS : S.Nonempty) (hR : R.Nonempty) {m r : ℝ}
    (hin : ∀ i ∈ S, |ev i - m| ≤ r)
    (hleft : ∃ i ∈ S, ev i = m - r) (hright : ∃ i ∈ S, ev i = m + r)
    (hout : ∀ j ∈ R, r ≤ |ev' j - m|) :
    finiteSpectralDistance ev ev' S R hS hR = R.inf' hR (fun j ↦ |ev' j-m|-r) := by
  unfold finiteSpectralDistance
  rw [Finset.inf'_comm]
  apply Finset.inf'_congr hR rfl
  intro j hj
  exact finite_distance_to_tight_hull ev S hS hin hleft hright (hout j hj)

/-- The exact gap of the band selected by a tight interval implies the interval collar predicate:
the eigenvalues outside the band lie at distance at least $\Gamma$ from its convex hull
$[m - r, m + r]$ (proof of the unnumbered endpoint-transfer estimate). -/
theorem hasGap_of_exact_distance {A : 𝕄} (hA : A.IsHermitian) {m r : ℝ}
    (S : Finset (Fin d)) (hS : S.Nonempty) (hR : Sᶜ.Nonempty)
    (hmem : ∀ i, i ∈ S ↔ |hA.eigenvalues i - m| ≤ r)
    (hleft : ∃ i ∈ S, hA.eigenvalues i = m - r)
    (hright : ∃ i ∈ S, hA.eigenvalues i = m + r) :
    HasGap hA m r (finiteSpectralDistance hA.eigenvalues hA.eigenvalues S Sᶜ hS hR) := by
  have heq := finiteSpectralDistance_eq_margin hA.eigenvalues hA.eigenvalues S Sᶜ hS hR
    (fun i hi ↦ (hmem i).mp hi) hleft hright (fun j hj ↦
      (lt_of_not_ge (fun h ↦ (Finset.mem_compl.mp hj) ((hmem j).mpr h))).le)
  intro i
  by_cases hi : i ∈ S
  · exact Or.inl ((hmem i).mp hi)
  · right
    have hb := Finset.inf'_le (fun j ↦ |hA.eigenvalues j-m|-r) (Finset.mem_compl.mpr hi)
    rw [heq]
    linarith

/-- Weyl preserves each selected ordered index, not just the number of selected eigenvalues: if
$A$ has a collar of width $\gamma$ around $[m - r, m + r]$ and $\|A - D\| < \gamma/2$, then
$\lambda_i(A)$ lies in the window iff $\lambda_i(D)$ lies in the window widened by $\gamma/2$.
In the unnumbered endpoint-transfer estimate, this makes $P_J(D_t)$ the projector onto the indices
of the band (Weyl). -/
theorem same_band_indices_of_small_perturbation {A D : 𝕄}
    (hA : A.IsHermitian) (hD : D.IsHermitian) {m r γ : ℝ}
    (hg : HasGap hA m r γ) (hsmall : ‖A - D‖ < γ / 2) (i : Fin d) :
    |hA.eigenvalues i-m| ≤ r ↔ |hD.eigenvalues i-m| ≤ r+γ/2 := by
  have key : |(|hA.eigenvalues i-m|)-(|hD.eigenvalues i-m|)| ≤ ‖A-D‖ :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans
      (by rw [sub_sub_sub_cancel_right]; exact abs_eigenvalues_sub_le hA hD i)
  rw [abs_le] at key
  -- The second case of `hg i` is vacuous (not inconsistent: the hypotheses hold with `A = D`): an
  -- eigenvalue of `A` beyond the collar would, by Weyl, put `λ_i(D)` beyond `r + γ/2`.
  exact ⟨fun hi ↦ by linarith [key.1], fun hi ↦ (hg i).resolve_right fun h ↦ by linarith [key.2]⟩

end UnitaryProducts
