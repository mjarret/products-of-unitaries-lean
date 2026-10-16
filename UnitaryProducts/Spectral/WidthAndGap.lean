/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.SampledWidth
public import UnitaryProducts.Spectral.BandTransfer

/-!
# The width hypothesis and band eigenphase gaps

## Declarations

- `phase_norm_ge_min`
- `sample_band_gap_width`
- `width_band_gap_incomparable`
-/

@[expose] public section

open Real Set Matrix
noncomputable section
namespace UnitaryProducts.Paper

/-- Supports "a width hypothesis on $H$ that by itself neither implies nor follows from eigenphase
gaps of a band of its sampled exponentials" (§1.2, the fourth difference from prior work).
(i) A zero sample meets the width hypothesis at every width `w ≥ 0`, but no band of its
exponential has a positive eigenphase gap.
(ii) The sample `diag(0,7)` has eigenvalue differences exceeding every width `w < 2π`, but the
band of its exponential at the eigenvalue `0` has a positive eigenphase gap.

Reading the statement against the paper:
* A sample $h$ stands for $(T/N)H(j/N)$. The eigenphases of $e^{-ih}$ are the eigenvalues of
  $h$, and `finiteEigenphaseGap` measures their distance along the circle,
  $\min_k |\theta - \phi + 2\pi k|$, as the `AddCircle (2π)` norm.
* In (i) the gap part is vacuous for $d \le 1$ (there is no proper band); it has content for every
  $d \ge 2$. Stronger than the paper's setting: (i) holds for every $d$, with no $d \ge 1$.
* In (ii), $7 > 2\pi$ gives the width violation, and the band $\{0\}$ has eigenphase gap
  $7 - 2\pi > 0$.

The proof: (i) every eigenvalue of the zero sample is `0`; (ii) the eigenvalues of `diag(0,7)`
are `0` and `7`, $2\pi < 7$, and $0 - 7 \notin 2\pi\mathbb Z$. -/
theorem width_band_gap_incomparable :
    (∀ (d : ℕ) (h : Matrix (Fin d) (Fin d) ℂ) (hh : h.IsHermitian), h = 0 →
      (∀ w : ℝ, 0 ≤ w → ∀ p q, |hh.eigenvalues p - hh.eigenvalues q| ≤ w) ∧
      ∀ (S : Finset (Fin d)) (hS : S.Nonempty) (hR : Sᶜ.Nonempty),
        finiteEigenphaseGap hh.eigenvalues S hS hR = 0) ∧
    (∃ (hh : (diagonal ![(0:ℂ), 7]).IsHermitian),
      (∀ w : ℝ, w < 2*π → ∃ p q, w < |hh.eigenvalues p - hh.eigenvalues q|) ∧
      ∃ (S : Finset (Fin 2)) (hS : S.Nonempty) (hR : Sᶜ.Nonempty),
        0 < finiteEigenphaseGap hh.eigenvalues S hS hR) := by
  refine ⟨fun d h hh h0 ↦ ?_, ?_⟩
  -- (i) Every eigenvalue of the zero sample is `0`: each width bound holds, and every circular
  -- distance between eigenphases is `‖0‖ = 0`.
  · have hz : hh.eigenvalues = 0 := hh.eigenvalues_eq_zero_iff.mpr h0
    exact ⟨fun w hw p q ↦ by simp [hz, hw], fun S hS hR ↦ by simp only [finiteEigenphaseGap, hz,
      Pi.zero_apply, sub_self, AddCircle.coe_zero, norm_zero, Finset.inf'_const]⟩
  -- (ii) The sample `diag(0,7)`.
  · have hsa : IsSelfAdjoint ![(0:ℂ), 7] := by
      -- Finite case analysis over the two entries of `![0, 7]`: both `0` and `7` are real.
      ext i; fin_cases i <;> simp
    let hh := isHermitian_diagonal_of_self_adjoint _ hsa
    -- Its eigenvalues are `0` (at index `p`) and `7` (at index `q`).
    have hmem (r : ℝ) (hr : (r:ℂ) ∈ Set.range ![(0:ℂ), 7]) : ∃ p, hh.eigenvalues p = r := by
      have hc : (algebraMap ℝ ℂ r) ∈ spectrum ℂ (diagonal ![(0:ℂ), 7]) := by
        rw [spectrum_diagonal]; exact hr
      have hR := (spectrum.algebraMap_mem_iff ℂ).mp hc
      rwa [hh.spectrum_real_eq_range_eigenvalues] at hR
    obtain ⟨p, hp⟩ := hmem 0 ⟨0, by simp⟩
    obtain ⟨q, hq⟩ := hmem 7 ⟨1, by simp⟩
    have hpq : p ≠ q := fun h ↦ by rw [h, hq] at hp; norm_num at hp
    -- Width: `7 > 2π`, so the difference `7 - 0` exceeds every width `w < 2π`.
    have h2pi : 2*π < 7 := by linarith [Real.pi_lt_d2]
    refine ⟨hh, fun w hw ↦ ⟨q, p, ?_⟩, {p}, Finset.singleton_nonempty p,
      ⟨q, by simpa [eq_comm] using hpq⟩, ?_⟩
    · rw [hp, hq]; norm_num; linarith
    -- Gap of the band `{p}`: its complement is `{q}`, and `0 - 7 ∉ 2πℤ` because
    -- `2π < 7 < 4π`, so the eigenphase gap is a positive norm on the circle.
    · have hq' : ∀ j ∈ ({p} : Finset (Fin 2))ᶜ, j = q := fun j hj ↦
        (show ∀ j p q : Fin 2, j ≠ p → p ≠ q → j = q by decide) j p q (by simpa using hj) hpq
      have hne : ((hh.eigenvalues p - hh.eigenvalues q : ℝ) : AddCircle (2*π)) ≠ 0 := by
        rw [hp, hq, Ne, AddCircle.coe_eq_zero_iff]
        rintro ⟨n, hn⟩
        have hn' : (n:ℝ)*(2*π) = -7 := by simpa [zsmul_eq_mul] using hn
        rcases le_or_gt n (-2) with h | h
        · have hr : (n:ℝ) ≤ -2 := by exact_mod_cast h
          linarith [Real.pi_gt_three, mul_le_mul_of_nonneg_right hr (by positivity : (0:ℝ) ≤ 2*π)]
        · have hr : (-1:ℝ) ≤ n := by exact_mod_cast h
          linarith [Real.pi_gt_three, mul_le_mul_of_nonneg_right hr (by positivity : (0:ℝ) ≤ 2*π)]
      unfold finiteEigenphaseGap
      rw [Finset.lt_inf'_iff]
      intro i hi
      rw [Finset.mem_singleton] at hi
      subst hi
      rw [Finset.lt_inf'_iff]
      intro j hj
      rw [hq' j hj]
      exact norm_pos_iff.mpr hne


end UnitaryProducts.Paper
