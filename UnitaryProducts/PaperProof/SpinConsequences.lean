/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.PrecessingSpin

/-! # Resonant spin consequences in Section 5 and the Discussion -/
@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Complex Real Filter
open scoped Topology
open UnitaryProducts UnitaryProducts.Paper
noncomputable section
namespace UnitaryProducts.PaperProof


namespace Spin


/-- The continuous endpoint and rounded product become opposite at θ=2π.
The norm of their sum is exactly the residual already shown to vanish. -/
theorem full_turn_antiphase_closed :
    Tendsto (fun T : ℕ ↦
      evol Z ((2 * π) / 2) * evol (((2 * π * T : ℝ) • X) - (2 * π) • Z) (1 / 2) +
      evol (family (2 * π) (2 * π) 1) (1 / 2) *
        (unitProduct (family (2 * π) (2 * π)) T).1 *
        evol (family (2 * π) (2 * π) 0) (-(1 / 2))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply (full_turn_residual_limit (2 * π)).congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [full_turn_product (2 * π) (by omega)]
  have hp : evol Z π = -1 := by
    rw [evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
    simp
  have hp2 : evol Z (2 * π) = 1 := by
    rw [evol_involution pauli_relations.2.2.1 pauli_relations.2.2.2.2.2.1]
    simp
  rw [show 2 * π / 2 = π by ring, hp, hp2, neg_one_mul]
  rw [← norm_neg]
  congr 1
  abel

/-- The final spin paragraph: for actual evolutions at θ=2π, their sums with
the rounded products tend to zero, and their distances tend to two. -/
theorem full_turn_antiphase (U : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ T : ℕ, 0 < T → IsEvolution
      (fun t ↦ family (2 * π) (2 * π) (t / T)) (U T) 0 T) :
    let V := fun T : ℕ ↦ evol (family (2 * π) (2 * π) 1) (1 / 2) *
      (unitProduct (family (2 * π) (2 * π)) T).1 *
      evol (family (2 * π) (2 * π) 0) (-(1 / 2))
    Tendsto (fun T ↦ U T T + V T) atTop (𝓝 0) ∧
      Tendsto (fun T ↦ ‖V T - U T T‖) atTop (𝓝 (2 : ℝ)) := by
  intro V
  constructor
  · apply full_turn_antiphase_closed.congr'
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [evolution_closed (2 * π) (2 * π) (by omega) (hU T (by omega))]
  · have hlim := full_turn_error_limit (2 * π)
    have hangle : 2 * π / 4 = π / 2 := by ring
    rw [hangle, Real.sin_pi_div_two, abs_one, mul_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [evolution_closed (2 * π) (2 * π) (by omega) (hU T (by omega))]


/-- The resonant example really satisfies a spectral-width bound of 2π at
every parameter, so its nonvanishing error tests the proposed closed boundary. -/
theorem full_turn_width (θ s : ℝ) (i j : Fin 2) :
    |(family_hermitian (2 * π) θ s).eigenvalues i -
      (family_hermitian (2 * π) θ s).eigenvalues j| ≤ 2 * π := by
  have haxis : ‖axis (θ * s)‖ = 1 := by
    have hh := congrArg norm (axis_relations (θ * s)).2
    rw [(axis_relations (θ * s)).1.isSelfAdjoint.norm_mul_self, norm_one] at hh
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hh)
  have hnorm : ‖family (2 * π) θ s‖ = π := by
    rw [family, norm_smul, haxis, mul_one, Real.norm_eq_abs]
    rw [show 2 * π / 2 = π by ring, abs_of_pos pi_pos]
  have hbound (k : Fin 2) : |(family_hermitian (2 * π) θ s).eigenvalues k| ≤ π := by
    have h := spectrum.norm_le_norm_of_mem
      ((family_hermitian (2 * π) θ s).eigenvalues_mem_spectrum_real k)
    simpa only [Real.norm_eq_abs, hnorm] using h
  exact (abs_sub _ _).trans (by linarith [hbound i, hbound j])

/-- The resonant width 2π cannot support a comparison bound decaying to zero. -/
theorem full_turn_not_tendsto_zero (U : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ T : ℕ, 0 < T → IsEvolution
      (fun t ↦ family (2 * π) (2 * π) (t / T)) (U T) 0 T) :
    ¬ Tendsto (fun T : ℕ ↦
      ‖evol (family (2 * π) (2 * π) 1) (1 / 2) *
        (unitProduct (family (2 * π) (2 * π)) T).1 *
        evol (family (2 * π) (2 * π) 0) (-(1 / 2)) - U T T‖) atTop (𝓝 0) := by
  intro hz
  have h := tendsto_nhds_unique (full_turn_antiphase U hU).2 hz
  norm_num at h

end Spin
end UnitaryProducts.PaperProof

