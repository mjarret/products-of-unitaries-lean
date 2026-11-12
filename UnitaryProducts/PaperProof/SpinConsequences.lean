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
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A fixed unitary change of basis conjugates a Hamiltonian and its actual
evolution. This identifies the Discussion's spin with the conjugated example. -/
theorem constant_unitary_conjugate_evolution {a b : ℝ} {H U : ℝ → 𝕄}
    (C : 𝕄) (hC : C ∈ unitary 𝕄) (hU : IsEvolution H U a b) :
    IsEvolution (fun t ↦ C * H t * star C) (fun t ↦ C * U t * star C) a b := by
  have hCC := Unitary.mem_iff.mp hC
  refine ⟨(continuousOn_const.mul hU.1).mul continuousOn_const, ?_, ?_, ?_⟩
  · dsimp only
    rw [hU.2.1, mul_one, hCC.2]
  · intro t ht
    have hUt : U t ∈ unitary 𝕄 := Matrix.mem_unitaryGroup_iff'.mpr (hU.2.2.1 t ht)
    exact (Unitary.mem_iff.mp (mul_mem (mul_mem hC hUt) (Unitary.star_mem hC))).1
  · obtain ⟨S, hS, hUd⟩ := hU.2.2.2
    refine ⟨S, hS, fun t ht hnt ↦ ?_⟩
    convert ((hUd t ht hnt).const_mul C).mul_const (star C) using 1
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [← mul_assoc (star C) C, hCC.1, one_mul]


namespace Spin

/-- The actual evolution of the Discussion's conjugated resonant spin has the
conjugated closed form used in its limiting-error calculation. -/
theorem discussion_evolution_closed (θ : ℝ) {T : ℕ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ π • (evol Y (θ * (t / T) / 2) * Z *
      evol Y (-(θ * (t / T) / 2)))) U 0 T) :
    U T = cyclic * (evol Z (θ / 2) *
      evol (((2 * π * T : ℝ) • X) - θ • Z) (1 / 2)) * star cyclic := by
  have hc := Unitary.mem_iff.mp cyclic_unitary
  have hconj := constant_unitary_conjugate_evolution (star cyclic)
    (Unitary.star_mem cyclic_unitary) hU
  have hgen : (fun t ↦ star cyclic * (π • (evol Y (θ * (t / T) / 2) * Z *
      evol Y (-(θ * (t / T) / 2)))) * star (star cyclic)) =
      (fun t ↦ family (2 * π) θ (t / T)) := by
    funext t
    rw [discussion_family, star_star]
    simp only [← mul_assoc, hc.1, one_mul]
    rw [mul_assoc, hc.1, mul_one]
  rw [hgen] at hconj
  have hclosed := evolution_closed (2 * π) θ hT hconj
  have hresult := congrArg (fun A ↦ cyclic * A * star cyclic) hclosed
  simp only [star_star, ← mul_assoc, hc.2, one_mul] at hresult
  simpa only [mul_assoc, hc.2, mul_one] using hresult

/-- The Discussion's limiting error, explicitly stated for actual evolutions
of its Hamiltonian rather than only for the conjugated closed expression. -/
theorem discussion_actual_error_limit (θ : ℝ)
    (U : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ T : ℕ, 0 < T → IsEvolution
      (fun t ↦ π • (evol Y (θ * (t / T) / 2) * Z * evol Y (-(θ * (t / T) / 2))))
      (U T) 0 T) :
    let H := fun s ↦ π • (evol Y (θ * s / 2) * Z * evol Y (-(θ * s / 2)))
    Tendsto (fun T : ℕ ↦ ‖evol (H 1) (1 / 2) * (unitProduct H T).1 *
      evol (H 0) (-(1 / 2)) - U T T‖) atTop (𝓝 (2 * |Real.sin (θ / 4)|)) := by
  intro H
  apply (discussion_error_limit θ).congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [discussion_evolution_closed θ (by omega) (hU T (by omega))]


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

