/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.CenteredUnitSteps
public import UnitaryProducts.Prose.SyncSteps
public import UnitaryProducts.Prose.LocalSteps
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.Prose.SharpnessExpansion
public import UnitaryProducts.PaperProof.UniformTruncation

/-!
# UnitExamples

## Declarations

- `ex_unit_sharp`
-/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Real Set Matrix Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

/-- The shared phase computation in Example 4.3, for any real endpoint
phase `b`. The paper uses `b = 0` and `b = 1/2`. -/
theorem sharp_phase_error {T : ℕ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T) (b : ℝ) :
    let Z := Matrix.diagonal ![(1 : ℂ), -1]
    ‖evol Z b * (unitProduct sharpFamily T).1 - U T‖ =
      ‖evol Z (b - 1 / 2 + 1 / (6 * T)) - 1‖ ∧
    ‖evol Z (b - 1 / 2 + 1 / (6 * T)) - 1‖ =
      2 * |Real.sin ((b - 1 / 2 + 1 / (6 * T)) / 2)| := by
  intro Z
  have hscale (x : ℝ) : x • Z = Matrix.diagonal ![(x : ℂ), -(x : ℂ)] := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    fin_cases i <;> simp [Complex.real_smul]
  have hdiag (x : ℝ) : evol Z x =
      evol (Matrix.diagonal ![(x : ℂ), -(x : ℂ)]) 1 := by
    rw [← hscale x, Prose.localSteps_evol_smul_sharp, one_mul]
  have hdist (x y : ℝ) : ‖evol Z x - evol Z y‖ =
      2 * |Real.sin ((x - y) / 2)| := by
    rw [hdiag x, hdiag y, entry_rounding_obstruction, one_mul]
  have heval : ‖evol Z (b - 1 / 2 + 1 / (6 * T)) - 1‖ =
      2 * |Real.sin ((b - 1 / 2 + 1 / (6 * T)) / 2)| := by
    rw [← evol_zero Z, hdist, sub_zero]
  refine ⟨?_, heval⟩
  rw [Prose.sharp_unit_step_expanded hT hU,
    Prose.sharp_evolution_endpoint_via_integral (Nat.cast_pos.mpr hT) hU,
    ← evol_add, hdist, heval]
  congr 3
  ring

/-- Computation behind Example 4.3 (`ex:unit-sharp`): the quadratic diagonal
Hamiltonian has the stated hypotheses, exponential phases, and exact errors. -/
theorem sharp_example_computation (T : ℕ) (hT : 1 ≤ T) :
    let H := sharpFamily
    let Z := Matrix.diagonal ![(1 : ℂ), -1]
    (∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) ∧
    ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1) ∧
    unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) = 2 ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤
        2 * |t - s|) ∧
    (∀ j : ℕ, j ≤ T → ∀ hj : (H (j / T)).IsHermitian, ∀ p q,
      |hj.eigenvalues p - hj.eigenvalues q| ≤ 2) ∧
    (∃ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ, IsEvolution (fun t ↦ H (t / T)) U 0 T) ∧
    (∀ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      IsEvolution (fun t ↦ H (t / T)) U 0 T →
      U T = evol Z ((T : ℝ) / 3) ∧
      (unitProduct H T).1 = evol Z (∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2) ∧
      (unitProduct H T).1 = evol Z (((T : ℝ) - 1) * (2 * T - 1) / (6 * T)) ∧
      evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) =
        evol Z ((T : ℝ) / 3 + 1 / (6 * T)) ∧
      ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ =
        2 * Real.sin (1 / (12 * T)) ∧
      ‖(unitProduct H T).1 - U T‖ = 2 * Real.sin (1 / 4 - 1 / (12 * T))) := by
  intro H Z
  have ht : 0 < T := by omega
  have htr : 0 < (T : ℝ) := Nat.cast_pos.mpr ht
  obtain ⟨hh, hc, hl, _hb, hw, hu⟩ := sharpFamily_hypotheses (N := T) htr
  refine ⟨hh, hc, sharpFamily_derivative_supNorm, hl, ?_, hu, ?_⟩
  · simpa only [div_self htr.ne', one_mul, mul_div_cancel_right₀ _ htr.ne'] using hw
  · intro U hU
    obtain ⟨hs, _, _⟩ := Prose.sharp_unit_step_exponentials ht hU
    have hUend := Prose.sharp_evolution_endpoint_via_integral htr hU
    have hp : (unitProduct H T).1 =
        evol Z (((T : ℝ) - 1) * (2 * T - 1) / (6 * T)) := by
      rw [hs]
      congr 1
      simp_rw [div_pow]
      rw [← Finset.sum_div, Prose.sum_sample_squares]
      field_simp [htr.ne']
    have he : evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) =
        evol Z ((T : ℝ) / 3 + 1 / (6 * T)) := by
      change evol (sharpFamily 1) (1 / 2) * (unitProduct sharpFamily T).1 *
        evol (sharpFamily 0) (-(1 / 2)) = _
      rw [Prose.quadratic_endpoints.1, Prose.quadratic_endpoints.2,
        Prose.sharp_unit_step_expanded ht hU]
      have hzero : evol (0 : Matrix (Fin 2) (Fin 2) ℂ) (-(1 / 2)) = 1 := by simp [evol]
      rw [hzero, mul_one, ← evol_add]
      congr 1
      ring
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast ht
    have hx0 : 0 < 1 / (12 * (T : ℝ)) := by positivity
    have hx1 : 1 / (12 * (T : ℝ)) ≤ 1 / 12 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    -- The paper's one computation specializes to the two endpoint phases.
    have hf : ‖evol (H 1) (1 / 2) * (unitProduct H T).1 *
        evol (H 0) (-(1 / 2)) - U T‖ = 2 * Real.sin (1 / (12 * T)) := by
      dsimp only [H]
      rw [Prose.quadratic_endpoints.1, Prose.quadratic_endpoints.2]
      have hz : evol (0 : Matrix (Fin 2) (Fin 2) ℂ) (-(1 / 2)) = 1 := by simp [evol]
      rw [hz, mul_one]
      rw [(sharp_phase_error ht hU (1 / 2)).1, (sharp_phase_error ht hU (1 / 2)).2]
      rw [show ((1 / 2 : ℝ) - 1 / 2 + 1 / (6 * T)) / 2 =
          1 / (12 * T) by ring]
      rw [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hx0
        (by linarith [Real.pi_gt_three]))]
    have hn : ‖(unitProduct H T).1 - U T‖ =
        2 * Real.sin (1 / 4 - 1 / (12 * T)) := by
      have h := (sharp_phase_error ht hU 0).1.trans (sharp_phase_error ht hU 0).2
      simp only [evol_zero, one_mul] at h
      rw [h]
      rw [show ((0 : ℝ) - 1 / 2 + 1 / (6 * T)) / 2 =
          -(1 / 4 - 1 / (12 * T)) by ring, Real.sin_neg, abs_neg]
      rw [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi
        (by linarith : 0 < 1 / 4 - 1 / (12 * (T : ℝ)))
        (by linarith [Real.pi_gt_three]))]
    exact ⟨hUend, hs, hp, he, hf, hn⟩


/-- The first sharpness error is asymptotic to `1/(6T)`: divide by that
quantity and use continuity of the standard sinc function at zero. -/
theorem sharp_corrected_error_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun T : ℕ ↦ 2 * Real.sin (1 / (12 * (T : ℝ))))
      (fun T : ℕ ↦ 1 / (6 * (T : ℝ))) := by
  have hinv : Tendsto (fun T : ℕ ↦ 1 / (12 * (T : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)
  have hsinc : Tendsto (fun T : ℕ ↦ Real.sinc (1 / (12 * (T : ℝ))))
      atTop (𝓝 1) := by
    simpa only [Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hinv
  have hpos : ∀ᶠ T : ℕ in atTop, 0 < (T : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact_mod_cast hT
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · exact hsinc.congr' (by
      filter_upwards [hpos] with T hT
      rw [Real.sinc_of_ne_zero (by positivity)]
      dsimp
      field_simp
      ring)
  · filter_upwards [hpos] with T hT
    positivity

/-- The uncorrected error in Example 4.3 has the stated nonzero limit. -/
theorem sharp_uncorrected_error_limit :
    Tendsto (fun T : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * (T : ℝ))))
      atTop (𝓝 (2 * Real.sin (1 / 4))) := by
  have hinv : Tendsto (fun T : ℕ ↦ 1 / (12 * (T : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)
  have harg : Tendsto (fun T : ℕ ↦ 1 / 4 - 1 / (12 * (T : ℝ)))
      atTop (𝓝 (1 / 4)) := by
    simpa using tendsto_const_nhds.sub hinv
  exact ((Real.continuous_sin.tendsto _).comp harg).const_mul 2

/-- **Example 4.3** (`ex:unit-sharp`): the quadratic diagonal Hamiltonian
satisfies the unit-step hypotheses with `h = w = 2`. The two errors are the
paper's displayed sine expressions, with their asymptotic equivalent and limit.
The rounded evolution is constructed with its half-step endpoint identity. The conclusion also
supplies the existence of both evolutions. -/
theorem ex_unit_sharp (T : ℕ) (hT : 2 ≤ T) :
    let H := sharpFamily
    (∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) ∧
    ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤
        2 * |t - s|) ∧
    (∀ j : ℕ, j ≤ T → ∀ hj : (H (j / T)).IsHermitian, ∀ p q,
      |hj.eigenvalues p - hj.eigenvalues q| ≤ 2) ∧
    (∃ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ, IsEvolution (fun t ↦ H (t / T)) U 0 T) ∧
    (∀ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      IsEvolution (fun t ↦ H (t / T)) U 0 T →
      ∃ V : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      IsEvolution (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) V 0 T ∧
      V T = evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) ∧
      ‖V T - U T‖ = 2 * Real.sin (1 / (12 * T)) ∧
      ‖(unitProduct H T).1 - U T‖ = 2 * Real.sin (1 / 4 - 1 / (12 * T))) ∧
    Asymptotics.IsEquivalent atTop
      (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * (N : ℝ))))
      (fun N : ℕ ↦ 1 / (6 * (N : ℝ))) ∧
    Tendsto (fun N : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * (N : ℝ))))
      atTop (𝓝 (2 * Real.sin (1 / 4))) := by
  intro H
  obtain ⟨hh, hc, hd, hl, hw, hex, herr⟩ := sharp_example_computation T (by omega)
  refine ⟨hh, hc, hl, hw, hex, ?_, sharp_corrected_error_asymptotic,
    sharp_uncorrected_error_limit⟩
  · intro U hU
    have ht : 0 < T := by omega
    have htr : 0 < (T : ℝ) := Nat.cast_pos.mpr ht
    obtain ⟨V, hV, heV⟩ := exists_rounded_evolution htr ht H hh
    have hclock (t : ℝ) : UnitStepsProse.sample T (t / T) = (⌊t + 1 / 2⌋ : ℝ) / T := by
      simp only [UnitStepsProse.sample, UnitStepsProse.clock, mul_div_cancel₀ t htr.ne']
    have hrounded : IsEvolution (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) V 0 T := by
      simpa only [hclock] using hV
    have hend : V T = evol (H 1) (1 / 2) * (unitProduct H T).1 *
        evol (H 0) (-(1 / 2)) := by
      simpa only [div_self htr.ne', one_smul,
        show (T : ℝ) / (2 * T) = 1 / 2 by field_simp] using heV
    refine ⟨V, hrounded, hend, ?_, (herr U hU).2.2.2.2.2⟩
    rw [hend]
    exact (herr U hU).2.2.2.2.1

end UnitaryProducts.PaperProof
