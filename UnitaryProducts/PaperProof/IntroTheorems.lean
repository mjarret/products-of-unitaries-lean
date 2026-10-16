/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.PaperProof.WalkCoefficients

/-!
# The introductory comparisons

## Declarations

- `introthm_unit`
- `introthm_unit_constants`
- `introthm_unit_step_length`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Set MeasureTheory Real
open UnitaryProducts.Paper UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Theorem B's numerical bounds for its exact, dimension-independent constants. -/
theorem introthm_unit_constants :
    1 / π - 1 / π ^ 2 + 1 / 24 ≤ (26 / 100 : ℝ) ∧
    5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 ≤ (61 / 1000 : ℝ) :=
  intro_constants

/-- **Theorem B** (`introthm:unit`): the unit-step comparison for every integer
`T ≥ 2`, with absolute constants `a ≤ 0.26` and `b ≤ 0.061`. The constants are explicit, and
dimension zero is allowed. -/
theorem introthm_unit :
    ∃ a b : ℝ,
      a = 1 / π - 1 / π ^ 2 + 1 / 24 ∧
      b = 5 / (8 * π) - 1 / (4 * π ^ 2) - 4 / π ^ 3 + 1 / 64 ∧
      (∀ {d : ℕ}
    (H U : ℝ → Matrix (Fin d) (Fin d) ℂ) (T : ℕ) (_ : 2 ≤ T)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (h : ℝ) (_ : ∀ s ∈ Icc (0 : ℝ) 1, ‖derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h)
      (_ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h * |t - s|)
      (_ : ∀ j : ℕ, ∀ hjT : j ≤ T, ∀ p q,
        |(hH _ (walkCubic_sample hjT)).eigenvalues p -
          (hH _ (walkCubic_sample hjT)).eigenvalues q| ≤ π)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
        let W := (unitProduct H T).1
        ‖UnitaryProducts.evol (H 1) (1 / 2) * W *
          UnitaryProducts.evol (H 0) (-(1 / 2)) - U T‖ ≤
          (a * h + b * h ^ 2) / T) ∧
      a ≤ 26 / 100 ∧ b ≤ 61 / 1000 := by
  refine ⟨_, _, rfl, rfl, ?_, introthm_unit_constants⟩
  intro d H U T hT hH hc h hbd hlip hdiff hU
  -- In dimension zero every matrix vanishes; handle this before choosing an eigenvalue.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    have hh : 0 ≤ h := by simpa [hz] using hbd 0 (by norm_num)
    simp only [hz, norm_zero]
    rw [← uniform_pi_coefficients.1, ← uniform_pi_coefficients.2]
    have hc₀ := UnitStepsProse.center_bound_nonneg pi_pos.le (by linarith [pi_pos])
    have hf := frameBound_nonneg pi_pos.le
    have hη : 0 ≤ (2 : ℝ) * frameLip π :=
      mul_nonneg (by norm_num) (frameLip_nonneg pi_pos.le)
    dsimp [uniform_linear_coefficient, uniform_quadratic_coefficient, uniform_c0, uniform_c1]
    positivity
  letI : NeZero d := ⟨hd.ne'⟩
  -- Apply the product comparison with identity truncation and the supplied bounds.
  have hb := thm_unit_steps_bounds H U T (by omega) hH
    (hc.differentiableOn (by norm_num)) h π hlip
    (by linarith [pi_pos]) hdiff hU id (fun _ ↦ rfl)
  dsimp only at hb
  obtain ⟨he, _⟩ := uniform_identity_entry_error H T
  simp only [he, sub_self, norm_zero, Finset.sum_const_zero, zero_add] at hb
  rw [(paper_series_eq pi_pos.le (by linarith [pi_pos])).1,
    (paper_series_eq (by positivity : 0 ≤ π / 2) (by linarith [pi_pos])).1] at hb
  have hends := add_le_add (hbd 0 (by norm_num)) (hbd 1 (by norm_num))
  have hc₀ := UnitStepsProse.center_bound_nonneg pi_pos.le (by linarith [pi_pos])
  have hlinear := mul_le_mul_of_nonneg_left hends hc₀
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hsup : unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) ≤ h :=
    csSup_le ((nonempty_Icc.mpr zero_le_one).image _) (forall_mem_image.mpr hbd)
  have hsup0 : 0 ≤ unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) :=
    (norm_nonneg (derivWithin H (Icc (0 : ℝ) 1) 0)).trans
      (norm_le_unitSupNorm (continuousOn_of_norm_sub_le hlip) (by norm_num))
  have hη : 0 ≤ (2 : ℝ) * frameLip π :=
      mul_nonneg (by norm_num) (frameLip_nonneg pi_pos.le)
  have hcoarse := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hlinear
      (le_refl ((1 / 24 + frameBound π) * h)))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsup0 hsup 2)
        (by positivity : 0 ≤ (frameBound π - frameBound (π / 2) / 2) / 4 + 1 / 64 +
          (2 * frameLip π)))) (le_of_lt (one_div_pos.mpr ht))
  have hb' := hb.trans hcoarse
  -- Collect 2c₀ + 1/24 + N(π) = a and c₁ + 2N′(π) = b.
  apply hb'.trans_eq
  rw [← uniform_pi_coefficients.1, ← uniform_pi_coefficients.2]
  dsimp [uniform_linear_coefficient, uniform_quadratic_coefficient, uniform_c0, uniform_c1]
  ring

end UnitaryProducts.PaperProof
