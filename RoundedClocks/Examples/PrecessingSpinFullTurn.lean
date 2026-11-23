/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinPowers
public import RoundedClocks.Examples.PrecessingSpinRounded
public import RoundedClocks.Examples.PrecessingSpinDerivative

/-! The full-turn product and vanishing residual in Example 5.2(ii). -/

@[expose] public section

open Filter Topology Real
open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Scalar restriction for the exponential sum and power formulas. -/
local instance fullTurnNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- Example 5.2(ii): at width 2π, every sampled exponential is minus the identity. -/
theorem full_turn_factor (θ s : ℝ) :
    exp (-I • (((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ * s / 2 * I)) • Z) * X * exp ((θ * s / 2 * I) • Z)))) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [sampled_factor]
  have hmiddle : exp ((-I * ((2 * Real.pi) / 2 : ℝ)) • X) =
      -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [show -I * (((2 * Real.pi) / 2 : ℝ) : ℂ) = -I * (Real.pi : ℂ) by
      push_cast
      ring]
    rw [exp_involution X matrix_relations.1 matrix_relations.2.2.1,
      Real.cos_pi, Real.sin_pi]
    simp
  rw [hmiddle]
  have hcancel : exp (-((θ * s / 2 * I)) • Z) * exp ((θ * s / 2 * I) • Z) = 1 := by
    rw [neg_smul]
    simpa only [one_smul] using rotating_frame_cancel ((θ * s / 2 * I) • Z) 1
  simp only [mul_neg, mul_one, neg_mul, hcancel]

/-- Example 5.2(ii): the product of the T full-turn factors is `(-1)^T`. -/
theorem full_turn_stepProduct (θ : ℝ) (T : ℕ) :
    stepProduct (fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ * s / 2 * I)) • Z) * X * exp ((θ * s / 2 * I) • Z))) T =
      ((-1 : ℂ) ^ T) • 1 := by
  unfold stepProduct sampleProduct
  simp_rw [full_turn_factor θ]
  rw [List.map_const', List.length_reverse, List.length_range, List.prod_replicate]
  rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1 by simp,
    smul_pow, one_pow]

/-- Example 5.2(ii): the end phases multiply to the Z rotation in the paper. -/
theorem full_turn_end_phases (θ : ℝ) :
    let H := fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ * s / 2 * I)) • Z) * X * exp ((θ * s / 2 * I) • Z))
    exp (-(I / 2) • H 1) * exp ((I / 2) • H 0) = exp (-(θ * I) • Z) := by
  dsimp only
  have hleft : exp (-(I / 2) • (((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ / 2 * I)) • Z) * X * exp ((θ / 2 * I) • Z)))) =
      exp (-((θ / 2 * I)) • Z) * ((-I) • X) * exp ((θ / 2 * I) • Z) := by
    have hs := sampled_factor Real.pi θ 1
    have hscale : -(I / 2) • (((2 * Real.pi) / 2 : ℝ) •
        (exp (-((θ / 2 * I)) • Z) * X * exp ((θ / 2 * I) • Z))) =
        -I • ((Real.pi / 2 : ℝ) •
          (exp (-((θ / 2 * I)) • Z) * X * exp ((θ / 2 * I) • Z))) := by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      ring
    rw [hscale]
    norm_num only [Complex.ofReal_one, mul_one] at hs
    rw [hs]
    rw [exp_involution X matrix_relations.1 matrix_relations.2.2.1,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num only [Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul,
      zero_sub, one_mul]
    simp only [mul_one, neg_smul]
  have hright : exp ((I / 2) • (((2 * Real.pi) / 2 : ℝ) • X)) = I • X := by
    rw [show (I / 2) • (((2 * Real.pi) / 2 : ℝ) • X) =
        (I * ((Real.pi / 2 : ℝ) : ℂ)) • X by
      ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      ring]
    rw [show I * (((Real.pi / 2 : ℝ) : ℂ)) =
        -I * ((-Real.pi / 2 : ℝ) : ℂ) by
      push_cast
      ring]
    rw [exp_involution X matrix_relations.1 matrix_relations.2.2.1,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hmove : X * exp ((θ / 2 * I) • Z) = exp (-((θ / 2 * I)) • Z) * X := by
    have hXZ : X * Z = -(Z * X) :=
      eq_neg_of_add_eq_zero_left matrix_relations.2.2.2.2
    have hpos : (θ : ℂ) / 2 * I = -I * ((-θ / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hneg : -((θ : ℂ) / 2 * I) = -I * ((θ / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    conv_lhs => rw [hpos]
    conv_rhs => rw [hneg]
    rw [exp_involution Z matrix_relations.2.1 matrix_relations.2.2.2.1,
      exp_involution Z matrix_relations.2.1 matrix_relations.2.2.2.1,
      show -θ / 2 = -(θ / 2) by ring,
      Real.cos_neg, Real.sin_neg]
    simp only [mul_sub, mul_smul_comm, mul_one, sub_mul, smul_mul_assoc, one_mul]
    rw [hXZ]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    push_cast
    ring
  norm_num only [Nat.cast_one, Nat.cast_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, zero_div, zero_mul, neg_zero, zero_smul,
    NormedSpace.exp_zero, one_mul] at ⊢
  rw [hleft, hright]
  simp only [mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show I * (-I) = 1 by simp, one_smul, ← mul_assoc X, hmove,
    mul_assoc, matrix_relations.2.2.1, mul_one,
    ← NormedSpace.exp_add_of_commute (Commute.refl (-((θ / 2 * I)) • Z)), ← add_smul]
  congr 2
  ring

/-- Example 5.2(ii): the factor product and end phases give the displayed endpoint. -/
theorem full_turn_product (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    let H := fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    roundedEvolution H T T = ((-1 : ℂ) ^ T) • exp (-(θ * I) • Z) := by
  intro H
  have hH : IsTimeDepHamiltonian H := by
    intro s _
    apply (show IsSelfAdjoint ((2 * Real.pi) / 2 : ℝ) from rfl).smul
    have hZ : star Z = Z := matrix_relations.2.1
    have hX : star X = X := matrix_relations.1
    change star (_ * _ * _) = _
    simp only [Matrix.star_mul, NormedSpace.star_exp, star_smul, hZ, hX,
      Complex.star_def, map_neg, map_mul, map_div₀, Complex.conj_ofReal,
      Complex.conj_I, map_ofNat, mul_neg, neg_neg]
    rw [mul_assoc]
  rw [roundedEvolution_end dieudonne_10_5_4 hH hT, full_turn_stepProduct θ T]
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_one]
  dsimp only [H]
  rw [full_turn_end_phases]

/-- Example 5.2(ii): splitting off T full turns leaves only the small phase defect. -/
theorem full_turn_axis_split (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.IsHermitian) (hMM : M * M = 1) (ρ : ℝ) (T : ℕ) :
    exp ((-I * (ρ : ℂ)) • M) = ((-1 : ℂ) ^ T) •
      exp ((-I * ((ρ - Real.pi * T : ℝ) : ℂ)) • M) := by
  have hs := axis_exp_split M hM hMM ρ (2 * T)
  dsimp only at hs
  have hsq : ((-I) • M) ^ 2 = (-1 : ℂ) • 1 := by
    rw [smul_pow, pow_two M, hMM]
    simp only [neg_sq, Complex.I_sq]
  rw [pow_mul, hsq, smul_pow, one_pow, smul_mul_assoc, one_mul] at hs
  convert hs using 2
  all_goals
    push_cast
    ring_nf

/-- Example 5.2(ii): the exponential residual vanishes with the phase defect. -/
theorem full_turn_residual_limit (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ ‖exp ((-I / 2) •
      (((2 * Real.pi * T : ℝ) • X) - θ • Z)) - ((-1 : ℂ) ^ T) • 1‖)
      atTop (𝓝 0) := by
  let ρ := fun T : ℕ ↦ Real.sqrt (Real.pi ^ 2 * (2 * T : ℕ) ^ 2 + θ ^ 2) / 2
  let ζ := fun T : ℕ ↦ ρ T - Real.pi * T
  let M := fun T : ℕ ↦ (2 * ρ T)⁻¹ • ((Real.pi * (2 * T : ℕ)) • X - θ • Z)
  have hζ : Tendsto ζ atTop (𝓝 0) := by
    convert phase_defect_tendsto_zero (show 0 < 2 * Real.pi by positivity) θ using 1
    funext T
    dsimp [ζ, ρ]
    push_cast
    ring_nf
  have hbound : Tendsto (fun T ↦ |Real.cos (ζ T) - 1| + |Real.sin (ζ T)|)
      atTop (𝓝 0) := by
    simpa only [Real.cos_zero, Real.sin_zero, sub_self, abs_zero, add_zero] using
      (((Real.continuous_cos.tendsto 0).comp hζ).sub_const 1).abs.add
        (((Real.continuous_sin.tendsto 0).comp hζ).abs)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hρ : ρ T ≠ 0 := by dsimp [ρ]; positivity
  have hM : (M T).IsHermitian ∧ M T * M T = 1 := M_involution θ (2 * T) (by omega)
  have hnorm : ‖M T‖ = 1 := by
    have hh := congrArg norm hM.2
    rw [hM.1.isSelfAdjoint.norm_mul_self, norm_one] at hh
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hh)
  have hgen : (-I / 2) • ((2 * Real.pi * T) • X - θ • Z) =
      (-I * (ρ T : ℂ)) • M T := by
    ext i j
    simp only [M, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hρ]
  rw [hgen, full_turn_axis_split _ hM.1 hM.2, ← smul_sub, norm_smul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [exp_involution _ hM.1 hM.2]
  have he : (Real.cos (ζ T) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (I * Real.sin (ζ T)) • M T - 1 =
      ((Real.cos (ζ T) : ℂ) - 1) • 1 - (I * Real.sin (ζ T)) • M T := by
    rw [sub_smul, one_smul]
    abel
  rw [he]
  simpa only [norm_smul, norm_one, mul_one, norm_mul, Complex.norm_I,
    one_mul, hnorm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using
    norm_sub_le (((Real.cos (ζ T) : ℂ) - 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      ((I * Real.sin (ζ T)) • M T)

/-- Example 5.2(ii), last equality: the distance of the Z rotation from 1. -/
theorem Z_rotation_distance (a : ℝ) :
    ‖exp (-(a * I) • Z) - 1‖ = 2 * |Real.sin (a / 2)| := by
  have he : I • (exp (-(a * I) • Z) - 1) =
      Real.sin a • Z + (I * (Real.cos a - 1)) • 1 := by
    rw [show -((a : ℂ) * I) = -I * (a : ℂ) by ring,
      exp_involution Z matrix_relations.2.1 matrix_relations.2.2.2.1]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      Complex.real_smul, smul_eq_mul]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hn := xz_imaginary_norm 0 (Real.sin a) (Real.cos a - 1)
  simp only [zero_smul, zero_add, norm_smul, Real.norm_eq_abs, norm_Z, mul_one,
    sq_abs] at hn
  have hs : Real.sin a ^ 2 + (Real.cos a - 1) ^ 2 =
      (2 * |Real.sin (a / 2)|) ^ 2 := by
    have htrig := Real.sin_sq_add_cos_sq a
    have hdouble := Real.cos_two_mul (a / 2)
    rw [show 2 * (a / 2) = a by ring] at hdouble
    rw [mul_pow, sq_abs]
    linear_combination htrig - 2 * hdouble - 4 * Real.sin_sq_add_cos_sq (a / 2)
  calc
    _ = ‖I • (exp (-(a * I) • Z) - 1)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ = Real.sqrt (Real.sin a ^ 2 + (Real.cos a - 1) ^ 2) := by
      rw [he]
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hn
    _ = _ := by rw [hs, Real.sqrt_sq (by positivity)]

/-- Example 5.2(ii), final display: the vanishing residual gives the endpoint norm limit. -/
theorem full_turn_error_limit (dieudonne_10_5_4 : Dieudonne_10_5_4) (θ : ℝ) :
    let H := fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    (∀ T : ℕ, 0 < (T : ℝ) → evolution H T T = exp (-(θ / 2 * I) • Z) *
      exp ((-I / 2) • ((2 * Real.pi * T) • X - θ • Z))) →
    Tendsto (fun T : ℕ ↦ ‖roundedEvolution H T T - evolution H T T‖)
      atTop (𝓝 (2 * |Real.sin (θ / 4)|)) := by
  intro H hU
  let R := exp (-(θ / 2 * I) • Z)
  let F := exp (-(θ * I) • Z)
  have hR : R ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [one_smul] using derivative_frame_unitary θ 1
  have hF : F = R * R := by
    dsimp only [F, R]
    rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
    congr 2
    ring
  have hdist : ‖F - R‖ = 2 * |Real.sin (θ / 4)| := by
    rw [hF, show R * R - R = R * (R - 1) by rw [mul_sub, mul_one],
      CStarRing.norm_mem_unitary_mul _ hR]
    have hz := Z_rotation_distance (θ / 2)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hz
    rw [hz]
    congr 3
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (g := fun T : ℕ ↦ ‖exp ((-I / 2) •
      (((2 * Real.pi * T : ℝ) • X) - θ • Z)) - ((-1 : ℂ) ^ T) • 1‖)
    ?_ (full_turn_residual_limit θ)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  rw [full_turn_product dieudonne_10_5_4 θ T hT, hU T ht]
  let c : ℂ := (-1) ^ T
  let E := exp ((-I / 2) • (((2 * Real.pi * T : ℝ) • X) - θ • Z))
  have hc : ‖c‖ = 1 := by simp only [c, norm_pow, norm_neg, norm_one, one_pow]
  have hn : ‖c • (F - R)‖ = 2 * |Real.sin (θ / 4)| := by
    rw [norm_smul, hc, one_mul, hdist]
  have hb := abs_norm_sub_norm_le (c • F - R * E) (c • (F - R))
  have he : c • F - R * E - c • (F - R) = -(R * (E - c • 1)) := by
    simp only [smul_sub, mul_sub, mul_smul_comm, mul_one]
    abel
  rw [hn, he, norm_neg, CStarRing.norm_mem_unitary_mul _ hR] at hb
  exact hb

end RoundedClocks.PrecessingSpin
