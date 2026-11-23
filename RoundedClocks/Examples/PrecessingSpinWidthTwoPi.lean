/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinOpeningDisplays
public import RoundedClocks.Examples.PrecessingSpinWidthPi

/-! # Example 5.2(ii): the limit at width `2π`

With `ω = 2π`, every factor `e^{-iH(j/T)}` is `-1`, so `V(T) = (-1)^T e^{-iθZ}`
(`full_turn_product`). As `e^{-i(2πTX-θZ)/2} - (-1)^T → 0` (`full_turn_exp_sub_tendsto_zero`),
`‖V(T) - U(T)‖ = ‖(-1)^T e^{-iθZ/2} - e^{-i(2πTX-θZ)/2}‖ → ‖e^{-iθZ/2} - 1‖ = 2|sin(θ/4)|`
(`full_turn_error_limit`, `Z_rotation_distance`).
-/

@[expose] public section

open Filter Topology Real
open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-- Mathlib's exponential lemmas use the matrices as a normed algebra over `ℚ`. -/
local instance fullTurnNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- In (ii), every factor is `-1`: at `ω = 2π`, `e^{-iH(s)} = e^{-iθsZ/2} e^{-iπX} e^{iθsZ/2} = -1`.
-/
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
    rw [exp_involution X X_isHermitian X_mul_X,
      Real.cos_pi, Real.sin_pi]
    simp
  rw [hmiddle]
  have hcancel : exp (-((θ * s / 2 * I)) • Z) * exp ((θ * s / 2 * I) • Z) = 1 := by
    rw [neg_smul]
    simpa only [one_smul] using rotating_frame_cancel ((θ * s / 2 * I) • Z) 1
  simp only [mul_neg, mul_one, neg_mul, hcancel]

/-- In (ii), the `T`-step product is `W_T = (-1)^T`. -/
theorem full_turn_stepProduct (θ : ℝ) (T : ℕ) :
    stepProduct (fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ * s / 2 * I)) • Z) * X * exp ((θ * s / 2 * I) • Z))) T =
      ((-1 : ℂ) ^ T) • 1 := by
  unfold stepProduct sampleProduct orderedProduct
  simp_rw [full_turn_factor θ]
  rw [List.map_const', List.length_reverse, List.length_range, List.prod_replicate]
  rw [show (-1 : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1 by simp,
    smul_pow, one_pow]

/-- In (ii), the end phases of (2.5) multiply to `e^{-iH(1)/2} e^{iH(0)/2} = e^{-iθZ}`. -/
theorem full_turn_end_phases (θ : ℝ) :
    let H := fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-((θ * s / 2 * I)) • Z) * X * exp ((θ * s / 2 * I) • Z))
    exp (-(I / 2) • H 1) * exp ((I / 2) • H 0) = exp (-(θ * I) • Z) := by
  dsimp only
  -- `e^{-iH(1)/2} = e^{-iθZ/2} (-iX) e^{iθZ/2}`.
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
    rw [exp_involution X X_isHermitian X_mul_X,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num only [Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul,
      zero_sub, one_mul]
    simp only [mul_one, neg_smul]
  -- `e^{iH(0)/2} = iX`.
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
    rw [exp_involution X X_isHermitian X_mul_X,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  -- `X e^{iθZ/2} = e^{-iθZ/2} X`, as `X` and `Z` anticommute.
  have hmove : X * exp ((θ / 2 * I) • Z) = exp (-((θ / 2 * I)) • Z) * X := by
    have hXZ : X * Z = -(Z * X) :=
      eq_neg_of_add_eq_zero_left X_mul_Z_add_Z_mul_X
    have hpos : (θ : ℂ) / 2 * I = -I * ((-θ / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hneg : -((θ : ℂ) / 2 * I) = -I * ((θ / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    conv_lhs => rw [hpos]
    conv_rhs => rw [hneg]
    rw [exp_involution Z Z_isHermitian Z_mul_Z,
      exp_involution Z Z_isHermitian Z_mul_Z,
      show -θ / 2 = -(θ / 2) by ring,
      Real.cos_neg, Real.sin_neg]
    simp only [mul_sub, mul_smul_comm, mul_one, sub_mul, smul_mul_assoc, one_mul]
    rw [hXZ]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
      smul_eq_mul]
    push_cast
    ring
  -- So the product is `e^{-iθZ/2} X e^{iθZ/2} X = e^{-iθZ/2} e^{-iθZ/2} = e^{-iθZ}`.
  norm_num only [Nat.cast_one, Nat.cast_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, zero_div, zero_mul, neg_zero, zero_smul,
    NormedSpace.exp_zero, one_mul] at ⊢
  rw [hleft, hright]
  simp only [mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show I * (-I) = 1 by simp, one_smul, ← mul_assoc X, hmove,
    mul_assoc, X_mul_X, mul_one,
    ← NormedSpace.exp_add_of_commute (Commute.refl (-((θ / 2 * I)) • Z)), ← add_smul]
  congr 2
  ring

/-- In (ii), `V(T) = (-1)^T e^{-iθZ}`, by (2.5). -/
theorem full_turn_product (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    let H := fun s : ℝ ↦ ((2 * Real.pi) / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    roundedEvolution H T T = ((-1 : ℂ) ^ T) • exp (-(θ * I) • Z) := by
  intro H
  have hH : IsTimeDepHamiltonian H := by
    intro s _
    have h : exp ((θ * s / 2 * I) • Z) = star (exp (-(θ * s / 2 * I) • Z)) := by
      simp [NormedSpace.star_exp, star_smul, show star Z = Z from Z_isHermitian]
    change IsHermitian (((2 * Real.pi) / 2 : ℝ) • _)
    rw [h]
    exact (IsSelfAdjoint.all ((2 * Real.pi) / 2 : ℝ)).smul
      (X_isHermitian.isSelfAdjoint.conjugate _)
  rw [roundedEvolution_end dieudonne_10_5_4 hH hT, full_turn_stepProduct θ T]
  rw [mul_smul_comm, smul_mul_assoc]
  simp only [mul_one]
  dsimp only [H]
  rw [full_turn_end_phases]

/-- For a Hermitian involution `A`, `e^{-irA} = (-1)^T e^{-i(r - πT)A}`, as `e^{-iπA} = -1`. -/
theorem full_turn_axis_split (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hAA : A * A = 1) (r : ℝ) (T : ℕ) :
    exp ((-I * (r : ℂ)) • A) = ((-1 : ℂ) ^ T) •
      exp ((-I * ((r - Real.pi * T : ℝ) : ℂ)) • A) := by
  have hs := axis_exp_split A hA hAA r (2 * T)
  have hsq : ((-I) • A) ^ 2 = (-1 : ℂ) • 1 := by
    rw [smul_pow, pow_two A, hAA]
    simp only [neg_sq, Complex.I_sq]
  rw [pow_mul, hsq, smul_pow, one_pow, smul_mul_assoc, one_mul] at hs
  convert hs using 2
  all_goals
    push_cast
    ring_nf

/-- In (ii), `e^{-i(2πTX-θZ)/2} - (-1)^T → 0`: the left term is `e^{-irA}` for a Hermitian
involution `A` and `r = (π²(2T)² + θ²)^{1/2}/2`, and `r - πT → 0`. -/
theorem full_turn_exp_sub_tendsto_zero (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ ‖exp ((-I / 2) •
      (((2 * Real.pi * T : ℝ) • X) - θ • Z)) - ((-1 : ℂ) ^ T) • 1‖)
      atTop (𝓝 0) := by
  let r := fun T : ℕ ↦ Real.sqrt (Real.pi ^ 2 * (2 * T : ℕ) ^ 2 + θ ^ 2) / 2
  let z := fun T : ℕ ↦ r T - Real.pi * T
  let A := fun T : ℕ ↦ (2 * r T)⁻¹ • ((Real.pi * (2 * T : ℕ)) • X - θ • Z)
  have hz : Tendsto z atTop (𝓝 0) := by
    convert phase_defect_tendsto_zero (show 0 < 2 * Real.pi by positivity) θ using 1
    funext T
    dsimp [z, r]
    push_cast
    ring_nf
  have hbound : Tendsto (fun T ↦ |Real.cos (z T) - 1| + |Real.sin (z T)|)
      atTop (𝓝 0) := by
    simpa only [Real.cos_zero, Real.sin_zero, sub_self, abs_zero, add_zero] using
      (((Real.continuous_cos.tendsto 0).comp hz).sub_const 1).abs.add
        (((Real.continuous_sin.tendsto 0).comp hz).abs)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hr : r T ≠ 0 := by dsimp [r]; positivity
  have hA : (A T).IsHermitian ∧ A T * A T = 1 := M_involution θ (2 * T) (by omega)
  have hnorm : ‖A T‖ = 1 := CStarRing.norm_of_mem_unitary
    (Matrix.mem_unitaryGroup_iff.mpr (by rw [show star (A T) = A T from hA.1]; exact hA.2))
  have hgen : (-I / 2) • ((2 * Real.pi * T) • X - θ • Z) =
      (-I * (r T : ℂ)) • A T := by
    ext i j
    simp only [A, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
  rw [hgen, full_turn_axis_split _ hA.1 hA.2, ← smul_sub, norm_smul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [exp_involution _ hA.1 hA.2]
  have he : (Real.cos (z T) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      (I * Real.sin (z T)) • A T - 1 =
      ((Real.cos (z T) : ℂ) - 1) • 1 - (I * Real.sin (z T)) • A T := by
    rw [sub_smul, one_smul]
    abel
  rw [he]
  simpa only [norm_smul, norm_one, mul_one, norm_mul, Complex.norm_I,
    one_mul, hnorm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using
    norm_sub_le (((Real.cos (z T) : ℂ) - 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      ((I * Real.sin (z T)) • A T)

/-- The last equality in (ii): `‖e^{-iaZ} - 1‖ = 2|sin(a/2)|`. -/
theorem Z_rotation_distance (a : ℝ) :
    ‖exp (-(a * I) • Z) - 1‖ = 2 * |Real.sin (a / 2)| := by
  have hZ : (-(a * I)) • Z = Matrix.diagonal ![I * ((-a : ℝ) : ℂ), I * (a : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Z, mul_comm]
  have hn : ∀ i, ‖(exp ![I * ((-a : ℝ) : ℂ), I * (a : ℂ)] - 1 : Fin 2 → ℂ) i‖ =
      2 * |Real.sin (a / 2)| := by
    intro i
    rw [Pi.exp_def]
    fin_cases i
    · simpa [← Complex.exp_eq_exp_ℂ, neg_div, abs_mul] using
        Complex.norm_exp_I_mul_ofReal_sub_one (-a)
    · simpa [← Complex.exp_eq_exp_ℂ, abs_mul] using
        Complex.norm_exp_I_mul_ofReal_sub_one a
  rw [hZ, Matrix.exp_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  exact le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ (hn i).le)
    ((hn 0).symm.le.trans (norm_le_pi_norm _ 0))

/-- The display in (ii):
`‖V(T) - U(T)‖ = ‖(-1)^T e^{-iθZ/2} - e^{-i(2πTX-θZ)/2}‖ → ‖e^{-iθZ/2} - 1‖ = 2|sin(θ/4)|`, from the
first opening display at `ω = 2π`. -/
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
    simpa only [one_smul] using frame_exp_mem_unitary θ 1
  -- `e^{-iθZ} = e^{-iθZ/2} e^{-iθZ/2}`.
  have hF : F = R * R := by
    dsimp only [F, R]
    rw [← NormedSpace.exp_add_of_commute (Commute.refl _), ← add_smul]
    congr 2
    ring
  -- `‖e^{-iθZ/2} - 1‖ = 2|sin(θ/4)|`.
  have hdist : ‖R - 1‖ = 2 * |Real.sin (θ / 4)| := by
    have hz := Z_rotation_distance (θ / 2)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hz
    rw [hz]
    congr 3
    ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (g := fun T : ℕ ↦ ‖exp ((-I / 2) •
      (((2 * Real.pi * T : ℝ) • X) - θ • Z)) - ((-1 : ℂ) ^ T) • 1‖)
    ?_ (full_turn_exp_sub_tendsto_zero θ)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  rw [full_turn_product dieudonne_10_5_4 θ T hT, hU T ht]
  let c : ℂ := (-1) ^ T
  let E := exp ((-I / 2) • (((2 * Real.pi * T : ℝ) • X) - θ • Z))
  have hc : ‖c‖ = 1 := by simp only [c, norm_pow, norm_neg, norm_one, one_pow]
  -- The displayed equality `‖V(T) - U(T)‖ = ‖(-1)^T e^{-iθZ/2} - e^{-i(2πTX-θZ)/2}‖`: remove the
  -- unitary factor `e^{-iθZ/2}`.
  have hdisplay : ‖c • F - R * E‖ = ‖c • R - E‖ := by
    rw [hF, show c • (R * R) - R * E = R * (c • R - E) by rw [mul_sub, mul_smul_comm],
      CStarRing.norm_mem_unitary_mul _ hR]
  -- `‖(-1)^T e^{-iθZ/2} - (-1)^T‖ = ‖e^{-iθZ/2} - 1‖ = 2|sin(θ/4)|`.
  have hn : ‖c • R - c • (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 2 * |Real.sin (θ / 4)| := by
    rw [← smul_sub, norm_smul, hc, one_mul, hdist]
  -- The two norms differ by at most `‖e^{-i(2πTX-θZ)/2} - (-1)^T‖`, which tends to zero.
  have hb := abs_norm_sub_norm_le (c • R - E) (c • R - c • (1 : Matrix (Fin 2) (Fin 2) ℂ))
  rw [hn, show c • R - E - (c • R - c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = -(E - c • 1) by abel,
    norm_neg, ← hdisplay] at hb
  exact hb

end RoundedClocks.PrecessingSpin
