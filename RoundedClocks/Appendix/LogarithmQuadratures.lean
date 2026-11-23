/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Lemma A.2: exact scalar quadratures

Lemma A.2 evaluates the two scalar resolvent integrals from their primitives, endpoint values, odd
cancellation, and an affine substitution.
-/

@[expose] public section
noncomputable section
open Real Set MeasureTheory
namespace RoundedClocks.WalkLogQuadratures

/-- Section 4, Lemma A.2 (`lem:walk-log`) proof: `v=2u-1` contributes the Jacobian factor `1/2`
and changes the integration interval from `[0,1]` to `[-1,1]`. -/
theorem chord_change_variable (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v in (-1 : ℝ)..1, f v := by
  have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    f (by norm_num : (2 : ℝ) ≠ 0) (-1)
  simpa only [mul_zero, zero_add, mul_one, show (2 : ℝ) + -1 = 1 by norm_num,
    sub_eq_add_neg, smul_eq_mul, one_div] using h

/-- Auxiliary antiderivative for the first standard integral in Lemma A.2,
in the variable `v=2u-1`. This formula assumes positive width; the integral theorem
`walk_slope_quadrature_with_zero` also covers zero width. -/
theorem chord_arctan_antiderivative {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ Real.arctan (v * Real.tan (w / 4)) /
        (Real.sin (w / 4) * Real.cos (w / 4)))
      (1 / (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2)) v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hs : 0 < Real.sin (w / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have h := ((Real.hasDerivAt_arctan (v * Real.tan (w / 4))).comp v
    ((hasDerivAt_id v).mul_const (Real.tan (w / 4)))).div_const
      (Real.sin (w / 4) * Real.cos (w / 4))
  convert h using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- Auxiliary antiderivative for the second standard integral in Lemma A.2: `v/(cos²(w/4) r)`
has derivative `r⁻³`, with `r²=cos²(w/4)+sin²(w/4)v²`. -/
theorem chord_cube_antiderivative {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ v / (Real.cos (w / 4) ^ 2 *
        Real.sqrt (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2)))
      (1 / Real.sqrt (Real.cos (w / 4) ^ 2 + Real.sin (w / 4) ^ 2 * v ^ 2) ^ 3) v := by
  let A := Real.cos (w / 4) ^ 2
  let B := Real.sin (w / 4) ^ 2
  let q : ℝ → ℝ := fun v ↦ A + B * v ^ 2
  have hA : 0 < A := sq_pos_of_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩)
  have hq : 0 < q v := add_pos_of_pos_of_nonneg hA (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : 0 < Real.sqrt (q v) := Real.sqrt_pos.mpr hq
  have hd : HasDerivAt q (B * (2 * v)) v := by
    convert (((hasDerivAt_id v).pow 2).const_mul B).const_add A using 1
    simp
  have h := (hasDerivAt_id v).div ((hd.sqrt hq.ne').const_mul A) (by positivity)
  change HasDerivAt (fun v ↦ v / (A * Real.sqrt (q v))) (1 / Real.sqrt (q v) ^ 3) v
  convert h using 1
  have he := Real.sq_sqrt hq.le
  simp only [id_eq]; field_simp [hA.ne', hs.ne']
  ring_nf; rw [he]
  dsimp [q]; ring


/-- The squared scalar radius after the centered substitution. -/
def radius (w v : ℝ) : ℝ := Real.cos (w / 4) ^ 2 + v ^ 2 * Real.sin (w / 4) ^ 2

/-- The radius is positive throughout the integration interval, indeed on the real line. -/
theorem radius_pos {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    0 < radius w v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The two endpoint radii in the last antiderivative evaluation are one. -/
theorem radius_endpoints (w : ℝ) : radius w (-1) = 1 ∧ radius w 1 = 1 := by
  simp [radius, Real.cos_sq_add_sin_sq]

/-- The exact first antiderivative printed in Lemma A.2. -/
theorem arctan_antiderivative {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.arctan (v * Real.tan (w / 4)) / Real.sin (w / 2))
      (1 / (2 * radius w v)) v := by
  have h := (chord_arctan_antiderivative hw0 hw v).div_const 2
  have hsin : Real.sin (w / 2) = 2 * Real.sin (w / 4) * Real.cos (w / 4) := by
    rw [show w / 2 = 2 * (w / 4) by ring, Real.sin_two_mul]
  convert h using 1
  · ext x
    rw [hsin]
    ring
  · simp only [radius, mul_comm (v ^ 2), one_div, mul_inv_rev]
    ring

/-- The exact second antiderivative printed in Lemma A.2, using square roots. -/
theorem cube_antiderivative {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ v / (Real.cos (w / 4) ^ 2 * Real.sqrt (radius w v)))
      (1 / Real.sqrt (radius w v) ^ 3) v := by
  simpa only [radius, mul_comm (Real.sin (w / 4) ^ 2)] using
    chord_cube_antiderivative hw0 hw v

/-- The first line of Lemma A.2's quadrature display, including zero width. -/
theorem square_quadrature {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (1 / 2 : ℝ) * (∫ v : ℝ in (-1 : ℝ)..1, 1 / radius w v) = κ w := by
  by_cases hz : w = 0
  · subst w
    norm_num [radius, κ]
  · have hp : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hz)
    have hcont : Continuous (fun v : ℝ ↦ 1 / (2 * radius w v)) :=
      continuous_const.div (by unfold radius; fun_prop)
        (fun v ↦ mul_ne_zero (by norm_num) (radius_pos hw0 hw v).ne')
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (-1 : ℝ)) (b := 1)
      (fun v _ ↦ arctan_antiderivative hp hw v) (hcont.intervalIntegrable _ _)
    have hid (v : ℝ) : 1 / (2 * radius w v) = (1 / 2 : ℝ) * (1 / radius w v) := by ring
    simp_rw [hid] at hFTC
    rw [intervalIntegral.integral_const_mul] at hFTC
    rw [hFTC]
    simp only [one_mul, neg_one_mul, Real.arctan_neg]
    rw [Real.arctan_tan (by linarith [pi_pos]) (by linarith),
      κ, if_neg hz]
    ring

/-- The last quadrature of Lemma A.2, from the second antiderivative and `r(±1)=1`. -/
theorem cube_quadrature {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (1 / 2 : ℝ) * (∫ v : ℝ in (-1 : ℝ)..1, 1 / Real.sqrt (radius w v) ^ 3) =
      1 / Real.cos (w / 4) ^ 2 := by
  have hcont : Continuous (fun v : ℝ ↦ 1 / Real.sqrt (radius w v) ^ 3) :=
    continuous_const.div ((Real.continuous_sqrt.comp (by unfold radius; fun_prop)).pow 3)
      (fun v ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (radius_pos hw0 hw v)).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ ↦ cube_antiderivative hw0 hw v) (hcont.intervalIntegrable _ _)]
  rw [(radius_endpoints w).1, (radius_endpoints w).2, Real.sqrt_one]
  ring

/-- The integrand `v r(v)^(-3/2)` in Lemma A.2 is odd. -/
theorem cube_odd (w : ℝ) :
    Function.Odd (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) := by
  intro v
  simp only [radius, neg_sq, neg_div]

/-- The odd part of the weight `1+v` integrates to zero. -/
theorem cube_odd_integral (w : ℝ) :
    (∫ v : ℝ in (-1 : ℝ)..1, v / Real.sqrt (radius w v) ^ 3) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) (a := (-1 : ℝ)) (b := 1)
  have hodd (v : ℝ) : (-v) / Real.sqrt (radius w (-v)) ^ 3 =
      -(v / Real.sqrt (radius w v) ^ 3) := cube_odd w v
  simp only [hodd, intervalIntegral.integral_neg, neg_neg] at h
  linarith

/-- The fifth line of the norm display removes the odd summand explicitly. -/
theorem cube_weighted_integral {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / Real.sqrt (radius w v) ^ 3) =
      ∫ v : ℝ in (-1 : ℝ)..1, 1 / Real.sqrt (radius w v) ^ 3 := by
  have hcont : Continuous (fun v : ℝ ↦ 1 / Real.sqrt (radius w v) ^ 3) :=
    continuous_const.div ((Real.continuous_sqrt.comp (by unfold radius; fun_prop)).pow 3)
      (fun v ↦ pow_ne_zero _ (Real.sqrt_pos.mpr (radius_pos hw0 hw v)).ne')
  have hoddcont : Continuous (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) := by
    convert continuous_id.mul hcont using 1
    ext v
    exact (mul_one_div v (Real.sqrt (radius w v) ^ 3)).symm
  simp_rw [add_div]
  rw [intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
    (hoddcont.intervalIntegrable _ _),
    cube_odd_integral, add_zero]

/-- The substitution in the second and fourth lines, before cancelling odd terms. -/
theorem quadrature_substitution (w : ℝ) :
    (∫ u : ℝ in (0 : ℝ)..1, 1 / radius w (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, 1 / radius w v ∧
    (∫ u : ℝ in (0 : ℝ)..1, (2 * u) / Real.sqrt (radius w (2 * u - 1)) ^ 3) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / Real.sqrt (radius w v) ^ 3 := by
  refine ⟨chord_change_variable (fun v ↦ 1 / radius w v), ?_⟩
  have h := chord_change_variable (fun v ↦ (1 + v) / Real.sqrt (radius w v) ^ 3)
  simpa only [show ∀ u : ℝ, 1 + (2 * u - 1) = 2 * u by intro u; ring] using h

end RoundedClocks.WalkLogQuadratures
