/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Lemma A.2: the two integrals of the norm display

With `r(v) = cos²(w/4) + v² sin²(w/4)`, the norm display in the proof of Lemma A.2 uses
`(1/2)∫_{-1}^{1} dv/r(v) = κ` and `(1/2)∫_{-1}^{1} r(v)^{-3/2} dv = 1/cos²(w/4)`, the substitution
`u = (1+v)/2`, and the vanishing of the integral of the odd function `v r(v)^{-3/2}`. Here
`radius w v` is `r(v)`.
-/

@[expose] public section
noncomputable section
open Real Set MeasureTheory
namespace RoundedClocks.WalkLog

/-- The substitution `u = (1+v)/2`, that is, `v = 2u - 1`: it contributes the factor `1/2` and
changes the interval from `[0,1]` to `[-1,1]`. -/
theorem chord_change_variable (f : ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, f (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v in (-1 : ℝ)..1, f v := by
  simpa only [mul_zero, zero_sub, mul_one, show (2 : ℝ) - 1 = 1 by norm_num,
    inv_eq_one_div, smul_eq_mul] using
    intervalIntegral.integral_comp_mul_sub (a := 0) (b := 1) f two_ne_zero 1

/-- The `r(v) = cos²(w/4) + v² sin²(w/4)` of the proof of Lemma A.2: a lower bound for
`|1 + u(e^{-iφ} - 1)|²` when `v = 2u - 1` and `|φ| ≤ w/2`. -/
def radius (w v : ℝ) : ℝ := Real.cos (w / 4) ^ 2 + v ^ 2 * Real.sin (w / 4) ^ 2

/-- `r(v) > 0` for every real `v`, also at width `0`. -/
theorem radius_pos {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    0 < radius w v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- `r(±1) = 1`. -/
theorem radius_endpoints (w : ℝ) : radius w (-1) = 1 ∧ radius w 1 = 1 := by
  simp [radius, Real.cos_sq_add_sin_sq]

/-- An antiderivative of `1/(2r(v))` for `0 < w < 2π`: `arctan(v tan(w/4))/sin(w/2)`. -/
theorem arctan_antiderivative {w : ℝ} (hw0 : 0 < w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.arctan (v * Real.tan (w / 4)) / Real.sin (w / 2))
      (1 / (2 * radius w v)) v := by
  have hc : 0 < Real.cos (w / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hs : 0 < Real.sin (w / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have h := ((Real.hasDerivAt_arctan (v * Real.tan (w / 4))).comp v
    ((hasDerivAt_id v).mul_const (Real.tan (w / 4)))).div_const
      (Real.sin (w / 2))
  convert h using 1
  rw [show w / 2 = 2 * (w / 4) by ring, Real.sin_two_mul,
    Real.tan_eq_sin_div_cos]
  simp only [radius, mul_comm (v ^ 2)]
  field_simp

/-- An antiderivative of `r(v)^{-3/2}`: `v/(cos²(w/4) r(v)^{1/2})`. -/
theorem cube_antiderivative {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) (v : ℝ) :
    HasDerivAt (fun v : ℝ ↦ v / (Real.cos (w / 4) ^ 2 * Real.sqrt (radius w v)))
      (1 / Real.sqrt (radius w v) ^ 3) v := by
  let A := Real.cos (w / 4) ^ 2
  let B := Real.sin (w / 4) ^ 2
  let q : ℝ → ℝ := fun v ↦ A + v ^ 2 * B
  have hA : 0 < A := sq_pos_of_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩)
  have hq : 0 < q v := add_pos_of_pos_of_nonneg hA (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : 0 < Real.sqrt (q v) := Real.sqrt_pos.mpr hq
  have hd : HasDerivAt q (B * (2 * v)) v := by
    convert (((hasDerivAt_id v).pow 2).const_mul B).const_add A using 1
    · funext x
      simp only [q, Pi.pow_apply, id_eq]
      ring
    · simp
  have h := (hasDerivAt_id v).div ((hd.sqrt hq.ne').const_mul A) (by positivity)
  change HasDerivAt (fun v ↦ v / (A * Real.sqrt (q v))) (1 / Real.sqrt (q v) ^ 3) v
  convert h using 1
  have he := Real.sq_sqrt hq.le
  simp only [id_eq]; field_simp [hA.ne', hs.ne']
  ring_nf; rw [he]
  dsimp [q, radius]
  ring

/-- `(1/2)∫_{-1}^{1} dv/r(v) = κ`, used in the second and fourth lines of the norm display in the
proof of Lemma A.2. Width `0` is included. -/
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

/-- `(1/2)∫_{-1}^{1} r(v)^{-3/2} dv = 1/cos²(w/4)`, used in the fifth line of the norm display, as
`r(±1) = 1`. -/
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

/-- `v r(v)^{-3/2}` is odd. -/
theorem cube_odd (w : ℝ) :
    Function.Odd (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) := by
  intro v
  simp only [radius, neg_sq, neg_div]

/-- The integral of the odd function `v r(v)^{-3/2}` over `[-1,1]` vanishes. -/
theorem cube_odd_integral (w : ℝ) :
    (∫ v : ℝ in (-1 : ℝ)..1, v / Real.sqrt (radius w v) ^ 3) = 0 := by
  have h := intervalIntegral.integral_comp_neg
    (fun v : ℝ ↦ v / Real.sqrt (radius w v) ^ 3) (a := (-1 : ℝ)) (b := 1)
  have hodd (v : ℝ) : (-v) / Real.sqrt (radius w (-v)) ^ 3 =
      -(v / Real.sqrt (radius w v) ^ 3) := cube_odd w v
  simp only [hodd, intervalIntegral.integral_neg, neg_neg] at h
  linarith

/-- The fourth line of the norm display drops the odd part `v r(v)^{-3/2}` of `(1+v) r(v)^{-3/2}`.
-/
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

/-- The substitution `u = (1+v)/2` in the first and third lines of the norm display. -/
theorem quadrature_substitution (w : ℝ) :
    (∫ u : ℝ in (0 : ℝ)..1, 1 / radius w (2 * u - 1)) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, 1 / radius w v ∧
    (∫ u : ℝ in (0 : ℝ)..1, (2 * u) / Real.sqrt (radius w (2 * u - 1)) ^ 3) =
      (1 / 2 : ℝ) * ∫ v : ℝ in (-1 : ℝ)..1, (1 + v) / Real.sqrt (radius w v) ^ 3 := by
  refine ⟨chord_change_variable (fun v ↦ 1 / radius w v), ?_⟩
  have h := chord_change_variable (fun v ↦ (1 + v) / Real.sqrt (radius w v) ^ 3)
  simpa only [show ∀ u : ℝ, 1 + (2 * u - 1) = 2 * u by intro u; ring] using h

end RoundedClocks.WalkLog
