/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Examples.PrecessingSpinMatrix
public import RoundedClocks.Preliminaries.Basic

/-! # Example 5.2(i): the limit at width `π`

With `ω = π` and `T` odd, the proof of Example 5.2 sets `N = cos(θ/(2T)) X - sin(θ/(2T)) Z`,
`ρ = (π²T² + θ²)^{1/2}/2`, `M = (πTX - θZ)/(2ρ)`, and `ζ = ρ - πT/2`. Its display has five
lines:

1. `‖V(T) - U(T)‖ = ‖(-iN)^T - (-iM)^T e^{-iζM}‖` (`norm_difference_eq_norm_powers`);
2. `= ‖N - M cos ζ + i sin ζ‖` (`norm_powers_eq_norm_axes`);
3. `= (‖N - M cos ζ‖² + sin² ζ)^{1/2}` (`norm_axes_eq_sqrt`);
4. `T ‖N - M cos ζ‖ → (π-2)|θ|/(2π)` (`tendsto_axes_distance`), which is
   `c₀ (‖H'(0)‖ + ‖H'(1)‖)` as `‖H'‖ = π|θ|/2` (`hamiltonian_derivWithin_norm`);
5. `T ζ → θ²/(4π)` (`tendsto_mul_ζ`).

The file follows this order, except that line 5 precedes line 4, which uses it.
-/

@[expose] public section

noncomputable section
namespace RoundedClocks.PrecessingSpin

/-! ## The matrices `N` and `M` and the numbers `ρ` and `ζ` -/

section Definitions

open Filter Topology Real
open scoped Matrix.Norms.L2Operator

/-- Example 5.2(i): `N = cos(θ/(2T)) X - sin(θ/(2T)) Z`. -/
def N (θ : ℝ) (T : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Real.cos (θ / (2 * T)) • X - Real.sin (θ / (2 * T)) • Z

/-- Example 5.2(i): `ρ = (π²T² + θ²)^{1/2}/2`. -/
def ρ (θ : ℝ) (T : ℕ) : ℝ := Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2

/-- Example 5.2(i): `M = (πTX - θZ)/(2ρ)`. -/
def M (θ : ℝ) (T : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 * ρ θ T)⁻¹ • ((Real.pi * T) • X - θ • Z)

/-- Example 5.2(i): `ζ = ρ - πT/2`. -/
def ζ (θ : ℝ) (T : ℕ) : ℝ := ρ θ T - Real.pi * T / 2

/-- The unit combination of `X` and `Z` proportional to `aX - θZ` is `cos β X - sin β Z` with
`β = arctan(θ/a)`. -/
theorem normalized_axis_angle {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    (Real.sqrt (a ^ 2 + θ ^ 2))⁻¹ • (a • X - θ • Z) =
      Real.cos (Real.arctan (θ / a)) • X -
        Real.sin (Real.arctan (θ / a)) • Z := by
  have hr : Real.sqrt (1 + (θ / a) ^ 2) = Real.sqrt (a ^ 2 + θ ^ 2) / a := by
    rw [show 1 + (θ / a) ^ 2 = (a ^ 2 + θ ^ 2) / a ^ 2 by field_simp,
      Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sqrt_sq ha.le]
  rw [Real.cos_arctan, Real.sin_arctan, hr, smul_sub, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

/-- The axis of `M`: `M = cos β X - sin β Z` with `β = arctan(θ/(πT))`. -/
theorem M_eq_axis (θ : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    M θ T = Real.cos (Real.arctan (θ / (Real.pi * T))) • X -
      Real.sin (Real.arctan (θ / (Real.pi * T))) • Z := by
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  unfold M ρ
  rw [show 2 * (Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2) =
      Real.sqrt (Real.pi ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) by ring,
    show Real.pi ^ 2 * (T : ℝ) ^ 2 = (Real.pi * T) ^ 2 by ring]
  exact normalized_axis_angle (mul_pos Real.pi_pos ht) θ

end Definitions

/-! ## Lines 1, 2, and 3 of the display in (i) -/

section FrameUnitary

open NormedSpace (exp)
open Complex (I)
open scoped Matrix.Norms.L2Operator

/-- The frame `e^{-isθZ/2}` is unitary. -/
theorem frame_exp_mem_unitary (θ s : ℝ) :
    exp (s • (-(θ / 2 * I) • Z)) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := .restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, show star Z = Z from Z_isHermitian]

end FrameUnitary

section Involutions

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

/-- Mathlib's exponential lemmas use the matrices as a normed algebra over `ℚ`. -/
local instance poweredAxisNormedAlgebra : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  .restrictScalars ℚ ℂ _

/-- An involution raised to an odd power is itself. -/
theorem odd_power_axis (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hAA : A * A = 1) (T : ℕ) (hT : Odd T) : A ^ T = A := by
  rw [pow_eq_pow_mod T (pow_two A ▸ hAA), Nat.odd_iff.mp hT, pow_one]

/-- Line 2 of the display in (i) uses `N^T = N` for odd `T`. -/
theorem N_odd_power (θ : ℝ) (T : ℕ) (hT : Odd T) : N θ T ^ T = N θ T := by
  unfold N
  apply odd_power_axis _ _ T hT
  rw [sub_eq_add_neg, ← neg_smul, xz_square, neg_sq,
    Real.cos_sq_add_sin_sq, one_smul]

/-- `M` is a Hermitian involution. -/
theorem M_involution (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (M θ T).IsHermitian ∧ M θ T * M θ T = 1 := by
  rw [M_eq_axis θ hT, sub_eq_add_neg, ← neg_smul]
  refine ⟨xz_hermitian _ _, ?_⟩
  rw [xz_square, neg_sq, Real.cos_sq_add_sin_sq, one_smul]

/-- Line 2 of the display in (i) uses `M^T = M` for odd `T`. -/
theorem M_odd_power (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) : M θ T ^ T = M θ T :=
  odd_power_axis _ (M_involution θ T hT).2 T hodd

/-- Line 1 of the display in (i) uses `e^{-iρM} = (-iM)^T e^{-iζM}`: for a Hermitian involution
`A`, `e^{-irA} = (-iA)^T e^{-i(r - πT/2)A}`, as `e^{-iπA/2} = -iA`. -/
theorem axis_exp_split (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hAA : A * A = 1) (r : ℝ) (T : ℕ) :
    exp ((-I * (r : ℂ)) • A) =
      ((-I) • A) ^ T * exp ((-I * ((r - Real.pi * T / 2 : ℝ) : ℂ)) • A) := by
  have hhalf : exp ((-I * ((Real.pi / 2 : ℝ) : ℂ)) • A) = (-I) • A := by
    rw [exp_involution A hA hAA, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [Complex.ofReal_zero, zero_smul, Complex.ofReal_one, mul_one,
      zero_sub, neg_smul]
  have hsum : (-I * (r : ℂ)) • A =
      T • ((-I * ((Real.pi / 2 : ℝ) : ℂ)) • A) +
        (-I * ((r - Real.pi * T / 2 : ℝ) : ℂ)) • A := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [hsum, NormedSpace.exp_add_of_commute, NormedSpace.exp_nsmul, hhalf]
  exact (((Commute.refl A).smul_left _).smul_right _).smul_left T

/-- Line 2 of the display in (i) uses `M e^{-iζM} = M cos ζ - i sin ζ`: for a Hermitian
involution `A`, `A e^{-izA} = A cos z - i sin z`. -/
theorem axis_mul_exp (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hAA : A * A = 1) (z : ℝ) :
    A * exp ((-I * (z : ℂ)) • A) =
      (Real.cos z : ℂ) • A - (I * Real.sin z) • 1 := by
  rw [exp_involution A hA hAA, mul_sub, mul_smul_comm, mul_one,
    mul_smul_comm, hAA]

end Involutions

section DisplayLines

open scoped Matrix.Norms.L2Operator
open NormedSpace (exp)
open Complex (I)

/-- Line 1 of the display in (i) uses `S = -iN` at `ω = π`, as `e^{-iπX/4} = (1 - iX)/√2`. -/
theorem S_eq_neg_I_smul_N (θ : ℝ) (T : ℕ) :
    exp (-((Real.pi : ℂ) / 4 * I) • X) * exp ((θ / (2 * T) * I) • Z) *
      exp (-((Real.pi : ℂ) / 4 * I) • X) = (-I) • N θ T := by
  have hquarter : -((Real.pi : ℂ) / 4 * I) =
      -I * ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  have hangle : (θ : ℂ) / (2 * T) * I = I * ((θ / (2 * T) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hquarter, hangle]
  exact half_turn_step (θ / (2 * T))

/-- Line 1 of the display in (i): `‖V(T) - U(T)‖ = ‖(-iN)^T - (-iM)^T e^{-iζM}‖`, from the two
opening displays at `ω = π`. The common frame `e^{-iθZ/2}` is unitary, `S = -iN`, and
`e^{-i(πTX-θZ)/2} = e^{-iρM} = (-iM)^T e^{-iζM}`. -/
theorem norm_difference_eq_norm_powers (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    let H := fun s : ℝ ↦ (Real.pi / 2 : ℝ) •
      (exp (-(θ * s / 2 * I) • Z) * X * exp ((θ * s / 2 * I) • Z))
    evolution H T T = exp (-(θ / 2 * I) • Z) *
      exp ((-I / 2) • ((Real.pi * T) • X - θ • Z)) →
    roundedEvolution H T T = exp (-(θ / 2 * I) • Z) *
      (exp (-(Real.pi / 4 * I) • X) * exp ((θ / (2 * T) * I) • Z) *
        exp (-(Real.pi / 4 * I) • X)) ^ T →
    ‖roundedEvolution H T T - evolution H T T‖ =
      ‖((-I) • N θ T) ^ T - ((-I) • M θ T) ^ T * exp ((-I * (ζ θ T : ℂ)) • M θ T)‖ := by
  intro H hcont hround
  have ht : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hρ : ρ θ T ≠ 0 := by unfold ρ; positivity
  -- `(πTX - θZ)/2 = ρM`.
  have hgen : (-I / 2) • ((Real.pi * T) • X - θ • Z) =
      (-I * (ρ θ T : ℂ)) • M θ T := by
    ext i j
    simp only [M, Matrix.smul_apply, Matrix.sub_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    have hc : (ρ θ T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
    field_simp [hc]
  have hframe : exp (-(θ / 2 * I) • Z) ∈
      unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    simpa only [one_smul] using frame_exp_mem_unitary θ 1
  have hstep := S_eq_neg_I_smul_N θ T
  have hM := M_involution θ T hT
  have hsplit : exp ((-I * (ρ θ T : ℂ)) • M θ T) =
      ((-I) • M θ T) ^ T * exp ((-I * (ζ θ T : ℂ)) • M θ T) :=
    axis_exp_split (M θ T) hM.1 hM.2 (ρ θ T) T
  change ‖roundedEvolution H T T - evolution H T T‖ = _
  rw [hround, hcont, hstep, hgen, hsplit, ← mul_sub]
  exact CStarRing.norm_mem_unitary_mul _ hframe

/-- Line 2 of the display in (i): `‖(-iN)^T - (-iM)^T e^{-iζM}‖ = ‖N - M cos ζ + i sin ζ‖` for odd
`T`, as `N^T = N`, `M^T = M`, and `M e^{-iζM} = M cos ζ - i sin ζ`. -/
theorem norm_powers_eq_norm_axes (θ : ℝ) (T : ℕ) (hT : 1 ≤ T) (hodd : Odd T) :
    ‖((-I) • N θ T) ^ T - ((-I) • M θ T) ^ T * exp ((-I * (ζ θ T : ℂ)) • M θ T)‖ =
      ‖N θ T - (Real.cos (ζ θ T) : ℂ) • M θ T + (I * Real.sin (ζ θ T)) • 1‖ := by
  have hM := M_involution θ T hT
  have hExp := axis_mul_exp (M θ T) hM.1 hM.2 (ζ θ T)
  rw [smul_pow, smul_pow, N_odd_power θ T hodd, M_odd_power θ T hT hodd, smul_mul_assoc,
    ← smul_sub, hExp,
    norm_smul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
  congr 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  ring

/-- Line 3 of the display in (i): `‖N - M cos ζ + i sin ζ‖ = (‖N - M cos ζ‖² + sin² ζ)^{1/2}`, as
`(A + is)†(A + is) = A² + s²` and `A² = ‖A‖²` for the real combination `A = N - M cos ζ` of `X`
and `Z`. -/
theorem norm_axes_eq_sqrt (θ : ℝ) (T : ℕ) :
    ‖N θ T - (Real.cos (ζ θ T) : ℂ) • M θ T + (I * Real.sin (ζ θ T)) • 1‖ =
      Real.sqrt (‖N θ T - (Real.cos (ζ θ T) : ℂ) • M θ T‖ ^ 2 + Real.sin (ζ θ T) ^ 2) := by
  let a := Real.cos (θ / (2 * T)) - Real.cos (ζ θ T) * (2 * ρ θ T)⁻¹ * (Real.pi * T)
  let b := -Real.sin (θ / (2 * T)) + Real.cos (ζ θ T) * (2 * ρ θ T)⁻¹ * θ
  have hA : N θ T - (Real.cos (ζ θ T) : ℂ) • M θ T = a • X + b • Z := by
    ext i j
    simp only [N, M, a, b, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  rw [hA]
  exact xz_imaginary_norm a b (Real.sin (ζ θ T))

end DisplayLines

/-! ## Line 5 of the display in (i): `T ζ → θ²/(4π)` -/

section PhaseLimit

open Filter Topology Real

/-- If `x_n → 0`, `n x_n → a`, and `f'(0) = b`, then `n (f(x_n) - f(0)) → ab`. -/
theorem scaled_derivative_limit {f : ℝ → ℝ} {b a : ℝ} {x : ℕ → ℝ}
    (hf : HasDerivAt f b 0) (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (f (x n) - f 0)) atTop (𝓝 (a * b)) := by
  simpa using hf.hasFDerivAt.hasFDerivWithinAt.lim (s := Set.univ)
    (c := fun n : ℕ ↦ (n : ℝ)) hx (Eventually.of_forall fun _ ↦ Set.mem_univ _) ha

/-- `ζ = θ²/(2(2ρ + πT))`, multiplied by `T`: for `a > 0` and `t > 0`,
`t((a²t² + θ²)^{1/2}/2 - at/2) = θ²/(2((a² + (θ/t)²)^{1/2} + a))`. With `a = π` and `t = T` the left
side is `Tζ`. -/
theorem phase_defect_rationalized {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (θ : ℝ) :
    t * (Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) / 2 - a * t / 2) =
      θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a)) := by
  have hinside : a ^ 2 * t ^ 2 + θ ^ 2 = t ^ 2 * (a ^ 2 + (θ / t) ^ 2) := by
    field_simp
  have hroot : Real.sqrt (a ^ 2 * t ^ 2 + θ ^ 2) =
      t * Real.sqrt (a ^ 2 + (θ / t) ^ 2) := by
    rw [hinside, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hden : Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha)
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg (θ / t)))
  rw [hroot]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hden)).mpr
  calc
    t * (t * Real.sqrt (a ^ 2 + (θ / t) ^ 2) / 2 - a * t / 2) *
        (2 * (Real.sqrt (a ^ 2 + (θ / t) ^ 2) + a)) =
        t ^ 2 * ((Real.sqrt (a ^ 2 + (θ / t) ^ 2)) ^ 2 - a ^ 2) := by ring
    _ = θ ^ 2 := by rw [hs]; field_simp; ring

/-- `T((a²T² + θ²)^{1/2}/2 - aT/2) → θ²/(4a)` as `T → ∞`. Part (i) uses `a = π` and part (ii) uses
`a = 2π`. -/
theorem phase_defect_limit {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2))
      atTop (𝓝 (θ ^ 2 / (4 * a))) := by
  have hzero : Tendsto (fun T : ℕ ↦ θ / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat θ
  have hroot : Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2))
      atTop (𝓝 a) := by
    have harg : Tendsto (fun T : ℕ ↦ a ^ 2 + (θ / (T : ℝ)) ^ 2)
        atTop (𝓝 (a ^ 2)) := by
      simpa using (tendsto_const_nhds (x := a ^ 2)).add (hzero.pow 2)
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    rw [Real.sqrt_sq ha.le] at hs
    exact hs
  have hlim : Tendsto (fun T : ℕ ↦ θ ^ 2 /
      (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) atTop
      (𝓝 (θ ^ 2 / (2 * (a + a)))) :=
    tendsto_const_nhds.div ((hroot.add_const a).const_mul 2)
      (by positivity : 2 * (a + a) ≠ 0)
  have heq : (fun T : ℕ ↦ (T : ℝ) *
      (Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)) =ᶠ[atTop]
      (fun T : ℕ ↦ θ ^ 2 / (2 * (Real.sqrt (a ^ 2 + (θ / (T : ℝ)) ^ 2) + a))) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact phase_defect_rationalized ha (by exact_mod_cast hT) θ
  simpa only [show 2 * (a + a) = 4 * a by ring] using hlim.congr' heq.symm

/-- `(a²T² + θ²)^{1/2}/2 - aT/2 → 0` as `T → ∞`. -/
theorem phase_defect_tendsto_zero {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ Real.sqrt (a ^ 2 * (T : ℝ) ^ 2 + θ ^ 2) / 2 - a * T / 2)
      atTop (𝓝 0) := by
  have hp := (phase_defect_limit ha θ).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  field_simp

/-- Line 5 of the display in (i): `T ζ → θ²/(4π)`, as `ζ = θ²/(2(2ρ + πT))`. -/
theorem tendsto_mul_ζ (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) * ζ θ T) atTop (𝓝 (θ ^ 2 / (4 * π))) :=
  phase_defect_limit pi_pos θ

/-- `ζ → 0` as `T → ∞`. -/
theorem tendsto_ζ (θ : ℝ) : Tendsto (fun T : ℕ ↦ ζ θ T) atTop (𝓝 0) :=
  phase_defect_tendsto_zero pi_pos θ

/-- `n (a/n) → a`. -/
theorem scaled_div_limit (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (a / n)) atTop (𝓝 a) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- `n arctan(a/n) → a`. -/
theorem scaled_arctan_limit (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.arctan (a / n)) atTop (𝓝 a) := by
  simpa using scaled_derivative_limit (Real.hasDerivAt_arctan 0)
    (tendsto_const_div_atTop_nhds_zero_nat a) (scaled_div_limit a)

end PhaseLimit

/-! ## Line 4 of the display in (i): `T ‖N - M cos ζ‖ → (π-2)|θ|/(2π)` -/

section AxisLimit

open Filter Topology Real
open scoped Matrix.Norms.L2Operator

/-- `‖Z‖ = 1`. -/
theorem norm_Z : ‖Z‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr
    (by rw [show star Z = Z from Z_isHermitian]; exact Z_mul_Z))

/-- If `x_n → 0` and `n x_n → a`, then `n sin(x_n) → a`. -/
theorem scaled_sin_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.sin (x n)) atTop (𝓝 a) := by
  simpa only [Real.sin_zero, Real.cos_zero, sub_zero, mul_one] using
    scaled_derivative_limit (Real.hasDerivAt_sin 0) hx ha

/-- If `x_n → 0` and `n x_n → a`, then `n (cos(x_n) - 1) → 0`. -/
theorem scaled_cos_sub_one_limit {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 0))
    (ha : Tendsto (fun n : ℕ ↦ (n : ℝ) * x n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * (Real.cos (x n) - 1)) atTop (𝓝 0) := by
  simpa only [Real.cos_zero, Real.sin_zero, neg_zero, mul_zero] using
    scaled_derivative_limit (Real.hasDerivAt_cos 0) hx ha

/-- Line 4 of the display in (i), with the axes written by their angles: the axes of `N` and `M`
make the angle `α - β` with `α = θ/(2T)` and `β = arctan(θ/(πT))`, and
`T ‖(cos α X - sin α Z) - cos ζ (cos β X - sin β Z)‖ → (π-2)|θ|/(2π)`. -/
theorem odd_axis_norm_limit (θ : ℝ) :
    let α := fun n : ℕ ↦ θ / (2 * n)
    let β := fun n : ℕ ↦ Real.arctan (θ / (π * n))
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ‖(Real.cos (α n) • X - Real.sin (α n) • Z) -
      (Real.cos (ζ θ n) : ℂ) • (Real.cos (β n) • X - Real.sin (β n) • Z)‖)
      atTop (𝓝 ((π - 2) * |θ| / (2 * π))) := by
  intro α β
  have hα : Tendsto α atTop (𝓝 0) := by
    simpa [α, div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ / 2)
  have hnα : Tendsto (fun n : ℕ ↦ (n : ℝ) * α n) atTop (𝓝 (θ / 2)) := by
    simpa only [α, div_div] using scaled_div_limit (θ / 2)
  have hβ : Tendsto β atTop (𝓝 0) := by
    have hh := (Real.continuous_arctan.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (θ / π))
    simpa [β, div_div] using hh
  have hnβ : Tendsto (fun n : ℕ ↦ (n : ℝ) * β n) atTop (𝓝 (θ / π)) := by
    simpa only [β, div_div] using scaled_arctan_limit (θ / π)
  have hcα := scaled_cos_sub_one_limit hα hnα
  have hcβ := scaled_cos_sub_one_limit hβ hnβ
  have hcζ := scaled_cos_sub_one_limit (tendsto_ζ θ) (tendsto_mul_ζ θ)
  have hcβ0 : Tendsto (fun n ↦ Real.cos (β n)) atTop (𝓝 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp hβ
  have hsβ0 : Tendsto (fun n ↦ Real.sin (β n)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sin.tendsto 0).comp hβ
  -- The coefficient of `X`: `T(cos α - cos ζ cos β) → 0`.
  have hx := (hcα.sub hcβ).sub (hcζ.mul hcβ0)
  -- The coefficient of `Z`: `T(cos ζ sin β - sin α) → θ/π - θ/2`.
  have hz := ((scaled_sin_limit hβ hnβ).sub (scaled_sin_limit hα hnα)).add
    (hcζ.mul hsβ0)
  -- So `T(N - M cos ζ) → (θ/π - θ/2) Z`, of norm `(π-2)|θ|/(2π)`.
  have hv := (hx.smul_const X).add (hz.smul_const Z)
  have hh := hv.norm
  simp only [sub_zero, zero_mul, add_zero, zero_smul, zero_add,
    norm_smul, Real.norm_eq_abs, norm_Z, mul_one] at hh
  have habs : |θ / π - θ / 2| = (π - 2) * |θ| / (2 * π) := by
    rw [show θ / π - θ / 2 = -((π - 2) * θ / (2 * π)) by field_simp; ring,
      abs_neg, abs_div, abs_mul, abs_of_pos (by linarith [pi_gt_three] : 0 < π - 2),
      abs_of_pos (by positivity : 0 < 2 * π)]
  rw [habs] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro n
  have he : ((n : ℝ) * (Real.cos (α n) - 1) - n * (Real.cos (β n) - 1) -
        n * (Real.cos (ζ θ n) - 1) * Real.cos (β n)) • X +
      (n * Real.sin (β n) - n * Real.sin (α n) +
        n * (Real.cos (ζ θ n) - 1) * Real.sin (β n)) • Z =
      (n : ℝ) • ((Real.cos (α n) • X - Real.sin (α n) • Z) -
        (Real.cos (ζ θ n) : ℂ) • (Real.cos (β n) • X - Real.sin (β n) • Z)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  dsimp only
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)
      from Nat.cast_nonneg n)]

/-- Line 4 of the display in (i): `T ‖N - M cos ζ‖ → (π-2)|θ|/(2π)`. -/
theorem tendsto_axes_distance (θ : ℝ) :
    Tendsto (fun T : ℕ ↦ (T : ℝ) * ‖N θ T - (Real.cos (ζ θ T) : ℂ) • M θ T‖)
      atTop (𝓝 ((Real.pi - 2) * |θ| / (2 * Real.pi))) := by
  apply (odd_axis_norm_limit θ).congr'
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [M_eq_axis θ hT]
  rfl

end AxisLimit

section DerivativeNorm

open NormedSpace (exp)
open Complex (I)
open scoped Matrix.Norms.L2Operator

/-- `(e^{sA} X e^{-sA})' = e^{sA} (AX - XA) e^{-sA}`. -/
theorem conjugated_X_derivative (A : Matrix (Fin 2) (Fin 2) ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ exp (t • A) * X * exp (t • (-A)))
      (exp (s • A) * (A * X - X * A) * exp (s • (-A))) s := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) A s).mul_const X).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s)
  convert h using 1
  noncomm_ring

/-- `‖[-iθZ/2, X]‖ = |θ|`, as `X` and `Z` anticommute. -/
theorem frame_commutator_norm (θ : ℝ) :
    ‖(-(θ / 2 * I) • Z) * X - X * (-(θ / 2 * I) • Z)‖ = |θ| := by
  have hXZ : X * Z = -(Z * X) := eq_neg_of_add_eq_zero_left X_mul_Z_add_Z_mul_X
  have he : (-(θ / 2 * I) • Z) * X - X * (-(θ / 2 * I) • Z) =
      (-(θ * I)) • (Z * X) := by
    rw [smul_mul_assoc, mul_smul_comm, hXZ, smul_neg, sub_neg_eq_add, ← add_smul]
    congr 1
    ring
  have hX : ‖X‖ = 1 := CStarRing.norm_of_mem_unitary
    (Matrix.mem_unitaryGroup_iff.mpr (by rw [show star X = X from X_isHermitian]; exact X_mul_X))
  have hZ : Z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
    Matrix.mem_unitaryGroup_iff.mpr (by rw [show star Z = Z from Z_isHermitian]; exact Z_mul_Z)
  have hc : ‖-((θ : ℂ) * I)‖ = |θ| := by
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  calc
    _ = ‖-((θ : ℂ) * I)‖ * ‖Z * X‖ := by rw [he, norm_smul]
    _ = |θ| := by rw [hc, CStarRing.norm_mem_unitary_mul X hZ, hX, mul_one]

/-- Line 4 of the display in (i) uses `‖H'‖ = π|θ|/2`: for `ω ≥ 0`, `‖H'(s)‖ = ω|θ|/2` for
`s ∈ [0,1]`, one-sided at `0` and `1`. -/
theorem hamiltonian_derivWithin_norm {ω : ℝ} (hω : 0 ≤ ω) (θ : ℝ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    let H := fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (-(θ * t / 2 * I) • Z) * X * exp ((θ * t / 2 * I) • Z))
    ‖derivWithin H (Set.Icc (0 : ℝ) 1) s‖ = ω * |θ| / 2 := by
  intro H
  let A := -(θ / 2 * I) • Z
  have hH : H = fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (t • A) * X * exp (t • (-A))) := by
    funext t
    have hl : -(θ * t / 2 * I) • Z = t • A := by
      rw [show t • A = ((t : ℂ) * -(θ / 2 * I)) • Z by
        ext i j
        simp only [A, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
        ring]
      congr 1
      ring
    have hr : (θ * t / 2 * I) • Z = t • (-A) := by
      rw [smul_neg, ← hl, ← neg_smul]
      congr 1
      ring
    change (ω / 2 : ℝ) • (exp _ * X * exp _) = _
    rw [hl, hr]
  rw [hH]
  have hd : HasDerivAt (fun t : ℝ ↦ (ω / 2 : ℝ) •
      (exp (t • A) * X * exp (t • (-A))))
      ((ω / 2 : ℝ) • (exp (s • A) * (A * X - X * A) * exp (s • (-A)))) s :=
    (conjugated_X_derivative A s).const_smul (ω / 2 : ℝ)
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs), norm_smul]
  have hright : exp (s • (-A)) ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [smul_neg, ← neg_smul]
    exact frame_exp_mem_unitary θ (-s)
  rw [CStarRing.norm_mul_mem_unitary _ hright,
    CStarRing.norm_mem_unitary_mul _ (frame_exp_mem_unitary θ s), frame_commutator_norm,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hω (by norm_num))]
  ring

end DerivativeNorm

/-! ## The limit in (i) -/

section Limit

open Filter Topology Real
open scoped Matrix.Norms.L2Operator

/-- Together, lines 3, 4, and 5 give (i):
`(((π-2)|θ|/(2π))² + (θ²/(4π))²)^{1/2} = c₀ · π|θ| · (1 + θ²/(4(π-2)²))^{1/2}` with
`c₀ = 1/(2π) - 1/π²`. -/
theorem odd_limit_factored (θ : ℝ) :
    Real.sqrt (((π - 2) * |θ| / (2 * π)) ^ 2 + (θ ^ 2 / (4 * π)) ^ 2) =
      (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) *
        Real.sqrt (1 + θ ^ 2 / (4 * (π - 2) ^ 2)) := by
  have hp : 0 < π - 2 := by linarith [pi_gt_three]
  have hc : (1 / (2 * π) - 1 / π ^ 2) * (π * |θ|) =
      (π - 2) * |θ| / (2 * π) := by field_simp
  rw [hc]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simp only [div_pow, mul_pow, sq_abs]
  field_simp
  ring

end Limit

end RoundedClocks.PrecessingSpin
