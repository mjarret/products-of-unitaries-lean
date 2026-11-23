/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # The scalar multiplier guessed in the proof of Lemma A.1

The manuscript sets `Y(τ) = 𝒩_τ([Ω,·]) D`. The scalar multiplier
`𝒩_τ(x)` satisfies `∂_τ 𝒩_τ(x) + i x 𝒩_τ(x) = τ`, is `C¹` in `τ`, and equals `𝒩(x)` at
`τ = ±1/2`.
-/

@[expose] public section

namespace RoundedClocks

open Complex

/-- The scalar multiplier `𝒩_τ(x)` guessed in the proof of Lemma A.1. -/
noncomputable def cellMultiplier (τ x : ℝ) : ℂ :=
  if x = 0 then (τ : ℂ) ^ 2 / 2 - 1 / 24 else
    (1 - Complex.I * (x : ℂ) * (τ : ℂ)) / (x : ℂ) ^ 2 -
      Complex.exp (-Complex.I * (x : ℂ) * (τ : ℂ)) / (2 * (x : ℂ) * (Real.sin (x / 2) : ℂ))

/-- The real embedding into the complex numbers has derivative one. -/
private lemma hasDerivAt_ofReal' (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id' t).ofReal_comp

/-- Differentiating the displayed scalar guess gives `∂_τ 𝒩_τ + i x 𝒩_τ = τ`. -/
theorem cellMultiplier_derivative (x τ : ℝ) :
    HasDerivAt (fun s : ℝ ↦ cellMultiplier s x)
      ((τ : ℂ) - Complex.I * (x : ℂ) * cellMultiplier τ x) τ := by
  by_cases hx : x = 0
  · subst x
    have h := (((hasDerivAt_ofReal' τ).pow 2).div_const (2 : ℂ)).sub_const (1 / 24 : ℂ)
    convert h using 1 <;> norm_num [cellMultiplier]
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    let c : ℂ := -1 / (2 * (x : ℂ) * (Real.sin (x / 2) : ℂ))
    let y : ℝ → ℂ := fun s ↦
      (1 / (x : ℂ) ^ 2 - Complex.I * (s : ℂ) / x) +
        c * Complex.exp (-Complex.I * (x : ℂ) * (s : ℂ))
    have ht := hasDerivAt_ofReal' τ
    have hy : HasDerivAt y ((τ : ℂ) - Complex.I * x * y τ) τ := by
      have h :=
        (((ht.const_mul Complex.I).div_const (x : ℂ)).const_sub (1 / (x : ℂ) ^ 2)).add
          ((((ht.const_mul (-Complex.I * (x : ℂ)))).cexp).const_mul c)
      convert h using 1
      have hinv : (x : ℂ) * (x : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hxC
      simp only [y]
      linear_combination ((τ : ℂ) * Complex.I ^ 2 - Complex.I * (x : ℂ)⁻¹) * hinv +
        (τ : ℂ) * Complex.I_sq
    have heq (s : ℝ) : cellMultiplier s x = y s := by
      rw [cellMultiplier, if_neg hx]
      dsimp only [y, c]
      field_simp
      ring
    simpa only [heq] using hy

/-- The multiplier is `C¹` in `τ`. -/
theorem cellMultiplier_contDiff (x : ℝ) : ContDiff ℝ 1 (fun τ : ℝ ↦ cellMultiplier τ x) := by
  have hd : Differentiable ℝ (fun τ : ℝ ↦ cellMultiplier τ x) :=
    fun τ ↦ (cellMultiplier_derivative x τ).differentiableAt
  rw [contDiff_one_iff_deriv]
  refine ⟨hd, ?_⟩
  have : deriv (fun τ : ℝ ↦ cellMultiplier τ x) =
      fun τ : ℝ ↦ (τ : ℂ) - Complex.I * (x : ℂ) * cellMultiplier τ x :=
    funext fun τ ↦ (cellMultiplier_derivative x τ).deriv
  rw [this]
  exact Complex.continuous_ofReal.sub (continuous_const.mul hd.continuous)

/-- Inside the admissible arc, `sin(x/2)` is nonzero away from `x = 0`. -/
private lemma sin_half_ne_zero_of_abs_lt {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 * Real.pi) :
    Real.sin (x / 2) ≠ 0 := by
  rcases lt_or_gt_of_ne hx0 with hn | hp
  · have hs : 0 < Real.sin ((-x) / 2) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by have := (abs_lt.mp hx).1; linarith)
    rw [show x / 2 = -((-x) / 2) by ring, Real.sin_neg]
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by have := (abs_lt.mp hx).2; linarith)).ne'

/-- Both endpoint values of the scalar guess are the multiplier `𝒩(x)`. -/
theorem cellMultiplier_endpoints {x : ℝ} (hx : |x| < 2 * Real.pi) :
    cellMultiplier (-1 / 2) x = (𝒩 x : ℂ) ∧ cellMultiplier (1 / 2) x = (𝒩 x : ℂ) := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [cellMultiplier, 𝒩]
  · have hs := sin_half_ne_zero_of_abs_lt hx0 hx
    have hsC : Complex.sin ((x : ℂ) / 2) ≠ 0 := by
      have := Complex.ofReal_ne_zero.mpr hs
      push_cast at this
      exact this
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0
    have eplus : Complex.exp (-Complex.I * (x : ℂ) * (1 / 2 : ℂ)) =
        Complex.cos (x / 2) - Complex.sin (x / 2) * Complex.I := by
      rw [show -Complex.I * (x : ℂ) * (1 / 2 : ℂ) = -((x : ℂ) / 2) * Complex.I by
        ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    have eminus : Complex.exp (-Complex.I * (x : ℂ) * (-1 / 2 : ℂ)) =
        Complex.cos (x / 2) + Complex.sin (x / 2) * Complex.I := by
      rw [show -Complex.I * (x : ℂ) * (-1 / 2 : ℂ) = (x : ℂ) / 2 * Complex.I by
        ring, Complex.exp_mul_I]
    rw [𝒩, if_neg hx0, Real.cot_eq_cos_div_sin]
    simp only [cellMultiplier, if_neg hx0]
    push_cast
    rw [eminus, eplus]
    constructor <;> field_simp <;> ring

end RoundedClocks
