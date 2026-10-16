/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.FrameDerivativeBounds

/-!
# Bounds on the series $\mathcal N$ and on the slope factor $S$

## Declarations

- `cos_quarter_inv_sq_le`
- `frameBound_le_pole`
- `frameBound_le_zero_ratio`
- `one_le_walkLogSlope`
- `walkLogSlope_half_le_jordan`
- `walkLogSlope_le_cos_quarter_inv_sq`
- `frameBound_eq_pf`
- `one_le_pnat_sq`
- `pf_den`
- `pf_le`
- `summable_pnat_pow`
- `tsum_pnat_inv_sq`
-/

@[expose] public section

open Real Set Complex UnitaryProducts.Corrector UnitaryProducts Filter
noncomputable section
namespace UnitaryProducts.Paper

private theorem one_le_pnat_sq (n : ℕ+) : (1:ℝ) ≤ (n:ℝ)^2 :=
  one_le_pow₀ (Nat.one_le_cast.mpr n.pos)

private theorem pf_den {n : ℕ+} {y : ℝ} (hy : y ^ 2 < 4 * π ^ 2) :
    0 < (4 * π^2-y ^ 2)*(n:ℝ)^2 ∧ (4 * π^2-y ^ 2)*(n:ℝ)^2 ≤ 4 * π^2*(n:ℝ)^2-y ^ 2 :=
  ⟨mul_pos (sub_pos.mpr hy) (zero_lt_one.trans_le (one_le_pnat_sq n)),
    by linarith [mul_le_mul_of_nonneg_left (one_le_pnat_sq n) (sq_nonneg y)]⟩

private theorem pf_le {n : ℕ+} {y : ℝ} (hy : y ^ 2 < 4 * π ^ 2) :
    2/(4 * π^2*(n:ℝ)^2-y ^ 2) ≤ 2/(4 * π^2-y ^ 2)*(1/(n:ℝ)^2) := by
  rw [div_mul_div_comm, mul_one]
  exact div_le_div_of_nonneg_left zero_le_two (pf_den hy).1 (pf_den hy).2

private theorem summable_pnat_pow {p : ℕ} (hp : 1 < p) :
    Summable (fun n : ℕ+ ↦ 1/(n:ℝ)^p) :=
  (Real.summable_one_div_nat_pow.mpr hp).comp_injective PNat.coe_injective

private theorem tsum_pnat_inv_sq : ∑' n : ℕ+, 1/(n:ℝ)^2 = π^2/6 := by
  have hz := (tsum_zero_pnat_eq_tsum_nat hasSum_zeta_two.summable).trans hasSum_zeta_two.tsum_eq
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_add] using hz

private theorem frameBound_eq_pf {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    frameBound w = ∑' n : ℕ+, 2/(4 * π^2*(n:ℝ)^2-w ^ 2) := by
  rw [← frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt ((abs_of_nonneg hw0).trans_lt hw)),
    ← frameBound_abs_eq_frameMult ((abs_of_nonneg hw0).trans_lt hw), abs_of_nonneg hw0]

/-- $\mathcal N(w) \le (\pi^2/3)/(4\pi^2 - w^2)$: termwise
$2/(4\pi^2n^2 - w^2) \le 2/(4\pi^2 - w^2) \cdot 1/n^2$, summed with $\zeta(2) = \pi^2/6$. -/
theorem frameBound_le_zero_ratio {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    frameBound w ≤ (π^2/3)/(4 * π^2-w ^ 2) := by
  have hy : w ^ 2 < 4 * π^2 := (sq_lt_sq' (by linarith [pi_pos]) hw).trans_eq (by ring)
  have hs : Summable (fun n : ℕ+ ↦ 2/(4 * π^2*(n:ℝ)^2-w ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ ↦ (div_pos two_pos ((pf_den hy).1.trans_le (pf_den hy).2)).le)
      (fun _ ↦ pf_le hy) ((summable_pnat_pow one_lt_two).mul_left _)
  rw [frameBound_eq_pf hw0 hw]
  refine (hs.tsum_le_tsum (fun _ ↦ pf_le hy)
    ((summable_pnat_pow one_lt_two).mul_left _)).trans_eq ?_
  rw [tsum_mul_left, tsum_pnat_inv_sq]; ring

/-- §4.3: $\mathcal N(w) \le \pi/(6(2\pi - w))$ on $[0, 2\pi)$, from
$4\pi^2 - w^2 \ge 2\pi(2\pi - w)$. -/
theorem frameBound_le_pole {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    frameBound w ≤ π/(6*(2*π-w)) := by
  have hθ : 0 < 2*π-w := sub_pos.mpr hw
  have hden : 2*π*(2*π-w) ≤ 4 * π^2-w ^ 2 := by linarith [mul_nonneg hw0 hθ.le]
  calc frameBound w ≤ (π^2/3)/(4 * π^2-w ^ 2) := frameBound_le_zero_ratio hw0 hw
    _ ≤ (π^2/3)/(2*π*(2*π-w)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos two_pi_pos hθ) hden
    _ = π/(6*(2*π-w)) := by
        rw [div_eq_div_iff (mul_pos two_pi_pos hθ).ne' (mul_pos (by norm_num) hθ).ne']; ring

/-- $S = (w/2)/\sin(w/2) \ge 1$ on $[0, 2\pi)$ (used as "$S \ge 1$" in the proof of Theorem
4.4(i)). -/
theorem one_le_walkLogSlope {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    1 ≤ walkLogSlope w := by
  rcases eq_or_lt_of_le hw0 with h | h
  · rw [← h, walkLogSlope_zero]
  · rw [walkLogSlope_eq_sinBound h hw, sinBound,
      one_le_div (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))]
    exact Real.sin_le (by linarith)

/-- $\cos^{-2}(w/4) \le S^2$, from $S(w) = S(w/2)/\cos(w/4)$ and $S(w/2) \ge 1$: Lemma A.2(ii)
and the constant of Theorem 4.4(i) are at most their forms with $S^2$ in place of $\cos^{-2}(w/4)$
(`exists_logarithm_with_derivative_bounds_sq`, `walkConstantChord_le`). -/
theorem cos_quarter_inv_sq_le {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (Real.cos (w/4))⁻¹^2 ≤ (walkLogSlope w)^2 := by
  rcases eq_or_lt_of_le hw0 with h | h
  · rw [← h, zero_div, Real.cos_zero, walkLogSlope_zero, inv_one]
  have hcos : 0 < Real.cos (w/4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hS : walkLogSlope w = walkLogSlope (w/2)/Real.cos (w/4) := by
    rw [walkLogSlope_eq_sinBound h hw, walkLogSlope_eq_sinBound (half_pos h) (by linarith),
      sinBound, sinBound, show w/2/2 = w/4 by ring, show w/2 = 2*(w/4) by ring, Real.sin_two_mul]
    ring
  refine pow_le_pow_left₀ (inv_nonneg.mpr hcos.le) ?_ 2
  rw [hS, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (one_le_walkLogSlope (by linarith) (by linarith)) hcos.le

/-- $S \le \cos^{-2}(w/4)$ on $[0, 2\pi)$, as $S\cos^2(w/4) = (w/4)\cot(w/4) \le 1$ by
$\tan x \ge x$ on $[0, \pi/2)$: it bounds the coefficients in the supporting common-coefficient
comparison:
$L$ and $M$ are bounded using the coefficient of $L^2$. -/
theorem walkLogSlope_le_cos_quarter_inv_sq {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    walkLogSlope w ≤ (Real.cos (w/4))⁻¹^2 := by
  rcases eq_or_lt_of_le hw0 with h | h
  · rw [← h, zero_div, Real.cos_zero, walkLogSlope_zero, inv_one, one_pow]
  have hcos : 0 < Real.cos (w/4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hsin4 : 0 < Real.sin (w/4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  -- S cos²(w/4) = ((w/4)cos(w/4))/sin(w/4) ≤ 1, from w/4 < tan(w/4).
  have hkey : walkLogSlope w*Real.cos (w/4)^2 = w/4*Real.cos (w/4)/Real.sin (w/4) := by
    rw [walkLogSlope_eq_sinBound h hw, sinBound, show w/2 = 2*(w/4) by ring, Real.sin_two_mul]
    field_simp
  rw [inv_pow, ← one_div, le_div_iff₀ (pow_pos hcos 2), hkey, div_le_one hsin4, ← le_div_iff₀ hcos,
    ← Real.tan_eq_sin_div_cos]
  exact (Real.lt_tan (by linarith) (by linarith)).le

end UnitaryProducts.Paper
