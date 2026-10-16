/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import UnitaryProducts.Corrector.FrameOperator

/-!
# The closed form of $\mathcal N$, and $\mathcal N(\mathrm{ad}_h)$ in an eigenbasis

## Declarations

- `frameBound_abs_eq_frameMult`
- `frameBound_zero`
- `frameMult`
- `frameSeries_ofReal_mul_I`
- `neg_one_pow_mul_bernoulli_two_mul_add_two`
- `entryCLM`
- `ad_power_eigenbasis_entry`
- `complex_smul_pow`
- `frameOp_eq_eigenbasis`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real

noncomputable section

namespace UnitaryProducts.Corrector

/-- The sign of the even Bernoulli numbers: `(-1)^k B_{2k+2} = |B_{2k+2}|`. -/
theorem neg_one_pow_mul_bernoulli_two_mul_add_two (k : ℕ) :
    (-1 : ℝ) ^ k * ((bernoulli (2 * k + 2) : ℚ) : ℝ) = |((bernoulli (2 * k + 2) : ℚ) : ℝ)| := by
  rw [show 2 * k + 2 = 2 * (k + 1) by ring, abs_bernoulli_two_mul (k := k + 1) k.succ_ne_zero]
  ring

/-- **The frame series at a purely imaginary argument is real**: `frameSeries (x i) = 𝔫(|x|)`,
term by term (odd Bernoulli numbers vanish, even ones alternate in sign). -/
theorem frameSeries_ofReal_mul_I (x : ℝ) :
    frameSeries ((x : ℂ) * Complex.I) = (frameBound |x| : ℂ) := by
  rw [frameSeries, frameBound, Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have hsign := neg_one_pow_mul_bernoulli_two_mul_add_two k
    have hpow : ((x : ℂ) * Complex.I) ^ (k + k) = (((-1 : ℝ) ^ k * x ^ (k + k) : ℝ) : ℂ) := by
      rw [← two_mul, pow_mul, mul_pow, Complex.I_sq]; push_cast; ring
    rw [hpow, smul_eq_mul, Even.pow_abs ⟨k, rfl⟩ x, show k + k + 2 = 2 * k + 2 by ring, ← hsign]
    push_cast; ring
  · subst hk
    rw [bernoulli_eq_bernoulli'_of_ne_one (by omega),
      bernoulli'_eq_zero_of_odd ⟨k + 1, by ring⟩ (by omega)]
    simp

/-- The paper's definition (eq:N-def, §4.1) of $\mathcal N$:
$(1 - (x/2)\cot(x/2))/x^2$, with its limit $1/12$ at $x = 0$. It equals
$\sum_{n \ge 1} 2/(4\pi^2n^2 - x^2)$ off $2\pi\mathbb Z \setminus \{0\}$
(`frameMult_eq_partialFractions`, `Comparison/UnitSteps.lean`) and `frameBound |x|` for
$|x| < 2\pi$ (`frameBound_abs_eq_frameMult`). At a pole $x = 2\pi n$, $n \ne 0$, Lean's `cot` is
$\cos/\sin$ with $\cos/0 = 0$, so `frameMult x` $= 1/x^2$ there: a junk value, where the paper's
$\mathcal N$ is undefined. -/
def frameMult (x : ℝ) : ℝ :=
  if x = 0 then 1 / 12 else (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2

/-- $\mathcal N(0) = 1/12$: the constant term of the Bernoulli series, $|B_2|/2!$. -/
theorem frameBound_zero : frameBound 0 = 1 / 12 := by
  rw [frameBound, tsum_eq_single 0]
  · norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_two, Nat.factorial]
  · intro n hn
    simp [zero_pow hn]

/-- **The majorant is the multiplier's closed form**: `𝔫(|x|) = θ(x)` for `|x| < 2π`. -/
theorem frameBound_abs_eq_frameMult {x : ℝ} (hx : |x| < 2 * π) :
    frameBound |x| = frameMult x := by
  unfold frameMult
  split_ifs with h0
  · rw [h0, abs_zero, frameBound_zero]
  · rcases lt_or_gt_of_ne h0 with hneg | hpos
    · rw [abs_of_neg hneg] at hx ⊢
      rw [frameBound_eq_closedForm (by linarith) hx, neg_div, Real.cot_eq_cos_div_sin,
        Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg, div_neg]
      ring
    · rw [abs_of_pos hpos] at hx ⊢
      exact frameBound_eq_closedForm hpos hx

end UnitaryProducts.Corrector

namespace UnitaryProducts

open UnitaryProducts.Corrector Complex Matrix Set

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The `(a, b)` entry as a continuous linear functional. -/
def entryCLM (a b : Fin d) : 𝕄 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)

namespace Paper.UnitStepsProse

/-- Section 4, the display preceding (ps-norm): every commutator power acts by the power
of the eigenvalue difference in the chosen eigenbasis. -/
theorem ad_power_eigenbasis_entry (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄)
    (n : ℕ) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * ((adL Ω) ^ n) D * U) p q =
      ((hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) : ℂ) ^ n * (star U * D * U) p q := by
  intro U
  let e := Unitary.conjStarAlgAut ℂ 𝕄 (star hΩ.eigenvectorUnitary)
  have he (X : 𝕄) : e X = star U * X * U := by
    simp only [e, U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]
  have hΩe := hΩ.conjStarAlgAut_star_eigenvectorUnitary
  change e Ω = Matrix.diagonal (fun p ↦ (hΩ.eigenvalues p : ℂ)) at hΩe
  simp only [← he]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, adL_apply, map_sub, map_mul, map_mul,
      hΩe]
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [ih, pow_succ]
    push_cast
    ring

end Paper.UnitStepsProse

namespace Prose

/-- Section 4, the scalar factor of an operator power, in a generic normed algebra. -/
theorem complex_smul_pow {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (z : ℂ) (a : A) (n : ℕ) : (z • a) ^ n = z ^ n • a ^ n := smul_pow z a n

end Prose

/-- **The frame operator in an eigenbasis.**  For `h` Hermitian with eigenvalues in an interval
of length `w < 2π`, with `U` the unitary of eigenvectors and `λ` the eigenvalues,
`N_h(D) = U · [θ(λ_a − λ_b) (U† D U)_{ab}] · U†`: in the eigenbasis of `h` the frame operator
multiplies the `(a, b)` entry by `θ(λ_a − λ_b)`. -/
theorem frameOp_eq_eigenbasis {h : 𝕄} (hh : h.IsHermitian) {m w : ℝ}
    (hw : w < 2 * π) (hev : ∀ i, hh.eigenvalues i ∈ Icc m (m + w)) (D : 𝕄) :
    frameOp h D
      = (hh.eigenvectorUnitary : 𝕄)
          * Matrix.of (fun a b ↦ (frameMult (hh.eigenvalues a - hh.eigenvalues b) : ℂ)
              * (star (hh.eigenvectorUnitary : 𝕄) * D * hh.eigenvectorUnitary) a b)
          * star (hh.eigenvectorUnitary : 𝕄) := by
  ext a b : 2
  letI : NeZero d := ⟨a.pos.ne'⟩
  apply congrArg (fun X : 𝕄 ↦ X a b)
  let U : 𝕄 := hh.eigenvectorUnitary
  -- the width hypothesis in the operator form used by the series
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by linarith [(hev 0).1, (hev 0).2]
  have hwidth : ‖h - (((m + w / 2 : ℝ)) : ℂ) • 1‖ ≤ w / 2 :=
    norm_sub_smul_one_le_of_eigenvalues hh hw0 hev
  have hA : ‖I • adL h‖ < 2 * π :=
    lt_of_le_of_lt ((norm_I_smul_adL_le h _).trans (by linarith)) hw
  have hsum : Summable (fun n : ℕ ↦
      (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • (I • adL h) ^ n) :=
    (summable_norm_frameSeries_terms (I • adL h) hA).of_norm
  set D' : 𝕄 := star U * D * U with hD'
  set x : Fin d → Fin d → ℂ :=
    fun a b ↦ ((hh.eigenvalues a - hh.eigenvalues b : ℝ) : ℂ) * I with hx
  have hfin (M : 𝕄) : U * (star U * M * U) * star U = M :=
    (Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary).apply_symm_apply M
  -- the frame operator, conjugated back into the eigenbasis, is the scalar series entrywise
  have hkey : star U * frameOp h D * U
      = Matrix.of (fun a b ↦ frameSeries (x a b) * D' a b) := by
    ext a b
    have hsumD : Summable (fun n : ℕ ↦ (ContinuousLinearMap.apply ℂ 𝕄 D)
        ((((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • (I • adL h) ^ n)) :=
      (ContinuousLinearMap.apply ℂ 𝕄 D).summable hsum
    have e := ((entryCLM a b).comp (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).map_tsum hsumD
    simp only [ContinuousLinearMap.comp_apply,
      show ∀ M : 𝕄, entryCLM a b M = M a b from fun _ ↦ rfl,
      ContinuousLinearMap.mulLeftRight_apply,
      ContinuousLinearMap.apply_apply] at e
    rw [Matrix.of_apply, frameOp, frameSeries, frameSeries, tsum_apply_of_summable hsum, e,
      ← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    rw [ContinuousLinearMap.smul_apply, Prose.complex_smul_pow I (adL h) n,
      ContinuousLinearMap.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
      Paper.UnitStepsProse.ad_power_eigenbasis_entry]
    simp only [hx, hD', mul_pow, smul_eq_mul]
    ring
  rw [← hfin (frameOp h D), hkey]
  congr 2
  ext a b
  have hab : |hh.eigenvalues a - hh.eigenvalues b| < 2 * π :=
    abs_lt.mpr ⟨by linarith [(hev a).1, (hev b).2], by linarith [(hev a).2, (hev b).1]⟩
  simp only [Matrix.of_apply, hx, frameSeries_ofReal_mul_I, frameBound_abs_eq_frameMult hab]

end UnitaryProducts
