/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogarithmBounds

/-!
# the spectral comparison and supporting bounds for the walk comparison

## Declarations

- `cubicSlopePair_self_eq_tail`
- `cubicSlopeTail`
- `cubicSlopeTail_add_left`
- `cubicSlopeTail_add_right`
- `cubic_geometric_tail_le`
- `exists_hasDerivAt_frameOp_walk_sharp`
- `frameBound_eq_closed`
- `frameBound_sub_div_eq_integral`
- `frameLip_eq_closed`
- `norm_cubicFrameSeriesDerivative_blocks_sharp`
- `norm_cubicFrameSlope_le_inverse_sharp`
- `norm_cubicSlopePair_self_le_sharp`
- `norm_cubicSlopeTail_full`
- `norm_cubicSlopeTail_input_diag`
- `unit_step_walk_comparison_chord`
- `walkConstant`
- `walkConstantChord`
- `walkConstantChord_eq`
- `walkFrameSharp`
- `walkFrameSharp_nonneg`
- `walkUnitCoefficientChord`
- `walkUnitCoefficientSharp`
- `walk_c0_bounds`
- `walk_constant_chord_limit`
- `walk_constant_limit`
- `walk_frame_jumps_sharp`
- `walk_transfer_sharp`
- `walk_unit_comparison_chord`
- `walk_unit_comparison_of_coeff`
- `walk_unit_comparison_sharp`
- `meshMoment_le_sSup_pow`
- `paper_mean_slope_eq`
- `sSup_norm_le_of_subset`
- `tendsto_mul_frameBound_half`
- `tendsto_nhdsGT_of_continuousAt`
- `walk_asymptotics`
- `walk_reflect`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter UnitaryProducts.Corrector
noncomputable section

namespace UnitaryProducts.Paper
open UnitaryProducts

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The degree-`n+1` contribution without its last term `j = n`, i.e. without the term in
which the varied commutator acts on the input directly. -/
def cubicSlopeTail (h D X : 𝕄) (n : ℕ) : 𝕄 :=
  ∑ j ∈ Finset.range n, ((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))

/-- `cubicSlopeTail` is additive in the varied Hamiltonian `D`. -/
theorem cubicSlopeTail_add_left (h D E X : 𝕄) (n : ℕ) :
    cubicSlopeTail h (D + E) X n = cubicSlopeTail h D X n + cubicSlopeTail h E X n := by
  have hadd : adL (D + E) = adL D + adL E := by
    ext1 Y; simp only [ContinuousLinearMap.add_apply, adL_apply]; noncomm_ring
  simp only [cubicSlopeTail, hadd, smul_add, ContinuousLinearMap.add_apply,
    map_add, Finset.sum_add_distrib]

/-- `cubicSlopeTail` is additive in the input `X`. -/
theorem cubicSlopeTail_add_right (h D X Y : 𝕄) (n : ℕ) :
    cubicSlopeTail h D (X + Y) n = cubicSlopeTail h D X n + cubicSlopeTail h D Y n := by
  simp only [cubicSlopeTail, map_add, Finset.sum_add_distrib]

/-- $\mathrm{ad}_X X = 0$: the term of `cubicSlopePair h X X n` in which $\mathrm{ad}_X$ acts on $X$
vanishes (the cancellation $\mathrm{ad}_{\Lambda'}\Lambda' = 0$ in the proof of the spectral
comparison). -/
theorem cubicSlopePair_self_eq_tail (h X : 𝕄) (n : ℕ) :
    cubicSlopePair h X X n = cubicSlopeTail h X X n := by
  have hlast : ((I • adL h) ^ n) ((I • adL X) (((I • adL h) ^ (n - n)) X)) = 0 := by
    rw [Nat.sub_self, pow_zero, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, adL_apply, sub_self, smul_zero, map_zero]
  unfold cubicSlopePair cubicSlopeTail
  rw [Finset.sum_range_succ, hlast, add_zero]

/-- The tail geometric sum: `∑_{j<n} w^j (w/2)^{n-j} ≤ wⁿ`. -/
theorem cubic_geometric_tail_le {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    (∑ j ∈ Finset.range n, w ^ j * (w / 2) ^ (n - j)) ≤ w ^ n := by
  cases n with
  | zero => simp
  | succ m =>
    have heq : (∑ j ∈ Finset.range (m + 1), w ^ j * (w / 2) ^ (m + 1 - j)) =
        (w / 2) * ∑ j ∈ Finset.range (m + 1), w ^ j * (w / 2) ^ (m - j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j hj ↦ by
        rw [Nat.succ_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), pow_succ]; ring
    rw [heq]
    calc
      (w / 2) * ∑ j ∈ Finset.range (m + 1), w ^ j * (w / 2) ^ (m - j) ≤ (w / 2) * (2 * w ^ m) :=
        mul_le_mul_of_nonneg_left (cubic_geometric_sum_reverse_le hw m) (by positivity)
      _ = w ^ (m + 1) := by rw [pow_succ]; ring

/-- The block-diagonal variation over the `n` remaining terms, at full width $w$ (the row
$2n\|B\|\|\Lambda'\|w^{n-1}$ in the proof of the spectral comparison, indexed one lower). -/
theorem norm_cubicSlopeTail_full {h D X : 𝕄} {w : ℝ} (ha : ‖I • adL h‖ ≤ w) (n : ℕ) :
    ‖cubicSlopeTail h D X n‖ ≤ 2 * ‖D‖ * ‖X‖ * n * w ^ n := by
  have hw : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  unfold cubicSlopeTail
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
        2 * ‖D‖ * ‖X‖ * w ^ n := by
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    calc
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
          w ^ j * ‖(I • adL D) (((I • adL h) ^ (n - j)) X)‖ :=
        cubic_norm_pow_apply_le ha _ _
      _ ≤ w ^ j * (2 * ‖D‖ * ‖((I • adL h) ^ (n - j)) X‖) := by
        gcongr; exact cubic_norm_commutator_le _ _
      _ ≤ w ^ j * (2 * ‖D‖ * (w ^ (n - j) * ‖X‖)) := by
        gcongr; exact cubic_norm_pow_apply_le ha _ _
      _ = 2 * ‖D‖ * ‖X‖ * w ^ n := by
        rw [show w ^ n = w ^ j * w ^ (n - j) by rw [← pow_add, Nat.add_sub_of_le hjn]]; ring
  refine (norm_sum_le_of_le _ hterm).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- An off-diagonal variation acting on a block-diagonal input over the `n` remaining terms:
the inner powers are narrow and every term has at least one, so the sum is at most `wⁿ`. -/
theorem norm_cubicSlopeTail_input_diag {h J D X : 𝕄} {c w : ℝ} (hh : Commute J h) (hX : Commute J X)
    (ha : ‖I • adL h‖ ≤ w) (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4) (n : ℕ) :
    ‖cubicSlopeTail h D X n‖ ≤ 2 * ‖D‖ * ‖X‖ * w ^ n := by
  have hw : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  unfold cubicSlopeTail
  have hterm (j : ℕ) :
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
        (2 * ‖D‖ * ‖X‖) * (w ^ j * (w / 2) ^ (n - j)) := by
    calc
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
          w ^ j * ‖(I • adL D) (((I • adL h) ^ (n - j)) X)‖ :=
        cubic_norm_pow_apply_le ha _ _
      _ ≤ w ^ j * (2 * ‖D‖ * ‖((I • adL h) ^ (n - j)) X‖) := by
        gcongr; exact cubic_norm_commutator_le _ _
      _ ≤ w ^ j * (2 * ‖D‖ * ((w / 2) ^ (n - j) * ‖X‖)) := by
        gcongr; exact cubic_narrow_pow_le hh hX hsmall (n - j)
      _ = _ := by ring
  refine (norm_sum_le_of_le _ (fun j _ ↦ hterm j)).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (cubic_geometric_tail_le hw n) (by positivity)

variable [NeZero d]

omit [NeZero d] in
/-- The block estimate in the proof of the spectral comparison, with the vanishing term removed: the
off-diagonal variation acting on the block-diagonal part costs $2\|E\|\|B\|w^n$, which
$\|E\| \le \|\Lambda'\|$ merges into the diagonal row. Here `cubicDiag J D`, `cubicOff J D` are the
paper's $B$, $E$. -/
theorem norm_cubicSlopePair_self_le_sharp {h J D : 𝕄} {c w : ℝ}
    (hJJ : J * J = 1) (hJn : ‖J‖ ≤ 1) (hh : Commute J h)
    (ha : ‖I • adL h‖ ≤ w) (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4) (n : ℕ) :
    ‖cubicSlopePair h D D n‖ ≤
      2 * ‖cubicDiag J D‖ * ‖D‖ * (n + 1) * w ^ n + 4 * ‖cubicOff J D‖ ^ 2 * w ^ n := by
  have hw : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  let A := cubicDiag J D
  let B := cubicOff J D
  have hA : Commute J A := cubicDiag_commute J D hJJ
  have hB : J * B = -(B * J) := cubicOff_anticommute J D hJJ
  have hd : D = A + B := (cubicDiag_add_cubicOff J D).symm
  have hBD : ‖B‖ ≤ ‖D‖ := norm_cubicOff_le J D hJn
  have heq : cubicSlopePair h D D n =
      cubicSlopeTail h A D n + (cubicSlopeTail h B A n + cubicSlopeTail h B B n) := by
    rw [cubicSlopePair_self_eq_tail, hd, cubicSlopeTail_add_left, cubicSlopeTail_add_right,
      cubicSlopeTail_add_right]
  have hBB : ‖cubicSlopeTail h B B n‖ ≤ 4 * ‖B‖ * ‖B‖ * w ^ n := by
    rw [← cubicSlopePair_self_eq_tail]
    exact norm_cubicSlopePair_off_off hh hB hB ha hsmall n
  rw [heq]
  calc
    ‖cubicSlopeTail h A D n + (cubicSlopeTail h B A n + cubicSlopeTail h B B n)‖ ≤
        ‖cubicSlopeTail h A D n‖ +
          (‖cubicSlopeTail h B A n‖ + ‖cubicSlopeTail h B B n‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 2 * ‖A‖ * ‖D‖ * n * w ^ n + (2 * ‖B‖ * ‖A‖ * w ^ n + 4 * ‖B‖ * ‖B‖ * w ^ n) :=
      add_le_add (norm_cubicSlopeTail_full ha n)
        (add_le_add (norm_cubicSlopeTail_input_diag hh hA ha hsmall n) hBB)
    _ ≤ 2 * ‖A‖ * ‖D‖ * n * w ^ n + (2 * ‖D‖ * ‖A‖ * w ^ n + 4 * ‖B‖ * ‖B‖ * w ^ n) := by
      gcongr
    _ = _ := by dsimp [A, B]; ring

/-- Summing the two rows against the coefficients of the corrector series (proof of the spectral
comparison): the
derivative term is at most $2\|B\|\|D\|\mathcal N'(w) + 4\|E\|^2(\mathcal N(w) - \mathcal N(0))/w$.
-/
theorem norm_cubicFrameSeriesDerivative_blocks_sharp {h J D : 𝕄} {c w : ℝ}
    (hw : w < 2 * π) (hJJ : J * J = 1) (hJn : ‖J‖ ≤ 1) (hh : Commute J h)
    (ha : ‖I • adL h‖ ≤ w) (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4) :
    ‖cubicFrameSeriesDerivative (I • adL h) (I • adL D) D‖ ≤
      2 * ‖cubicDiag J D‖ * ‖D‖ * frameLip w +
      4 * ‖cubicOff J D‖ ^ 2 * ((frameBound w - 1 / 12) / w) := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  let β : ℝ := 2 * ‖cubicDiag J D‖ * ‖D‖
  let γ : ℝ := 4 * ‖cubicOff J D‖ ^ 2
  let φ : ℝ → ℕ → ℝ := fun x n ↦
    |((bernoulli (n + 3) : ℚ) : ℝ)| * ((n : ℝ) + 1) * x ^ n /
      (Nat.factorial (n + 3) : ℝ)
  let ψ : ℝ → ℕ → ℝ := fun x n ↦
    |((bernoulli (n + 3) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 3) : ℝ)
  have hs₂ : Summable (fun n ↦ β * φ w n) :=
    (summable_frameLip_shifted hw0 hw).mul_left β
  have hs₃ : Summable (fun n ↦ γ * ψ w n) :=
    (summable_frameBound_tail_div_nonneg hw0 hw).mul_left γ
  have hnorm := summable_norm_cubicFrameSlope_terms h D D (ha.trans_lt hw)
  have hterm (n : ℕ) :
      ‖(((bernoulli (n + 3) : ℚ) : ℂ) / (Nat.factorial (n + 3) : ℂ)) •
        cubicSlopePair h D D n‖ ≤ β * φ w n + γ * ψ w n := by
    rw [norm_smul]
    have hc : ‖(((bernoulli (n + 3) : ℚ) : ℂ) / (Nat.factorial (n + 3) : ℂ))‖ =
        |((bernoulli (n + 3) : ℚ) : ℝ)| / (Nat.factorial (n + 3) : ℝ) :=
      norm_frame_coefficient (n + 1)
    rw [hc]
    exact (mul_le_mul_of_nonneg_left (norm_cubicSlopePair_self_le_sharp hJJ hJn hh ha hsmall n)
      (by positivity)).trans_eq (by dsimp [β, γ, φ, ψ]; ring)
  rw [cubicFrameSeriesDerivative_apply h D D (ha.trans_lt hw)]
  calc
    _ ≤ ∑' n : ℕ,
        ‖(((bernoulli (n + 3) : ℚ) : ℂ) / (Nat.factorial (n + 3) : ℂ)) •
          cubicSlopePair h D D n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (β * φ w n + γ * ψ w n) :=
      hnorm.tsum_le_tsum hterm (hs₂.add hs₃)
    _ = _ := by
      rw [hs₂.tsum_add hs₃, tsum_mul_left, tsum_mul_left]
      change β * (∑' n, φ w n) + γ * (∑' n, ψ w n) = _
      rw [show (∑' n, φ w n) = frameLip w from tsum_frameLip_shifted hw0 hw,
        show (∑' n, ψ w n) = (frameBound w - 1 / 12) / w from
          tsum_frameBound_tail_div_nonneg hw0 hw]

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts

/-- The coefficient $\eta = 2S(\kappa\mathcal N'(w) + 2S\int_0^1\mathcal N'(tw)\,dt)$ of the
spectral comparison,
with $S$ = `walkLogSlope w`, $\kappa$ = `walkLogSlope (w/2)`, $\mathcal N$ = `frameBound` and
$\mathcal N'$ = `frameLip`. The mean slope $\int_0^1\mathcal N'(tw)\,dt$ is written here as
$(\mathcal N(w) - 1/12)/w$ (`frameBound_sub_div_eq_integral`); both are `0` at $w = 0$
(`x / 0 = 0`). Every use assumes $0 \le w < 2\pi$, where the series converge. -/
def walkFrameSharp (w : ℝ) : ℝ :=
  2*walkLogSlope (w/2)*walkLogSlope w*frameLip w+
    4*(walkLogSlope w)^2*(frameBound w-1/12)/w

/-- $\eta \ge 0$ on $[0, 2\pi)$. -/
theorem walkFrameSharp_nonneg {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ walkFrameSharp w := by
  have hS := walkLogSlope_nonneg hw0 hw
  have hk := walkLogSlope_nonneg (show 0 ≤ w/2 by linarith) (show w/2 < 2*π by linarith)
  have hL := frameLip_nonneg hw0
  have hN := sub_nonneg.mpr (one_div_twelve_le_frameBound hw0 hw)
  unfold walkFrameSharp
  positivity

/-- The endpoint coefficient satisfies $0≤c_0≤\mathcal N(w)$; useful for common-coefficient
bounds. -/
theorem walk_c0_bounds {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    0 ≤ frameBound w-frameBound (w/2)/2 ∧ frameBound w-frameBound (w/2)/2 ≤ frameBound w := by
  have hh0 : 0 ≤ w/2 := div_nonneg hw0 two_pos.le
  have hmono := frameBound_mono hh0 (half_le_self hw0) hw
  have hnn := frameBound_nonneg hh0
  exact ⟨sub_nonneg.mpr ((half_le_self hnn).trans hmono), sub_le_self _ (div_nonneg hnn two_pos.le)⟩

/-- The mean slope of $\mathcal N$ on $[0, w]$ (the spectral comparison):
$\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ for $0 \le w < 2\pi$, both sides $0$ at
$w = 0$. The proof substitutes $x = tw$ and integrates $\mathcal N' = $ `frameLip`, the derivative
of $\mathcal N$ = `frameBound` (`hasDerivAt_frameBound`), from $\mathcal N(0) = 1/12$; $\mathcal N'$
is integrable as a nonnegative derivative. -/
theorem frameBound_sub_div_eq_integral {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (frameBound w - 1/12)/w = ∫ t in (0:ℝ)..1, frameLip (t*w) := by
  rcases eq_or_lt_of_le hw0 with h | h
  · -- At `w = 0` both sides are `0`: `x / 0 = 0`, and `𝒩'(0) = 0`.
    subst h
    simp only [div_zero, mul_zero, cubic_frameLip_zero, intervalIntegral.integral_zero]
  · have hw' : w ≠ 0 := h.ne'
    rw [intervalIntegral.integral_comp_mul_right frameLip hw', zero_mul, one_mul, smul_eq_mul]
    have hder : ∀ x ∈ uIcc (0:ℝ) w, HasDerivAt frameBound (frameLip x) x := by
      intro x hx
      rw [uIcc_of_le hw0] at hx
      exact hasDerivAt_frameBound (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
    have hint : IntervalIntegrable frameLip volume 0 w := by
      refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := frameBound)
        (fun x hx ↦ (hder x hx).continuousAt.continuousWithinAt) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · rw [min_eq_left hw0, max_eq_right hw0] at hx
        exact hder x (by rw [uIcc_of_le hw0]; exact Ioo_subset_Icc_self hx)
      · rw [min_eq_left hw0, max_eq_right hw0] at hx
        exact frameLip_nonneg hx.1.le
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, frameBound_zero]
    field_simp

/-- The paper's series $\mathcal N(x) = \sum_{n\ge1}2/(4\pi^2n^2 - x^2)$ has mean slope
$\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ on $[0, w]$, $0 \le w < 2\pi$. -/
private theorem paper_mean_slope_eq {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    ∫ t in (0:ℝ)..1, deriv (fun y : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-y^2)) (t*w) =
      (frameBound w - 1/12)/w := by
  rw [frameBound_sub_div_eq_integral hw0 hw]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact (paper_series_eq (mul_nonneg ht.1 hw0)
    (lt_of_le_of_lt (mul_le_of_le_one_left hw0 ht.2) hw)).2

/-- The closed form (eq:N-def) of $\mathcal N$ on $(0, 2\pi)$:
$\mathcal N(x) = (1 - (x/2)\cot(x/2))/x^2$. -/
theorem frameBound_eq_closed {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameBound x = (1-(x/2)*Real.cot (x/2))/x^2 :=
  Corrector.frameBound_eq_closedForm hx0 hx

/-- The derivative of (eq:N-def) on $(0, 2\pi)$ (proof of the walk comparison):
$\mathcal N'(x) = -2/x^3 + \cot(x/2)/(2x^2) + 1/(4x\sin^2(x/2))$. The proof differentiates
$1/x^2 - \cos(x/2)/(2x\sin(x/2))$, which is `frameMult` near $x$, and compares with
`hasDerivAt_frameMult`. -/
theorem frameLip_eq_closed {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameLip x = -2/x^3+Real.cot (x/2)/(2*x^2)+1/(4*x*Real.sin (x/2)^2) := by
  have ha : |x| < 2 * π := by rwa [abs_of_pos hx0]
  have hsx : 0 < Real.sin (x/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- The closed form agrees with `frameMult` near `x`.
  have hev : (fun y ↦ 1/y^2 - Real.cos (y/2)/(2*y*Real.sin (y/2))) =ᶠ[𝓝 x] frameMult := by
    filter_upwards [lt_mem_nhds hx0] with y hy
    rw [frameMult, if_neg hy.ne', Real.cot_eq_cos_div_sin]
    field_simp
  have hs : HasDerivAt (fun y : ℝ ↦ Real.sin (y/2)) (Real.cos (x/2) * (1/2)) x :=
    ((hasDerivAt_id' x).div_const 2).sin
  have hc : HasDerivAt (fun y : ℝ ↦ Real.cos (y/2)) (-Real.sin (x/2) * (1/2)) x :=
    ((hasDerivAt_id' x).div_const 2).cos
  have hden : HasDerivAt (fun y : ℝ ↦ 2*y*Real.sin (y/2))
      (2*1*Real.sin (x/2) + 2*x*(Real.cos (x/2) * (1/2))) x :=
    ((hasDerivAt_id' x).const_mul 2).mul hs
  have hq : HasDerivAt (fun y : ℝ ↦ 1/y^2) (-(2*x)/(x^2)^2) x := by
    simpa [one_div] using (hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0.ne')
  have hne : 2*x*Real.sin (x/2) ≠ 0 := by positivity
  have hf := (hq.sub (hc.div hden hne)).congr_of_eventuallyEq hev.symm
  rw [(hasDerivAt_frameMult ha).unique hf, Real.cot_eq_cos_div_sin]
  field_simp
  linear_combination (4*x^2) * Real.sin_sq_add_cos_sq (x/2)

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
variable [NeZero d]

/-- The part of $F'$ not involving $\Lambda''$ is at most $\eta\|X\|^2$ when $D = \Phi^{-1}(X)$
(`bernSeries`): insert $\|B\| \le \kappa\|X\|$ and $\|E\| \le \|D\| \le S\|X\|$ into the summed
block estimate (proof of the spectral comparison). -/
theorem norm_cubicFrameSlope_le_inverse_sharp {h J D X : 𝕄} {c w : ℝ}
    (hh : h.IsHermitian) (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hJn : ‖J‖ ≤ 1) (hJh : Commute J h) (hw : w < 2 * π) (ha : ‖I • adL h‖ ≤ w)
    (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4)
    (hD : D = bernSeries (I • adL h) X) :
    ‖cubicFrameSeriesDerivative (I • adL h) (I • adL D) D‖ ≤
      walkFrameSharp w * ‖X‖ ^ 2 := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  have hblock :=
    norm_cubicFrameSeriesDerivative_blocks_sharp (D := D) hw hJJ hJn hJh ha hsmall
  rcases eq_or_lt_of_le hw0 with he | hp
  · subst w
    -- Width zero: `frameLip 0 = 0` and `x / 0 = 0` (the paper's reading of the quotient at
    -- `w = 0`) make both the right side of `hblock` and `walkFrameSharp 0 * ‖X‖ ^ 2` zero.
    simpa [walkFrameSharp, cubic_frameLip_zero] using hblock
  · have hw2 : w / 2 < 2 * π := by linarith
    have hw20 : 0 ≤ w / 2 := by positivity
    have hk0 := walkLogSlope_nonneg hw20 hw2
    have hS0 := walkLogSlope_nonneg hw0 hw
    have hfl0 := frameLip_nonneg hw0
    have htail0 : 0 ≤ (frameBound w - 1 / 12) / w :=
      div_nonneg (sub_nonneg.mpr (one_div_twelve_le_frameBound hw0 hw)) hw0
    have hdiag : ‖cubicDiag J D‖ ≤ walkLogSlope (w / 2) * ‖X‖ := by
      rw [hD, walkLogSlope_eq_sinBound (by linarith) hw2]
      exact norm_cubicDiag_bernSeries_le hh hJ hJJ hJn hJh hp hw ha hsmall X
    have hglob : ‖D‖ ≤ walkLogSlope w * ‖X‖ := by
      rw [hD]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_inverse_le_walkLogSlope hh hw ha) (norm_nonneg X))
    have hoff : ‖cubicOff J D‖ ≤ walkLogSlope w * ‖X‖ :=
      (norm_cubicOff_le J D hJn).trans hglob
    refine hblock.trans ?_
    calc
      _ ≤ 2 * (walkLogSlope (w / 2) * ‖X‖) * (walkLogSlope w * ‖X‖) * frameLip w +
          4 * (walkLogSlope w * ‖X‖) ^ 2 * ((frameBound w - 1 / 12) / w) := by
        gcongr
      _ = walkFrameSharp w * ‖X‖ ^ 2 := by unfold walkFrameSharp; ring

/-- the spectral comparison at one point: if $H(s)$ is Hermitian with spectrum in a window of width
$w < 2\pi$, $D(s) = H'(s)$, and $W = e^{-iH}$ has derivative `Wd` at $s$, then the end value
$t \mapsto \mathcal N(\mathrm{ad}_{H(t)})(D(t))$ has a derivative of norm at most
$\mathcal N(w)\|D'(s)\| + \eta\|W'(s)\|^2$. -/
theorem exists_hasDerivAt_frameOp_walk_sharp
    {H D : ℝ → 𝕄} {Dd Wd : 𝕄} {s m w : ℝ}
    (hHs : (H s).IsHermitian) (hw : w < 2 * π)
    (hev : ∀ i, hHs.eigenvalues i ∈ Set.Icc m (m + w))
    (hH : HasDerivAt H (D s) s) (hD : HasDerivAt D Dd s)
    (hW : HasDerivAt (fun t ↦ evol (H t) 1) Wd s) :
    ∃ Fd : 𝕄, HasDerivAt (fun t ↦ frameOp (H t) (D t)) Fd s ∧
      ‖Fd‖ ≤ frameBound w * ‖Dd‖ + walkFrameSharp w * ‖Wd‖ ^ 2 := by
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by have h := hev 0; linarith [h.1, h.2]
  have hwidth : ‖H s - ((m + w / 2 : ℝ) : ℂ) • 1‖ ≤ w / 2 :=
    norm_sub_smul_one_le_of_eigenvalues hHs hw0 hev
  have ha : ‖I • adL (H s)‖ ≤ w :=
    (norm_I_smul_adL_le (H s) ((m + w / 2 : ℝ) : ℂ)).trans (by linarith)
  obtain ⟨J, hJJ, hJ, hJn, hJh, hsmall⟩ := exists_cubic_spectral_split hHs hw0 hev
  let X : 𝕄 := I • (star (evol (H s) 1) * Wd)
  have hDeq : D s = bernSeries (I • adL (H s)) X := by
    have hder : D s = evolDerivInv (H s) Wd := by
      rw [hW.unique (hasDerivAt_evol_path hHs hH)]
      exact (evolDerivInv_evolDeriv hHs (ha.trans_lt hw) (D s)).symm
    simpa only [evolDerivInv_apply, X] using hder
  have hX : ‖X‖ ≤ ‖Wd‖ := by
    dsimp only [X]
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg Wd) (by rw [norm_star]; exact norm_evol_le hHs 1))
  have hslope := norm_cubicFrameSlope_le_inverse_sharp hHs hJ hJJ hJn hJh hw ha hsmall hDeq
  have hslope' : ‖cubicFrameSeriesDerivative (I • adL (H s)) (I • adL (D s)) (D s)‖ ≤
      walkFrameSharp w * ‖Wd‖ ^ 2 := hslope.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg X) hX 2)
      (walkFrameSharp_nonneg hw0 hw))
  refine ⟨_, hasDerivAt_cubic_frameOp hH hD (ha.trans_lt hw), ?_⟩
  exact (norm_add_le _ _).trans (by linarith [hslope', norm_frameOp_le (D := Dd) hw hwidth])

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- One corrector jump in the proof of the walk comparison: with $m_1$ and $m_2$ the maxima of
$\|W'\|$
and $\|W''\|$ on mesh cell $j + 1$, respectively,
$\|F((j+2)/T) - F((j+1)/T)\| \le (\mathcal N(w)(Sm_2 + \cos^{-2}(w/4)m_1^2) + \eta m_1^2)/T$, by
the spectral comparison, the Hessian bound of Lemma A.2 and the mean-value inequality. -/
theorem walk_frame_jumps_sharp [NeZero d]
    (H W : ℝ → 𝕄) (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hcH : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hcW : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (he : ∀ s ∈ Icc (0 : ℝ) 1, evol (H s) 1 = W s)
    (hwindow : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) i,
      (hH s hs).eigenvalues i ∈ Icc (a s) (a s + w))
    (T j : ℕ) (hj : j + 2 < T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Wd := derivWithin W (Icc (0 : ℝ) 1)
    let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
    ‖frameOp (H ((j + 2:ℕ)/T)) (Hd ((j + 2:ℕ)/T)) -
      frameOp (H ((j+1:ℕ)/T)) (Hd ((j+1:ℕ)/T))‖ ≤
      (frameBound w*(walkLogSlope w*meshSupNorm Wdd T (j+1)+
        (Real.cos (w/4))⁻¹^2*(meshSupNorm Wd T (j+1))^2)+
        walkFrameSharp w*(meshSupNorm Wd T (j+1))^2)/T := by
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by have h := hwindow 0 ⟨le_rfl, zero_le_one⟩ 0; linarith [h.1, h.2]
  intro Hd Wd Wdd
  let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
  have hHd : ContDiffOn ℝ 1 Hd (Icc (0 : ℝ) 1) :=
    hcH.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWd : ContDiffOn ℝ 1 Wd (Icc (0 : ℝ) 1) :=
    hcW.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖H s-(c:ℂ) • 1‖ ≤ w/2 := fun s hs ↦
    ⟨a s+w/2, norm_sub_smul_one_le_of_eigenvalues (hH s hs) hw0 (hwindow s hs)⟩
  have hsecond : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hdd s‖ ≤
      walkLogSlope w*‖Wdd s‖+(Real.cos (w/4))⁻¹^2*‖Wd s‖^2 :=
    norm_walkLogHessian_on_Icc_le hw hH hcH hcW hcenter he
  have hframe : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ Fd : 𝕄,
      HasDerivAt (fun t ↦ frameOp (H t) (Hd t)) Fd s ∧
        ‖Fd‖ ≤ frameBound w*‖Hdd s‖+walkFrameSharp w*‖Wd s‖^2 := by
    intro s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    refine exists_hasDerivAt_frameOp_walk_sharp (hH s hs01) hw (hwindow s hs01)
      (((hcH.differentiableOn (by norm_num) s hs01).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2))
      (((hHd.differentiableOn (by norm_num) s hs01).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)) ?_
    apply (((hcW.differentiableOn (by norm_num) s hs01).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem (Icc_mem_nhds hs.1 hs.2) he
  exact walk_cubic_jump_of_derivative H Hd Hdd Wd Wdd T j w (walkLogSlope w)
    ((Real.cos (w/4))⁻¹^2) (walkFrameSharp w) hj hw0
    (walkLogSlope_nonneg hw0 hw) (sq_nonneg _) (walkFrameSharp_nonneg hw0 hw)
    hWd.continuousOn (hWd.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num))
    hsecond hframe

/-- A common coefficient for the supporting mesh comparison `walk_unit_comparison_sharp`:
$(1/8+c_2+\mathcal N(w))S^2+\eta$, with $c_2=\mathcal N(w)-\mathcal N(w/2)/2+1/24$.
the walk comparison keeps separate coefficients, proved by
`UnitaryProducts.Prose.walk_comparison_jrs`.
Every use assumes $0\le w<2\pi$. -/
def walkUnitCoefficientSharp (w : ℝ) : ℝ :=
  (1/8+(frameBound w-frameBound (w/2)/2+1/24)+frameBound w)*(walkLogSlope w)^2+walkFrameSharp w

/-- The coefficient $c_3$ of $\max\|W'\|^2$ in the walk comparison, parametrized by $w$:
$(1/8+\mathcal N(w))\cos^{-2}(w/4)+c_2S^2+\eta$.
Here $c_2=\mathcal N(w)-\mathcal N(w/2)/2+1/24$, $S$ is `walkLogSlope w`, and
$\eta$ is `walkFrameSharp w`. Every use assumes $0\le w<2\pi$. -/
def walkUnitCoefficientChord (w : ℝ) : ℝ :=
  (1/8+frameBound w)*(Real.cos (w/4))⁻¹^2+(frameBound w-frameBound (w/2)/2+1/24)*(walkLogSlope w)^2+
    walkFrameSharp w

/-- The comparison behind the walk comparison against the end maxima and mesh norms, for every $T
\ge 1$,
with any coefficient $C$ that is at least $S/4$ and the three coefficients of the walk comparison:
$2c_0S$, $(\frac18 + \mathcal N(w))S$, and
$(\frac18 + \mathcal N(w))\cos^{-2}(w/4) + c_2S^2 + \eta$,
with $c_0 = \mathcal N(w) - \mathcal N(w/2)/2$ and $c_2 = c_0 + 1/24$.
`walk_unit_comparison_chord` takes $C$ the last of these and
`walk_unit_comparison_sharp` the larger `walkUnitCoefficientSharp w`.

The supporting comparison uses the same logarithm and end-value estimates: (1) Lemma A.2 supplies
$\Lambda$, $C^2$, with
$\|\Lambda'\| \le S\|W'\|$ and $\|\Lambda''\| \le S\|W''\| + \cos^{-2}(w/4)\|W'\|^2$, and the walk's
sampled product is the unit-step product of $\Lambda$; (2) for $T = 1$, the half-cell bound gives
$\max\|\Lambda'\|/4 \le (S/4)\max\|W'\|$ and $S/4 \le C$; (3) for $T \ge 2$, Theorem 4.2 for
$\Lambda$ with $N = T$, the mesh sups of $\Lambda'$, $\Lambda''$ bounded by those of $W'$, $W''$
(Lemma A.2), and each corrector jump bounded through the spectral comparison
(`walk_frame_jumps_sharp`); (4) the
three coefficients are at most $C$ by hypothesis. -/
theorem walk_unit_comparison_of_coeff [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) (C : ℝ)
    (hC1 : walkLogSlope w / 4 ≤ C)
    (hC2 : 2 * (frameBound w - frameBound (w / 2) / 2) * walkLogSlope w ≤ C)
    (hC3 : (1 / 8 + frameBound w) * walkLogSlope w ≤ C)
    (hC4 : (1 / 8 + frameBound w) * (Real.cos (w / 4))⁻¹ ^ 2 +
      (frameBound w - frameBound (w / 2) / 2 + 1 / 24) * (walkLogSlope w) ^ 2 +
      walkFrameSharp w ≤ C) :
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1 = W s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ T : ℕ, 0<T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ Λ (t/T)) U 0 T →
        ‖(walk W T).2-evol (Λ 1) (-(1/2))*U T*evol (Λ 0) (1/2)‖ ≤
          C*((sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) (1/T))+
            sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1))/2+
            meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1+
            meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2)/T := by
  -- Lemma A.2: the continuous logarithm Λ with spectrum in [a(s), a(s) + w] (i), C² (ii), and
  -- ‖Λ'‖ ≤ S‖W'‖ (iii), ‖Λ''‖ ≤ S‖W''‖ + cos⁻²(w/4)‖W'‖² (iv, before cos⁻²(w/4) ≤ S²).
  obtain ⟨Λ,hΛ,hcont,he⟩ := walk_log_moving a w hw W ha hc.continuousOn hunit harc
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by have h := (he 0 ⟨le_rfl, zero_le_one⟩).1 0; linarith [h.1, h.2]
  have hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖Λ s-(c:ℂ) • 1‖≤w/2 := fun s hs ↦
    ⟨a s+w/2,norm_sub_smul_one_le_of_eigenvalues (hΛ s hs) hw0 (he s hs).1⟩
  have hΛc : ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) := by
    apply contDiffOn_log_of_continuous hcont hΛ _ (fun s hs ↦ (he s hs).2) hc
    intro s hs
    obtain ⟨c,hc⟩ := hcenter s hs
    exact ((norm_I_smul_adL_le (Λ s) (c:ℂ)).trans
      (by linarith : 2*‖Λ s-(c:ℂ) • 1‖≤w)).trans_lt hw
  let Λd := derivWithin Λ (Icc (0 : ℝ) 1)
  let Λdd := derivWithin Λd (Icc (0 : ℝ) 1)
  let Wd := derivWithin W (Icc (0 : ℝ) 1)
  let Wdd := derivWithin Wd (Icc (0 : ℝ) 1)
  have hWd : ContDiffOn ℝ 1 Wd (Icc (0 : ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWdd : ContDiffOn ℝ 0 Wdd (Icc (0 : ℝ) 1) :=
    hWd.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hfirst : ∀ s ∈ Icc (0 : ℝ) 1, ‖Λd s‖ ≤ walkLogSlope w*‖Wd s‖ :=
    norm_walkLogSlope_on_Icc_le hw hΛ hcont hc hcenter (fun s hs ↦ (he s hs).2)
  have hsecond : ∀ s ∈ Icc (0 : ℝ) 1, ‖Λdd s‖ ≤
      walkLogSlope w*‖Wdd s‖+(Real.cos (w/4))⁻¹^2*‖Wd s‖^2 :=
    norm_walkLogHessian_on_Icc_le hw hΛ hΛc hc hcenter (fun s hs ↦ (he s hs).2)
  refine ⟨Λ,hΛ,he,hΛc,?_⟩
  intro T hT U hU
  -- Scalar facts: S ≥ 0, η ≥ 0, 𝒩(w) ≥ 0, and cos⁻²(w/4) ≥ 0.
  have hS0 := walkLogSlope_nonneg hw0 hw
  have hη := walkFrameSharp_nonneg hw0 hw
  have hn0 := frameBound_nonneg hw0
  have hR0 := sq_nonneg (Real.cos (w/4))⁻¹
  have hh0 : 0 ≤ w/2 := by linarith
  have hh : w/2 < 2*π := by linarith
  obtain ⟨hE0,hm0,hq0⟩ := walk_cubic_data_nonneg Wd Wdd T
  -- The walk's sampled product is the unit-step product of Λ, as e^{-iΛ(j/T)} = W(j/T).
  have hp := stepProduct_eq_pieceProduct
    (fun j hj ↦ (he _ (walkCubic_sample hj.le)).2) T le_rfl
  change ‖stepProduct W T T-_‖≤_
  rw [hp]
  rcases Nat.lt_or_ge T 2 with hT1 | hN2
  · -- T = 1: ‖W₁ − e^{iΛ(1)/2}U(1)e^{-iΛ(0)/2}‖ ≤ ∫‖Λ(t) − Λ(q(t))‖ ≤ max‖Λ'‖/4
    -- ≤ (S/4) max‖W'‖, and S/4 ≤ C by hypothesis.
    obtain rfl : T = 1 := by omega
    have hb := unit_steps_one_norms Λ U 1 zero_lt_one hΛ hΛc
      (by simpa only [Nat.cast_one] using hU)
    simp only [one_smul, one_mul] at hb
    have hE : endSupMean Wd 1 = unitSupNorm Wd := by
      simp only [endSupMean, intervalSupNorm, unitSupNorm, Nat.cast_one, div_one, sub_self]
      ring
    change ‖(unitProduct Λ 1).1-evol (Λ 1) (-(1/2))*U ((1:ℕ):ℝ)*evol (Λ 0) (1/2)‖ ≤
      C*(endSupMean Wd 1+meshMoment Wdd 1 1+meshMoment Wd 1 2)/((1:ℕ):ℝ)
    rw [hE, Nat.cast_one, div_one]
    have hΛdSup : unitSupNorm Λd ≤ walkLogSlope w*unitSupNorm Wd := by
      apply csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
      rintro y ⟨s,hs,rfl⟩
      exact (hfirst s hs).trans (mul_le_mul_of_nonneg_left
        (walkCubic_interval_bound hWd.continuousOn (Subset.refl _) hs) hS0)
    have huW0 : 0 ≤ unitSupNorm Wd := walkCubic_interval_nonneg Wd 0 1
    have hC0 : 0 ≤ C := (div_nonneg hS0 (by norm_num)).trans hC1
    refine hb.trans ?_
    calc unitSupNorm Λd/4 ≤ (walkLogSlope w/4)*unitSupNorm Wd :=
          (div_le_div_of_nonneg_right hΛdSup (by norm_num)).trans_eq (by ring)
      _ ≤ C*unitSupNorm Wd := mul_le_mul_of_nonneg_right hC1 huW0
      _ ≤ C*(unitSupNorm Wd+meshMoment Wdd 1 1+meshMoment Wd 1 2) :=
          mul_le_mul_of_nonneg_left
            ((le_add_of_nonneg_right hm0).trans (le_add_of_nonneg_right hq0)) hC0
  -- T ≥ 2: Theorem 4.2 for Λ with N = T, in its jump form (`unit_steps_width`).
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hTne : (T:ℝ) ≠ 0 := hTr.ne'
  have hInv : (0 : ℝ) ≤ 1/T := div_nonneg zero_le_one hTr.le
  have hInv1 : (1:ℝ)/T ≤ 1 := (div_le_one hTr).mpr (Nat.one_le_cast.mpr hT)
  obtain ⟨c₀, c₁, c₂, ⟨hc₀, -, -, -⟩, hper, -⟩ := unit_steps_width (d := d) w hw0 hw
  obtain ⟨hNw, -⟩ := paper_series_eq hw0 hw
  obtain ⟨hNh, -⟩ := paper_series_eq hh0 hh
  simp only [hNw, hNh] at hc₀
  have hc0 : 0 ≤ c₀ := hc₀ ▸ (walk_c0_bounds hw0 hw).1
  -- The width hypothesis of Theorem 4.2: the eigenvalues of Λ(s) lie in [a(s), a(s) + w].
  have hgap : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hΛ s hs).eigenvalues p-(hΛ s hs).eigenvalues q| ≤ w := fun s hs p q ↦
    abs_sub_le_iff.mpr ⟨by linarith only [((he s hs).1 p).2, ((he s hs).1 q).1],
      by linarith only [((he s hs).1 q).2, ((he s hs).1 p).1]⟩
  obtain ⟨-, h⟩ := hper Λ U T T hTr hN2 hΛ hΛc
    (fun j _ hjN p q ↦ by
      rw [div_self hTne, one_mul]; exact hgap _ (walkCubic_sample hjN.le) p q) hU
  have h2T : (T:ℝ)/(2*T) = 1/2 := by field_simp
  have hT2 : (T:ℝ)/T^2 = 1/T := by field_simp
  have hT3 : (T:ℝ)/T^3 = 1/T^2 := by field_simp
  rw [div_self hTne, h2T, hT2, hT3] at h
  simp only [one_smul, mul_one] at h
  refine h.trans ?_
  change _ ≤ C*(endSupMean Wd T+meshMoment Wdd T 1+meshMoment Wd T 2)/T
  -- Lemma A.2(iii), (iv) on mesh cells and end cells: sups of ‖Λ'‖, ‖Λ''‖ by those of ‖W'‖, ‖W''‖.
  have hfirstSup i : meshSupNorm Λd T i ≤ walkLogSlope w*meshSupNorm Wd T i :=
    Real.sSup_le (by
      rintro y ⟨s, hs, rfl⟩
      exact (hfirst s (cubic_mesh_subset hs)).trans (mul_le_mul_of_nonneg_left
        (walkCubic_interval_bound hWd.continuousOn cubic_mesh_subset hs) hS0))
      (mul_nonneg hS0 (walkCubic_interval_nonneg Wd _ _))
  have hfirstSq i : (meshSupNorm Λd T i)^2 ≤ (walkLogSlope w)^2*(meshSupNorm Wd T i)^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (walkCubic_interval_nonneg Λd _ _) (hfirstSup i) 2
  have hsecondSup i : meshSupNorm Λdd T i ≤
      walkLogSlope w*meshSupNorm Wdd T i+(Real.cos (w/4))⁻¹^2*(meshSupNorm Wd T i)^2 := by
    refine Real.sSup_le ?_ (add_nonneg
      (mul_nonneg hS0 (walkCubic_interval_nonneg Wdd _ _)) (mul_nonneg hR0 (sq_nonneg _)))
    rintro y ⟨s, hs, rfl⟩
    exact (hsecond s (cubic_mesh_subset hs)).trans (add_le_add
      (mul_le_mul_of_nonneg_left
        (walkCubic_interval_bound hWdd.continuousOn cubic_mesh_subset hs) hS0)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (walkCubic_interval_bound hWd.continuousOn cubic_mesh_subset hs) 2) hR0))
  have hend0 : ‖Λd (1/T)‖ ≤ walkLogSlope w*intervalSupNorm Wd 0 (1/T) :=
    (hfirst _ ⟨hInv, hInv1⟩).trans (mul_le_mul_of_nonneg_left
      (walkCubic_interval_bound hWd.continuousOn (Icc_subset_Icc le_rfl hInv1)
        ⟨hInv, le_rfl⟩) hS0)
  have hend1 : ‖Λd (1-1/T)‖ ≤ walkLogSlope w*intervalSupNorm Wd (1-1/T) 1 :=
    (hfirst _ ⟨sub_nonneg.mpr hInv1, sub_le_self _ hInv⟩).trans (mul_le_mul_of_nonneg_left
      (walkCubic_interval_bound hWd.continuousOn
        (Icc_subset_Icc (sub_nonneg.mpr hInv1) le_rfl) ⟨le_rfl, sub_le_self _ hInv⟩) hS0)
  -- the spectral comparison: each corrector jump is at most g(j + 1) (`walk_frame_jumps_sharp`),
  -- and the
  -- T − 2 interior jumps are dominated by the sum over all T cells.
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ i, g i = (frameBound w*(walkLogSlope w*meshSupNorm Wdd T i+
      (Real.cos (w/4))⁻¹^2*(meshSupNorm Wd T i)^2)+walkFrameSharp w*(meshSupNorm Wd T i)^2)/T :=
    ⟨_, fun _ ↦ rfl⟩
  have hg0 i : 0 ≤ g i := by
    rw [hg]
    exact div_nonneg (add_nonneg (mul_nonneg hn0 (add_nonneg
      (mul_nonneg hS0 (walkCubic_interval_nonneg Wdd _ _)) (mul_nonneg hR0 (sq_nonneg _))))
      (mul_nonneg hη (sq_nonneg _))) hTr.le
  have hjump : ∀ j, j + 2 < T →
      ‖frameOp (Λ ((j + 2:ℕ)/T)) (Λd ((j + 2:ℕ)/T))-frameOp (Λ ((j+1:ℕ)/T)) (Λd ((j+1:ℕ)/T))‖ ≤
        g (j+1) := by
    intro j hj
    rw [hg]
    exact walk_frame_jumps_sharp Λ W a w hw hΛ hΛc hc
      (fun s hs ↦ (he s hs).2) (fun s hs ↦ (he s hs).1) T j hj
  have hjsum : ∑ j ∈ Finset.range (T-2), g (j+1) ≤ ∑ i ∈ Finset.range T, g i := by
    obtain ⟨n, hn⟩ : ∃ n, T = n+2 := ⟨T-2, by omega⟩
    rw [hn, Nat.add_sub_cancel, show n+2 = n+1+1 from rfl, Finset.sum_range_succ',
      Finset.sum_range_succ]
    exact (le_add_of_nonneg_right (hg0 _)).trans (le_add_of_nonneg_right (hg0 _))
  -- Collect the coefficients of the paper's 2c₀Sm + (c₁ + 𝒩(w))S‖W''‖₁ + C‖W'‖₂²; each is at
  -- most C by hypothesis.
  have hs1 : ∑ j ∈ Finset.range T, ((walkLogSlope w*meshSupNorm Wdd T j+
        (Real.cos (w/4))⁻¹^2*(meshSupNorm Wd T j)^2)/8+
        (c₀+1/24)*((walkLogSlope w)^2*(meshSupNorm Wd T j)^2)) =
      walkLogSlope w/8*∑ j ∈ Finset.range T, meshSupNorm Wdd T j+
        ((Real.cos (w/4))⁻¹^2/8+(c₀+1/24)*(walkLogSlope w)^2)*
          ∑ j ∈ Finset.range T, (meshSupNorm Wd T j)^2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hs2 : ∑ i ∈ Finset.range T, g i =
      frameBound w*walkLogSlope w/T*∑ i ∈ Finset.range T, meshSupNorm Wdd T i+
        (frameBound w*(Real.cos (w/4))⁻¹^2+walkFrameSharp w)/T*
          ∑ i ∈ Finset.range T, (meshSupNorm Wd T i)^2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hg]; ring
  have hA1 : 2*c₀*walkLogSlope w ≤ C := by rw [hc₀]; exact hC2
  have hA3 : (1/8+frameBound w)*(Real.cos (w/4))⁻¹^2+(c₀+1/24)*(walkLogSlope w)^2+
      walkFrameSharp w ≤ C := by rw [hc₀]; exact hC4
  -- The three terms of Theorem 4.2 by the walk data (end terms, cell residuals, jumps).
  calc _ ≤ c₀*(1/(T:ℝ))*(walkLogSlope w*intervalSupNorm Wd 0 (1/T)+
          walkLogSlope w*intervalSupNorm Wd (1-1/T) 1)+
        1/(T:ℝ)^2*∑ j ∈ Finset.range T, ((walkLogSlope w*meshSupNorm Wdd T j+
          (Real.cos (w/4))⁻¹^2*(meshSupNorm Wd T j)^2)/8+
          (c₀+1/24)*((walkLogSlope w)^2*(meshSupNorm Wd T j)^2))+
        1/(T:ℝ)*∑ i ∈ Finset.range T, g i := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left (add_le_add hend0 hend1) (mul_nonneg hc0 hInv)
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ add_le_add
            (div_le_div_of_nonneg_right (hsecondSup j) (by norm_num))
            (mul_le_mul_of_nonneg_left (hfirstSq j) (by linarith only [hc0])))
            (div_nonneg zero_le_one (sq_nonneg _))
        · exact mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun j hj ↦
            hjump j (by have := Finset.mem_range.mp hj; omega)).trans hjsum) hInv
    _ = (2*c₀*walkLogSlope w*endSupMean Wd T+
          (1/8+frameBound w)*walkLogSlope w*meshMoment Wdd T 1+
          ((1/8+frameBound w)*(Real.cos (w/4))⁻¹^2+(c₀+1/24)*(walkLogSlope w)^2+
            walkFrameSharp w)*meshMoment Wd T 2)/T := by
        rw [hs1, hs2]
        simp only [endSupMean, meshMoment, pow_one]
        ring
    _ ≤ (C*endSupMean Wd T+C*meshMoment Wdd T 1+C*meshMoment Wd T 2)/T :=
        div_le_div_of_nonneg_right (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right hA1 hE0) (mul_le_mul_of_nonneg_right hC3 hm0))
          (mul_le_mul_of_nonneg_right hA3 hq0)) hTr.le
    _ = C*(endSupMean Wd T+meshMoment Wdd T 1+meshMoment Wd T 2)/T := by ring

/-- The comparison behind the walk comparison with $C$ = `walkUnitCoefficientSharp w`
$= (\frac18 + c_2 + \mathcal N(w))S^2 + \eta$, for every $T \ge 1$: `walk_unit_comparison_of_coeff`,
as $S \ge 1$, $0 \le c_0 \le \mathcal N(w)$, $\mathcal N(w) \ge 1/12$, and $\cos^{-2}(w/4) \le S^2$.
`unit_step_walk_comparison` restates it with the paper's $\mathcal N$ and $S$. -/
theorem walk_unit_comparison_sharp [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let C := walkUnitCoefficientSharp w
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1 = W s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ T : ℕ, 0<T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ Λ (t/T)) U 0 T →
        ‖(walk W T).2-evol (Λ 1) (-(1/2))*U T*evol (Λ 0) (1/2)‖ ≤
          C*((sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) (1/T))+
            sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1))/2+
            meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1+
            meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2)/T := by
  obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (W 0)
  obtain ⟨θ, hθ, -⟩ := harc 0 ⟨le_rfl, zero_le_one⟩ z hz
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by linarith [hθ.1, hθ.2]
  intro C
  -- C = (c₁ + c₂ + 𝒩(w))S² + η with c₁ = 1/8, c₂ = c₀ + 1/24, c₀ = 𝒩(w) − 𝒩(w/2)/2.
  have hC : C = (1/8+(frameBound w-frameBound (w/2)/2+1/24)+frameBound w)*(walkLogSlope w)^2+
      walkFrameSharp w := rfl
  have hS0 := walkLogSlope_nonneg hw0 hw
  have hη := walkFrameSharp_nonneg hw0 hw
  have hn0 := frameBound_nonneg hw0
  have h12 := one_div_twelve_le_frameBound hw0 hw
  have hS1 := one_le_walkLogSlope hw0 hw
  have hSS : walkLogSlope w ≤ (walkLogSlope w)^2 := le_self_pow₀ hS1 two_ne_zero
  obtain ⟨hhalf, hcN⟩ := walk_c0_bounds hw0 hw
  have hS2 := sq_nonneg (walkLogSlope w)
  have hQS : (Real.cos (w/4))⁻¹^2 ≤ (walkLogSlope w)^2 := cos_quarter_inv_sq_le hw0 hw
  refine walk_unit_comparison_of_coeff a w hw W ha hunit harc hc C ?_ ?_ ?_ ?_
  · -- S/4 ≤ C, as S ≥ 1, c₁ = 1/8, c₂ ≥ 1/24, 𝒩(w) ≥ 1/12.
    have hP2 := mul_nonneg hhalf hS2
    have hP3 := mul_le_mul_of_nonneg_right h12 hS2
    rw [hC]
    linarith only [hSS, hP2, hP3, hη]
  · -- 2c₀S ≤ C, as c₀ ≤ 𝒩(w) and S ≤ S².
    have hQ1 := mul_le_mul_of_nonneg_right hcN hS0
    have hQ2 := mul_le_mul_of_nonneg_left hSS (add_nonneg hhalf hn0)
    rw [hC]
    linarith only [hQ1, hQ2, hη, hS2]
  · -- (c₁ + 𝒩(w))S ≤ C, as S ≤ S² and c₀ ≥ 0.
    have hR1 := mul_le_mul_of_nonneg_left hSS (by linarith only [hn0] : (0 : ℝ) ≤ 1/8+frameBound w)
    have hR2 := mul_nonneg hhalf hS2
    rw [hC]
    linarith only [hR1, hR2, hη, hS2]
  · -- (c₁ + 𝒩(w))cos⁻²(w/4) + c₂S² + η ≤ C, as cos⁻²(w/4) ≤ S².
    have hR3 := mul_le_mul_of_nonneg_left hQS (by linarith only [hn0] : (0 : ℝ) ≤ 1/8+frameBound w)
    rw [hC]
    linarith only [hR3]

/-- The comparison behind the walk comparison with $C$ = `walkUnitCoefficientChord w`
$= (\frac18 + \mathcal N(w))\cos^{-2}(w/4) + c_2S^2 + \eta$, the coefficient of the mean square,
for every $T \ge 1$: `walk_unit_comparison_of_coeff`, as the other coefficients are at most it.
With $Q = \cos^{-2}(w/4)$: $S \le Q$ (`walkLogSlope_le_cos_quarter_inv_sq`) and $S \le S^2$ give
$(\frac18 + \mathcal N(w))S \le (\frac18 + \mathcal N(w))Q$, and
$2c_0S \le \mathcal N(w)Q + c_2S^2$ by $0 \le c_0 \le \mathcal N(w)$ and $c_0 < c_2$; and
$S/4 \le (\frac18 + \frac1{12})S + \frac1{24}S$. -/
theorem walk_unit_comparison_chord [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let C := walkUnitCoefficientChord w
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1 = W s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ T : ℕ, 0<T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ Λ (t/T)) U 0 T →
        ‖(walk W T).2-evol (Λ 1) (-(1/2))*U T*evol (Λ 0) (1/2)‖ ≤
          C*((sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) (1/T))+
            sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1))/2+
            meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1+
            meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2)/T := by
  obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (W 0)
  obtain ⟨θ, hθ, -⟩ := harc 0 ⟨le_rfl, zero_le_one⟩ z hz
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by linarith [hθ.1, hθ.2]
  intro C
  have hC : C = (1/8+frameBound w)*(Real.cos (w/4))⁻¹^2+
      (frameBound w-frameBound (w/2)/2+1/24)*(walkLogSlope w)^2+walkFrameSharp w := rfl
  have hS0 := walkLogSlope_nonneg hw0 hw
  have hη := walkFrameSharp_nonneg hw0 hw
  have hn0 := frameBound_nonneg hw0
  have h12 := one_div_twelve_le_frameBound hw0 hw
  have hS1 := one_le_walkLogSlope hw0 hw
  have hSS : walkLogSlope w ≤ (walkLogSlope w)^2 := le_self_pow₀ hS1 two_ne_zero
  obtain ⟨hhalf, hcN⟩ := walk_c0_bounds hw0 hw
  have hSQ : walkLogSlope w ≤ (Real.cos (w/4))⁻¹^2 := walkLogSlope_le_cos_quarter_inv_sq hw0 hw
  have h8 : (0 : ℝ) ≤ 1/8+frameBound w := by linarith only [hn0]
  have hc2 : 0 ≤ frameBound w-frameBound (w/2)/2+1/24 := by linarith only [hhalf]
  have hR0 := sq_nonneg (Real.cos (w/4))⁻¹
  -- (c₁ + 𝒩(w))S ≤ (c₁ + 𝒩(w))cos⁻²(w/4), and c₂S ≤ c₂S².
  have hM := mul_le_mul_of_nonneg_left hSQ h8
  have hc2S := mul_le_mul_of_nonneg_left hSS hc2
  have hP := mul_nonneg hc2 (sq_nonneg (walkLogSlope w))
  refine walk_unit_comparison_of_coeff a w hw W ha hunit harc hc C ?_ ?_ ?_ (le_of_eq hC.symm)
  · -- S/4 ≤ C, as (c₁ + 𝒩(w))cos⁻²(w/4) ≥ (1/8 + 1/12)S and c₂S² ≥ S/24.
    have hP1 := mul_le_mul_of_nonneg_right h12 hS0
    have hP2 := mul_le_mul_of_nonneg_right (by linarith only [hhalf] :
      (1 : ℝ)/24 ≤ frameBound w-frameBound (w/2)/2+1/24) hS0
    rw [hC]
    linarith only [hM, hP1, hP2, hc2S, hη]
  · -- 2c₀S ≤ C, as c₀S ≤ 𝒩(w)S ≤ 𝒩(w)cos⁻²(w/4) and c₀S ≤ c₂S ≤ c₂S².
    have hQ1 := mul_le_mul_of_nonneg_right hcN hS0
    have hQ2 := mul_le_mul_of_nonneg_left hSQ hn0
    have hQ3 := mul_le_mul_of_nonneg_right (by linarith only :
      frameBound w-frameBound (w/2)/2 ≤ frameBound w-frameBound (w/2)/2+1/24) hS0
    have hQ4 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/8) hR0
    rw [hC]
    linarith only [hQ1, hQ2, hQ3, hQ4, hc2S, hη]
  · -- (c₁ + 𝒩(w))S ≤ C.
    rw [hC]
    linarith only [hM, hP, hη]

/-- Leakage transfer to a walk with the common-coefficient mesh bound of
`walk_unit_comparison_sharp`. The endpoint projectors commute with the logarithm,
so the unitary half-step phases preserve the compressed norms.
This supports the transfer argument in §4.4; its sharper paper comparison uses the
separate coefficients of `UnitaryProducts.Prose.walk_comparison_jrs` (the walk comparison). -/
theorem walk_transfer_sharp [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1 = W s) ∧
      ∀ T : ℕ, 0<T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ Λ (t/T)) U 0 T →
      ∀ P Q : 𝕄, IsStarProjection P → IsStarProjection Q → Commute P (Λ 0) → Commute Q (Λ 1) →
        |‖(1-Q)*(walk W T).2*P‖ - ‖(1-Q)*U T*P‖| ≤
          walkUnitCoefficientSharp w*((sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc
            (0 : ℝ) (1/T))+
            sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1))/2+
            meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1+
            meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2)/T := by
  obtain ⟨Λ, hΛ, he, -, hcmp⟩ := walk_unit_comparison_sharp a w hw W ha hunit harc hc
  refine ⟨Λ, hΛ, he, ?_⟩
  intro T hT U hU P Q hP hQ hPc hQc
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hp : (T:ℝ)/(2*T) = 1/2 := by field_simp
  have hb := unit_steps_transfer_windows.1 Λ (U T) T T
    (hΛ 0 ⟨le_rfl, zero_le_one⟩) (hΛ 1 ⟨zero_le_one, le_rfl⟩) P Q hP hQ hPc hQc
  dsimp only at hb
  simp only [div_self hTR.ne', one_smul, hp] at hb
  have hW : (unitProduct Λ T).1 = (walk W T).2 := by
    rw [walk_step_products W Λ (fun j hj ↦ (he _ (walkCubic_sample hj.le)).2),
      step_products_unit Λ]
  rw [hW] at hb
  exact hb.trans (hcmp T hT U hU)

/-- The maximum of $\|F\|$ over a part of $[0,1]$ is at most its maximum over $[0,1]$. -/
private theorem sSup_norm_le_of_subset {F : ℝ → 𝕄} (hc : ContinuousOn F (Icc (0 : ℝ) 1))
    {A : Set ℝ} (hA : A ⊆ Icc (0 : ℝ) 1) :
    sSup ((fun s ↦ ‖F s‖) '' A) ≤ sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1) := by
  apply Real.sSup_le
  · rintro y ⟨s, hs, rfl⟩
    exact hc.norm.le_sSup_image_Icc (hA hs)
  · exact Real.sSup_nonneg (by rintro y ⟨s, -, rfl⟩; exact norm_nonneg _)

/-- A mesh norm is at most the maximum: $\|F\|_{p,N}^p \le (\max_{[0,1]}\|F\|)^p$. -/
private theorem meshMoment_le_sSup_pow {F : ℝ → 𝕄} (hc : ContinuousOn F (Icc (0 : ℝ) 1))
    {N : ℕ} (p : ℕ) :
    meshMoment F N p ≤ (sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1))^p := by
  have hn : 0 ≤ sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1) :=
    Real.sSup_nonneg (by rintro y ⟨s, -, rfl⟩; exact norm_nonneg _)
  have hb : ∀ i ∈ Finset.range N,
      (meshSupNorm F N i)^p ≤ (sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1))^p :=
    fun _ _ ↦ pow_le_pow_left₀ meshSup_nonneg
      (sSup_norm_le_of_subset hc mesh_subset) p
  apply div_le_of_le_mul₀ (Nat.cast_nonneg N) (pow_nonneg hn p)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_sum hb

/-- The common coefficient of `unit_step_walk_comparison_max`, in the omitted-arc length:
$(1/8+c_2+\mathcal N(w))S^2+\eta$ with $w=2\pi-\vartheta$.
It bounds the separate coefficients in `UnitaryProducts.Prose.walk_comparison_jrs`.
Every use assumes $0<\vartheta\le2\pi$. -/
def walkConstant (ϑ : ℝ) : ℝ :=
  (1/8+(frameBound (2*π-ϑ)-frameBound ((2*π-ϑ)/2)/2+1/24)+frameBound (2*π-ϑ))*
    (walkLogSlope (2*π-ϑ))^2+walkFrameSharp (2*π-ϑ)

/-- A function continuous at `0` tends to its value there from the right. -/
private theorem tendsto_nhdsGT_of_continuousAt {f : ℝ → ℝ} {L : ℝ} (hf : ContinuousAt f 0)
    (h0 : f 0 = L) : Tendsto f (𝓝[>] 0) (𝓝 L) :=
  h0 ▸ hf.tendsto.mono_left nhdsWithin_le_nhds

/-- `sin(φ/2) = (φ/2) sinc(φ/2)`, and at `w = 2π - φ` the reflections `sin(w/2) = sin(φ/2)`,
`cos(w/2) = -cos(φ/2)`, `sin(w/4) = cos(φ/4)`. -/
private theorem walk_reflect {φ : ℝ} (hφ : φ ≠ 0) :
    Real.sin (φ/2) = φ/2*Real.sinc (φ/2) ∧
    Real.sin ((2*π-φ)/2) = Real.sin (φ/2) ∧
    Real.cos ((2*π-φ)/2) = -Real.cos (φ/2) ∧
    Real.sin ((2*π-φ)/2/2) = Real.cos (φ/4) := by
  have e1 : (2*π-φ)/2 = π-φ/2 := by ring
  have e2 : (2*π-φ)/2/2 = π/2-φ/4 := by ring
  refine ⟨?_, by rw [e1, Real.sin_pi_sub], by rw [e1, Real.cos_pi_sub],
    by rw [e2, Real.sin_pi_div_two_sub]⟩
  rw [Real.sinc_of_ne_zero (div_ne_zero hφ two_ne_zero)]
  field_simp

/-- The asymptotics in the proof of the walk comparison, at $w = 2\pi - \vartheta$ as $\vartheta
\to 0^+$:
$\vartheta S \to 2\pi$, $\kappa \to \pi/2$, $\vartheta\mathcal N(w) \to 1/(2\pi)$, and
$\vartheta^2\mathcal N'(w) \to 1/(2\pi)$. Each quantity is, for $0 < \vartheta < \pi$, a function
continuous at $0$ written with $\operatorname{sinc}(\vartheta/2) = \sin(\vartheta/2)/(\vartheta/2)$,
by the closed forms of $S$, (eq:N-def), and its derivative (`frameLip_eq_closed`), with
$\sin(w/2) = \sin(\vartheta/2)$ and $\cot(w/2) = -\cot(\vartheta/2)$. -/
private theorem walk_asymptotics :
    Tendsto (fun φ ↦ φ*walkLogSlope (2*π-φ)) (𝓝[>] 0) (𝓝 (2*π)) ∧
    Tendsto (fun φ ↦ walkLogSlope ((2*π-φ)/2)) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun φ ↦ φ*frameBound (2*π-φ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun φ ↦ φ^2*frameLip (2*π-φ)) (𝓝[>] 0) (𝓝 (1/(2*π))) := by
  have hpi := pi_pos
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hsinc : ContinuousAt (fun φ : ℝ ↦ Real.sinc (φ/2)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 2)).continuousAt
  have hw : ContinuousAt (fun φ : ℝ ↦ 2*π-φ) 0 := continuousAt_const.sub continuousAt_id
  have hw0 : (2*π-0) ≠ 0 := by linarith
  have hc2 : ContinuousAt (fun φ : ℝ ↦ Real.cos (φ/2)) 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt
  have hc4 : ContinuousAt (fun φ : ℝ ↦ Real.cos (φ/4)) 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 4)).continuousAt
  have hs0 : Real.sinc ((0:ℝ)/2) ≠ 0 := by rw [zero_div, Real.sinc_zero]; norm_num
  -- At `0 < φ < π`: `sin(φ/2) > 0`, so `sinc(φ/2) ≠ 0`, and `w = 2π - φ ∈ (π, 2π)`.
  have hpos : ∀ φ ∈ Ioo 0 π, Real.sinc (φ/2) ≠ 0 ∧ 0 < 2*π-φ ∧ 2*π-φ < 2*π := by
    intro φ hφ
    obtain ⟨h1, -, -, -⟩ := walk_reflect hφ.1.ne'
    have hs : 0 < Real.sin (φ/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1])
      (by linarith [hφ.2])
    refine ⟨fun h ↦ ?_, by linarith [hφ.2], by linarith [hφ.1]⟩
    rw [h, mul_zero] at h1
    exact hs.ne' h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- φS(w) = (2π - φ)/sinc(φ/2).
    have hA : ContinuousAt (fun φ : ℝ ↦ (2*π-φ)/Real.sinc (φ/2)) 0 := hw.div hsinc hs0
    refine (tendsto_nhdsGT_of_continuousAt hA
      (by rw [zero_div, Real.sinc_zero]; ring)).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, -, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [walkLogSlope_eq_sinBound hwp hw2, sinBound, h2, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    field_simp
  · -- κ = (π/2 - φ/4)/cos(φ/4).
    have hA : ContinuousAt (fun φ : ℝ ↦ (2*π-φ)/4/Real.cos (φ/4)) 0 :=
      (hw.div_const 4).div hc4 (by rw [zero_div, Real.cos_zero]; norm_num)
    refine (tendsto_nhdsGT_of_continuousAt hA (by rw [zero_div, Real.cos_zero]; ring)).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨-, -, -, h4⟩ := walk_reflect hφ.1.ne'
    obtain ⟨-, hwp, hw2⟩ := hpos φ hφ
    rw [walkLogSlope_eq_sinBound (by linarith) (by linarith), sinBound, h4]
    ring
  · -- φ𝒩(w) = φ/w² + cos(φ/2)/(sinc(φ/2) w).
    have hA : ContinuousAt
        (fun φ : ℝ ↦ φ/(2*π-φ)^2+Real.cos (φ/2)/(Real.sinc (φ/2)*(2*π-φ))) 0 :=
      (continuousAt_id.div (hw.pow 2) (pow_ne_zero 2 hw0)).add
        (hc2.div (hsinc.mul hw) (mul_ne_zero hs0 hw0))
    have h0 : (0:ℝ)/(2*π-0)^2+Real.cos (0/2)/(Real.sinc (0/2)*(2*π-0)) = 1/(2*π) := by
      simp only [zero_div, Real.sinc_zero, Real.cos_zero, sub_zero, zero_add]; field_simp
    refine (tendsto_nhdsGT_of_continuousAt hA h0).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, h3, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [frameBound_eq_closed hwp hw2, Real.cot_eq_cos_div_sin, h2, h3, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    generalize Real.cos (φ/2) = γ
    field_simp
    ring
  · -- φ²𝒩'(w) = -2φ²/w³ - φcos(φ/2)/(w² sinc(φ/2)) + 1/(w sinc(φ/2)²).
    have hA : ContinuousAt (fun φ : ℝ ↦ -2*φ^2/(2*π-φ)^3-
        φ*Real.cos (φ/2)/((2*π-φ)^2*Real.sinc (φ/2))+1/((2*π-φ)*Real.sinc (φ/2)^2)) 0 :=
      (((continuousAt_const.mul (continuousAt_id.pow 2)).div (hw.pow 3) (pow_ne_zero 3 hw0)).sub
        ((continuousAt_id.mul hc2).div ((hw.pow 2).mul hsinc)
          (mul_ne_zero (pow_ne_zero 2 hw0) hs0))).add
        (continuousAt_const.div (hw.mul (hsinc.pow 2)) (mul_ne_zero hw0 (pow_ne_zero 2 hs0)))
    have h0 : -2*(0:ℝ)^2/(2*π-0)^3-0*Real.cos (0/2)/((2*π-0)^2*Real.sinc (0/2))+
        1/((2*π-0)*Real.sinc (0/2)^2) = 1/(2*π) := by
      simp only [zero_div, Real.sinc_zero, Real.cos_zero, sub_zero]; field_simp; ring
    refine (tendsto_nhdsGT_of_continuousAt hA h0).congr' ?_
    filter_upwards [hev] with φ hφ
    obtain ⟨h1, h2, h3, -⟩ := walk_reflect hφ.1.ne'
    obtain ⟨hsc, hwp, hw2⟩ := hpos φ hφ
    have hφ0 : φ ≠ 0 := hφ.1.ne'
    rw [frameLip_eq_closed hwp hw2, Real.cot_eq_cos_div_sin, h2, h3, h1]
    generalize Real.sinc (φ/2) = σ at hsc ⊢
    generalize Real.cos (φ/2) = γ
    field_simp
    ring

/-- $\vartheta\,\mathcal N(w/2) \to 0$ as $\vartheta \to 0^+$, with $w = 2\pi - \vartheta$: by the
pole bound, $1/12 \le \mathcal N(w/2) \le \pi/(6(2\pi - w/2)) \le 1/6$ for $0 < \vartheta < \pi$. -/
private theorem tendsto_mul_frameBound_half :
    Tendsto (fun φ ↦ φ*frameBound ((2*π-φ)/2)) (𝓝[>] 0) (𝓝 0) := by
  have hpi := pi_pos
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hid : Tendsto (fun φ : ℝ ↦ φ) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have h6 := hid.div_const 6
  rw [zero_div] at h6
  refine squeeze_zero' ?_ ?_ h6
  · filter_upwards [hev] with φ hφ
    have h12 := one_div_twelve_le_frameBound (w := (2*π-φ)/2) (by linarith [hφ.2])
      (by linarith [hφ.1])
    exact mul_nonneg hφ.1.le (by linarith)
  · filter_upwards [hev] with φ hφ
    have hp := frameBound_le_pole (w := (2*π-φ)/2) (by linarith [hφ.2]) (by linarith [hφ.1])
    have hq : π/(6*(2*π-(2*π-φ)/2)) ≤ π/(6*π) :=
      div_le_div_of_nonneg_left hpi.le (by positivity) (by linarith [hφ.1])
    have he : π/(6*π) = 1/6 := by field_simp
    exact (mul_le_mul_of_nonneg_left ((hp.trans hq).trans_eq he) hφ.1.le).trans_eq (by ring)

/-- The closed forms and asymptotics the last paragraph of the proof of the walk comparison uses,
and the
order of the larger constant `walkConstant`: $(\frac18 + c_2 + \mathcal N(w))S^2 + \eta$ times
$\vartheta^3$ tends to $5\pi + 4$ as $\vartheta \to 0^+$. With $w = 2\pi - \vartheta$:
* (eq:N-def) and its derivative on $(0, 2\pi)$:
  $\mathcal N(x) = (1 - (x/2)\cot(x/2))/x^2$ and
  $\mathcal N'(x) = -2/x^3 + \cot(x/2)/(2x^2) + 1/(4x\sin^2(x/2))$;
* the mean slope $\int_0^1\mathcal N'(tw)\,dt = (\mathcal N(w) - 1/12)/w$ for $0 < w < 2\pi$;
* $\vartheta S \to 2\pi$, $\kappa \to \pi/2$, $\vartheta\mathcal N(w) \to 1/(2\pi)$,
  $\vartheta^2\mathcal N'(w) \to 1/(2\pi)$,
  $\vartheta\int_0^1\mathcal N'(tw)\,dt \to 1/(4\pi^2)$, and
  $\vartheta c_2 \to 1/(2\pi)$ for $c_2 = \mathcal N(w) - \mathcal N(w/2)/2 + 1/24$ of Theorem 4.2,
  as $\mathcal N(w/2)$ stays bounded;
* `walkConstant ϑ`$\cdot\vartheta^3 \to 0 + 4\pi + \pi + 4$, from its four terms $S^2/8$,
  $(c_2 + \mathcal N(w))S^2$, $2\kappa S\mathcal N'(w)$, and $4S^2\int_0^1\mathcal N'(tw)\,dt$
  (`walk_constant_chord_limit` gives the limit for $c_3$ in the walk comparison).

Reading the statement against the paper: `N` is the partial-fraction series, equal to (eq:N-def) on
$[0, 2\pi)$ (`periodicCorrector_N_trig`), so `deriv N` is $\mathcal N'$ there; `S x` is
the paper's $g(x)=(x/2)/\sin(x/2)$, with $g(0)=1$, so `S (2*π-ϑ)` is $S$ and `S ((2*π-ϑ)/2)` is
$\kappa$;
`𝓝[>] 0` is the limit $\vartheta \to 0^+$; and `walkConstant ϑ` is the larger constant, whose
value in these terms is the second conjunct of `unit_step_walk_comparison_max`. -/
theorem walk_constant_limit :
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    (∀ x : ℝ, 0 < x → x < 2*π → N x = (1-(x/2)*Real.cot (x/2))/x^2 ∧
      deriv N x = -2/x^3+Real.cot (x/2)/(2*x^2)+1/(4*x*Real.sin (x/2)^2)) ∧
    (∀ w : ℝ, 0 < w → w < 2*π → ∫ t in (0:ℝ)..1, deriv N (t*w) = (N w-1/12)/w) ∧
    Tendsto (fun ϑ ↦ ϑ*S (2*π-ϑ)) (𝓝[>] 0) (𝓝 (2*π)) ∧
    Tendsto (fun ϑ ↦ S ((2*π-ϑ)/2)) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun ϑ ↦ ϑ*N (2*π-ϑ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ ϑ^2*deriv N (2*π-ϑ)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ ϑ*∫ t in (0:ℝ)..1, deriv N (t*(2*π-ϑ))) (𝓝[>] 0) (𝓝 (1/(4*π^2))) ∧
    Tendsto (fun ϑ ↦ ϑ*(N (2*π-ϑ)-N ((2*π-ϑ)/2)/2+1/24)) (𝓝[>] 0) (𝓝 (1/(2*π))) ∧
    Tendsto (fun ϑ ↦ walkConstant ϑ*ϑ^3) (𝓝[>] 0) (𝓝 (5*π+4)) := by
  intro N S
  have hpi := pi_pos
  obtain ⟨hS, hκ, hN, hN'⟩ := walk_asymptotics
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hNx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : N x = frameBound x := (paper_series_eq hx0 hx).1
  have hDx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : deriv N x = frameLip x :=
    (paper_series_eq hx0 hx).2
  have hIx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) :
      ∫ t in (0:ℝ)..1, deriv N (t*x) = (frameBound x-1/12)/x := paper_mean_slope_eq hx0 hx
  have hSx (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2*π) : S x = walkLogSlope x := walkLogSlope_closed hx0 hx
  have hid : Tendsto (fun φ : ℝ ↦ φ) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hwlim : Tendsto (fun φ : ℝ ↦ 2*π-φ) (𝓝[>] 0) (𝓝 (2*π)) := by
    simpa using tendsto_const_nhds.sub hid
  -- φ(𝒩(w) - 1/12)/w → (1/(2π))/(2π) = 1/(4π²).
  have hQ : Tendsto (fun φ ↦ φ*((frameBound (2*π-φ)-1/12)/(2*π-φ))) (𝓝[>] 0)
      (𝓝 (1/(4*π^2))) := by
    have h := (hN.sub (hid.div_const 12)).div hwlim (by positivity)
    have e : (1/(2*π)-0/12)/(2*π) = 1/(4*π^2) := by field_simp; ring
    rw [e] at h
    exact h.congr fun φ ↦ by simp only [Pi.div_apply]; ring
  -- φc₂ = φ𝒩(w) - φ𝒩(w/2)/2 + φ/24 → 1/(2π), as φ𝒩(w/2) → 0.
  have hC : Tendsto (fun φ ↦ φ*frameBound (2*π-φ)-φ*frameBound ((2*π-φ)/2)/2+φ/24) (𝓝[>] 0)
      (𝓝 (1/(2*π))) := by
    have h := (hN.sub (tendsto_mul_frameBound_half.div_const 2)).add (hid.div_const 24)
    rw [zero_div, zero_div, sub_zero, add_zero] at h
    exact h
  refine ⟨fun x hx0 hx ↦ ⟨(hNx x hx0.le hx).trans (frameBound_eq_closed hx0 hx),
      (hDx x hx0.le hx).trans (frameLip_eq_closed hx0 hx)⟩,
    fun w hw0 hw ↦ (hIx w hw0.le hw).trans (by rw [hNx w hw0.le hw]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hS.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hSx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hκ.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hSx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hN.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hNx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hN'.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hDx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hQ.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hIx _ (by linarith [hφ.2]) (by linarith [hφ.1])]
  · refine hC.congr' ?_
    filter_upwards [hev] with φ hφ
    rw [hNx _ (by linarith [hφ.2]) (by linarith [hφ.1]),
      hNx ((2*π-φ)/2) (by linarith [hφ.2]) (by linarith [hφ.1])]
    ring
  · -- c(φ)φ³ = (φS)²φ/8 + (φS)²(φc₂ + φ𝒩) + 2(φS)κ(φ²𝒩') + 4(φS)²(φ·mean slope).
    have h := ((((hS.pow 2).mul hid).const_mul (1/8)).add
      ((hS.pow 2).mul (hC.add hN))).add
      ((((hS.mul hκ).mul hN').const_mul 2).add (((hS.pow 2).mul hQ).const_mul 4))
    have e : 1/8*((2*π)^2*0)+(2*π)^2*(1/(2*π)+1/(2*π))+
        (2*(2*π*(π/2)*(1/(2*π)))+4*((2*π)^2*(1/(4*π^2)))) = 5*π+4 := by
      field_simp; ring
    rw [e] at h
    refine h.congr fun φ ↦ ?_
    unfold walkConstant walkFrameSharp
    ring

/-- The coefficient $c_3$ of $\max\|W'\|^2$ in the walk comparison, parametrized by $\vartheta$:
$(1/8+\mathcal N(w))/\cos^2(w/4)+c_2S^2+\eta$, with $w=2\pi-\vartheta$.
The separate-coefficient statement is `UnitaryProducts.Prose.walk_comparison_jrs`.
Every use assumes $0<\vartheta\le2\pi$. -/
def walkConstantChord (ϑ : ℝ) : ℝ :=
  (1/8+frameBound (2*π-ϑ))*(Real.cos ((2*π-ϑ)/4))⁻¹^2+
    (frameBound (2*π-ϑ)-frameBound ((2*π-ϑ)/2)/2+1/24)*(walkLogSlope (2*π-ϑ))^2+
    walkFrameSharp (2*π-ϑ)

/-- $c(\vartheta)$ is the coefficient $C$ of `walk_unit_comparison_chord` at
$w = 2\pi - \vartheta$. -/
theorem walkConstantChord_eq (ϑ : ℝ) :
    walkConstantChord ϑ = walkUnitCoefficientChord (2*π-ϑ) := rfl

/-- The order of the coefficient $c_3$ of $\max\|W'\|^2$ in the walk comparison (the last
paragraph of its proof): with $w = 2\pi - \vartheta$, $\cos(w/4) = \sin(\vartheta/4)$,
$\vartheta/\cos(w/4) \to 4$, and $c(\vartheta)\vartheta^3 \to 3\pi + 4 + 8/\pi$ as
$\vartheta \to 0^+$, from the four terms $(\frac18 + \mathcal N(w))/\cos^2(w/4)$, $c_2S^2$,
$2\kappa S\mathcal N'(w)$, and $4S^2\int_0^1\mathcal N'(tw)\,dt$ of $c(\vartheta)$ (the final
display in the
proof), which contribute $16/(2\pi) = 8/\pi$, $2\pi$, $\pi$, and $4$. The other asymptotics the
proof uses are `walk_constant_limit`. -/
theorem walk_constant_chord_limit :
    (∀ ϑ : ℝ, Real.cos ((2*π-ϑ)/4) = Real.sin (ϑ/4)) ∧
    Tendsto (fun ϑ ↦ ϑ/Real.cos ((2*π-ϑ)/4)) (𝓝[>] 0) (𝓝 4) ∧
    Tendsto (fun ϑ ↦ walkConstantChord ϑ*ϑ^3) (𝓝[>] 0) (𝓝 (3*π+4+8/π)) := by
  have hpi := pi_pos
  have hcs (φ : ℝ) : Real.cos ((2*π-φ)/4) = Real.sin (φ/4) := by
    rw [show (2*π-φ)/4 = π/2-φ/4 by ring, Real.cos_pi_div_two_sub]
  obtain ⟨hS, hκ, hN, hN'⟩ := walk_asymptotics
  have hev : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ ∈ Ioo 0 π := Ioo_mem_nhdsGT hpi
  have hid : Tendsto (fun φ : ℝ ↦ φ) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  have hwlim : Tendsto (fun φ : ℝ ↦ 2*π-φ) (𝓝[>] 0) (𝓝 (2*π)) := by
    simpa using tendsto_const_nhds.sub hid
  -- φ/cos(w/4) = φ/sin(φ/4) = 4/sinc(φ/4) → 4.
  have hsinc : ContinuousAt (fun φ : ℝ ↦ Real.sinc (φ/4)) 0 :=
    (Real.continuous_sinc.comp (continuous_id.div_const 4)).continuousAt
  have hs0 : Real.sinc ((0:ℝ)/4) ≠ 0 := by rw [zero_div, Real.sinc_zero]; norm_num
  have hA : ContinuousAt (fun φ : ℝ ↦ 4/Real.sinc (φ/4)) 0 := continuousAt_const.div hsinc hs0
  have hR : Tendsto (fun φ ↦ φ/Real.cos ((2*π-φ)/4)) (𝓝[>] 0) (𝓝 4) := by
    refine (tendsto_nhdsGT_of_continuousAt hA
      (by rw [zero_div, Real.sinc_zero, div_one])).congr' ?_
    filter_upwards [hev] with φ hφ
    have hs : Real.sin (φ/4) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2])).ne'
    rw [hcs, Real.sinc_of_ne_zero (div_ne_zero hφ.1.ne' four_ne_zero)]
    field_simp
  -- φ(𝒩(w) - 1/12)/w → (1/(2π))/(2π) = 1/(4π²).
  have hQ : Tendsto (fun φ ↦ φ*((frameBound (2*π-φ)-1/12)/(2*π-φ))) (𝓝[>] 0)
      (𝓝 (1/(4*π^2))) := by
    have h := (hN.sub (hid.div_const 12)).div hwlim (by positivity)
    have e : (1/(2*π)-0/12)/(2*π) = 1/(4*π^2) := by field_simp; ring
    rw [e] at h
    exact h.congr fun φ ↦ by simp only [Pi.div_apply]; ring
  -- φc₂ = φ𝒩(w) - φ𝒩(w/2)/2 + φ/24 → 1/(2π), as φ𝒩(w/2) → 0.
  have hC : Tendsto (fun φ ↦ φ*frameBound (2*π-φ)-φ*frameBound ((2*π-φ)/2)/2+φ/24) (𝓝[>] 0)
      (𝓝 (1/(2*π))) := by
    have h := (hN.sub (tendsto_mul_frameBound_half.div_const 2)).add (hid.div_const 24)
    rw [zero_div, zero_div, sub_zero, add_zero] at h
    exact h
  refine ⟨hcs, hR, ?_⟩
  -- c(φ)φ³ = (φ/cos(w/4))²(φ/8 + φ𝒩) + (φS)²(φc₂) + 2(φS)κ(φ²𝒩') + 4(φS)²(φ·mean slope).
  have h := (((hR.pow 2).mul ((hid.div_const 8).add hN)).add ((hS.pow 2).mul hC)).add
    ((((hS.mul hκ).mul hN').const_mul 2).add (((hS.pow 2).mul hQ).const_mul 4))
  have e : 4^2*(0/8+1/(2*π))+(2*π)^2*(1/(2*π))+
      (2*(2*π*(π/2)*(1/(2*π)))+4*((2*π)^2*(1/(4*π^2)))) = 3*π+4+8/π := by
    field_simp; ring
  rw [e] at h
  refine h.congr fun φ ↦ ?_
  unfold walkConstantChord walkFrameSharp
  ring

/-- A supporting walk comparison with the common coefficient `walkConstantChord`:
$\|W_T-e^{i\Lambda(1)/2}U_\Lambda(T)e^{-i\Lambda(0)/2}\|\le c(\vartheta)(L+M+L^2)/T$.
The paper's the walk comparison states separate coefficients of the derivative maxima and their
square,
proved by `UnitaryProducts.Prose.walk_comparison_jrs`.

The walk and logarithm satisfy Lemma A.2. The `sSup`s $L$ and $M$ are the maxima of
$\|W'\|$ and $\|W''\|$ on the compact interval. `IsEvolution` specifies the evolution
of $\Lambda$ over time $T$, and `evol` supplies the two endpoint half-step phases.
The second conjunct expands the common coefficient; the last gives its cubic order.
The proof bounds the end maxima and mesh moments in `walk_unit_comparison_chord`
by $L$, $M$, and $L^2$. -/
theorem unit_step_walk_comparison_chord [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let L := sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) 1)
    let M := sSup ((fun s ↦ ‖derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1) s‖) ''
      Icc (0 : ℝ) 1)
    let N : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    (∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol (Λ s) 1 = W s) ∧
      ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) ∧
      ∀ T : ℕ, 2 ≤ T → ∀ U : ℝ → 𝕄, IsEvolution (fun t ↦ Λ (t/T)) U 0 T →
        ‖(walk W T).2-evol (Λ 1) (-(1/2))*U T*evol (Λ 0) (1/2)‖ ≤
          walkConstantChord (2*π-w)*(L+M+L^2)/T) ∧
    walkConstantChord (2*π-w) = (1/8+N w)/Real.cos (w/4)^2+(N w-N (w/2)/2+1/24)*(S w)^2+
      2*S w*(S (w/2)*deriv N w+2*S w*∫ t in (0:ℝ)..1, deriv N (t*w)) ∧
    Tendsto (fun ϑ ↦ walkConstantChord ϑ*ϑ^3) (𝓝[>] 0) (𝓝 (3*π+4+8/π)) := by
  obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (W 0)
  obtain ⟨θ, hθ, -⟩ := harc 0 ⟨le_rfl, zero_le_one⟩ z hz
  -- An eigenvalue (or spectral angle) lies between a and a+w, so w ≥ 0.
  have hw0 : 0 ≤ w := by linarith [hθ.1, hθ.2]
  intro L M N S
  -- `c(ϑ)` in `w` is the coefficient `C` of `walk_unit_comparison_chord`.
  have hval : walkConstantChord (2*π-w) = walkUnitCoefficientChord w := by
    rw [walkConstantChord_eq, sub_sub_cancel]
  refine ⟨?_, ?_, walk_constant_chord_limit.2.2⟩
  swap
  · -- The "where" clause: the paper's 𝒩, 𝒩', S, κ and mean slope (the spectral comparison).
    have hN (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2 * π) : N x=frameBound x := (paper_series_eq hx0 hx).1
    have hD : deriv N w=frameLip w := (paper_series_eq hw0 hw).2
    have hI : ∫ t in (0:ℝ)..1, deriv N (t*w) = (frameBound w-1/12)/w := paper_mean_slope_eq hw0 hw
    have hS (x : ℝ) (hx0 : 0 ≤ x) (hx : x < 2 * π) : S x=walkLogSlope x :=
      walkLogSlope_closed hx0 hx
    rw [hval, hN w hw0 hw, hN (w/2) (by linarith) (by linarith), hD, hI, hS w hw0 hw,
      hS (w/2) (by linarith) (by linarith)]
    unfold walkUnitCoefficientChord walkFrameSharp
    ring
  obtain ⟨Λ, hΛ, he, hc2, hcmp⟩ := walk_unit_comparison_chord a w hw W ha hunit harc hc
  refine ⟨Λ, hΛ, he, hc2, fun T hT U hU ↦ ?_⟩
  have hT0 : 0 < T := by omega
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT0
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hT0
  have hd1 : ContDiffOn ℝ 1 (derivWithin W (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWd : ContinuousOn (derivWithin W (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) := hd1.continuousOn
  have hWdd : ContinuousOn (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1))
      (Icc (0 : ℝ) 1) :=
    hd1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hinv : 1/(T:ℝ) ≤ 1 := (div_le_one hTR).mpr hT1
  have hinv0 : 0 ≤ 1/(T:ℝ) := by positivity
  -- Each end maximum is at most L, ‖W''‖_{1,T} ≤ M and ‖W'‖_{2,T}² ≤ L².
  have hA : sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) (1/T)) ≤ L :=
    sSup_norm_le_of_subset hWd (Icc_subset_Icc le_rfl hinv)
  have hB : sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1) ≤ L :=
    sSup_norm_le_of_subset hWd (Icc_subset_Icc (by linarith) le_rfl)
  have hM : meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1 ≤ M :=
    (meshMoment_le_sSup_pow hWdd 1).trans_eq (pow_one _)
  have hL2 : meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2 ≤ L^2 :=
    meshMoment_le_sSup_pow hWd 2
  have hnn (A : Set ℝ) (F : ℝ → 𝕄) : 0 ≤ sSup ((fun s ↦ ‖F s‖) '' A) :=
    Real.sSup_nonneg (by rintro y ⟨s, -, rfl⟩; exact norm_nonneg _)
  have hmesh (F : ℝ → 𝕄) (p : ℕ) : 0 ≤ meshMoment F T p :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦ pow_nonneg (hnn _ F) p) (Nat.cast_nonneg _)
  set X := (sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (0 : ℝ) (1/T))+
      sSup ((fun s ↦ ‖derivWithin W (Icc (0 : ℝ) 1) s‖) '' Icc (1-1/T) 1))/2+
      meshMoment (derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1)) T 1+
      meshMoment (derivWithin W (Icc (0 : ℝ) 1)) T 2 with hXdef
  have hX0 : 0 ≤ X :=
    add_nonneg (add_nonneg (div_nonneg (add_nonneg (hnn _ _) (hnn _ _)) (by norm_num))
      (hmesh _ 1)) (hmesh _ 2)
  have hX : X ≤ L+M+L^2 := by linarith
  -- 0 ≤ c(ϑ), as 𝒩(w) ≥ 0, c₂ ≥ 0, and η ≥ 0.
  have hK0 : 0 ≤ walkUnitCoefficientChord w := by
    have hn0 := frameBound_nonneg hw0
    have hc0 : 0 ≤ frameBound w-frameBound (w/2)/2 :=
      (norm_nonneg _).trans (norm_frameSeries_sub_half_le (a := (0:ℂ)) (w := w)
        (by simpa only [norm_zero] using hw0) hw)
    unfold walkUnitCoefficientChord
    exact add_nonneg (add_nonneg (mul_nonneg (by linarith only [hn0]) (sq_nonneg _))
      (mul_nonneg (by linarith only [hc0]) (sq_nonneg _))) (walkFrameSharp_nonneg hw0 hw)
  have hCX : walkUnitCoefficientChord w*X ≤ walkConstantChord (2*π-w)*(L+M+L^2) := by
    rw [hval]
    exact mul_le_mul_of_nonneg_left hX hK0
  exact (hcmp T hT0 U hU).trans (div_le_div_of_nonneg_right hCX hTR.le)

end UnitaryProducts.Paper
