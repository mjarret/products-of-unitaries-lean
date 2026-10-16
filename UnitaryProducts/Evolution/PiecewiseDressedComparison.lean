/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.DuhamelIntegral
public import UnitaryProducts.Evolution.RoundedClock

/-!
# Dressed comparison, cell by cell

## Declarations

- `UnitaryProducts.Paper.UnitStepsProse.abs_integral_distance_of_outside`
- `norm_cellPrimitive_sub_le`
- `cellPrimitive`
- `frameExtension`
- `hasDerivAt_cellPrimitive`
- `hasDerivAt_frameExtension`
- `hasDerivWithinAt_integrated_comparison`
- `integral_affine`
- `norm_cellPrimitive_deriv_le`
- `norm_cellPrimitive_left_le`
- `norm_cellPrimitive_right_le`
- `norm_dressed_jump_le`
- `norm_dressed_steps_le`
- `norm_piecewise_sub_le`
- `sum_piece_sub`
- `norm_sub_le_dressed_add`
-/

@[expose] public section

namespace UnitaryProducts.Dressed
open Real Set MeasureTheory

/-- Integrating the affine sawtooth on either side of its zero. -/
theorem integral_affine (a b c k : ℝ) :
    (∫ t in a..b, (t-c)*k) = ((b-c)^2/2-(a-c)^2/2)*k := by
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

end UnitaryProducts.Dressed

namespace UnitaryProducts.Paper

/-- The finite telescope in Theorem 2.2: neighboring endpoint values leave the jumps. -/
theorem sum_piece_sub {E : Type*} [AddCommGroup E] (l r : ℕ → E) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (r j - l j) =
      r m - l 0 - ∑ j ∈ Finset.range m, (l (j + 1) - r j) := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_succ, Finset.sum_sub_distrib,
    Finset.sum_range_succ' l]
  abel

namespace UnitStepsProse
open Set Real MeasureTheory

/-- the proof of Lemma A.1, the quadratic Taylor bound: integrating distance from a point outside
the interval
is the trapezoid area, with orientation removed. -/
theorem abs_integral_distance_of_outside {a b c : ℝ}
    (hc : c ≤ min a b ∨ max a b ≤ c) :
    |(∫ u in a..b, |u - c|)| = (|a - c| + |b - c|) * |b - a| / 2 := by
  have he : |(∫ u in a..b, |u - c|)| = |(∫ u in a..b, u - c)| := by
    rcases hc with hc | hc
    · exact congrArg abs (intervalIntegral.integral_congr fun u hu ↦
        abs_of_nonneg (sub_nonneg.mpr (hc.trans hu.1)))
    · rw [← abs_neg (∫ u in a..b, u - c), ← intervalIntegral.integral_neg]
      exact congrArg abs (intervalIntegral.integral_congr fun u hu ↦
        abs_of_nonpos (sub_nonpos.mpr (hu.2.trans hc)))
  have habs : |(a - c) + (b - c)| = |a - c| + |b - c| := by
    apply (abs_add_eq_add_abs_iff _ _).2
    rcases hc with hc | hc
    · exact Or.inl ⟨sub_nonneg.mpr (hc.trans (min_le_left _ _)),
        sub_nonneg.mpr (hc.trans (min_le_right _ _))⟩
    · exact Or.inr ⟨sub_nonpos.mpr ((le_max_left _ _).trans hc),
        sub_nonpos.mpr ((le_max_right _ _).trans hc)⟩
  rw [he, show (∫ u in a..b, u - c) = ((b-c)^2/2-(a-c)^2/2) from
    by simpa only [mul_one] using Dressed.integral_affine a b c 1,
    show (b-c)^2/2-(a-c)^2/2 = ((a-c)+(b-c))*(b-a)/2 by ring,
    abs_div, abs_mul, habs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

end UnitStepsProse

end UnitaryProducts.Paper

namespace UnitaryProducts.Dressed
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory UnitaryProducts UnitaryProducts.Corrector Real
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The product rule behind Theorem 2.2, at one point and within an arbitrary set:
$(U^\dagger(1 - iY)V)' = iU^\dagger(K - G - Y' - i(KY - YG))V$, the residual (2.3). Used in
the Lean proof of Theorem 4.2, cell by cell. -/
theorem hasDerivWithinAt_integrated_comparison
    {U V Y : ℝ → 𝕄} {K G Yd : 𝕄} {s : Set ℝ} {t : ℝ}
    (hK : K.IsHermitian)
    (hU : HasDerivWithinAt U (-I • (K * U t)) s t)
    (hV : HasDerivWithinAt V (-I • (G * V t)) s t)
    (hY : HasDerivWithinAt Y Yd s t) :
    HasDerivWithinAt (fun t ↦ star (U t) * (1 - I • Y t) * V t)
      (I • (star (U t) * (K - G - Yd - I • (K * Y t - Y t * G)) * V t)) s t := by
  convert (hU.star.mul ((hasDerivWithinAt_const t s (1 : 𝕄)).sub
    (hY.const_smul I))).mul hV using 1
  simp [show star K = K from hK.eq, mul_add, add_mul,
    mul_assoc, sub_eq_add_neg, smul_smul, add_comm, add_left_comm, add_assoc]


/-- At a switch the dressed curve $U^\dagger(1 - iY)V$ changes by at most the jump of $Y$: this is
how the Lean proof of Theorem 4.2 pays each corrector jump $\|\Delta_j\|$. -/
theorem norm_dressed_jump_le {U V Y Z : 𝕄} (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖star U * (1 - I • Y) * V - star U * (1 - I • Z) * V‖ ≤ ‖Y - Z‖ := by
  rw [← sub_mul, ← mul_sub, sub_sub_sub_cancel_left, ← smul_sub,
    mul_smul_comm, smul_mul_assoc, norm_smul, Complex.norm_I, one_mul]
  simpa only [one_mul, mul_one, norm_sub_rev] using
    norm_mul_le_of_le (norm_mul_le_of_le ((norm_star U).trans_le hU) (le_refl ‖Z - Y‖)) hV

/-- Telescoping over cells: the total displacement is at most the sum of the cell displacements
and the jumps between cells. Used in the Lean proof of Theorem 4.2. -/
theorem norm_piecewise_sub_le {E : Type*} [SeminormedAddCommGroup E]
    (left right : ℕ → E) (n : ℕ) :
    ‖right n - left 0‖ ≤ (∑ j ∈ Finset.range (n+1), ‖right j - left j‖)
      + ∑ j ∈ Finset.range n, ‖left (j+1) - right j‖ := by
  rw [sub_eq_iff_eq_add.mp (Paper.sum_piece_sub left right n).symm]
  exact norm_add_le_of_le (norm_sum_le _ _) (norm_sum_le _ _)

/-- $\int_0^t (s - \frac12)e^{ish}De^{-ish}\,ds$, in the cell coordinate $s = \tau + \frac12 \in
[0,1]$: the integral term of the variation-of-constants formula for the periodic corrector
(the canonical-cell construction in Lemma A.1). Defined for all $t$. -/
def cellPrimitive (h D : 𝕄) (t : ℝ) : 𝕄 :=
  ∫ s in (0 : ℝ)..t, (s-1/2) • (evol h (-s) * D * evol h s)

/-- The primitive has the sawtooth conjugate as derivative. -/
theorem hasDerivAt_cellPrimitive (h D : 𝕄) (t : ℝ) :
    HasDerivAt (cellPrimitive h D)
      ((t-1/2) • (evol h (-t) * D * evol h t)) t := by
  have hc : Continuous (fun s : ℝ ↦ (s-1/2) • (evol h (-s) * D * evol h s)) :=
    (continuous_id.sub continuous_const).smul
      ((((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h))
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Variation of constants in the coordinate $s = \tau + \frac12$:
$e^{-ish}(Y_0 + \int_0^s (\sigma - \frac12)e^{i\sigma h}De^{-i\sigma h}\,d\sigma)e^{ish}$, the
solution of $Y' + i[h, Y] = (s - \frac12)D$ with $Y(0) = Y_0$, $Y_0 =$ `Ybar`
(`hasDerivAt_frameExtension`). With $Y_0 = \mathcal N(\mathrm{ad}_h)(D)$ it is the periodic
corrector of the canonical-cell construction in Lemma A.1. -/
def frameExtension (h D Ybar : 𝕄) (s : ℝ) : 𝕄 :=
  evol h s * (Ybar + cellPrimitive h D s) * evol h (-s)

/-- Supports "the periodic corrector of $D$ at $\Omega$ is the solution $Y(\tau)$,
$-\tfrac12\le\tau\le\tfrac12$, of" in the canonical-cell construction in Lemma A.1: the solution
exists.
`frameExtension h D Ybar` solves the corrector equation; its uniqueness is
`periodic_corrector_unique`.

Reading the statement against the paper:
* `h` is the paper's $\Omega$, and the variable is $s=\tau+\frac12$, so the paper's
  $[-\frac12,\frac12]$ is $[0,1]$ and the right side $\tau D$ is $(s-\frac12)D$.
* The equation is written as $Y'=(s-\frac12)D-i(\Omega Y-Y\Omega)$, at every real $s$.
* `frameExtension h D Ybar 0 = Ybar` (`frameExtension_zero`), so with `Ybar`
  $=\mathcal N(\mathrm{ad}_\Omega)(D)$ the initial condition
  $Y(-\frac12)=\mathcal N(\mathrm{ad}_\Omega)(D)$ holds.
* No hypothesis on $\Omega$, $D$, or the initial value is needed.

The paper takes existence for linear initial-value problems as standard. The proof
differentiates the variation-of-constants formula
$e^{-ish}(Y_0+\int_0^s(\sigma-\frac12)e^{i\sigma h}De^{-i\sigma h}\,d\sigma)e^{ish}$: (1) the
derivatives of $e^{\mp ish}$ and of the integral; (2) the product rule; (3)
$e^{-ish}e^{ish}=1$ and $e^{ish}h=he^{ish}$ collapse the middle term to $(s-\frac12)D$. -/
theorem hasDerivAt_frameExtension (h D Ybar : 𝕄) (t : ℝ) :
    HasDerivAt (frameExtension h D Ybar)
      ((t-1/2) • D - I • (h * frameExtension h D Ybar t - frameExtension h D Ybar t * h)) t := by
  have hn : HasDerivAt (fun s : ℝ ↦ evol h (-s)) (I • (h * evol h (-t))) t := by
    simpa only [smul_mul_assoc, neg_smul, neg_neg, one_smul, neg_mul] using
      (hasDerivAt_evol h (-t)).scomp t (hasDerivAt_neg t)
  have hinv : evol h t * evol h (-t) = 1 := by rw [← evol_add, add_neg_cancel, evol_zero]
  have hc := ((Commute.smul_left_iff₀ (neg_ne_zero.mpr I_ne_zero)).mp (commute_evol h (-t))).eq.symm
  have he : evol h t * ((t-1/2) • (evol h (-t) * D * evol h t)) * evol h (-t) = (t-1/2) • D := by
    simp only [mul_smul_comm, smul_mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [mul_assoc D, hinv, mul_one]
  convert ((hasDerivAt_evol h t).mul
    ((hasDerivAt_const t Ybar).add (hasDerivAt_cellPrimitive h D t))).mul hn using 1
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [zero_add, add_mul, mul_add, he, frameExtension]
  simp only [mul_smul_comm, smul_sub, neg_smul, mul_assoc]
  rw [← hc]
  simp only [mul_add, add_mul, smul_add, smul_mul_assoc, neg_mul, mul_assoc]
  abel

/-- The frozen conjugate in the primitive has speed at most the scalar sawtooth. -/
theorem norm_cellPrimitive_deriv_le (h D : 𝕄) (hh : h.IsHermitian) (t : ℝ) :
    ‖deriv (cellPrimitive h D) t‖ ≤ |t-1/2| * ‖D‖ := by
  rw [(hasDerivAt_cellPrimitive h D t).deriv, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_evol_conj_le hh D t) (abs_nonneg _)


/-- Primitive increments on one side of the center are bounded by the trapezoid area. -/
theorem norm_cellPrimitive_sub_le (h D : 𝕄) (hh : h.IsHermitian) (a b : ℝ)
    (hab : 1 / 2 ≤ min a b ∨ max a b ≤ 1 / 2) :
    ‖cellPrimitive h D b - cellPrimitive h D a‖ ≤
      (|a - 1 / 2| + |b - 1 / 2|) * |b - a| / 2 * ‖D‖ := by
  have hc : Continuous (fun t : ℝ ↦ (t - 1 / 2) • (evol h (-t) * D * evol h t)) :=
    (continuous_id.sub continuous_const).smul
      ((((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h))
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_cellPrimitive h D t) (hc.intervalIntegrable _ _)]
  refine (intervalIntegral.norm_integral_le_abs_of_norm_le
    (ae_of_all _ fun t ↦ by
      simpa only [← (hasDerivAt_cellPrimitive h D t).deriv] using
        norm_cellPrimitive_deriv_le h D hh t)
    ((by fun_prop : Continuous fun t : ℝ ↦ |t - 1 / 2| * ‖D‖).intervalIntegrable _ _)).trans_eq ?_
  rw [intervalIntegral.integral_mul_const, abs_mul, abs_of_nonneg (norm_nonneg D),
    Paper.UnitStepsProse.abs_integral_distance_of_outside hab]

/-- Left-half primitive estimate, integrating from the left boundary. -/
theorem norm_cellPrimitive_left_le (h D : 𝕄) (hh : h.IsHermitian)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    ‖cellPrimitive h D s‖ ≤ (1/8-(s-1/2)^2/2)*‖D‖ := by
  have hb := norm_cellPrimitive_sub_le h D hh 0 s (Or.inr (max_le (by norm_num) hs'))
  simp only [cellPrimitive, intervalIntegral.integral_same, sub_zero,
    zero_sub, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2),
    abs_of_nonpos (sub_nonpos.mpr hs'), abs_of_nonneg hs] at hb
  exact hb.trans_eq (by ring)

/-- Right-half primitive estimate, integrating back from the periodic boundary. -/
theorem norm_cellPrimitive_right_le (h D : 𝕄) (hh : h.IsHermitian)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs' : s ≤ 1) :
    ‖cellPrimitive h D 1 - cellPrimitive h D s‖ ≤ (1/8-(s-1/2)^2/2)*‖D‖ := by
  have hb := norm_cellPrimitive_sub_le h D hh s 1 (Or.inl (le_min hs (by norm_num)))
  simp only [abs_of_nonneg (sub_nonneg.mpr hs),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 1/2),
    abs_of_nonneg (sub_nonneg.mpr hs')] at hb
  exact hb.trans_eq (by ring)

/-- Removing a boundary corrector costs its norm, by unitarity. -/
theorem norm_sub_le_dressed_add {u v Y : 𝕄}
    (hu : star u * u = 1) (hv : ‖v‖ ≤ 1) :
    ‖u-v‖ ≤ ‖star u*(1-I • Y)*v-1‖+‖Y‖ := by
  have he : u-v = -(u*(star u*(1-I • Y)*v-1))-I • (Y*v) := by
    simp only [mul_sub, sub_mul, mul_one, mul_smul_comm, smul_mul_assoc,
      ← mul_assoc, mul_eq_one_comm.mp hu, one_mul]
    abel
  rw [he]; refine (norm_sub_le _ _).trans ?_
  simp only [norm_neg, norm_smul, Complex.norm_I, one_mul]
  simpa only [one_mul, mul_one] using
    add_le_add (norm_mul_le_of_le (norm_le_one_of_star_mul_self hu) le_rfl)
      (norm_mul_le_of_le (le_refl ‖Y‖) hv)

/-- Add the dressed cell displacements and charge every boundary jump once. -/
theorem norm_dressed_steps_le {u v Y : ℕ → 𝕄} {ε : ℕ → ℝ} (n : ℕ)
    (hu : ∀ j ≤ n, star (u j) * u j = 1) (hv : ∀ j ≤ n, ‖v j‖ ≤ 1) (hY0 : Y 0 = 0)
    (hstep : ∀ j < n,
      ‖star (u (j + 1)) * (1 - I • Y (j + 1)) * v (j + 1) - star (u j) * (1 - I • Y (j + 1)) * v j‖
        ≤ ε j) :
    ‖u n-v n‖ ≤ ‖u 0-v 0‖+∑ j ∈ Finset.range n, (ε j+‖Y (j+1)-Y j‖)+‖Y n‖ := by
  let F : ℕ → 𝕄 := fun j ↦ star (u j) * (1 - I • Y j) * v j
  have hzero : ‖F 0 - 1‖ ≤ ‖u 0 - v 0‖ := by
    rw [show F 0 - 1 = star (u 0) * (v 0 - u 0) by simp [F, hY0, mul_sub, hu 0 (Nat.zero_le n)],
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem
      (Matrix.mem_unitaryGroup_iff'.mpr (hu 0 (Nat.zero_le n)))), norm_sub_rev]
  have hacc : ‖F n - F 0‖ ≤ ∑ j ∈ Finset.range n, (ε j + ‖Y (j + 1) - Y j‖) := by
    rw [← Finset.sum_range_sub F]
    refine norm_sum_le_of_le _ fun j hj ↦ (norm_sub_le_norm_sub_add_norm_sub (F (j + 1))
      (star (u j) * (1 - I • Y (j + 1)) * v j) (F j)).trans (add_le_add (hstep j ?_)
      (norm_dressed_jump_le (norm_le_one_of_star_mul_self (hu j ?_)) (hv j ?_))) <;>
      first | exact Finset.mem_range.mp hj | exact (Finset.mem_range.mp hj).le
  exact (norm_sub_le_dressed_add (Y := Y n) (hu n le_rfl) (hv n le_rfl)).trans
    (add_le_add_left ((norm_sub_le_norm_sub_add_norm_sub (F n) (F 0) 1).trans
      ((add_le_add hacc hzero).trans_eq (add_comm _ _))) _)

end
end UnitaryProducts.Dressed
