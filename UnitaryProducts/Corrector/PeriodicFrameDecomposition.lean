/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import UnitaryProducts.Evolution.PiecewiseDressedComparison

/-!
# The periodic corrector on one cell

## Declarations

- `UnitaryProducts.Paper.corrector_cancels_taylor`
- `norm_borrowed_frame_cell`
- `residual_of_borrowed_frame`
- `frameExtension_periodic_iff`
- `frameExtension_sub_left_le`
- `frameExtension_sub_right_le`
- `frameExtension_zero`
- `frameRemainder`
- `norm_frameExtension_le_endpoint`
- `norm_periodic_frame_comparison_le`
- `norm_periodic_frame_comparison_of_integrand`
- `norm_periodic_frame_residual_le`
- `norm_periodic_frame_residual_le_endpoint`
- `periodic_frame_decomposition`
-/

@[expose] public section

namespace UnitaryProducts.Paper
open Complex
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1 and the abstract, within-step cancellation: substituting the corrector equation
removes the linear Taylor term from the comparison residual. The Taylor remainder and
the product of the Hamiltonian difference with the corrector remain. -/
theorem corrector_cancels_taylor (K G Y Yd D : 𝕄) (τ : ℝ)
    (heq : Yd + I • (G * Y - Y * G) = τ • D) :
    K - G - Yd - I • (K * Y - Y * G) =
      K - G - τ • D - I • ((K - G) * Y) := by
  rw [← heq]
  simp only [smul_sub, sub_mul, sub_sub]
  abel

end UnitaryProducts.Paper

namespace UnitaryProducts.Dressed
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The periodic endpoint condition is exactly Stein's equation: the corrector ends where it
started if and only if
$e^{ih}\bar Ye^{-ih}-\bar Y=\int_0^1(\tau-\frac12)e^{i\tau h}De^{-i\tau h}\,d\tau$. -/
theorem frameExtension_periodic_iff (h D Ybar : 𝕄) :
    frameExtension h D Ybar 1 = Ybar ↔
      evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1 := by
  have hi : evol h 1 * evol h (-1) = 1 := by
    simpa only [neg_neg] using evol_neg_mul_self h (-1)
  have hinj := (Matrix.mul_left_injective_of_inv (evol h 1) (evol h (-1)) hi).comp
    (Matrix.mul_right_injective_of_inv (evol h 1) (evol h (-1)) hi)
  conv_lhs => rw [← hinj.eq_iff]
  simp only [Function.comp_apply, frameExtension, ← mul_assoc, evol_neg_mul_self, one_mul]
  simp only [mul_assoc, evol_neg_mul_self, mul_one]
  rw [sub_eq_iff_eq_add', eq_comm]


/-- The left endpoint is the prescribed frame value. -/
theorem frameExtension_zero (h D Ybar : 𝕄) : frameExtension h D Ybar 0 = Ybar := by
  simp only [frameExtension, cellPrimitive, intervalIntegral.integral_same, add_zero,
    neg_zero, evol_zero, one_mul, mul_one]

/-- Distance from the left endpoint's freely rotated frame. -/
theorem frameExtension_sub_left_le (h D Ybar : 𝕄) (hh : h.IsHermitian)
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    ‖frameExtension h D Ybar s - evol h s * Ybar * evol h (-s)‖ ≤
      (1/8-(s-1/2)^2/2)*‖D‖ := by
  rw [frameExtension, mul_add, add_mul, add_sub_cancel_left]
  simpa only [neg_neg] using
    (norm_evol_conj_le hh (cellPrimitive h D s) (-s)).trans
      (norm_cellPrimitive_left_le h D hh hs hs')

/-- Distance from the right endpoint's freely rotated frame. -/
theorem frameExtension_sub_right_le (h D Ybar : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {s : ℝ} (hs : 1 / 2 ≤ s) (hs' : s ≤ 1) :
    ‖frameExtension h D Ybar s - evol h (s-1) * Ybar * evol h (-(s-1))‖ ≤
      (1/8-(s-1/2)^2/2)*‖D‖ := by
  have hrot : evol h (s-1) * Ybar * evol h (-(s-1)) =
      evol h s * (Ybar + cellPrimitive h D 1) * evol h (-s) := by
    rw [← hstein, add_sub_cancel, sub_eq_add_neg, neg_add_rev, neg_neg,
      evol_add, evol_add]
    simp only [mul_assoc]
  rw [hrot, frameExtension, ← sub_mul, ← mul_sub, add_sub_add_left_eq_sub]
  simpa only [neg_neg, norm_sub_rev] using
    (norm_evol_conj_le hh (cellPrimitive h D s - cellPrimitive h D 1) (-s)).trans
      (by simpa only [norm_sub_rev] using norm_cellPrimitive_right_le h D hh hs hs')

/-- The remainder from the freely rotated frame at the nearer endpoint: the corrector minus
$e^{-i(s-e)h}\,Y_0\,e^{i(s-e)h}$, $Y_0 =$ `Ybar`, with $e = 0$ for $s \le \tfrac12$ and $e = 1$
otherwise. -/
def frameRemainder (h D Ybar : 𝕄) (s : ℝ) : 𝕄 :=
  frameExtension h D Ybar s -
    evol h (s - if s ≤ 1/2 then 0 else 1) * Ybar * evol h (-(s - if s ≤ 1/2 then 0 else 1))

/-- Exact nearest-endpoint decomposition and its sharp parabolic remainder bound. -/
theorem periodic_frame_decomposition (h D Ybar : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1) :
    (∀ s ∈ Icc (0 : ℝ) 1,
      frameExtension h D Ybar s =
        evol h (s - if s ≤ 1/2 then 0 else 1) * Ybar *
          evol h (-(s - if s ≤ 1/2 then 0 else 1)) + frameRemainder h D Ybar s ∧
      ‖frameRemainder h D Ybar s‖ ≤ (1/8-(s-1/2)^2/2)*‖D‖) ∧
    frameRemainder h D Ybar 0 = 0 ∧ frameRemainder h D Ybar 1 = 0 := by
  refine ⟨fun s hs ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · dsimp only [frameRemainder]; abel
  · by_cases hleft : s ≤ 1/2
    · simpa only [frameRemainder, if_pos hleft, sub_zero] using
        frameExtension_sub_left_le h D Ybar hh hs.1 hleft
    · simpa only [frameRemainder, if_neg hleft] using
        frameExtension_sub_right_le h D Ybar hh hstein (le_of_not_ge hleft) hs.2
  · norm_num [frameRemainder, frameExtension_zero, evol_zero]
  · rw [frameRemainder, (frameExtension_periodic_iff h D Ybar).mpr hstein]
    norm_num [evol_zero]

/-- The frame norm depends directly on its endpoint value and parabolic remainder. -/
theorem norm_frameExtension_le_endpoint (h D Ybar : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖frameExtension h D Ybar s‖ ≤ ‖Ybar‖ + (1/8-(s-1/2)^2/2)*‖D‖ := by
  obtain ⟨he, hn⟩ := (periodic_frame_decomposition h D Ybar hh hstein).1 s hs
  rw [he]
  exact norm_add_le_of_le
    (by simpa only [neg_neg] using
      norm_evol_conj_le hh Ybar (-(s - if s ≤ 1/2 then 0 else 1))) hn

/-- Residual bound using the actual endpoint value, without a scalar frame bound. -/
theorem norm_periodic_frame_residual_le_endpoint (h D Ybar K : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖K-h-(s-1/2) • D-I • ((K-h)*frameExtension h D Ybar s)‖ ≤
      ‖K-h-(s-1/2) • D‖ + (‖Ybar‖ + (1/8-(s-1/2)^2/2)*‖D‖)*‖K-h‖ := by
  apply norm_sub_le_of_le le_rfl
  rw [norm_smul, Complex.norm_I, one_mul, mul_comm _ ‖K-h‖]
  exact norm_mul_le_of_le le_rfl (norm_frameExtension_le_endpoint h D Ybar hh hstein hs)

/-- Sharp residual bound, with the frame value and remainder contributions separated. -/
theorem norm_periodic_frame_residual_le (h D Ybar K : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {N s : ℝ} (hYbar : ‖Ybar‖ ≤ N * ‖D‖) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖K-h-(s-1/2) • D-I • ((K-h)*frameExtension h D Ybar s)‖ ≤
      ‖K-h-(s-1/2) • D‖ +
        N*‖D‖*‖K-h‖ + (1/8-(s-1/2)^2/2)*‖D‖*‖K-h‖ := by
  linarith [norm_periodic_frame_residual_le_endpoint h D Ybar K hh hstein hs,
    mul_le_mul_of_nonneg_right hYbar (norm_nonneg (K-h))]

/-- The residual $R=K-G-Y'-i(KY-YG)$ of (2.3) when $Y$ is the corrector of slope $D$ at
a frozen $h$ (so $Y'+i[h,Y]=\tau D$) but the cell holds $G$: it equals
$K-G-\tau D-i((K-h)Y-Y(G-h))$. Used for the end half cells, which borrow a neighbour's corrector. -/
theorem residual_of_borrowed_frame (K G h Y Yd D : 𝕄) (τ : ℝ)
    (heq : Yd + I • (h * Y - Y * h) = τ • D) :
    K-G-Yd-I • (K*Y-Y*G) = K-G-τ • D-I • ((K-h)*Y-Y*(G-h)) := by
  rw [← heq]
  simp only [sub_mul, mul_sub, smul_sub, sub_add_eq_sub_sub]
  abel


/-- Theorem 2.2 on one piece $[a,b]$: with $Y(t)$ the corrector of slope $D$ at $h$ centered
at $c$, $U$ the evolution of $K$ and $V$ that of the constant matrix $g$, the dressed product
$U^\dagger(1-iY)V$ changes by at most $\int_a^bf$ whenever $f$ bounds the residual
$\|K-g-(t-c)D-i((K-h)Y-Y(g-h))\|$ (`residual_of_borrowed_frame`). -/
theorem norm_borrowed_frame_cell {K U V : ℝ → 𝕄} {h g D Ybar : 𝕄} {a b c : ℝ}
    (hab : a ≤ b) (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hK : ∀ t ∈ Ioo a b, (K t).IsHermitian)
    (hU : ∀ t ∈ Ioo a b, HasDerivAt U (-I • (K t * U t)) t)
    (hV : ∀ t ∈ Ioo a b, HasDerivAt V (-I • (g * V t)) t)
    (hUn : ∀ t ∈ Ioo a b, ‖U t‖ ≤ 1) (hVn : ∀ t ∈ Ioo a b, ‖V t‖ ≤ 1)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hb : ∀ t ∈ Ioo a b,
      ‖K t - g - (t - c) • D - I • ((K t - h) * frameExtension h D Ybar (t - c + 1 / 2) -
        frameExtension h D Ybar (t - c + 1 / 2) * (g - h))‖ ≤ f t) :
    ‖star (U b)*(1-I • frameExtension h D Ybar (b-c+1/2))*V b-
      star (U a)*(1-I • frameExtension h D Ybar (a-c+1/2))*V a‖ ≤ ∫ t in a..b, f t := by
  let Y : ℝ → 𝕄 := fun t ↦ frameExtension h D Ybar (t-c+1/2)
  let Yd : ℝ → 𝕄 := fun t ↦ (t-c) • D-I • (h*Y t-Y t*h)
  have hY (t : ℝ) : HasDerivAt Y (Yd t) t := by
    simpa only [add_sub_cancel_right] using
      ((hasDerivAt_frameExtension h D Ybar (t-c+1/2)).comp_add_const (t-c) (1/2)).comp_sub_const t c
  have hYc : Continuous Y := continuous_iff_continuousAt.mpr fun t ↦ (hY t).continuousAt
  have hder t (ht : t ∈ Ioo a b) :=
    (hasDerivWithinAt_integrated_comparison (hK t ht) (hU t ht).hasDerivWithinAt
      (hV t ht).hasDerivWithinAt (hY t).hasDerivWithinAt (s := Set.univ)).hasDerivAt Filter.univ_mem
  apply norm_sub_le_integral_off_countable ∅ countable_empty hab
    ((hUc.star.mul (continuousOn_const.sub (hYc.continuousOn.const_smul I))).mul hVc)
    (fun t ht _ ↦ (hder t ht).differentiableAt) _ hf
  intro t ht _
  change ‖deriv (fun s ↦ star (U s)*(1-I • Y s)*V s) t‖ ≤ f t
  rw [(hder t ht).deriv, norm_smul, Complex.norm_I, one_mul]
  have heq : Yd t+I • (h*Y t-Y t*h)=(t-c) • D := sub_add_cancel _ _
  rw [residual_of_borrowed_frame _ _ _ _ _ _ _ heq]
  simpa only [one_mul, mul_one] using norm_mul_le_of_le
    (norm_mul_le_of_le ((norm_star _).trans_le (hUn t ht)) (hb t ht)) (hVn t ht)

/-- A periodic frame consumes the piece's integrand majorant directly.
No operator bound or separate corrected-step increment is assumed. -/
theorem norm_periodic_frame_comparison_of_integrand
    (h D Ybar : 𝕄)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {K U V : ℝ → 𝕄} {f : ℝ → ℝ}
    (hUc : ContinuousOn U (Icc 0 1)) (hVc : ContinuousOn V (Icc 0 1))
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, (K t).IsHermitian)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt U (-I • (K t * U t)) t)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V (-I • (h * V t)) t)
    (hUn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖U t‖ ≤ 1)
    (hVn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖V t‖ ≤ 1)
    (hfi : IntervalIntegrable f volume 0 1)
    (hresidual : ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖K t - h - (t - 1 / 2) • D - I • ((K t - h) * frameExtension h D Ybar t)‖ ≤ f t) :
    ‖star (U 1)*(1-I • Ybar)*V 1-star (U 0)*(1-I • Ybar)*V 0‖ ≤
      ∫ t in (0 : ℝ)..1, f t := by
  have hb := norm_borrowed_frame_cell (h := h) (g := h) (D := D) (Ybar := Ybar)
    (c := 1 / 2) zero_le_one hUc hVc hK hU hV hUn hVn f hfi
    (fun t ht ↦ by simpa only [sub_self, mul_zero, sub_zero, sub_add_cancel] using hresidual t ht)
  simpa only [sub_add_cancel, frameExtension_zero,
    (frameExtension_periodic_iff h D Ybar).mpr hstein] using hb

/-- The value bound and the decomposition supply the sharp piece integrand. -/
theorem norm_periodic_frame_comparison_le
    (h D Ybar : 𝕄) (hh : h.IsHermitian)
    (hstein : evol h (-1) * Ybar * evol h 1 - Ybar = cellPrimitive h D 1)
    {N : ℝ} (hYbar : ‖Ybar‖ ≤ N * ‖D‖)
    {K U V : ℝ → 𝕄}
    (hKc : ContinuousOn K (Icc 0 1))
    (hUc : ContinuousOn U (Icc 0 1)) (hVc : ContinuousOn V (Icc 0 1))
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, (K t).IsHermitian)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt U (-I • (K t * U t)) t)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V (-I • (h * V t)) t)
    (hUn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖U t‖ ≤ 1)
    (hVn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖V t‖ ≤ 1) :
    ‖star (U 1)*(1-I • Ybar)*V 1-star (U 0)*(1-I • Ybar)*V 0‖ ≤
      ∫ t in (0 : ℝ)..1, ‖K t-h-(t-1/2) • D‖ +
        ‖K t-h‖*((N+1/8-(t-1/2)^2/2)*‖D‖) := by
  apply norm_periodic_frame_comparison_of_integrand h D Ybar hstein hUc hVc hK hU hV
    hUn hVn (ContinuousOn.intervalIntegrable_of_Icc zero_le_one (by fun_prop))
  intro t ht
  exact (norm_periodic_frame_residual_le h D Ybar (K t) hh hstein hYbar
    (Ioo_subset_Icc_self ht)).trans_eq (by ring)

end
end UnitaryProducts.Dressed
