/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Comparison.IntegralDressedCell
public import UnitaryProducts.Comparison.IntegralUnitSteps
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Corrector.SeparatedStein
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Evolution.RoundedClock
public import UnitaryProducts.Spectral.ProjectorDistance
public import UnitaryProducts.Walks.LogarithmConstruction

/-!
# The first half cell of the unit-step comparison

## Declarations

- `norm_first_half_center_le`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real

noncomputable section
namespace UnitaryProducts.Dressed
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- The first half cell $[0,\frac12]$, which holds $K(0)$ and borrows the corrector of the sample
$K(1)$: given Stein's equation at $K(1)$ (equal end values), $\|K'\|\le L$ and $M$-Lipschitz $K'$
on $[0,B]$, and the center bound $\|Y(0)\|\le qL$, the dressed product moves from
$1-iY_1(0)$ at time $0$ by at most $5M/48+(7q/8+13/384)L^2$. -/
theorem norm_first_half_center_le {K Kd U : ℝ → 𝕄} {B q L M : ℝ}
    (hB : 1 ≤ B) (hK : ∀ t, (K t).IsHermitian)
    (hd : ∀ t ∈ Icc (0 : ℝ) B, HasDerivWithinAt K (Kd t) (Icc 0 B) t)
    (hL : ∀ t ∈ Icc (0 : ℝ) B, ‖Kd t‖ ≤ L)
    (hlip : ∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B, ‖Kd t - Kd s‖ ≤ M * |t - s|)
    (hU : SolvesSchrodinger K U 0 B) (hUn : ∀ t ∈ Icc (0 : ℝ) B, ‖U t‖ ≤ 1)
    (hU0 : U 0 = 1)
    (hstein : evol (K 1) (-1) * frameOp (K 1) (Kd 1) * evol (K 1) 1 - frameOp (K 1) (Kd 1) =
      cellPrimitive (K 1) (Kd 1) 1)
    (hcenter : ‖frameExtension (K 1) (Kd 1) (frameOp (K 1) (Kd 1)) (1 / 2)‖ ≤ q * L) :
    ‖star (U (1/2))*(1-I • frameOp (K 1) (Kd 1))*evol (K 0) (1/2)-
      (1-I • frameExtension (K 1) (Kd 1) (frameOp (K 1) (Kd 1)) (1/2))‖ ≤
      5*M/48+(7*q/8+13/384)*L^2 := by
  have hc : Icc (0:ℝ) (1/2) ⊆ Icc (0:ℝ) B := Icc_subset_Icc le_rfl (by linarith)
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) B := ⟨le_rfl, by linarith⟩
  have h1 : (1:ℝ) ∈ Icc (0:ℝ) B := ⟨zero_le_one, hB⟩
  have hKlip := norm_sub_le_of_derivWithin_le hd hL
  have hb := norm_borrowed_frame_cell (a := 0) (b := 1/2) (c := 0)
    (h := K 1) (g := K 0) (D := Kd 1) (Ybar := frameOp (K 1) (Kd 1))
    (V := evol (K 0))
    (by norm_num) (fun t ht ↦ ((hU t (hc ht)).mono hc).continuousWithinAt)
    (continuous_evol _).continuousOn (fun t _ ↦ hK t)
    (fun t ht ↦ ((hU t (hc (Ioo_subset_Icc_self ht))).mono hc).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))
    (fun t _ ↦ by simpa only [smul_mul_assoc] using hasDerivAt_evol (K 0) t)
    (fun t ht ↦ hUn t (hc (Ioo_subset_Icc_self ht))) (fun t _ ↦ norm_evol_le (hK 0) t)
    (fun t ↦ M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2)
    ((by fun_prop : Continuous fun t:ℝ ↦ M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2).intervalIntegrable _ _)
    (fun t ht ↦ by
      have htm := hc (Ioo_subset_Icc_self ht)
      have hr := norm_borrowed_taylor_right hd hlip h0 htm h1 ht.1.le (by linarith [ht.2] : t ≤ 1)
      have hu := hKlip 1 h1 t htm
      have hv := hKlip 1 h1 0 h0
      rw [abs_of_nonpos (by linarith [ht.2] : t-1 ≤ 0)] at hu
      norm_num only [sub_zero, one_mul] at hr
      norm_num at hv
      have hp := norm_borrowed_residual_profile (hK 1) (hL 1 h1) hcenter hr hu hv
      simpa only [sub_zero] using hp.trans_eq (by ring))
  simpa only [sub_zero, zero_add, show (1/2:ℝ)+1/2=1 by norm_num,
    (frameExtension_periodic_iff _ _ _).mpr hstein, hU0, star_one, one_mul,
    evol_zero, mul_one, integral_borrowed_half_majorant] using hb

end UnitaryProducts.Dressed

