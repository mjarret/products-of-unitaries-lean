/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PeriodicFrameDecomposition

/-!
# One unit cell with the corrector, in integral form

## Declarations

- `norm_dressed_full_cell_integral_sharp_le`
-/

@[expose] public section

namespace UnitaryProducts.Dressed
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory UnitaryProducts UnitaryProducts.Corrector Real
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- One unit cell in integral form: if $h$ is within $w/2$ of a scalar, $w<2\pi$, the dressed
product with $Y$ started at $\mathcal N(\mathrm{ad}_h)(D)$ (`frameOp h D`) changes over $[0,1]$ by
at most
$\int_0^1\bigl(\|K-h-(t-\frac12)D\|+\|K-h\|(\mathcal N(w)+\frac18-\frac{(t-1/2)^2}2)\|D\|\bigr)dt$,
for any slope $D$ (no derivative bounds; `frameBound w` is $\mathcal N(w)$). -/
theorem norm_dressed_full_cell_integral_sharp_le [NeZero d]
    {K U V : ℝ → 𝕄} {h D : 𝕄} {c w : ℝ}
    (hh : h.IsHermitian) (hw : w < 2 * Real.pi)
    (hwidth : ‖h - (c : ℂ) • 1‖ ≤ w / 2)
    (hKc : ContinuousOn K (Icc 0 1))
    (hUc : ContinuousOn U (Icc 0 1)) (hVc : ContinuousOn V (Icc 0 1))
    (hK : ∀ t ∈ Ioo (0 : ℝ) 1, (K t).IsHermitian)
    (hU : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt U (-I • (K t * U t)) t)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V (-I • (h * V t)) t)
    (hUn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖U t‖ ≤ 1)
    (hVn : ∀ t ∈ Ioo (0 : ℝ) 1, ‖V t‖ ≤ 1) :
    ‖star (U 1) * (1-I • frameOp h D) * V 1 -
      star (U 0) * (1-I • frameOp h D) * V 0‖ ≤
      ∫ t in (0 : ℝ)..1, ‖K t-h-(t-1/2) • D‖ +
        ‖K t-h‖*((frameBound w+1/8-(t-1/2)^2/2)*‖D‖) := by
  have ha : ‖I • adL h‖ < 2 * Real.pi :=
    lt_of_le_of_lt ((norm_I_smul_adL_le h (c : ℂ)).trans (by linarith)) hw
  exact norm_periodic_frame_comparison_le h D (frameOp h D) hh
    (evol_conj_frameOp_sub h D ha) (norm_frameOp_le hw hwidth)
    hKc hUc hVc hK hU hV hUn hVn

end
end UnitaryProducts.Dressed
