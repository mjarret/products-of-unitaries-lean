/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.TrackedBands

/-!
# Empty spectral arcs and phase coordinates

## Declarations

- `norm_of_mem_spectrum`
- `phase_inj`
- `phase_of_unit`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Complex Set Real Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Phases in one open turn $(\alpha, \alpha + 2\pi)$ with the same $e^{-i\theta}$ are equal. -/
theorem phase_inj {α x y : ℝ}
    (hx : x ∈ Ioo α (α + 2 * π)) (hy : y ∈ Ioo α (α + 2 * π))
    (he : Complex.exp (-I * (x : ℂ)) = Complex.exp (-I * (y : ℂ))) : x=y := by
  have hx' : |(-x)-(-(α+π))|<π := abs_lt.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hy' : |(-y)-(-(α+π))|<π := abs_lt.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have he' : Complex.exp (((-x:ℝ) : ℂ)*I)=Complex.exp (((-y:ℝ) : ℂ)*I) := by
    convert he using 1 <;> congr 1 <;> push_cast <;> ring
  have hb := congrArg (UnitaryProducts.argBranch (-(α+π))) he'
  rw [UnitaryProducts.argBranch_exp_mul_I hx',UnitaryProducts.argBranch_exp_mul_I hy'] at hb
  simpa only [Complex.ofReal_neg,neg_neg,Complex.ofReal_inj] using hb

/-- Every unit complex number is $e^{-i\theta}$ for some $\theta \in [a, a + 2\pi)$. -/
theorem phase_of_unit {z : ℂ} (hz : ‖z‖ = 1) (a : ℝ) :
    ∃ θ ∈ Ico a (a+2 * π), z=Complex.exp (-I*(θ:ℂ)) := by
  have h1 : z=Complex.exp (-I*((-arg z:ℝ) : ℂ)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hz,Complex.ofReal_one,one_mul]
    congr 1; push_cast; ring
  refine ⟨toIcoMod two_pi_pos a (-arg z),toIcoMod_mem_Ico _ _ _,h1.trans ?_⟩
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-toIcoDiv two_pi_pos a (-arg z),?_⟩
  rw [toIcoMod,zsmul_eq_mul]
  push_cast
  ring

/-- The eigenvalues of a unitary matrix have modulus one. -/
theorem norm_of_mem_spectrum {U : 𝕄} (hU : star U * U = 1) {z : ℂ}
    (hz : z ∈ spectrum ℂ U) : ‖z‖=1 :=
  mem_sphere_zero_iff_norm.mp (spectrum.subset_circle_of_unitary (𝕜 := ℂ)
    (Matrix.mem_unitaryGroup_iff'.mpr hU) hz)

end UnitaryProducts.Paper
