/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Lipschitz regularity of the derivative

A twice continuously differentiable matrix family on the unit interval has a Lipschitz
derivative there.
-/

@[expose] public section

open Set
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RoundedClocks.WalkLeakageRegularity

variable {d : ℕ}

/-- On the compact unit interval, a C² family has a Lipschitz derivative. -/
theorem exists_lipschitz_derivative
    {K : ℝ → Matrix (Fin d) (Fin d) ℂ} (hK : IsC2Family K) :
    ∃ L, HasLipschitzDerivative K L := by
  have hder : ContDiffOn ℝ 1 (∂K) (Icc (0 : ℝ) 1) :=
    hK.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)
  obtain ⟨L, hL⟩ := hder.exists_lipschitzOnWith (by norm_num)
    (convex_Icc 0 1) isCompact_Icc
  refine ⟨L, hK.differentiableOn (by norm_num), ?_⟩
  intro s hs t ht
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hL.dist_le_mul s hs t ht

end RoundedClocks.WalkLeakageRegularity
