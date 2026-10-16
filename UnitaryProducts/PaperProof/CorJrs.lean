/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.LocalSteps

/-!
# The paper's proof of transfer of a continuous leakage bound

## Declarations

- `regulated_of_contDiffOn_two`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Set
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- After Example 3.7: a C² path has finite variation and hence satisfies the regulatedness
hypothesis. The external Jansen–Ruskai–Seiler theorem supplies the continuous leakage hypothesis. -/
theorem regulated_of_contDiffOn_two (F : ℝ → 𝕄)
    (hF : ContDiffOn ℝ 2 F (Icc 0 1)) : IsRegulated F 0 1 := by
  obtain ⟨K, hK⟩ :=
    (hF.of_le one_le_two).exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  exact regulated_of_boundedVariation
    ((eVariationOn_le_lipschitz hK).trans_lt ENNReal.ofReal_lt_top).ne

end UnitaryProducts.PaperProof
