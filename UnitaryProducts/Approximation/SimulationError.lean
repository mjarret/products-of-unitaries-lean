/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Regulated

/-!
# Same-projector leakage comparison

## Declarations

- `projector_leakage_comparison`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace Prose

/-- Section 4, every orthogonal projection is contractive in the matrix operator norm. -/
theorem norm_orthogonal_projector_le {P : 𝕄} (hP : P.IsHermitian) (hPP : P * P = P) :
    ‖P‖ ≤ 1 := by
  have hs : star P = P := hP
  have hh := CStarRing.norm_star_mul_self (x := P)
  rw [hs, hPP] at hh
  have hid : ‖P‖ ^ 2 = ‖P‖ := by simpa only [pow_two] using hh.symm
  rcases eq_zero_or_one_of_sq_eq_self hid with hzero | hone
  · rw [hzero]; norm_num
  · exact hone.le

end Prose

/-- Same-projector comparison for arbitrary matrices: if $\|W-V\|\le e$ then the leakages
$\|(1-Q)WP\|$ and $\|(1-Q)VP\|$ differ by at most $e$, because $1-Q$ and $P$ are contractions.
This is the two-sided comparison at the start of Section 3.3. -/
theorem projector_leakage_comparison {W V P Q : 𝕄} {e : ℝ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hWV : ‖W - V‖ ≤ e) :
    |‖(1 - Q) * W * P‖ - ‖(1 - Q) * V * P‖| ≤ e := by
  have hp := Prose.norm_orthogonal_projector_le hP.isSelfAdjoint hP.isIdempotentElem.eq
  have hq := Prose.norm_orthogonal_projector_le hQ.one_sub.isSelfAdjoint
    hQ.one_sub.isIdempotentElem.eq
  have hb : ‖(1 - Q) * (W - V) * P‖ ≤ ‖W - V‖ := by
    calc
      _ ≤ (1 * ‖W - V‖) * 1 :=
        norm_mul_le_of_le (norm_mul_le_of_le hq (le_refl _)) hp
      _ = _ := by rw [one_mul, mul_one]
  refine (abs_norm_sub_norm_le _ _).trans
    (le_of_eq_of_le ?_ (hb.trans hWV))
  simp only [mul_sub, sub_mul]

end UnitaryProducts
