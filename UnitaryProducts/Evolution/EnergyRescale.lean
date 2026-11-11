/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.ExplicitSchedule

/-!
# Rescaling energy and time together

## Declarations

- `continuousOn_energy_rescale`
- `schrodinger_energy_rescale_off_set`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator
open Complex Set
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- If $U$ solves $iU' = HU$ on $[0,T]$ outside $S$, then $t \mapsto U(ct)$ solves the equation of
$cH(ct)$ on $[0, T/c]$ outside the preimage of $S$. -/
theorem schrodinger_energy_rescale_off_set {H U : ℝ → 𝕄} {T c : ℝ}
    (hc : 0 < c) (S : Set ℝ)
    (hU : ∀ t ∈ Icc 0 T, t ∉ S →
      HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 (T / c), t ∉ (fun x : ℝ ↦ c * x) ⁻¹' S →
      HasDerivWithinAt (fun x ↦ U (c * x))
        (-I • ((c • H (c * t)) * U (c * t))) (Icc 0 (T / c)) t := by
  have hm : MapsTo (fun x : ℝ ↦ c * x) (Icc 0 (T / c)) (Icc 0 T) := fun x hx ↦
    ⟨mul_nonneg hc.le hx.1, (le_div_iff₀' hc).mp hx.2⟩
  intro t ht htS
  convert (hU (c * t) (hm ht) htS).scomp t ((hasDerivAt_id t).const_mul c).hasDerivWithinAt hm
    using 1
  simp only [mul_one, smul_mul_assoc, smul_comm c (-I)]

/-- Continuity is preserved on the rescaled interval. -/
theorem continuousOn_energy_rescale {U : ℝ → 𝕄} {T c : ℝ} (hc : 0 < c)
    (hU : ContinuousOn U (Icc 0 T)) :
    ContinuousOn (fun t ↦ U (c * t)) (Icc 0 (T / c)) :=
  hU.comp (continuous_const.mul continuous_id).continuousOn fun _ hx ↦
    ⟨mul_nonneg hc.le hx.1, (le_div_iff₀' hc).mp hx.2⟩

end UnitaryProducts
