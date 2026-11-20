/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.BandTransfer

/-!
# Midpoint approximation and continuous leakage bounds

## Declarations

- `UnitaryProducts.Prose.localSteps_norm_integrable`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Complex Set MeasureTheory Filter
noncomputable section
namespace UnitaryProducts.Prose
open UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 3.2: the norm integrands on checkpoint intervals are integrable. -/
theorem localSteps_norm_integrable {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) {n : ℕ} {t : ℕ → ℝ}
    (ht : (variationCheckpoints H T n).2.1 t) {j : ℕ} (hj : j < n) (c : 𝕄) :
    IntervalIntegrable (fun x ↦ ‖H x - c‖) volume (t j) (t (j + 1)) :=
  (((hreg.intervalIntegrable_on hT.le).mono_set (by
    rw [uIcc_of_le (ht.1 (Nat.le_succ j)), uIcc_of_le hT.le]
    exact Icc_subset_Icc (ht.2.1 ▸ ht.1 (Nat.zero_le j)) (ht.2.2 ▸ ht.1 hj))).sub
    (intervalIntegrable_const (c := c))).norm

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end UnitaryProducts.Paper
