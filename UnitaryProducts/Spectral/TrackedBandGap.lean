/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.CircularBands

/-!
# Exact gaps meet the tracked-band hypotheses

## Declarations

-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The circular gap is at most every admissible angular distance between a band phase and a
phase of the rest of the spectrum: `circularGap` is the `sInf` of these distances, a set bounded
below by `0`. The lower-bound clause of `trackedCircularBand` for $g = \Gamma$. -/
theorem circularGap_le_gb {U : 𝕄} {α β x y : ℝ} (hx : x ∈ Ioo α β) (hy : y ∈ Ioo β (α + 2 * π))
    (hxs : Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U)
    (hys : Complex.exp (-I * (y : ℂ)) ∈ spectrum ℂ U) :
    circularGap U α β ≤ min (y-x) (2*π-(y-x)) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro g ⟨x', y', hx', hy', -, -, rfl⟩
    exact le_min (by linarith [hx'.2, hy'.1]) (by linarith [hx'.1, hy'.2])
  · exact ⟨x, y, hx, hy, hxs, hys, rfl⟩

/-- Supports "Let a $C^2$ walk have a band of $m$ eigenvalues on arcs
$\{e^{-i\theta}:\alpha(s)<\theta<\beta(s)\}$, with $\alpha<\beta<\alpha+2\pi$ and spectral gap
continuous in $s$"
(§4.3): a band of a unitary family on moving arcs whose circular gap
$\Gamma(W(s))$ is continuous and positive on $[0,1]$ is a tracked circular band
(`trackedCircularBand`) with $g = \Gamma$.

Reading the statement against the paper:
* `circularBand W α β` is the band of the family on the arcs (Definition 2.5, `bandData`).
* `circularGap (W s) (α s) (β s)` is $\Gamma(W(s))$, measured along the circle. It is an
  `sInf`, whose junk value `0` on an empty set does not arise under `circularBand`.
* Positivity of the gap (`hpos`) is assumed, as in the paper's hypotheses on the band.

The proof copies the fields of `circularBand` into `trackedCircularBand`, adding `hcont`, `hpos`
and the lower-bound clause `circularGap_le_gb`. -/
theorem trackedCircularBand_circularGap (W : ℝ → 𝕄) (α β : ℝ → ℝ) (hW : circularBand W α β)
    (hcont : ContinuousOn (fun s ↦ circularGap (W s) (α s) (β s)) (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < circularGap (W s) (α s) (β s)) :
    trackedCircularBand W α β (fun s ↦ circularGap (W s) (α s) (β s)) := by
  obtain ⟨ha, hb, h⟩ := hW
  exact ⟨ha, hb, hcont, fun s hs ↦ ⟨hpos s hs, (h s hs).1, (h s hs).2.1, (h s hs).2.2.1,
    (h s hs).2.2.2.1, (h s hs).2.2.2.2.1, (h s hs).2.2.2.2.2,
    fun _ _ hx hy hxs hys ↦ circularGap_le_gb hx hy hxs hys⟩⟩

end UnitaryProducts.Paper
