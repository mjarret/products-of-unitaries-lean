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

- `exactGap`
- `exactGap_le_gb`
- `exactGap_pos_gb`
- `jrs_coefficient_tracked_exactGap`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The exact spectral gap $\Gamma(F(s))$ of a band `B` of a Hermitian family at `s` (paragraph
after Definition 2.5): the distance `min |λ_i - λ_j|` from the eigenvalues `λ_i ∈ B s` to the
eigenvalues `λ_j ∉ B s` (`UnitaryProducts.finiteSpectralDistance`, as in `bandGap`).

Junk value: it is `0` when `s ∉ [0,1]` or when the band or its complement has no eigenvalue. On
$[0,1]$ a band of $m > 0$ eigenvalues with an eigenvalue outside excludes both, and then the
value is positive (`exactGap_pos_gb`). -/
def exactGap (F : ℝ → 𝕄) (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (B : ℝ → Set ℝ) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ Icc (0 : ℝ) 1 then
    if h : (Finset.univ.filter (fun i ↦ (hF s hs).eigenvalues i ∈ B s)).Nonempty ∧
        (Finset.univ.filter (fun i ↦ (hF s hs).eigenvalues i ∉ B s)).Nonempty then
      UnitaryProducts.finiteSpectralDistance (hF s hs).eigenvalues (hF s hs).eigenvalues
        _ _ h.1 h.2
    else 0
  else 0

/-- The exact gap is at most every distance from an eigenvalue in the band to one outside it: the
lower-bound clause of `jrsCoefficientTracked` for $g = \Gamma$. -/
theorem exactGap_le_gb (F : ℝ → 𝕄) (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (B : ℝ → Set ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {i j : Fin d}
    (hi : (hF s hs).eigenvalues i ∈ B s) (hj : (hF s hs).eigenvalues j ∉ B s) :
    exactGap F hF B s ≤ |(hF s hs).eigenvalues i-(hF s hs).eigenvalues j| := by
  classical
  unfold exactGap UnitaryProducts.finiteSpectralDistance
  rw [dif_pos hs]
  split
  · refine (Finset.inf'_le _ (b := i) ?_).trans (Finset.inf'_le
      (fun l ↦ |(hF s hs).eigenvalues i-(hF s hs).eigenvalues l|) (b := j) ?_)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  · next h =>
    exact (h ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩,
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩).elim

/-- On a band of `m` eigenvalues that leaves an eigenvalue outside at every `s`, the exact gap
is positive on `[0,1]`: the positivity clause of `jrsCoefficientTracked` for $g = \Gamma$. -/
theorem exactGap_pos_gb (F : ℝ → 𝕄) (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (m : ℕ) (B : ℝ → Set ℝ) (hband : (band F hF m B).1)
    (hout : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ∃ i, (hF s hs).eigenvalues i ∉ B s) :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 < exactGap F hF B s := by
  intro s hs
  have h0 := hband.1
  rw [← hband.2.1 s hs] at h0
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
  obtain ⟨j, hj⟩ := hout s hs
  classical
  unfold exactGap UnitaryProducts.finiteSpectralDistance
  rw [dif_pos hs]
  split
  · rw [Finset.lt_inf'_iff]
    intro k hk
    rw [Finset.lt_inf'_iff]
    intro l hl
    exact abs_pos.mpr (sub_ne_zero.mpr fun h ↦
      (Finset.mem_filter.mp hl).2 (h ▸ (Finset.mem_filter.mp hk).2))
  · next h =>
    exact (h ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩⟩,
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩).elim

/-- Supports the hypothesis "spectral gap $\Gamma(H(s))>0$ continuous in $s$" in the application
after
Example 3.7 (and in the Jansen–Ruskai–Seiler instance of the transfer paragraph in Section 4.2):
for a $C^2$ Hermitian
family $H$ with a band of $m$
eigenvalues, the exact gap, if continuous on $[0,1]$, is an admissible gap bound $g = \Gamma$ in
the hypothesis bundle `jrsCoefficientTracked` behind $J_m(H)$.

Reading the statement against the paper:
* `exactGap F hF B s` is $\Gamma(\tilde H(s))$; its junk value `0` is excluded on $[0,1]$ by
  `hband` and `hout`.
* `hout` (an eigenvalue outside `B s` at every $s$) is the properness of the band in
  Definition 2.5.
* Positivity of $\Gamma$, which the paper assumes, is derived here. Continuity (`hcont`) is
  assumed, as in the paper.
* Stronger than the paper's setting: no $d\ge1$.
* `(jrsCoefficientTracked F hF m g B).1` is the bundle: $C^2$, $g$ continuous, $0 < g \le$ every
  distance from an eigenvalue in the band to one outside, and the band
  (`jrs_coefficient_tracked_band`).

The proof unpacks the bundle with `jrs_coefficient_tracked_band`, takes positivity from
`exactGap_pos_gb` and the lower-bound clause from `exactGap_le_gb`, and passes the $C^2$ and
continuity hypotheses through. -/
theorem jrs_coefficient_tracked_exactGap (F : ℝ → 𝕄)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian) (m : ℕ) (B : ℝ → Set ℝ)
    (hC : ContDiffOn ℝ 2 F (Icc 0 1)) (hband : (band F hF m B).1)
    (hout : ∀ s (hs : s ∈ Icc (0 : ℝ) 1), ∃ i, (hF s hs).eigenvalues i ∉ B s)
    (hcont : ContinuousOn (exactGap F hF B) (Icc 0 1)) :
    (jrsCoefficientTracked F hF m (exactGap F hF B) B).1 :=
  (jrs_coefficient_tracked_band F hF m _ B).1.2
    ⟨hC, hcont, fun s hs ↦ ⟨exactGap_pos_gb F hF m B hband hout s hs,
      fun _ _ hi hj ↦ exactGap_le_gb F hF B hs hi hj⟩, hband⟩


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
