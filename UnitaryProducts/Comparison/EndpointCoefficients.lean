/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps

/-!
# The `C²` unit-step comparison with separate end and interior coefficients

## Declarations

- `unit_steps_local_norms_ends`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `unit_steps_local_data_ends` with the per-step bounds taken to be the step maxima of $\|H'\|$
and $\|H''\|$ (`meshSupNorm`). -/
theorem unit_steps_local_norms_ends [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ)
    (w b₀ b₁ r₀ r₁ : ℝ) (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hb0 : (1/8:ℝ)≤b₀) (hb1 : 1/24+frameBound w≤b₁)
    (hr0 : frameBound w-frameBound (w/2)/2+1/24≤r₀)
    (hr1 : (frameBound w-frameBound (w/2)/2)/4+1/64+2*frameLip w≤r₁) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(2*(frameBound w-frameBound (w/2)/2)*boundaryMean Hd N+
        b₀*((meshSupNorm Hdd N 0+meshSupNorm Hdd N (N-1))/N)+b₁*((∑ j ∈ Finset.range (N-2),
          meshSupNorm Hdd N (j+1))/N)+(T/N)*(r₀*(((meshSupNorm Hd N 0)^2+(meshSupNorm Hd N
          (N-1))^2)/N)+
          r₁*((∑ j ∈ Finset.range (N-2), (meshSupNorm Hd N (j+1))^2)/N))) := by
  intro Hd Hdd
  have hd : ContDiffOn ℝ 1 Hd (Icc (0 : ℝ) 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by
    norm_num)
  have hdd : ContDiffOn ℝ 0 Hdd (Icc (0 : ℝ) 1) := hd.derivWithin uniqueDiffOn_Icc_zero_one (by
    norm_num)
  exact unit_steps_local_data_ends H U T N w b₀ b₁ r₀ r₁ (meshSupNorm Hd N) (meshSupNorm Hdd N)
    hT hN2 hw hH hc
    (fun i _ s hs ↦ meshSup_bound hd.continuousOn hs)
    (fun i _ s hs ↦ meshSup_bound hdd.continuousOn hs)
    hdiff hU hb0 hb1 hr0 hr1

end UnitaryProducts.Paper
