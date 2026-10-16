/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import UnitaryProducts.Approximation.JRSComparison
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Comparison.IntegralDressedCell
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Corrector.SecondDerivative
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Evolution.RoundedTransfer
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmBranch
public import UnitaryProducts.Walks.LogarithmConstruction
public import UnitaryProducts.Walks.LogarithmSmoothness

/-!
# The unit-step comparison in integral form

## Declarations

- `cellIntegral`
- `halfIntegral`
- `halfIntegral_le_lipschitz`
- `unit_steps_integral`
-/

@[expose] public section

namespace UnitaryProducts.Dressed
open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory UnitaryProducts UnitaryProducts.Corrector Real
noncomputable section
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The Duhamel cost of the two end half steps of the rounded clock on $[0,N]$:
$\int_0^{1/2}\|H(t/N)-H(0)\|\,dt+\int_{N-1/2}^N\|H(t/N)-H(1)\|\,dt$. An interval integral, so `0`
for a non-integrable integrand; every use has $H$ continuous on $[0,1]$ and $N\ge1$. -/
def halfIntegral (H : ℝ → 𝕄) (N : ℕ) : ℝ :=
  (∫ t in (0 : ℝ)..(1/2), ‖H (t/N)-H 0‖) +
  (∫ t in ((N : ℝ)-1/2)..(N : ℝ), ‖H (t/N)-H 1‖)

/-- The integrated residual majorant of the interior cell $[j-\frac12,j+\frac12]$ of $[0,N]$ with
sample
$H(j/N)$: the Taylor term $\|H(\cdot/N)-H(j/N)-(t-\frac12)D_j/N\|$ plus the displacement
$\|H(\cdot/N)-H(j/N)\|$ weighted by the corrector profile
$(\mathcal N(w_j)+\frac18-\frac{(t-1/2)^2}2)\|D_j/N\|$. `D j` is the slow-time slope; the slope on
$[0,N]$ is $D_j/N$. An interval integral, so `0` for a non-integrable integrand. -/
def cellIntegral (H : ℝ → 𝕄) (D : ℕ → 𝕄) (N : ℕ) (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ‖H ((t+(j:ℝ)-1/2)/N)-H (j/N)-(t-1/2) • ((N:ℝ)⁻¹ • D j)‖ +
    ‖H ((t+(j:ℝ)-1/2)/N)-H (j/N)‖ *
      ((frameBound (w j)+1/8-(t-1/2)^2/2)*‖(N:ℝ)⁻¹ • D j‖)

/-- The unit-step comparison in integral form: with interior samples $H(j/N)$ within $w_j/2$ of a
scalar, $w_j<2\pi$, and any slopes $D_j$, the error of the product of the $H(j/N)$ against the
evolution of $H(t/N)$ on $[0,N]$ is at most `halfIntegral H N`, plus the cell integrals and the
corrector jumps $\|Y_{j+1}-Y_j\|$, plus the last corrector value $\|Y_{N-1}\|$. The proof
telescopes the dressed product over the cells (`norm_dressed_steps_le`) with Duhamel on the two
end half steps. -/
theorem unit_steps_integral [NeZero d] (H : ℝ → 𝕄) (D : ℕ → 𝕄) (N : ℕ)
    (w c : ℕ → ℝ) (U : ℝ → 𝕄) (hN : 0 < N) (hherm : ∀ s, (H s).IsHermitian)
    (hcont : ContinuousOn H (Icc 0 1))
    (hU : SolvesSchrodinger (fun t ↦ H (t / N)) U 0 N) (hU0 : U 0 = 1)
    (hw : ∀ j, 0 < j → j < N → w j < 2 * Real.pi)
    (hwidth : ∀ j, 0 < j → j < N → ‖H (j / N) - (c j : ℂ) • 1‖ ≤ w j / 2)
 :
    let Y : ℕ → 𝕄 := fun j ↦ if j = 0 then 0 else frameOp (H (j / N)) ((N : ℝ)⁻¹ • D j)
    ‖pieceProduct (fun _ ↦ 1) (fun j ↦ H (j / N)) N
        - evol (H 1) (-(1 / 2)) * U N * evol (H 0) (1 / 2)‖ ≤
      halfIntegral H N
        + ∑ j ∈ Finset.range (N - 1),
            (cellIntegral H D N w (j+1)
              + ‖Y (j + 1) - Y j‖)
        + ‖Y (N - 1)‖ := by
  intro Y
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmem : ∀ t ∈ Icc (0 : ℝ) N, t / N ∈ Icc (0 : ℝ) 1 := fun t ht ↦
    ⟨div_nonneg ht.1 hNpos.le, (div_le_one hNpos).mpr ht.2⟩
  have hKc : ContinuousOn (fun t : ℝ ↦ H (t / N)) (Icc 0 N) :=
    hcont.comp (continuous_id.div_const _).continuousOn hmem
  have hKh : ∀ t : ℝ, (H (t / N)).IsHermitian := fun t ↦ hherm _
  have hUn : ∀ t ∈ Icc (0 : ℝ) N, ‖U t‖ ≤ 1 := fun t ht ↦
    hU.norm_le_one_of_initial_one (fun t _ ↦ hKh t) hU0 ht
  have hY0 : Y 0 = 0 := if_pos rfl
  have hYs : ∀ j, Y (j + 1)
      = frameOp (H ((j + 1 : ℕ) / N)) ((N : ℝ)⁻¹ • D (j + 1)) :=
    fun j ↦ if_neg (Nat.succ_ne_zero j)
  have hUunit : ∀ t ∈ Icc (0 : ℝ) N, star (U t)*U t=1 := fun t ht ↦ by
    rw [hU.star_mul_self_eq (fun t _ ↦ hKh t) t ht, hU0, star_one, one_mul]
  have hstep : ∀ j < N-1,
      ‖star (U ((j+1 : ℕ)+1/2))*(1-I • Y (j+1))*
        pieceProduct (fun j ↦ if j=0 then (1/2 : ℝ) else 1) (fun j : ℕ ↦ H (j/N)) (j+1+1)
       - star (U ((j : ℝ)+1/2))*(1-I • Y (j+1))*
        pieceProduct (fun j ↦ if j=0 then (1/2 : ℝ) else 1) (fun j : ℕ ↦ H (j/N)) (j+1)‖ ≤
      cellIntegral H D N w (j+1) := by
    intro j hj
    have hjN : j+1<N := by omega
    have hjN' : (j : ℝ)+2≤N := by exact_mod_cast (by omega : j+2≤N)
    let a : ℝ := j+1/2
    let P := pieceProduct (fun j ↦ if j=0 then (1/2 : ℝ) else 1) (fun j : ℕ ↦ H (j/N)) (j+1)
    let h := H ((j+1 : ℕ)/N)
    have hPn : ‖P‖ ≤ 1 := norm_le_one_of_star_mul_self
      (star_pieceProduct_mul_self fun j _ ↦ hherm _)
    have hsub : ∀ t ∈ Icc (0 : ℝ) 1, t+a ∈ Icc (0 : ℝ) N := fun t ht ↦ by
      dsimp [a]; constructor <;> linarith [ht.1, ht.2, Nat.cast_nonneg (α := ℝ) j]
    have hucont : ContinuousOn (fun t : ℝ ↦ U (t+a)) (Icc 0 1) :=
      (show ContinuousOn U (Icc (0 : ℝ) N) from fun t ht ↦ (hU t ht).continuousWithinAt).comp
        (continuous_id.add continuous_const).continuousOn hsub
    have hud : ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t ↦ U (t+a)) (-I • (H ((t+a)/N)*U (t+a))) t := by
      intro t ht
      have hmem : t+a ∈ Ioo (0 : ℝ) N := by
        dsimp [a]; constructor <;> linarith [ht.1, ht.2, Nat.cast_nonneg (α := ℝ) j]
      simpa only [Function.comp_def, one_smul] using
        ((hU _ (Ioo_subset_Icc_self hmem)).hasDerivAt
          (Icc_mem_nhds hmem.1 hmem.2)).scomp t ((hasDerivAt_id t).add_const a)
    have hvd : ∀ t : ℝ, HasDerivAt (fun t ↦ evol h t*P) (-I • (h*(evol h t*P))) t := by
      intro t
      simpa only [smul_mul_assoc, mul_assoc] using (hasDerivAt_evol h t).mul_const P
    have hb := norm_dressed_full_cell_integral_sharp_le (K := fun t ↦ H ((t+a)/N))
      (U := fun t ↦ U (t+a)) (V := fun t ↦ evol h t*P)
      (D := (N : ℝ)⁻¹ • D (j+1))
      (hherm _) (hw _ (Nat.succ_pos j) hjN) (hwidth _ (Nat.succ_pos j) hjN)
      (hKc.comp (continuous_id.add continuous_const).continuousOn hsub)
      hucont ((continuous_evol h).mul continuous_const).continuousOn
      (fun t _ ↦ hherm _) hud (fun t _ ↦ hvd t)
      (fun t ht ↦ hUn _ (hsub t (Ioo_subset_Icc_self ht)))
      (fun t _ ↦ by simpa only [one_mul] using norm_mul_le_of_le (norm_evol_le (hherm _) t) hPn)
    have hright : 1+a=((j+1 : ℕ) : ℝ)+1/2 := by dsimp [a]; push_cast; ring
    dsimp only at hb
    rw [hright, zero_add, evol_zero, one_mul] at hb
    rw [hYs]
    change ‖star (U ((j+1 : ℕ)+1/2))*(1-I • frameOp h ((N : ℝ)⁻¹ • D (j+1)))*
      (evol h (if j+1=0 then 1/2 else 1)*P)-
      star (U a)*(1-I • frameOp h ((N : ℝ)⁻¹ • D (j+1)))*P‖ ≤ _
    rw [if_neg (Nat.succ_ne_zero j)]
    have he : ∀ t : ℝ, t+((j+1:ℕ):ℝ)-1/2=t+a := fun t ↦ by dsimp [a]; push_cast; ring
    simpa only [cellIntegral, he] using hb
  have hmain := norm_dressed_steps_le (u := fun j : ℕ ↦ U ((j : ℝ)+1/2))
    (v := fun j ↦ pieceProduct (fun j ↦ if j=0 then (1/2 : ℝ) else 1) (fun j : ℕ ↦ H (j/N)) (j+1))
    (Y := Y) (N-1)
    (fun j hj ↦ hUunit _ ⟨by positivity, by
      have hj' : (j : ℝ)+1≤N := by exact_mod_cast (by omega : j+1≤N)
      linarith⟩)
    (fun j _ ↦ norm_le_one_of_star_mul_self (star_pieceProduct_mul_self fun j _ ↦ hherm _))
    hY0 hstep
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  dsimp only at hmain
  rw [hN1] at hmain
  set P := pieceProduct (fun j ↦ if j = 0 then (1 / 2 : ℝ) else 1) (fun j : ℕ ↦ H (j / N)) N
    with hPdef
  have hPn : ‖P‖ ≤ 1 :=
    norm_le_one_of_star_mul_self (star_pieceProduct_mul_self fun j _ ↦ hherm _)
  -- the first half cell
  have hfirst : ‖U (((0 : ℕ) : ℝ)+1/2)-pieceProduct
        (fun j ↦ if j=0 then (1/2 : ℝ) else 1) (fun j : ℕ ↦ H (j/N)) 1‖ ≤ (∫ t in (0 : ℝ)..(1/2),
          ‖H (t/N)-H 0‖) := by
    have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) N := Icc_subset_Icc le_rfl (by linarith)
    have h := (hU.mono hsub).norm_sub_evol_mul_le_integral (G := H 0) (by norm_num) (hherm 0)
      (hKc.mono hsub) (fun t _ ↦ hKh t) (hUn 0 ⟨le_rfl, hNpos.le⟩)
    rw [sub_zero, hU0, mul_one] at h
    have e3 : pieceProduct (fun j ↦ if j = 0 then (1 / 2 : ℝ) else 1)
        (fun j : ℕ ↦ H (j / N)) 1 = evol (H 0) (1 / 2) := by simp [pieceProduct]
    rwa [e3, Nat.cast_zero, zero_add]
  -- the last half cell
  have hlast : ‖U N - evol (H 1) (1 / 2) * U (((N - 1 : ℕ) : ℝ) + 1 / 2)‖ ≤ (∫ t in ((N :
    ℝ)-1/2)..(N : ℝ), ‖H (t/N)-H 1‖) := by
    rw [show ((N - 1 : ℕ) : ℝ) + 1 / 2 = (N : ℝ) - 1 / 2 by rw [Nat.cast_sub hN]; push_cast; ring]
    have hb0 : (0 : ℝ) ≤ (N : ℝ) - 1 / 2 := by linarith
    have hbN : (N : ℝ) - 1 / 2 ≤ N := by linarith
    have hsub : Icc ((N : ℝ) - 1 / 2) (N : ℝ) ⊆ Icc (0 : ℝ) N := Icc_subset_Icc hb0 le_rfl
    have h := (hU.mono hsub).norm_sub_evol_mul_le_integral (G := H 1) hbN (hherm 1)
      (hKc.mono hsub) (fun t _ ↦ hKh t) (hUn _ ⟨hb0, hbN⟩)
    rwa [show (N : ℝ) - ((N : ℝ) - 1 / 2) = 1 / 2 by ring] at h
  have hfin : ‖evol (H 1) (1 / 2) * P - U N‖ ≤ halfIntegral H N
      + ∑ j ∈ Finset.range (N - 1),
          (cellIntegral H D N w (j+1)
            + ‖Y (j + 1) - Y j‖)
      + ‖Y (N - 1)‖ := by
    have he : evol (H 1) (1/2)*P-U N =
        -(U N-evol (H 1) (1/2)*U (((N-1 : ℕ) : ℝ)+1/2))-
        evol (H 1) (1/2)*(U (((N-1 : ℕ) : ℝ)+1/2)-P) := by
      rw [mul_sub]; abel
    rw [he]
    have hm := hmain.trans (add_le_add (add_le_add hfirst le_rfl) le_rfl)
    calc _ ≤ ‖U N-evol (H 1) (1/2)*U (((N-1 : ℕ) : ℝ)+1/2)‖+
          ‖evol (H 1) (1/2)*(U (((N-1 : ℕ) : ℝ)+1/2)-P)‖ :=
            (norm_sub_le _ _).trans_eq (by rw [norm_neg])
      _ ≤ (∫ t in ((N : ℝ)-1/2)..(N : ℝ), ‖H (t/N)-H 1‖)+1*((∫ t in (0 : ℝ)..(1/2), ‖H (t/N)-H 0‖)+
        ∑ j ∈ Finset.range (N-1),
          (cellIntegral H D N w (j+1)+‖Y (j+1)-Y j‖)+‖Y (N-1)‖) :=
        add_le_add hlast (norm_mul_le_of_le (norm_evol_le (hherm 1) _) hm)
      _ = _ := by unfold halfIntegral; ring
  have hW : pieceProduct (fun _ ↦ 1) (fun j : ℕ ↦ H (j / N)) N = P * evol (H 0) (1 / 2) := by
    have h1 := pieceProduct_one_eq_half_mul (fun j : ℕ ↦ H (j / N)) (N - 1)
    rw [hN1] at h1; rw [h1, hPdef, Nat.cast_zero, zero_div]
  have e : pieceProduct (fun _ ↦ 1) (fun j : ℕ ↦ H (j / N)) N
        - evol (H 1) (-(1 / 2)) * U N * evol (H 0) (1 / 2)
      = evol (H 1) (-(1 / 2)) * (evol (H 1) (1 / 2) * P - U N) * evol (H 0) (1 / 2) := by
    rw [hW, mul_sub, sub_mul, ← mul_assoc, evol_neg_mul_self, one_mul]
  rw [e]
  exact (norm_mul_le_of_le (norm_mul_le_of_le (norm_evol_le (hherm 1) _) hfin)
    (norm_evol_le (hherm 0) _)).trans_eq (by ring)

/-- For $L$-Lipschitz $H$ on $[0,1]$, the two end half steps cost at most $L/(8N)$ each, so
`halfIntegral H N` $\le L/(4N)$. -/
theorem halfIntegral_le_lipschitz (H : ℝ → 𝕄) (N : ℕ) (L : ℝ) (hN : 0 < N)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖H t - H s‖ ≤ L * |t - s|) :
    halfIntegral H N ≤ L/(4*N) := by
  have hcont : ContinuousOn H (Icc 0 1) := continuousOn_of_norm_sub_le hlip
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmem : ∀ t ∈ Icc (0 : ℝ) N, t / N ∈ Icc (0 : ℝ) 1 := fun t ht ↦
    ⟨div_nonneg ht.1 hNpos.le, (div_le_one hNpos).mpr ht.2⟩
  have hKc : ContinuousOn (fun t : ℝ ↦ H (t / N)) (Icc 0 N) :=
    hcont.comp (continuous_id.div_const _).continuousOn hmem
  have htop : 1/(2*(N:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hlip0 : ∀ t ∈ Icc (0 : ℝ) (1/(2*N)), ‖H t-H 0‖ ≤ L*t := fun t ht ↦ by
    simpa only [sub_zero, abs_of_nonneg ht.1] using
      hlip 0 ⟨le_rfl, zero_le_one⟩ t ⟨ht.1, ht.2.trans htop⟩
  have hlip1 : ∀ t ∈ Icc (1-1/(2*N):ℝ) 1, ‖H t-H 1‖ ≤ L*(1-t) := fun t ht ↦ by
    simpa only [abs_of_nonpos (by linarith [ht.2] : t-1 ≤ 0), neg_sub] using
      hlip 1 ⟨zero_le_one, le_rfl⟩ t ⟨by linarith [ht.1], ht.2⟩
  have hfirst : (∫ t in (0 : ℝ)..(1/2), ‖H (t/N)-H 0‖) ≤ L/(8*N) := by
    have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc (0 : ℝ) N := Icc_subset_Icc le_rfl (by linarith)
    calc (∫ t in (0 : ℝ)..(1 / 2), ‖H (t / N) - H 0‖)
        ≤ ∫ t in (0 : ℝ)..(1 / 2), (L / N * (t - 0) + 0) :=
          intervalIntegral.integral_mono_on (by norm_num)
            (((hKc.mono hsub).sub continuousOn_const).norm.intervalIntegrable_of_Icc
              (by norm_num))
            ((by fun_prop : Continuous fun t : ℝ ↦ L / N * (t - 0) + 0).intervalIntegrable _ _)
            fun t ht ↦ by
              exact (hlip0 (t / N) ⟨div_nonneg ht.1 hNpos.le,
                (div_le_div_of_nonneg_right ht.2 hNpos.le).trans_eq (by rw [div_div])⟩).trans_eq
                (by ring)
      _ = L / (8 * N) := by rw [UnitaryProducts.integral_affine]; field_simp; ring
  have hlast : (∫ t in ((N:ℝ)-1/2)..(N:ℝ), ‖H (t/N)-H 1‖) ≤ L/(8*N) := by
    have hbN : (N : ℝ) - 1 / 2 ≤ N := by linarith
    have hsub : Icc ((N : ℝ) - 1 / 2) (N : ℝ) ⊆ Icc (0 : ℝ) N := Icc_subset_Icc (by linarith) le_rfl
    calc (∫ t in ((N : ℝ) - 1 / 2)..(N : ℝ), ‖H (t / N) - H 1‖)
        ≤ ∫ t in ((N : ℝ) - 1 / 2)..(N : ℝ),
            (-(L / N) * (t - ((N : ℝ) - 1 / 2)) + L / (2 * N)) :=
          intervalIntegral.integral_mono_on hbN
            (((hKc.mono hsub).sub continuousOn_const).norm.intervalIntegrable_of_Icc hbN)
            ((by fun_prop : Continuous fun t : ℝ ↦
              -(L / N) * (t - ((N : ℝ) - 1 / 2)) + L / (2 * N)).intervalIntegrable _ _)
            fun t ht ↦ by
              have e : (1 - 1 / (2 * (N : ℝ))) * N = (N : ℝ) - 1 / 2 := by field_simp
              exact (hlip1 (t / N) ⟨by rw [le_div_iff₀ hNpos, e]; exact ht.1,
                (div_le_one hNpos).mpr ht.2⟩).trans_eq (by field_simp; ring)
      _ = L / (8 * N) := by rw [UnitaryProducts.integral_affine]; field_simp; ring
  exact (add_le_add hfirst hlast).trans_eq (by ring)

end
end UnitaryProducts.Dressed
