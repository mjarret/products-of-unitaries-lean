/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.LipschitzDerivative
public import UnitaryProducts.Evolution.RoundedClockEvolution

/-!
# the width-π scaling bound: the unit-step comparison with an absolute constant

## Declarations

- `unit_step_comparison_scaling`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real Filter MeasureTheory UnitaryProducts.Corrector
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **the width-π scaling bound with two sizes** (unit-step comparison in $L=\max\|H'\|$ and $M$).
This is the
two-size form of the width-π scaling bound; the comparison's the width-π scaling bound, with one
size $h$ bounding $\|H'\|$ and the
Lipschitz constant of $H'$, is `unit_step_comparison_scaling_one_size`, derived from this one at
$M=h$, $L\le h$. For a Hamiltonian $H$
on $[0,1]$ whose derivative is $M$-Lipschitz, $T>0$, and an integer $N\ge2$ such that every
interior sample $(T/N)H(j/N)$ has eigenvalue differences at most $\pi$,
$\|e^{-iTH(1)/(2N)}W_Ne^{iTH(0)/(2N)}-U(T)\|\le\frac T{N^2}(L+M)+\frac{T^2}{N^3}L^2$, with
$L=\max_{[0,1]}\|H'\|$.

Reading the statement against the comparison:
* The $O(\cdot)$ of the width-π scaling bound holds here with constant $1$, in the two sizes $L$
and $M$.
* `derivWithin H (Icc 0 1)` is $H'$, one-sided at $0$ and $1$; the Lipschitz bound
  already implies `0 ≤ M` by evaluating it at the two endpoints.
* `L := sSup …` is $\max_{[0,1]}\|H'\|$: $H'$ is continuous on the compact $[0,1]$, so the
  supremum is attained.
* `evol G u` is $e^{-iuG}$, so `evol (H 1) (T/(2*N))` is $e^{-iTH(1)/(2N)}$, and
  `(unitProduct (fun s ↦ (T/N) • H s) N).1` is $W_N$.
* The width hypothesis is stated for the eigenvalues of $H(j/N)$ times $T/N>0$, which are the
  eigenvalues of $(T/N)H(j/N)$, for all pairs `p q` and $0<j<N$.

The proof follows the comparison's: (1) the interior-sample comparison(i) at width $\pi$ with one
Lipschitz constant
(`unit_steps_global_lip`) bounds $\|W_N-e^{iTH(1)/(2N)}U(T)e^{-iTH(0)/(2N)}\|$; (2) the half-step
phases are unitary, so moving them from $U(T)$ onto $W_N$ does not change the norm; (3) at width
$\pi$ the three coefficients are at most $1$: $2c_0=1/\pi-2/\pi^2$, $1/8+\mathcal N(\pi)=
1/8+1/\pi^2$, and $c_2+2\mathcal N'(\pi)=1/\pi+1/24-1/\pi^2-4/\pi^3$ (`frameBound_center_pi`,
`frameBound_frameLip_pi`), using $\pi\ge2$. -/
theorem unit_step_comparison_scaling [NeZero d] :
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ), 0 < T → 2 ≤ N →
    ∀ (hH : ∀ s ∈ Icc (0:ℝ) 1, (H s).IsHermitian),
    ContDiffOn ℝ 1 H (Icc 0 1) →
    ∀ M : ℝ,
    (∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
      ‖derivWithin H (Icc (0:ℝ) 1) t-derivWithin H (Icc (0:ℝ) 1) s‖ ≤ M*|t-s|) →
    (∀ j : ℕ, 0 < j → ∀ hjN : j < N, ∀ p q,
      T/N * |(hH _ (unit_sample_mem hjN)).eigenvalues p -
        (hH _ (unit_sample_mem hjN)).eigenvalues q| ≤ π) →
    IsEvolution (fun t ↦ H (t/T)) U 0 T →
    let Hd := derivWithin H (Icc (0:ℝ) 1)
    let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc 0 1)
    ‖UnitaryProducts.evol (H 1) (T/(2*N)) * (unitProduct (fun s ↦ (T/N) • H s) N).1 *
        UnitaryProducts.evol (H 0) (-(T/(2*N))) - U T‖
      ≤ T/N^2*(L+M) + T^2/N^3*L^2 := by
  intro H U T N hT hN2 hH hc M hlip hdiff hU Hd L
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  -- Step 1 (interior-sample comparison at width `π`), with the phases on the evolution.
  have hmain := unit_steps_global_lip H U T N π M hT hN2
    (by linarith [pi_pos]) hH hc hlip hdiff hU
  dsimp only at hmain
  rw [← PaperProof.uniform_phase_error_norm _ _ _ _
    (hH 0 ⟨le_rfl, zero_le_one⟩) (hH 1 ⟨zero_le_one, le_rfl⟩)]
  -- Step 3: at width `π` each coefficient is at most 1, using `π ≥ 2`.
  have hL : 0 ≤ L := Real.sSup_nonneg (by rintro _ ⟨s, _, rfl⟩; exact norm_nonneg _)
  have hπ2 : (2:ℝ) ≤ π := Real.two_le_pi
  have hrec : 1/π ≤ (1:ℝ)/2 := one_div_le_one_div_of_le (by norm_num) hπ2
  have hrec2 : 1/π^2 ≤ (1:ℝ)/4 := one_div_le_one_div_of_le (by norm_num)
    (by linarith [mul_le_mul hπ2 hπ2 (by norm_num : (0:ℝ) ≤ 2) pi_pos.le])
  have hc0 : 2*(frameBound π-frameBound (π/2)/2) ≤ 1 := by
    rw [frameBound_center_pi, show (2:ℝ)*(1/(2*π)-1/π^2) = 1/π-2/π^2 by ring]
    linarith [show (0:ℝ) ≤ 2/π^2 by positivity]
  have hc1 : (1/8:ℝ)+frameBound π ≤ 1 := by rw [frameBound_frameLip_pi.1]; linarith
  have hc2 : frameBound π-frameBound (π/2)/2+1/24+2*frameLip π ≤ 1 := by
    rw [frameBound_center_pi, frameBound_frameLip_pi.2,
      show (1/(2*π)-1/π^2:ℝ)+1/24+(1/(2*π)-4/π^3) = 1/π+1/24-(1/π^2+4/π^3) by ring]
    linarith [show (0:ℝ) ≤ 1/π^2+4/π^3 by positivity]
  -- Step 4: assemble `T/N²(L + M) + T²/N³ L²`.
  have hterm0 := mul_le_mul_of_nonneg_right hc0 hL
  have hterm1 := mul_le_mul_of_nonneg_right hc1 (unit_lipschitz_constant_nonneg hlip)
  have hterm2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hT.le) (sq_nonneg L)) hNR.le
  have hbound : T/N^2*(2*(frameBound π-frameBound (π/2)/2)*L+
      (1/8+frameBound π)*M+(frameBound π-frameBound (π/2)/2+1/24+2*frameLip π)*T*L^2/N) ≤
      T/N^2*(L+M)+T^2/N^3*L^2 := by
    calc _ ≤ T/N^2*(L+M+T*L^2/N) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add (by simpa only [one_mul] using hterm0)
              (by simpa only [one_mul] using hterm1)) (by simpa only [one_mul] using hterm2))
            (div_nonneg hT.le (sq_nonneg _))
      _ = _ := by ring
  exact hmain.trans hbound

end UnitaryProducts.Paper
