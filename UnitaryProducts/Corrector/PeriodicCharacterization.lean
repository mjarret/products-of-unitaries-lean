/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Corrector.ScalarEntrySolutions
public import UnitaryProducts.Spectral.GapDistance
public import Mathlib.NumberTheory.ZetaValues

/-!
# Characterization and halving of the periodic corrector

## Declarations

- `frameMult_eq_partialFractions`
- `ne_two_pi_mul_of_abs_lt`
- `exponentialOperators`
- `eigen_interval`
- `scaled_eigenvalue`
- `periodicCorrectorData`
- `periodicCorrector_zero`
- `hasDerivAt_periodic_corrector`
- `corrector_eigenbasis_derivative`
- `frameOp_eq_paper_value`
- `corrector_end_eigenbasis_entry`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed

noncomputable section

attribute [local instance] matrixCStarAlgebra

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace UnitaryProducts.Paper

/-- The partial-fraction series of $\mathcal N$, the scalar series used by the walk comparison,
used by `frameBound_abs_eq_frameMult`: off
$2\pi\mathbb Z\setminus\{0\}$, the series
$\sum_{n\ge1}2/(4\pi^2n^2-x^2)$ equals `frameMult x`, the cotangent form by which the paper
defines $\mathcal N$ (eq:N-def, §4.1).

Reading the statement against the paper:
* For $x\ne0$, `frameMult x` is $(1-(x/2)\cot(x/2))/x^2$, so the equation is the paper's
  identity divided by $x^2$.
* The right side is the series, summed over `ℕ+`.
* The hypothesis excludes only $2\pi\mathbb Z\setminus\{0\}$, where $\mathcal N$ is undefined. At
  $x=0$, where `frameMult 0 = 1/12`, the statement is $\mathcal N(0)=1/12$.

The proof follows the paper's: (1) at $x=0$, $\sum_n n^{-2}=\pi^2/6$ (Mathlib's
`hasSum_zeta_two`); (2) otherwise Mathlib's partial fractions of the cotangent, rescaled
(`frameMult_eq_tsum`). -/
theorem frameMult_eq_partialFractions {x : ℝ}
    (hx : ∀ n : ℤ, n ≠ 0 → x ≠ 2 * π*n) :
    UnitaryProducts.Corrector.frameMult x = ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2) := by
  by_cases h0 : x = 0
  · subst x
    have hz := (tsum_zero_pnat_eq_tsum_nat hasSum_zeta_two.summable).trans hasSum_zeta_two.tsum_eq
    -- `decide` checks the natural-number fact `2 ≠ 0` that `zero_pow` needs to rewrite `0 ^ 2`.
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_add] at hz
    calc
      UnitaryProducts.Corrector.frameMult 0 = (2/(4*π^2)) * (∑' n : ℕ+, 1/(n:ℝ)^2) := by
        rw [UnitaryProducts.Corrector.frameMult, if_pos rfl, hz]
        field_simp
        ring
      _ = ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-0^2) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n ↦ by ring
  · refine UnitaryProducts.Corrector.frameMult_eq_tsum fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using h0
    · exact hx n hn

/-- Width below $2\pi$ excludes resonance: if $|x|<2\pi$, then
$x\notin2\pi\mathbb Z\setminus\{0\}$. -/
theorem ne_two_pi_mul_of_abs_lt {x : ℝ} (hx : |x| < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    x ≠ 2 * π*n := by
  rintro rfl
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  rw [abs_mul, abs_of_pos Real.two_pi_pos] at hx
  exact hx.not_ge (le_mul_of_one_le_right Real.two_pi_pos.le h1)

/-- The corrector data of the canonical-cell construction in Lemma A.1 for a Hermitian $\Omega$
and a slope $D$, as a tuple:
the map $E\mapsto i(\Omega E-E\Omega)$; the series $\mathcal N(x)=\sum_{n\ge1}2/(4\pi^2n^2-x^2)$;
the end value $\mathcal N(\mathrm{ad}_\Omega)(D)$, with entries
$\mathcal N(\lambda_p-\lambda_q)D_{pq}$ in the eigenbasis `hΩ.eigenvectorUnitary`; and the periodic
corrector $\tau\mapsto Y(\tau)$, given by the variation-of-constants formula
`frameExtension Ω D Ybar (τ + 1/2)`, which equals $\mathcal N(\mathrm{ad}_\Omega)(D)$ at
$\tau=-\frac12$. So `.2.1` is $\mathcal N$, `.2.2.1` is $\mathcal N(\mathrm{ad}_\Omega)(D)$ and
`.2.2.2` is $Y$.

Junk values: at a resonance $\lambda_p-\lambda_q=2\pi m$, $m\ne0$, the term $n=|m|$ of the series
is `2/0 = 0` in Lean, so $\mathcal N$ and $\mathcal N(\mathrm{ad}_\Omega)(D)$ take finite values
where the paper's
definition is not made; every theorem that reads them assumes non-resonance or width $<2\pi$.
At width $<2\pi$, $\mathcal N(\mathrm{ad}_\Omega)(D)$ equals the basis-free series `frameOp Ω D`
(`frameOp_eq_paper_value`), so the choice of eigenbasis does not matter there. -/
def exponentialOperators (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄) :
    (𝕄 → 𝕄) × (ℝ → ℝ) × 𝕄 × (ℝ → 𝕄) :=
  let V : 𝕄 := hΩ.eigenvectorUnitary
  let Ybar : 𝕄 := V * Matrix.of (fun p q ↦
    ((∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-(hΩ.eigenvalues p - hΩ.eigenvalues q)^2) : ℝ) : ℂ) *
      (star V * D * V) p q) * star V
  (fun E ↦ I • (Ω * E - E * Ω),
   (fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)), Ybar,
   fun τ ↦ UnitaryProducts.Dressed.frameExtension Ω D Ybar (τ + 1 / 2))

/-- Eigenvalues spread by at most $w$ lie in $[\lambda_{\min}, \lambda_{\min} + w]$. -/
theorem eigen_interval {h : 𝕄} (hh : h.IsHermitian) {w : ℝ}
    (hw : ∀ p q, |hh.eigenvalues p - hh.eigenvalues q| ≤ w) :
    ∀ i, hh.eigenvalues i ∈ Icc (sInf (Set.range hh.eigenvalues))
      (sInf (Set.range hh.eigenvalues) + w) := by
  intro i
  obtain ⟨q, hq⟩ := (show (Set.range hh.eigenvalues).Nonempty from ⟨_, i, rfl⟩).csInf_mem
    (Set.finite_range hh.eigenvalues)
  have hlow := ciInf_le (Set.finite_range hh.eigenvalues).bddBelow i
  change sInf (Set.range hh.eigenvalues) ≤ hh.eigenvalues i at hlow
  have hupp := (abs_le.mp (hw i q)).2
  rw [hq] at hupp
  exact ⟨hlow, sub_le_iff_le_add.mp hupp |>.trans_eq (add_comm _ _)⟩

/-- Scaling a Hermitian matrix scales its spectrum, without choosing an ordering. -/
theorem scaled_eigenvalue {A : 𝕄} (hA : A.IsHermitian)
    (c : ℝ) (i : Fin d) : ∃ j,
    (UnitaryProducts.Separation.isHermitian_real_smul hA c).eigenvalues i = c * hA.eigenvalues j
      := by
  letI : NeZero d := ⟨i.pos.ne'⟩
  have hmem := (UnitaryProducts.Separation.isHermitian_real_smul hA
    c).eigenvalues_mem_spectrum_real i
  rw [spectrum.smul_eq_smul c A ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩,
    hA.spectrum_real_eq_range_eigenvalues] at hmem
  rcases hmem with ⟨z, ⟨j, rfl⟩, hz⟩
  exact ⟨j, hz.symm⟩

/-- the canonical-cell construction in Lemma A.1 (the periodic corrector). The triple
$(\mathcal N, \mathcal N(\mathrm{ad}_\Omega)(D), Y)$:
* `.1` is $\mathcal N(x) = \sum_{n \ge 1} 2/(4\pi^2 n^2 - x^2)$ (a `tsum` over `ℕ+`); the paper
  defines $\mathcal N$ by its cotangent form (eq:N-def), equal to this series for
  $|x|<2\pi$, including the value $1/12$ at $0$ (`frameBound_abs_eq_frameMult`);
* `.2.1` is $\mathcal N(\mathrm{ad}_\Omega)(D)$, with entries
  $\mathcal N(\lambda_p - \lambda_q) D_{pq}$ in the eigenbasis `hΩ.eigenvectorUnitary` of $\Omega$;
* `.2.2` is $Y(\tau)$, $-\frac12 \le \tau \le \frac12$, given by the variation-of-constants
  formula `Dressed.frameExtension Ω D Ybar (τ + 1/2)`. It solves $Y' + i[\Omega, Y] = \tau D$
  (`hasDerivAt_frameExtension`), starts at $Y(-\frac12) = \mathcal N(\mathrm{ad}_\Omega)(D)$
  (`frameExtension_zero`), and is the only solution (`periodic_corrector_unique`).

the canonical-cell construction assumes all eigenvalue differences have modulus $<2\pi$.
On that domain `PaperProof.periodic_corrector_characterization` proves the ODE, periodic
endpoints, zero integral, and uniqueness among continuous solutions differentiable in the
interior. The implementation here is total. At a resonant difference
$\lambda_p - \lambda_q = 2\pi n$, $n \ne 0$, the $n$-th term of $\mathcal N$ is `2/0 = 0` in Lean,
so $\mathcal N(\mathrm{ad}_\Omega)(D)$ is a meaningless finite matrix instead of undefined. Every
theorem that uses it assumes non-resonance or width $< 2\pi$. The `tsum` converges everywhere (its
terms are $O(1/n^2)$), so it has no divergence junk.

$D$ is any matrix, as in the paper. The eigenbasis is a choice, but at width $< 2\pi$ the value
equals the choice-free series `frameOp Ω D` (`frameOp_eq_paper_value`). -/
def periodicCorrectorData (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄) :
    (ℝ → ℝ) × 𝕄 × (ℝ → 𝕄) :=
  (exponentialOperators Ω hΩ D).2

/-- Zero forcing gives the zero corrector at every real local time. -/
theorem periodicCorrector_zero (Ω : 𝕄) (hΩ : Ω.IsHermitian) (t : ℝ) :
    (periodicCorrectorData Ω hΩ (0 : 𝕄)).2.2 t = 0 := by
  simp only [periodicCorrectorData, exponentialOperators, Dressed.frameExtension,
    Dressed.cellPrimitive, mul_zero, zero_mul, smul_zero, intervalIntegral.integral_zero,
    add_zero, Matrix.zero_apply]
  change _ * (_ * (0 : 𝕄) * _) * _ = 0
  simp only [mul_zero, zero_mul]

/-- The paper's corrector end value $\mathcal N(\mathrm{ad}_h)(D)$, defined entrywise (entries
$\mathcal N(\lambda_p-\lambda_q)D_{pq}$ in an eigenbasis, `exponentialOperators`), is the power
series `frameOp h D` in $\mathrm{ad}_h$ at spectral width $w<2\pi$ (§4.1, "At
$\Phi=\mathrm{ad}_\Omega$, the series $f(\Phi)$ is the map $f(\mathrm{ad}_\Omega)$ defined
before the canonical-cell construction in Lemma A.1"). -/
theorem frameOp_eq_paper_value {h : 𝕄} (hh : h.IsHermitian) {w : ℝ}
    (hw : w < 2 * π) (hwid : ∀ p q, |hh.eigenvalues p - hh.eigenvalues q| ≤ w) (D : 𝕄) :
    frameOp h D = (exponentialOperators h hh D).2.2.1 := by
  rw [frameOp_eq_eigenbasis hh hw (eigen_interval hh hwid) D]
  dsimp only [exponentialOperators]
  congr 2
  ext p q
  simp only [Matrix.of_apply,
    frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt ((hwid p q).trans_lt hw))]

namespace UnitStepsProse

/-- Section 4.1 after the canonical-cell construction in Lemma A.1: the periodic corrector
satisfies its equation at every real
local time in the release's variation-of-constants extension. -/
theorem hasDerivAt_periodic_corrector (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄) (t : ℝ) :
    HasDerivAt (periodicCorrectorData Ω hΩ D).2.2
      (t • D - I • (Ω * (periodicCorrectorData Ω hΩ D).2.2 t -
        (periodicCorrectorData Ω hΩ D).2.2 t * Ω)) t := by
  simpa only [add_sub_cancel_right] using HasDerivAt.comp_add_const t (1 / 2 : ℝ)
    (Dressed.hasDerivAt_frameExtension Ω D (periodicCorrectorData Ω hΩ D).2.1 (t + 1/2))

/-- Conjugating the corrector equation gives the scalar equation for each entry. -/
theorem corrector_eigenbasis_derivative (Ω : 𝕄) (hΩ : Ω.IsHermitian) (D : 𝕄)
    {Z : ℝ → 𝕄} {t : ℝ}
    (hZ : HasDerivAt Z (t • D - I • (Ω * Z t - Z t * Ω)) t) (p q : Fin d) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    let E := ((entryCLM p q).comp
      (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).restrictScalars ℝ
    HasDerivAt (fun s ↦ E (Z s))
      ((t : ℂ) * E D - I * (hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) * E (Z t)) t := by
  intro U E
  let E' := (entryCLM p q).comp (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)
  have had : E' (adL Ω (Z t)) = (hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) * E' (Z t) := by
    simpa only [pow_one] using ad_power_eigenbasis_entry Ω hΩ (Z t) 1 p q
  convert E.hasFDerivAt.comp_hasDerivAt t hZ using 1
  change _ = E' (t • D - I • adL Ω (Z t))
  rw [map_sub, E'.map_smul_of_tower, map_smul, had]
  simp only [smul_eq_mul, ← Complex.coe_smul, mul_assoc]
  rfl

end UnitStepsProse
end UnitaryProducts.Paper

namespace UnitaryProducts.PaperProof
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse

/-- The corrector end value in its defining eigenbasis. -/
theorem corrector_end_eigenbasis_entry {Ω : 𝕄} (hΩ : Ω.IsHermitian) (D : 𝕄)
    (p q : Fin d) (hdiff : |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π) :
    let U : 𝕄 := hΩ.eigenvectorUnitary
    (star U * (periodicCorrectorData Ω hΩ D).2.1 * U) p q =
      (frameMult (hΩ.eigenvalues p - hΩ.eigenvalues q) : ℂ) * (star U * D * U) p q := by
  intro U
  let e := Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary
  change e.symm (e _) p q = _
  rw [e.symm_apply_apply, Matrix.of_apply,
    frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt hdiff)]

end UnitaryProducts.PaperProof
