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
- `scaled_eigenvalue_bound`
- `periodicCorrectorData`
- `periodicCorrector_zero`
- `hasDerivAt_periodic_corrector`
- `corrector_eigenbasis_derivative`
- `frameOp_eq_paper_value`
- `corrector_end_eigenbasis_entry`
- `corrector_endpoint`
- `IsPeriodicCorrector`
- `periodic_corrector_characterization`
- `integral_halving_pair`
- `periodic_corrector_halving`
- `periodic_corrector_center`
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

/-- A nonnegative scaling transports a bound on all eigenvalue differences. -/
theorem scaled_eigenvalue_bound {A : 𝕄} (hA : A.IsHermitian)
    {c w : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ p q, c * |hA.eigenvalues p - hA.eigenvalues q| ≤ w) :
    ∀ p q, |(Separation.isHermitian_real_smul hA c).eigenvalues p -
      (Separation.isHermitian_real_smul hA c).eigenvalues q| ≤ w := by
  intro p q
  obtain ⟨p', hp⟩ := scaled_eigenvalue hA c p
  obtain ⟨q', hq⟩ := scaled_eigenvalue hA c q
  simpa only [hp, hq, ← mul_sub, abs_mul, abs_of_nonneg hc] using hbound p' q'

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

/-- the proof of Lemma A.1: the scalar endpoint calculation in a fixed eigenbasis. -/
theorem corrector_endpoint {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hdiff : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π) (D : 𝕄) :
    (periodicCorrectorData Ω hΩ D).2.2 (1 / 2) =
      (periodicCorrectorData Ω hΩ D).2.1 := by
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let Y := (periodicCorrectorData Ω hΩ D).2.2
  have hB (p q : Fin d) := corrector_end_eigenbasis_entry hΩ D p q (hdiff p q)
  have hinit : Y (-1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 := by
    simp [Y, periodicCorrectorData, exponentialOperators, neg_div, frameExtension_zero]
  apply (Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary).symm.injective
  change star U * Y (1 / 2) * U = star U * (periodicCorrectorData Ω hΩ D).2.1 * U
  ext p q
  let E := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).restrictScalars ℝ
  rw [hB]
  exact corrector_entry_endpoint
    (Separation.zero_or_sin_half_ne_zero (ne_two_pi_mul_of_abs_lt (hdiff p q)))
    (E D) (fun s ↦ E (Y s))
    (fun t ↦ corrector_eigenbasis_derivative Ω hΩ D
      (hasDerivAt_periodic_corrector Ω hΩ D t) p q)
    (by change (star U * Y (-1 / 2) * U) p q = _; rw [hinit, hB]; rfl)

/-- The three conditions in the canonical-cell construction, on precisely the closed cell. -/
def IsPeriodicCorrector (Ω D : 𝕄) (Y : ℝ → 𝕄) : Prop :=
  ContinuousOn Y (Icc (-1 / 2 : ℝ) (1 / 2)) ∧
  (∀ t ∈ Ioo (-1 / 2 : ℝ) (1 / 2),
    HasDerivAt Y (t • D - I • (Ω * Y t - Y t * Ω)) t) ∧
  Y (-1 / 2) = Y (1 / 2) ∧ (∫ t in (-1 / 2 : ℝ)..(1 / 2), Y t) = 0

/-- The canonical-corrector auxiliary, with existence and uniqueness
from the corrector construction: the initial-value corrector satisfies its ODE, periodicity and
mean-zero conditions (`IsPeriodicCorrector`). Both endpoint values are N(ad_Ω)(D),
and every continuous solution of the three conditions agrees with it on [-1/2,1/2].
The commutator and spectral multiplier before Lemma A.1 are `exponentialOperators`. -/
theorem periodic_corrector_characterization {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hdiff : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π) (D : 𝕄) :
    let Y := (periodicCorrectorData Ω hΩ D).2.2
    IsPeriodicCorrector Ω D Y ∧
    Y (-1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 ∧
    Y (1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 ∧
    ∀ Z, IsPeriodicCorrector Ω D Z → EqOn Z Y (Icc (-1 / 2 : ℝ) (1 / 2)) := by
  intro Y
  let U : 𝕄 := hΩ.eigenvectorUnitary
  let E (p q : Fin d) := ((entryCLM p q).comp
    (ContinuousLinearMap.mulLeftRight ℂ 𝕄 (star U) U)).restrictScalars ℝ
  have hinj {X X' : 𝕄} (h : ∀ p q, E p q X = E p q X') : X = X' :=
    (Unitary.conjStarAlgAut ℂ 𝕄 hΩ.eigenvectorUnitary).symm.injective (Matrix.ext h)
  have hode {Z : ℝ → 𝕄} {t : ℝ} :=
    corrector_eigenbasis_derivative Ω hΩ D (Z := Z) (t := t)
  have hY := hasDerivAt_periodic_corrector Ω hΩ D
  have hYc : Continuous Y := continuous_iff_continuousAt.mpr fun t ↦ (hY t).continuousAt
  have hl : Y (-1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 := by
    simp [Y, periodicCorrectorData, exponentialOperators, neg_div, frameExtension_zero]
  have hr : Y (1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 := corrector_endpoint hΩ hdiff D
  have hm : ∫ t in (-1 / 2 : ℝ)..(1 / 2), Y t = 0 := by
    apply hinj
    intro p q
    rw [map_zero, ← (E p q).intervalIntegral_comp_comm (hYc.intervalIntegrable _ _)]
    exact corrector_entry_mean_zero (E p q D) (fun t ↦ E p q (Y t))
      (fun t ↦ hode (hY t) p q) (congrArg (E p q) (hr.trans hl.symm))
      ((congrArg (E p q) hl).trans (corrector_end_eigenbasis_entry hΩ D p q (hdiff p q)))
  refine ⟨⟨hYc.continuousOn, fun t _ ↦ hY t, hl.trans hr.symm, hm⟩, hl, hr, ?_⟩
  intro Z ⟨hZc, hZ, hZp, hZm⟩ t ht
  apply hinj
  intro p q
  have hcont := ((E p q).continuous.comp_continuousOn hZc).sub
    ((E p q).continuous.comp hYc).continuousOn
  have hd (s) (hs : s ∈ Ioo (-1 / 2 : ℝ) (1 / 2)) :
      HasDerivAt (fun s ↦ E p q (Z s) - E p q (Y s))
        (-I * (hΩ.eigenvalues p - hΩ.eigenvalues q : ℝ) *
          (E p q (Z s) - E p q (Y s))) s := by
    convert (hode (hZ s hs) p q).sub (hode (hY s) p q) using 1
    ring
  have hm' : ∫ s in (-1 / 2 : ℝ)..(1 / 2), (E p q (Z s) - E p q (Y s)) = 0 := by
    have hi := hZc.intervalIntegrable_of_Icc (μ := volume) (by norm_num)
    simp only [← map_sub]
    rw [(E p q).intervalIntegral_comp_comm (hi.sub (hYc.intervalIntegrable _ _)),
      intervalIntegral.integral_sub hi (hYc.intervalIntegrable _ _), hZm, hm, sub_self, map_zero]
  exact sub_eq_zero.mp (corrector_entry_homogeneous_eq_zero
    (ne_two_pi_mul_of_abs_lt (hdiff p q)) _ hcont hd
    (by simp only [Function.comp_apply, hZp, hl, hr]) (fun _ ↦ hm') t ht)

/-- The half-period translates have twice the mean of the original corrector. -/
theorem integral_halving_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : ℝ → E) (hc : Continuous Y) :
    (∫ u in (-1 / 2 : ℝ)..(1 / 2), (Y (u / 2 - 1 / 4) + Y (u / 2 + 1 / 4))) =
      (2 : ℝ) • ∫ t in (-1 / 2 : ℝ)..(1 / 2), Y t := by
  -- The two affine substitutions cover [-1/2,0] and [0,1/2], each with Jacobian 2.
  -- Split their sum, evaluate the new endpoints, and glue the adjacent integrals.
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_div_add Y (by norm_num : (2 : ℝ) ≠ 0),
    intervalIntegral.integral_comp_div_add Y (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num [← smul_add, intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

/-- the proof of Lemma A.1: the halved sum is characterized at matrix level by its ODE,
equal endpoints and zero mean; uniqueness identifies its endpoint. -/
theorem periodic_corrector_halving {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hdiff : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| < 2 * π) (D : 𝕄) :
    let Y := (periodicCorrectorData Ω hΩ D).2.2
    let Ωh := (1 / 2 : ℝ) • Ω
    let hΩh := Separation.isHermitian_real_smul hΩ (1 / 2 : ℝ)
    let W := fun u : ℝ ↦ Y (u / 2 - 1 / 4) + Y (u / 2 + 1 / 4)
    IsPeriodicCorrector Ωh ((1 / 2 : ℝ) • D) W ∧
    EqOn W (periodicCorrectorData Ωh hΩh ((1 / 2 : ℝ) • D)).2.2
      (Icc (-1 / 2 : ℝ) (1 / 2)) ∧
    (periodicCorrectorData Ω hΩ D).2.1 + Y 0 =
      (periodicCorrectorData Ωh hΩh ((1 / 2 : ℝ) • D)).2.1 := by
  intro Y Ωh hΩh W
  have hchar := periodic_corrector_characterization hΩ hdiff D
  have hy := hasDerivAt_periodic_corrector Ω hΩ D
  have hc : Continuous Y := continuous_iff_continuousAt.mpr fun t ↦ (hy t).continuousAt
  have hw (u : ℝ) : HasDerivAt W
      (u • ((1 / 2 : ℝ) • D) - I • (Ωh * W u - W u * Ωh)) u := by
    convert ((hy (u / 2 - 1 / 4)).scomp u
      (((hasDerivAt_id' u).div_const 2).sub_const (1 / 4))).add
      ((hy (u / 2 + 1 / 4)).scomp u
        (((hasDerivAt_id' u).div_const 2).add_const (1 / 4))) using 1
    simp only [W, Ωh, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_sub, smul_smul, smul_comm (1 / 2 : ℝ) I]
    module
  -- The two half-cell translates meet at Y(0).
  have hWl : W (-1 / 2) = Y (-1 / 2) + Y 0 := by norm_num [W]
  have hWr : W (1 / 2) = Y 0 + Y (1 / 2) := by norm_num [W]
  have hperiod : Y (-1 / 2) = Y (1 / 2) := hchar.1.2.2.1
  have hend : Y (-1 / 2) = (periodicCorrectorData Ω hΩ D).2.1 := hchar.2.1
  have hprop : IsPeriodicCorrector Ωh ((1 / 2 : ℝ) • D) W :=
    ⟨(continuous_iff_continuousAt.mpr fun u ↦ (hw u).continuousAt).continuousOn,
      fun u _ ↦ hw u,
      by rw [hWl, hWr, hperiod, add_comm],
      by rw [integral_halving_pair Y hc, hchar.1.2.2.2, smul_zero]⟩
  have hhd (p q) : |hΩh.eigenvalues p - hΩh.eigenvalues q| < 2 * π :=
    (scaled_eigenvalue_bound hΩ (w := π) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (fun p q ↦ by linarith [hdiff p q]) p q).trans_lt (by linarith [pi_pos])
  have hhalf := periodic_corrector_characterization hΩh hhd ((1 / 2 : ℝ) • D)
  have he := hhalf.2.2.2 W hprop
  refine ⟨hprop, he, ?_⟩
  -- Uniqueness identifies W with the half-width corrector; evaluate at its left endpoint.
  have hleft := (he (x := (-1 / 2 : ℝ)) (by norm_num)).trans hhalf.2.1
  rw [hWl, hend] at hleft
  exact hleft

/-- The center identity obtained from matrix-level halving uniqueness. -/
theorem periodic_corrector_center {w : ℝ} (hw : w < 2 * π) {Ω : 𝕄}
    (hΩ : Ω.IsHermitian)
    (hwid : ∀ p q, |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w) (D : 𝕄) :
    (periodicCorrectorData Ω hΩ D).2.2 0 =
      -((frameSeries (I • adL Ω) -
        (1 / 2 : ℂ) • frameSeries ((1 / 2 : ℂ) • (I • adL Ω))) D) := by
  let hΩh := Separation.isHermitian_real_smul hΩ (1 / 2 : ℝ)
  have hhalf : ∀ p q, |hΩh.eigenvalues p - hΩh.eigenvalues q| ≤ w / 2 :=
    scaled_eigenvalue_bound hΩ (by norm_num : (0 : ℝ) ≤ 1 / 2) fun p q ↦ by linarith [hwid p q]
  have he := (periodic_corrector_halving hΩ (fun p q ↦ (hwid p q).trans_lt hw) D).2.2
  change (exponentialOperators Ω hΩ D).2.2.1 + (periodicCorrectorData Ω hΩ D).2.2 0 =
    (exponentialOperators ((1 / 2 : ℝ) • Ω) hΩh ((1 / 2 : ℝ) • D)).2.2.1 at he
  rw [← frameOp_eq_paper_value hΩ hw hwid D,
    ← frameOp_eq_paper_value hΩh (by linarith [pi_pos] : w / 2 < 2 * π) hhalf
      ((1 / 2 : ℝ) • D)] at he
  have had : I • adL ((1 / 2 : ℝ) • Ω) = (1 / 2 : ℂ) • (I • adL Ω) := by
    rw [← Complex.coe_smul]
    simp only [adL, map_smul, ← smul_sub, smul_comm I]
    norm_num
  simp only [frameOp, had] at he
  rw [← Complex.coe_smul, map_smul] at he
  -- Normalize the real half-scaling as a complex scalar, then solve the endpoint sum for Y(0).
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at he
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  rw [neg_sub]
  exact eq_sub_of_add_eq' he

end UnitaryProducts.PaperProof
