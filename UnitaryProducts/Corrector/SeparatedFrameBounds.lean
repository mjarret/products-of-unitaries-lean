/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.SeparatedFrameKernel

/-!
# A Schwartz-kernel operator acting by $\mathcal N$ on separated eigenoperators

## Declarations

- `frameExtension`
- `frameExtension_eq`
- `frameKernel`
- `isHermitian_real_smul`
- `separatedFrame`
- `separatedFrame_add`
- `separatedFrame_of_eigen`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator FourierTransform
open Complex MeasureTheory Set
noncomputable section
namespace UnitaryProducts.Separation

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Some Schwartz function that agrees with `frameMult` ($\mathcal N$ in closed form) on
`allowedDifferences ε W`, picked with `Classical.choose` from `exists_schwartz_frameMult` (a
smooth cutoff times `frameMult`, which is analytic near that compact set). It depends only on
`ε` and `W`, not on a matrix.

The chosen function is not determined, but every choice gives the same results.
`frameExtension_eq` pins its values on `allowedDifferences ε W`, and no result reads any other
value: `separatedFrame` enters proofs only through additivity in `D` (`separatedFrame_add`, and
its value $0$ at `D = 0`), which holds for every kernel, and through `separatedFrame_of_eigen`,
which evaluates `frameExtension` only at an eigenvalue difference $p - q$ in that set, where it is
`frameMult (p - q)`. Hence for every $h$ with `HasSeparatedSpectrum hh ε W`,
`separatedFrame ε W hε h D` is the choice-free eigenbasis formula $\mathcal N(\mathrm{ad}_h)(D)$
(`separatedFrame_eq_correctorSeries`, `Comparison/UnitSteps.lean`), whichever function was chosen;
when the eigenvalue differences of $h$ have modulus below $2\pi$, that is also the operator series
`frameOp h D` (`frameOp_eq_paper_value`, `Comparison/SpectralWidth.lean`). -/
def frameExtension (ε W : ℝ) (hε : 0 < ε) : SchwartzMap ℝ ℂ :=
  Classical.choose (exists_schwartz_frameMult hε W)

/-- The specification of the choice: `frameExtension` is `frameMult` on the allowed set. -/
theorem frameExtension_eq (ε W : ℝ) (hε : 0 < ε) {x : ℝ}
    (hx : x ∈ allowedDifferences ε W) :
    frameExtension ε W hε x = (UnitaryProducts.Corrector.frameMult x : ℂ) :=
  Classical.choose_spec (exists_schwartz_frameMult hε W) x hx

/-- The Fourier transform of `frameExtension`: one kernel $g$ for every matrix, used by
`separatedFrame`. It inherits the choice made in `frameExtension`. -/
def frameKernel (ε W : ℝ) (hε : 0 < ε) : SchwartzMap ℝ ℂ :=
  𝓕 (frameExtension ε W hε)

/-- The operator $D \mapsto \int g(s)\, e^{2\pi i s h} D e^{-2\pi i s h}\, ds$ with
$g$ = `frameKernel ε W hε`. By Fourier inversion it multiplies each eigenoperator of $h$ whose
eigenvalue difference lies in `allowedDifferences ε W` by `frameMult` of that difference
(`separatedFrame_of_eigen`), so for $h$ with `HasSeparatedSpectrum hh ε W` it is
$\mathcal N(\mathrm{ad}_h)(D)$ (`separatedFrame_eq_correctorSeries`). It is defined for every $h$;
where the eigenvalue differences of $h$ leave the allowed set its value depends on the choice in
`frameExtension`, and no lemma uses it there. -/
def separatedFrame (ε W : ℝ) (hε : 0 < ε) (h D : 𝕄) : 𝕄 :=
  kernelFrame (frameKernel ε W hε) ((2 * Real.pi) • h) D

/-- A real multiple of a Hermitian matrix is Hermitian (applied to $2\pi h$). -/
theorem isHermitian_real_smul {h : 𝕄} (hh : h.IsHermitian) (r : ℝ) :
    (r • h).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint] at hh ⊢; exact (IsSelfAdjoint.all r).smul hh

/-- Additivity in the drift variable. -/
theorem separatedFrame_add (ε W : ℝ) (hε : 0 < ε) {h : 𝕄}
    (hh : h.IsHermitian) (D E : 𝕄) :
    separatedFrame ε W hε h (D+E) =
      separatedFrame ε W hε h D + separatedFrame ε W hε h E := by
  unfold separatedFrame kernelFrame
  simp only [mul_add, add_mul, smul_add]
  refine integral_add ?_ ?_ <;>
    exact integrable_kernelFrame (frameKernel ε W hε).integrable (isHermitian_real_smul hh _) _

/-- Exact action of the separated frame on each matrix eigenoperator. -/
theorem separatedFrame_of_eigen (ε W : ℝ) (hε : 0 < ε) {h E : 𝕄} {p q : ℝ}
    (hp : h * E = (p : ℂ) • E) (hq : E * h = (q : ℂ) • E)
    (hpq : p - q ∈ allowedDifferences ε W) :
    separatedFrame ε W hε h E = (UnitaryProducts.Corrector.frameMult (p-q) : ℂ) • E := by
  have hp' : ((2 * Real.pi) • h) * E = ((2 * Real.pi * p : ℝ) : ℂ) • E := by
    rw [smul_mul_assoc, hp, ← Complex.coe_smul, smul_smul]; congr 1; push_cast; ring
  have hq' : E * ((2 * Real.pi) • h) = ((2 * Real.pi * q : ℝ) : ℂ) • E := by
    rw [mul_smul_comm, hq, ← Complex.coe_smul, smul_smul]; congr 1; push_cast; ring
  rw [separatedFrame, kernelFrame_of_eigen _ hp' hq',
    show 2 * Real.pi * p - 2 * Real.pi * q = 2 * Real.pi * (p-q) by ring,
    frameKernel, kernelSymbol_fourier, frameExtension_eq ε W hε hpq]

end UnitaryProducts.Separation
