/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Walks.LogarithmDerivative

/-!
# Kernel conjugation operators

## Declarations

- `evol_conj_of_eigen`
- `integrable_kernelFrame`
- `kernelFrame`
- `kernelFrame_of_eigen`
- `kernelSymbol`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex MeasureTheory Set

noncomputable section
namespace UnitaryProducts.Separation

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The conjugations $e^{ish} D e^{-ish}$ integrated against the kernel $g$ over $\mathbb R$.
It is the Bochner junk value $0$ when the integrand is not integrable; for integrable $g$ and
Hermitian $h$ it is integrable (`integrable_kernelFrame`). -/
def kernelFrame (g : ℝ → ℂ) (h D : 𝕄) : 𝕄 :=
  ∫ s : ℝ, g s • (evol h (-s) * D * evol h s)

/-- The integrand of `kernelFrame` is integrable when $g$ is and $h$ is Hermitian. -/
theorem integrable_kernelFrame {g : ℝ → ℂ} (hg : Integrable g) {h : 𝕄}
    (hh : h.IsHermitian) (D : 𝕄) :
    Integrable (fun s : ℝ ↦ g s • (evol h (-s) * D * evol h s)) := by
  have hc : Continuous (fun s : ℝ ↦ evol h (-s) * D * evol h s) :=
    (((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h)
  apply (hg.norm.mul_const ‖D‖).mono'
    (hg.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun s ↦ (norm_smul _ _).trans_le
    (mul_le_mul_of_nonneg_left (norm_evol_conj_le hh D s) (norm_nonneg _))

/-- The scalar symbol $\int g(s) e^{ixs}\, ds$ of a conjugation kernel (angular-frequency
convention); the Bochner junk value $0$ when the integrand is not integrable. -/
def kernelSymbol (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ s : ℝ, g s * Complex.exp ((x : ℂ) * I * (s : ℂ))

/-- Conjugation on a left/right eigenoperator: $e^{ish} E e^{-ish} = e^{i(p - q)s} E$. -/
theorem evol_conj_of_eigen {h E : 𝕄} {p q : ℝ}
    (hp : h * E = (p : ℂ) • E) (hq : E * h = (q : ℂ) • E) (s : ℝ) :
    evol h (-s) * E * evol h s = Complex.exp (((p-q : ℝ) : ℂ) * I * (s : ℂ)) • E := by
  have hp' : (I • h) * E = (I * (p : ℂ)) • E := by rw [smul_mul_assoc, hp, smul_smul]
  have hq' : E * (I • h) = (I * (q : ℂ)) • E := by rw [mul_smul_comm, hq, smul_smul]
  rw [evol_neg_eq_exp, evol_eq_exp, ← neg_smul, exp_smul_mul_of_eigen hp' (s : ℂ),
    smul_mul_assoc, mul_exp_smul_of_eigen hq' (-(s : ℂ)), smul_smul, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- Exact action on an eigenoperator, without any bound on its eigenvalue difference. -/
theorem kernelFrame_of_eigen (g : ℝ → ℂ) {h E : 𝕄} {p q : ℝ}
    (hp : h * E = (p : ℂ) • E) (hq : E * h = (q : ℂ) • E) :
    kernelFrame g h E = kernelSymbol g (p-q) • E := by
  unfold kernelFrame kernelSymbol
  simp_rw [evol_conj_of_eigen hp hq, smul_smul]
  exact integral_smul_const _ _

end UnitaryProducts.Separation
