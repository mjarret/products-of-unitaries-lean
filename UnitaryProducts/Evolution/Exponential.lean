/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Simulation

/-!
# Real exponentials of matrices

## Declarations

- `norm_exp_smul_le`
- `norm_exp_sub_exp_le`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open NormedSpace Set Finset Matrix

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Growth of real exponentials** (Grönwall): `‖e^{sX}‖ ≤ e^{s‖X‖}` for `s ≥ 0`. -/
theorem norm_exp_smul_le (X : 𝕄) {s : ℝ} (hs : 0 ≤ s) : ‖exp (s • X)‖ ≤ Real.exp (s * ‖X‖) := by
  have h1 : ‖exp ((0 : ℝ) • X)‖ ≤ 1 := by
    rw [zero_smul, exp_zero]; exact norm_le_one_of_star_mul_self (by simp)
  simpa [gronwallBound_ε0, mul_comm] using norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun u : ℝ ↦ exp (u • X)) (f' := fun u ↦ X * exp (u • X)) (δ := 1) (K := ‖X‖) (ε := 0)
    (a := 0) (b := s)
    (fun u _ ↦ (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X u).continuousAt.continuousWithinAt)
    (fun u _ ↦ (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X u).hasDerivWithinAt) h1
    (fun u _ ↦ by simpa using norm_mul_le X (exp (u • X))) s ⟨hs, le_rfl⟩

/-- **Lipschitz bound for the exponential**: `‖e^{A} - e^{B}‖ ≤ ‖A - B‖ e^{max(‖A‖, ‖B‖)}`.
Differentiate `v ↦ e^{vA} e^{(1-v)B}`, whose derivative is `e^{vA} (A - B) e^{(1-v)B}`. -/
theorem norm_exp_sub_exp_le (A B : 𝕄) :
    ‖exp A - exp B‖ ≤ ‖A - B‖ * Real.exp (max ‖A‖ ‖B‖) := by
  set φ : ℝ → 𝕄 := fun v ↦ exp (v • A) * exp ((1 - v) • B)
  have hderiv : ∀ v ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (exp (v • A) * (A - B) * exp ((1 - v) • B)) (Icc 0 1) v := by
    intro v _
    have hB : HasDerivAt (fun v : ℝ ↦ exp ((1 - v) • B)) (-(B * exp ((1 - v) • B))) v := by
      simpa [Function.comp_def] using
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (1 - v)).scomp v ((hasDerivAt_id v).const_sub 1)
    convert ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) A v).mul hB).hasDerivWithinAt using 1
    rw [((Commute.refl A).smul_right v).exp_right.eq]
    noncomm_ring
  have hbound : ∀ v ∈ Ico (0 : ℝ) 1, ‖exp (v • A) * (A - B) * exp ((1 - v) • B)‖
      ≤ ‖A - B‖ * Real.exp (max ‖A‖ ‖B‖) := by
    intro v hv
    have h1 := norm_exp_smul_le A hv.1
    have h2 := norm_exp_smul_le B (by linarith [hv.2] : 0 ≤ 1 - v)
    have hexp : Real.exp (v * ‖A‖) * Real.exp ((1 - v) * ‖B‖) ≤ Real.exp (max ‖A‖ ‖B‖) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith [mul_le_mul_of_nonneg_left (le_max_left ‖A‖ ‖B‖) hv.1,
        mul_le_mul_of_nonneg_left (le_max_right ‖A‖ ‖B‖) (sub_nonneg.mpr hv.2.le)]
    calc _ ≤ Real.exp (v * ‖A‖) * ‖A - B‖ * Real.exp ((1 - v) * ‖B‖) :=
          norm_mul_le_of_le (norm_mul_le_of_le h1 le_rfl) h2
      _ = ‖A - B‖ * (Real.exp (v * ‖A‖) * Real.exp ((1 - v) * ‖B‖)) := by ring
      _ ≤ _ := by gcongr
  simpa [φ] using norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1 ⟨zero_le_one, le_rfl⟩

end UnitaryProducts
