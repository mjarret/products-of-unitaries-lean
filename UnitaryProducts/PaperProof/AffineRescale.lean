/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.UnifiedDerivative

/-! # Affine cell reparametrization in the proof of the jump theorem -/
@[expose] public section
noncomputable section
open Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace UnitaryProducts.PaperProof

/-- The normalized parameter maps to the physical cell, including both endpoints. -/
theorem affineCell_mapsTo {T : ℝ} (hT : 0 < T) (l : ℝ) :
    MapsTo (fun u : ℝ ↦ l + u / T) (Icc 0 1) (Icc l (l + 1 / T)) := by
  intro u hu
  exact ⟨le_add_of_nonneg_right (div_nonneg hu.1 hT.le),
    add_le_add le_rfl (div_le_div_of_nonneg_right hu.2 hT.le)⟩

section BanachSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chain rule contributes one factor `1/T` on the closed cell. -/
theorem hasDerivWithinAt_affineCell {f : ℝ → E} {fd : E} {T l u : ℝ}
    (hT : 0 < T)
    (hf : HasDerivWithinAt f fd (Icc l (l + 1 / T)) (l + u / T)) :
    HasDerivWithinAt (fun v ↦ f (l + v / T)) ((1 / T) • fd) (Icc 0 1) u := by
  exact hf.scomp u (((hasDerivAt_id u).div_const T).const_add l).hasDerivWithinAt
    (affineCell_mapsTo hT l)

/-- A prefactor `1/T` and the parameter change contribute two factors together. -/
theorem hasDerivWithinAt_affineCell_scaled {f : ℝ → E} {fd : E} {T l u : ℝ}
    (hT : 0 < T)
    (hf : HasDerivWithinAt f fd (Icc l (l + 1 / T)) (l + u / T)) :
    HasDerivWithinAt (fun v ↦ (1 / T) • f (l + v / T))
      ((1 / T) ^ 2 • fd) (Icc 0 1) u := by
  simpa only [smul_smul, sq] using (hasDerivWithinAt_affineCell hT hf).const_smul (1 / T)

/-- The first within derivative on the normalized cell is the rescaled
physical derivative, including one-sided endpoint derivatives. -/
theorem derivWithin_affineCell {f : ℝ → E} {T l u : ℝ}
    (hT : 0 < T) (hu : u ∈ Icc (0 : ℝ) 1)
    (hf : DifferentiableWithinAt ℝ f (Icc l (l + 1 / T)) (l + u / T)) :
    derivWithin (fun v ↦ f (l + v / T)) (Icc (0 : ℝ) 1) u =
      (1 / T) • derivWithin f (Icc l (l + 1 / T)) (l + u / T) :=
  (hasDerivWithinAt_affineCell hT hf.hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu)

/-- Differentiating the first derivative contributes the second factor `1/T`. -/
theorem second_derivWithin_affineCell {f : ℝ → E} {T l u : ℝ}
    (hT : 0 < T) (hu : u ∈ Icc (0 : ℝ) 1)
    (hf : DifferentiableOn ℝ f (Icc l (l + 1 / T)))
    (hfd : DifferentiableWithinAt ℝ (derivWithin f (Icc l (l + 1 / T)))
      (Icc l (l + 1 / T)) (l + u / T)) :
    derivWithin (derivWithin (fun v ↦ f (l + v / T)) (Icc (0 : ℝ) 1))
        (Icc (0 : ℝ) 1) u =
      (1 / T) ^ 2 • derivWithin (derivWithin f (Icc l (l + 1 / T)))
        (Icc l (l + 1 / T)) (l + u / T) := by
  have he (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :=
    derivWithin_affineCell hT hv (hf _ (affineCell_mapsTo hT l hv))
  rw [derivWithin_congr he (he u hu)]
  exact (hasDerivWithinAt_affineCell_scaled hT hfd.hasDerivWithinAt).derivWithin
    (uniqueDiffOn_Icc_zero_one u hu)

/-- The common quadratic scaling factor multiplies the derivative norm. -/
theorem norm_affineCell_scaled (T : ℝ) (A : E) :
    ‖(1 / T) ^ 2 • A‖ = (1 / T) ^ 2 * ‖A‖ :=
  norm_smul_of_nonneg (sq_nonneg _) _

/-- The two end-value estimates have the same quadratic scaling on the
right: one second derivative, or a product of two first derivatives. -/
theorem affineCell_rhs_scaling {T : ℝ} (hT : 0 < T)
    (c₀ c₁ c₂ : ℝ) (Dd V D : E) :
    c₀ * ‖(1 / T) ^ 2 • Dd‖ +
        c₁ * ‖(1 / T) • V‖ * ‖(1 / T) • D‖ + c₂ * ‖(1 / T) • D‖ ^ 2 =
      (1 / T) ^ 2 * (c₀ * ‖Dd‖ + c₁ * ‖V‖ * ‖D‖ + c₂ * ‖D‖ ^ 2) := by
  rw [norm_smul_of_nonneg (sq_nonneg _),
    norm_smul_of_nonneg (one_div_pos.mpr hT).le,
    norm_smul_of_nonneg (one_div_pos.mpr hT).le]
  ring

end BanachSpace

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
open UnitaryProducts UnitaryProducts.Corrector

/-- The multiplier is linear in its input; the first derivative's scaling
and the chain rule therefore give exactly the claimed `T⁻²` factor. -/
theorem hasDerivWithinAt_affineCell_frame {Ω D : ℝ → 𝕄} {Fd : 𝕄} {T l u : ℝ}
    (hT : 0 < T)
    (hF : HasDerivWithinAt (fun s ↦ frameOp (Ω s) (D s)) Fd
      (Icc l (l + 1 / T)) (l + u / T)) :
    HasDerivWithinAt
      (fun v ↦ frameOp (Ω (l + v / T)) ((1 / T) • D (l + v / T)))
      ((1 / T) ^ 2 • Fd) (Icc 0 1) u := by
  simpa only [frameOp, ContinuousLinearMap.map_smul_of_tower] using
    hasDerivWithinAt_affineCell_scaled hT hF

/-- Both sides of a real norm estimate may be divided by the common positive
factor `T⁻²`, precisely as in the physical-cell application of Lemma A.3. -/
theorem affineCell_quadratic_bound_iff {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    (1 / T) ^ 2 * a ≤ (1 / T) ^ 2 * b ↔ a ≤ b :=
  mul_le_mul_iff_right₀ (sq_pos_of_pos (one_div_pos.mpr hT))

end UnitaryProducts.PaperProof
