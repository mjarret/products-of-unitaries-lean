/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.Adiabatic

/-!
# Transfer of leakage bounds

Proposition 2.4 (`prop:transfer`): unitary endpoint phases and changes of orthogonal
projectors alter leakage by at most the comparison error and the projector errors.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The three-term identity in the proof of Proposition 2.4 (`prop:transfer`), in the
same order as the paper: evolution error, final projector error, initial error. -/
theorem transfer_identity (P Q Pt Qt U W A B : 𝕄) :
    (1 - Qt) * A * W * B * Pt - (1 - Q) * U * P =
      (1 - Qt) * (A * W * B - U) * Pt +
        (Q - Qt) * U * P + (1 - Qt) * U * (Pt - P) := by
  noncomm_ring

/-- The first sentence of the transfer proof: commuting endpoint phases can be
moved outside the leakage compression and removed by unitary invariance. -/
theorem transfer_phase_norm {Pt Qt A B : 𝕄} (W : 𝕄)
    (hA : A ∈ unitary 𝕄) (hB : B ∈ unitary 𝕄)
    (hAQ : Commute A Qt) (hBP : Commute B Pt) :
    ‖(1 - Qt) * A * W * B * Pt‖ = ‖(1 - Qt) * W * Pt‖ := by
  have hleft : (1 - Qt) * A = A * (1 - Qt) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAQ.eq]
  have hmove : (1 - Qt) * A * W * B * Pt =
      A * ((1 - Qt) * W * Pt) * B := by
    rw [hleft]
    simp only [mul_assoc, hBP.eq]
  rw [hmove, CStarRing.norm_mul_mem_unitary _ hB,
    CStarRing.norm_mem_unitary_mul _ hA]

/-- Proposition 2.4 (`prop:transfer`) (Transfer of leakage bounds). The evolution and
product are arbitrary matrices; only the endpoint phases are unitary. The proof
is the paper's commutation, three-term identity, contraction estimates, and
reverse triangle inequality. The hypothesis that Q is an orthogonal projector
expresses the paper’s setting; the three-term bound does not need it. -/
@[nolint unusedArguments]
theorem prop_transfer {P Q Pt Qt U W A B : 𝕄}
    (hP : IsStarProjection P) (_hQ : IsStarProjection Q)
    (hPt : IsStarProjection Pt) (hQt : IsStarProjection Qt)
    (hA : A ∈ unitary 𝕄) (hB : B ∈ unitary 𝕄)
    (hAQ : Commute A Qt) (hBP : Commute B Pt) :
    |‖(1 - Qt) * W * Pt‖ - ‖(1 - Q) * U * P‖| ≤
      ‖A * W * B - U‖ + ‖U‖ * (‖Pt - P‖ + ‖Qt - Q‖) := by
  have hphase := transfer_phase_norm W hA hB hAQ hBP
  have hPc := norm_le_one_of_isStarProjection hP
  have hPtc := norm_le_one_of_isStarProjection hPt
  have hQtc := norm_le_one_of_isStarProjection hQt.one_sub
  have herror : ‖(1 - Qt) * (A * W * B - U) * Pt‖ ≤ ‖A * W * B - U‖ := by
    simpa only [one_mul, mul_one] using
      norm_mul_le_of_le (norm_mul_le_of_le hQtc (le_refl ‖A * W * B - U‖)) hPtc
  have hfinal : ‖(Q - Qt) * U * P‖ ≤ ‖Qt - Q‖ * ‖U‖ := by
    simpa only [mul_one, norm_sub_rev] using
      norm_mul_le_of_le (norm_mul_le (Q - Qt) U) hPc
  have hinitial : ‖(1 - Qt) * U * (Pt - P)‖ ≤ ‖U‖ * ‖Pt - P‖ := by
    simpa only [one_mul] using
      norm_mul_le_of_le (norm_mul_le_of_le hQtc (le_refl ‖U‖)) (le_refl ‖Pt - P‖)
  calc
    _ = |‖(1 - Qt) * A * W * B * Pt‖ - ‖(1 - Q) * U * P‖| := by rw [hphase]
    _ ≤ ‖(1 - Qt) * A * W * B * Pt - (1 - Q) * U * P‖ := abs_norm_sub_norm_le _ _
    _ = ‖(1 - Qt) * (A * W * B - U) * Pt +
          (Q - Qt) * U * P + (1 - Qt) * U * (Pt - P)‖ := by rw [transfer_identity]
    _ ≤ ‖A * W * B - U‖ + ‖Qt - Q‖ * ‖U‖ + ‖U‖ * ‖Pt - P‖ :=
      norm_add_le_of_le (norm_add_le_of_le herror hfinal) hinitial
    _ = _ := by ring

/-- Section 3: with unchanged endpoint projectors and identity phases, leakage
bounds transfer in both directions with additive operator-norm error. -/
theorem transfer_same_projectors {P Q : 𝕄} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (U W : 𝕄) :
    |‖(1 - Q) * W * P‖ - ‖(1 - Q) * U * P‖| ≤ ‖W - U‖ := by
  simpa using prop_transfer (U := U) (W := W) hP hQ hP hQ
    (show (1 : 𝕄) ∈ unitary 𝕄 from one_mem _) (one_mem _)
    (Commute.one_left Q) (Commute.one_left P)

end UnitaryProducts.PaperProof
