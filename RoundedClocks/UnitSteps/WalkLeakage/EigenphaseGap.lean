/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.WalkLeakage.Band

/-! # The least eigenphase gap of Theorem 4.7

Theorem 4.7 takes `ϑ` to be the least eigenphase gap of the band over `s ∈ [0,1]` and sets
`w = 2π - ϑ`. The eigenphase gap of a band is positive (`eigenphaseGap_pos`), as the distance
`|e^{-iθ} - e^{-iφ}|` is at most the distance along the circle (`chord_le_circleDistance`), and a
continuous gap attains its least value (`gap_minimum`). Hence `ϑ > 0` and `w < 2π`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section

namespace RoundedClocks.WalkLeakage

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `|e^{-iθ} - e^{-iφ}|` is at most the distance along the circle between `e^{-iθ}` and
`e^{-iφ}`. -/
theorem chord_le_circleDistance (θ φ : ℝ) :
    ‖Complex.exp (-I * (θ : ℂ)) - Complex.exp (-I * (φ : ℂ))‖ ≤
      circleDistance θ φ := by
  apply le_ciInf
  intro k
  have he : Complex.exp (I * ((θ - φ + 2 * π * k : ℝ) : ℂ)) =
      Complex.exp (I * ((θ - φ : ℝ) : ℂ)) := by
    have ha : I * ((θ - φ + 2 * π * k : ℝ) : ℂ) =
        I * ((θ - φ : ℝ) : ℂ) + (k : ℂ) * (2 * (π : ℂ) * I) := by
      push_cast
      ring
    rw [ha, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hf : Complex.exp (-I * (θ : ℂ)) - Complex.exp (-I * (φ : ℂ)) =
      Complex.exp (-I * (θ : ℂ)) *
        (1 - Complex.exp (I * ((θ - φ : ℝ) : ℂ))) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  rw [hf, norm_mul]
  have hn : ‖Complex.exp (-I * (θ : ℂ))‖ = 1 := by
    simpa using Complex.norm_exp_I_mul_ofReal (-θ)
  rw [hn, one_mul, norm_sub_rev, ← he]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- Every eigenvalue of a unitary matrix is `e^{-iθ}` for a real `θ`. -/
theorem exists_phase {A : 𝕄} (hA : IsUnitary A) {z : ℂ}
    (hz : z ∈ spectrum ℂ A) : ∃ θ : ℝ, Complex.exp (-I * (θ : ℂ)) = z := by
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp
    (spectrum.norm_eq_one_of_unitary hA hz)
  exact ⟨-θ, by push_cast; ring_nf⟩

/-- The eigenphase gap of a band of a unitary matrix is positive. -/
theorem eigenphaseGap_pos {A : 𝕄} {a b : ℝ} (hband : IsArcBand A a b) :
    0 < eigenphaseGap A a b := by
  let S := spectrum ℂ A ∩ arc a b
  let C := spectrum ℂ A \ arc a b
  let D := (fun p : ℂ × ℂ ↦ ‖p.1 - p.2‖) '' (S ×ˢ C)
  have hS : S.Nonempty := hband.nonempty_inter
  have hC : C.Nonempty := hband.nonempty_diff
  have hD : D.Nonempty := (hS.prod hC).image _
  have hDf : D.Finite :=
    (((Matrix.finite_spectrum A).subset inter_subset_left).prod
      ((Matrix.finite_spectrum A).subset diff_subset)).image _
  have hpos : 0 < sInf D := by
    apply (hDf.lt_csInf_iff hD).mpr
    rintro r ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    apply norm_pos_iff.mpr
    intro he
    exact hw.2 (sub_eq_zero.mp he ▸ hz.2)
  have hne : {r : ℝ | ∃ θ φ : ℝ,
      Complex.exp (-I * (θ : ℂ)) ∈ S ∧
      Complex.exp (-I * (φ : ℂ)) ∈ C ∧ r = circleDistance θ φ}.Nonempty := by
    obtain ⟨z, hz⟩ := hS
    obtain ⟨w, hw⟩ := hC
    obtain ⟨θ, hθ⟩ := exists_phase hband.isUnitary hz.1
    obtain ⟨φ, hφ⟩ := exists_phase hband.isUnitary hw.1
    exact ⟨_, θ, φ, hθ.symm ▸ hz, hφ.symm ▸ hw, rfl⟩
  apply hpos.trans_le
  apply le_csInf hne
  rintro r ⟨θ, φ, hθ, hφ, rfl⟩
  exact (csInf_le hDf.bddBelow ⟨(_, _), ⟨hθ, hφ⟩, rfl⟩).trans
    (chord_le_circleDistance θ φ)

/-- The least eigenphase gap `ϑ` of a band of a unitary family over `s ∈ [0,1]` is positive, and
`ϑ` is at most the eigenphase gap at every `s`, when the gap is continuous in `s`. -/
theorem gap_minimum {W : ℝ → 𝕄} {α β : ℝ → ℝ}
    (hband : IsArcBandFamily W α β)
    (hgap : IsContinuousFamily (fun s ↦ eigenphaseGap (W s) (α s) (β s))) :
    0 < sInf ((fun s ↦ eigenphaseGap (W s) (α s) (β s)) '' Icc 0 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, sInf ((fun s ↦ eigenphaseGap (W s) (α s) (β s)) '' Icc 0 1) ≤
        eigenphaseGap (W s) (α s) (β s) := by
  let g := fun s ↦ eigenphaseGap (W s) (α s) (β s)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr zero_le_one) hgap
  have hleast : IsLeast (g '' Icc 0 1) (g s₀) :=
    ⟨⟨s₀, hs₀, rfl⟩, by rintro y ⟨s, hs, rfl⟩; exact hmin hs⟩
  change 0 < sInf (g '' Icc 0 1) ∧ _
  rw [hleast.csInf_eq]
  exact ⟨eigenphaseGap_pos (hband.isArcBand hs₀), fun s hs ↦ hmin hs⟩

end RoundedClocks.WalkLeakage
