/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Appendix.SeriesDerivative

/-! # Lemma A.3: the map `𝓕` and its value on a commutator

For matrices `A`, the proof of Lemma A.3 sets
`𝓕(A) = ∑_{n ≥ 1} νₙ ∑_{k<n} [Ω,·]^k [A, [Ω,·]^{n-1-k} Ω']`. Here `endValue_F Ω B D` is `𝓕(B)` with
`D` in place of `Ω'`. The map `𝓕` is linear, and on a commutator `[Ω,Λ]` the sum over `k`
telescopes (lines 1 and 2 of (A.4)), which gives
`‖𝓕([Ω,Λ])‖ ≤ 4(𝒩(w) - 𝒩(0)) ‖Λ‖ ‖Ω'‖`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real

noncomputable section

namespace RoundedClocks

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The `𝓕(B) = ∑ₙ νₙ ∑_{k<n} [Ω,·]^k [B, [Ω,·]^{n-1-k} D]` of the proof of Lemma A.3, where the
paper has `D = Ω'`. The sum over `k` is `powDeriv (adL Ω) (adL B) n D`. -/
def endValue_F (Ω B D : 𝕄) : 𝕄 :=
  ∑' n : ℕ, (multiplierCoeff n : ℂ) • (powDeriv (adL Ω) (adL B) n) D

/-- The series defining `𝓕(B)` converges when `‖[Ω,·]‖ < 2π`. -/
theorem endValue_summable_F [NeZero d] (Ω B D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      (multiplierCoeff n : ℂ) • (powDeriv (adL Ω) (adL B) n) D) := by
  exact (summable_norm_powDeriv_series (Ω := Ω) (B := B) (A := D)
    (w := ‖adL Ω‖) multiplierCoeff_nonneg (norm_nonneg (adL Ω)) le_rfl
    (summable_multiplierCoeff_deriv (norm_nonneg (adL Ω)) ha)).of_norm

/-- `𝓕` is additive: `𝓕(B + C) = 𝓕(B) + 𝓕(C)`. -/
theorem endValue_F_add [NeZero d] (Ω B C D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    endValue_F Ω (B + C) D = endValue_F Ω B D + endValue_F Ω C D := by
  have hadd : adL (B + C) = adL B + adL C :=
    (adLCLM (d := d)).map_add B C
  simp only [endValue_F, hadd, powDeriv_add, ContinuousLinearMap.add_apply, smul_add]
  exact (endValue_summable_F Ω B D ha).tsum_add (endValue_summable_F Ω C D ha)

/-- Lines 1 and 2 of (A.4):
`𝓕([Ω,Λ]) = ∑_{n ≥ 1} νₙ ([Ω,·]ⁿ[Λ,D] - [Λ,[Ω,·]ⁿD])`. -/
theorem endValue_F_commutator_series [NeZero d] (Ω Λ D : 𝕄)
    (ha : ‖adL Ω‖ < 2 * π) :
    endValue_F Ω (adL Ω Λ) D = ∑' n : ℕ,
      (multiplierCoeff (n + 1) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL Λ D) - adL Λ ((adL Ω ^ (n + 1)) D)) := by
  rw [endValue_F, (endValue_summable_F Ω (adL Ω Λ) D ha).tsum_eq_zero_add]
  have hz : powDeriv (adL Ω) (adL (adL Ω Λ)) 0 = 0 := by simp [powDeriv]
  rw [hz, ContinuousLinearMap.zero_apply, smul_zero, zero_add]
  apply tsum_congr
  intro n
  rw [powDeriv_adL_commutator]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]

/-- `𝒩(0) = ν₀`. -/
theorem 𝒩_zero_eq_multiplierCoeff : 𝒩 0 = multiplierCoeff 0 := by
  rw [𝒩, if_pos rfl, multiplierCoeff_zero]

/-- `𝒩(w) - 𝒩(0) = ∑_{n ≥ 1} νₙ wⁿ`. -/
theorem tsum_multiplierCoeff_tail {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∑' n : ℕ, multiplierCoeff (n + 1) * w ^ (n + 1)) = 𝒩 w - 𝒩 0 := by
  have hs := (summable_multiplierCoeff_power
    (by rwa [abs_of_nonneg hw0])).tsum_eq_zero_add
  rw [multiplierCoeff_series_eq w (by rwa [abs_of_nonneg hw0])] at hs
  rw [𝒩_zero_eq_multiplierCoeff]
  simpa only [pow_zero, mul_one, eq_sub_iff_add_eq, add_comm] using hs.symm

/-- The last bound in (A.4): each of the two terms in line 2 has norm at most
`2(𝒩(w) - 𝒩(0)) ‖Λ‖ ‖D‖`, by (A.1) for `𝒩(x) - 𝒩(0) = ∑_{n ≥ 1} νₙ xⁿ`, so
`‖𝓕([Ω,Λ])‖ ≤ 4(𝒩(w) - 𝒩(0)) ‖Λ‖ ‖D‖`. -/
theorem norm_endValue_F_commutator_le [NeZero d] {Ω : 𝕄}
    (hΩ : IsHermitian Ω) {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π)
    (hwidth : HasEigenvalueDifferences Ω w) (Λ D : 𝕄) :
    ‖endValue_F Ω (adL Ω Λ) D‖ ≤ 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by
  have ha := (norm_adL_le_width hΩ hw0 hwidth).trans_lt hw
  have hadL := norm_adL_le_width hΩ hw0 hwidth
  have hc (E : 𝕄) : ‖adL Λ E‖ ≤ 2 * ‖Λ‖ * ‖E‖ := by
    simpa only [zero_smul, sub_zero] using norm_adL_apply_le Λ E 0
  have hscalar : Summable (fun n : ℕ ↦ multiplierCoeff (n + 1) * w ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr
      (summable_multiplierCoeff_power (by rwa [abs_of_nonneg hw0]))
  let tailSeries : 𝕄 → 𝕄 := fun E ↦ ∑' n : ℕ,
    (multiplierCoeff (n + 1) : ℂ) • (adL Ω ^ (n + 1)) E
  have hs (E : 𝕄) : Summable (fun n : ℕ ↦
      (multiplierCoeff (n + 1) : ℂ) • (adL Ω ^ (n + 1)) E) :=
    (summable_norm_adL_series (c := fun n ↦ multiplierCoeff (n + 1))
      (k := fun n ↦ n + 1) (fun n ↦ multiplierCoeff_nonneg (n + 1)) hadL hscalar).of_norm
  have htail (E : 𝕄) : ‖tailSeries E‖ ≤ (𝒩 w - 𝒩 0) * ‖E‖ := by
    have h := norm_adL_series_le (c := fun n ↦ multiplierCoeff (n + 1))
      (k := fun n ↦ n + 1) (fun n ↦ multiplierCoeff_nonneg (n + 1)) hadL hscalar
      (E := E)
    rw [tsum_multiplierCoeff_tail hw0 hw] at h
    exact h
  have htail0 : 0 ≤ 𝒩 w - 𝒩 0 := by
    rw [← tsum_multiplierCoeff_tail hw0 hw]
    exact tsum_nonneg fun n ↦ mul_nonneg (multiplierCoeff_nonneg _) (pow_nonneg hw0 _)
  have hseries :
      (∑' n : ℕ, (multiplierCoeff (n + 1) : ℂ) •
        ((adL Ω ^ (n + 1)) (adL Λ D) - adL Λ ((adL Ω ^ (n + 1)) D))) =
      tailSeries (adL Λ D) - adL Λ (tailSeries D) := by
    have hsmap : Summable (fun n : ℕ ↦ adL Λ
        ((multiplierCoeff (n + 1) : ℂ) • (adL Ω ^ (n + 1)) D)) :=
      ((hs D).map (adL Λ) (adL Λ).continuous).congr fun _ ↦ rfl
    rw [show tailSeries (adL Λ D) = ∑' n : ℕ,
        (multiplierCoeff (n + 1) : ℂ) • (adL Ω ^ (n + 1)) (adL Λ D) from rfl,
      show tailSeries D = ∑' n : ℕ,
        (multiplierCoeff (n + 1) : ℂ) • (adL Ω ^ (n + 1)) D from rfl,
      (adL Λ).map_tsum (hs D), ← (hs (adL Λ D)).tsum_sub hsmap]
    apply tsum_congr
    intro n
    simp only [map_smul, smul_sub]
  rw [endValue_F_commutator_series Ω Λ D ha]
  calc
    _ = ‖tailSeries (adL Λ D) - adL Λ (tailSeries D)‖ := congrArg norm hseries
    _ ≤ ‖tailSeries (adL Λ D)‖ + ‖adL Λ (tailSeries D)‖ := norm_sub_le _ _
    _ ≤ (𝒩 w - 𝒩 0) * (2 * ‖Λ‖ * ‖D‖) +
        2 * ‖Λ‖ * ((𝒩 w - 𝒩 0) * ‖D‖) := by
      apply add_le_add
      · exact (htail (adL Λ D)).trans
          (mul_le_mul_of_nonneg_left (hc D) htail0)
      · exact (hc (tailSeries D)).trans
          (mul_le_mul_of_nonneg_left (htail D) (by positivity))
    _ = 4 * (𝒩 w - 𝒩 0) * ‖Λ‖ * ‖D‖ := by ring

end RoundedClocks
