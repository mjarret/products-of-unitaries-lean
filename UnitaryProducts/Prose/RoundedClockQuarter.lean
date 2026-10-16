/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.UnitStepsCorrector

/-!
# The sharp rounded-clock Duhamel bound

## Declarations

- `clock_error_eq_on_closed_cell`
- `rounded_duhamel_quarter`
- `rounded_hamiltonian_error_chain`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set MeasureTheory Real

noncomputable section
namespace UnitaryProducts.Paper

open UnitStepsProse

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1, rounded Hamiltonian error (sec1-42): the pointwise estimate with its
intermediate distance factor, including the endpoint half-cells and rounding ties. -/
theorem rounded_hamiltonian_error_chain {H Hd : ℝ → 𝕄} {N : ℕ}
    {h : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ h) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) N) :
    ‖H ((⌊t + 1 / 2⌋ : ℝ) / N) - H (t / N)‖ ≤
        h * |t - (⌊t + 1 / 2⌋ : ℝ)| / N ∧
      h * |t - (⌊t + 1 / 2⌋ : ℝ)| / N ≤ h / (2 * N) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hh : 0 ≤ h := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, zero_le_one⟩)
  have ht' : t / N ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hn, div_le_one_of_le₀ ht.2 hn⟩
  constructor
  · have hb := UnitaryProducts.norm_sub_le_of_derivWithin_le hd hbd
      _ ht' _ (rounded_clock_sample_mem (N := N) ht)
    rwa [← sub_div, abs_div, abs_of_nonneg hn, abs_sub_comm, ← mul_div_assoc] at hb
  · calc h * |t - (⌊t + 1 / 2⌋ : ℝ)| / N ≤ h * (1 / 2) / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (by simpa only [abs_sub_comm] using (rounded_clock_error_and_tie t).1) hh) hn
      _ = h / (2 * N) := by ring

/-- Section 1, Duhamel display (sec1-43): integrating the rounded error gives `h/4`.
Only the stated derivative bound within `[0,1]` is needed; Lipschitz continuity of the
path follows from it. Evolutions here use physical time `[0,N]`. -/
theorem rounded_duhamel_quarter {H Hd U V : ℝ → 𝕄} {N : ℕ} {h : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ h)
    (hU : IsEvolution (fun t ↦ H (t / N)) U 0 N)
    (hV : IsEvolution (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / N)) V 0 N) :
    ‖V N - U N‖ ≤ h / 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hh := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, zero_le_one⟩)
    simpa [hU.2.1, hV.2.1] using div_nonneg hh (by norm_num : (0 : ℝ) ≤ 4)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖H x - H s‖ ≤ h * |x - s| :=
    fun x hx s hs ↦ UnitaryProducts.norm_sub_le_of_derivWithin_le hd hbd s hs x hx
  have hu' : IsEvolution (fun s ↦ (N : ℝ) • H s) (fun s ↦ U (N * s)) 0 1 := by
    simpa only [div_self hn.ne', div_one] using rescaled_evolution hU hn
  have hv : IsEvolution (fun t ↦ H (sample N (t / N))) V 0 N := by
    simpa only [sample, clock, mul_div_cancel₀ _ hn.ne'] using hV
  have hv' : IsEvolution (fun s ↦ (N : ℝ) • H (sample N s))
      (fun s ↦ V (N * s)) 0 1 := by
    simpa only [div_self hn.ne', div_one] using
      rescaled_evolution (H := fun s ↦ H (sample N s)) hv hn
  simpa only [mul_one] using rounded_evolution_unit_steps hL hu' hv'

namespace UnitStepsProse

/-- Section 4, cell integral calculation (sec4a-6): on a closed cell the distance to the
rounded clock equals the distance to the center, including both ties. -/
theorem clock_error_eq_on_closed_cell {x : ℝ} (j : ℤ)
    (hx : |x - j| ≤ 1 / 2) : |(clock x : ℝ) - x| = |x - j| := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  by_cases ht : x < (j : ℝ) + 1 / 2
  · have hq : clock x = j := by
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith
    rw [hq, abs_sub_comm]
  · have he : x = (j : ℝ) + 1 / 2 := by linarith
    subst x
    have hq : clock ((j : ℝ) + 1 / 2) = j + 1 := by
      unfold clock
      rw [show (j : ℝ) + 1 / 2 + 1 / 2 = (j : ℝ) + 1 by ring]
      simp
    rw [hq]
    push_cast
    ring_nf


end UnitStepsProse
end UnitaryProducts.Paper
