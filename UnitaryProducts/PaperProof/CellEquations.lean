/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.PaperProof.LocalCell
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Corrector.SeparatedFrame
public import UnitaryProducts.Evolution.RoundedClock
/-! # The opening cell argument and residual split in Section 4 -/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
open Complex Real Set MeasureTheory Matrix
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- Entrywise conjugation in an eigenbasis: the phase is the eigenvalue
difference, multiplied by the local time and the corresponding entry. -/
theorem cell_eigenbasis_entry (lam : Fin d → ℝ) (D : 𝕄) (τ : ℝ) (p q : Fin d) :
    (evol (diagonal (fun k ↦ (lam k : ℂ))) (-τ) * (τ • D) *
      evol (diagonal (fun k ↦ (lam k : ℂ))) τ) p q =
      (τ : ℂ) * Complex.exp (I * τ * (lam p - lam q)) * D p q := by
  have he (u : ℝ) : evol (diagonal (fun k ↦ (lam k : ℂ))) u =
      diagonal (fun k ↦ Complex.exp ((u : ℂ) * (-I * (lam k : ℂ)))) := by
    rw [evol, ← diagonal_smul, ← diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext k
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      Complex.real_smul]
  rw [he, he, mul_diagonal, diagonal_mul]
  simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_neg]
  rw [show Complex.exp (-(τ : ℂ) * (-I * (lam p : ℂ))) *
      ((τ : ℂ) * D p q) * Complex.exp ((τ : ℂ) * (-I * (lam q : ℂ))) =
      (τ : ℂ) * (Complex.exp (-(τ : ℂ) * (-I * (lam p : ℂ))) *
      Complex.exp ((τ : ℂ) * (-I * (lam q : ℂ)))) * D p q by ring,
    ← Complex.exp_add]
  congr 2
  ring


/-- Section 4 opening: Duhamel first bounds the integral of the generator
norm difference. The derivative estimate bounds that integral by `h/4`;
the intervening rounded-clock integral is evaluated without an inequality. -/
theorem rounded_duhamel_display_chain {H Hd U V : ℝ → 𝕄} {T : ℕ}
    (hT : 0 < T) {h : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ h)
    (hKr : IsRegulated (fun t ↦ H (t / T)) 0 T)
    (hGr : IsRegulated (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) 0 T)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H ((⌊t + 1 / 2⌋ : ℝ) / T)) V 0 T) :
    ‖V T - U T‖ ≤ (∫ t in (0 : ℝ)..T,
      ‖H (t / T) - H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) ∧
    (∫ t in (0 : ℝ)..T, ‖H (t / T) - H ((⌊t + 1 / 2⌋ : ℝ) / T)‖) ≤
      h / T * (∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) ∧
    h / T * (∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) = h / 4 := by
  have ht : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hi := ((hKr.intervalIntegrable_on ht).sub
    (hGr.intervalIntegrable_on ht)).norm
  have hclock : IntervalIntegrable (fun t : ℝ ↦ |t - (⌊t + 1 / 2⌋ : ℝ)|)
      volume 0 T := by
    simpa only [UnitStepsProse.clock, abs_sub_comm] using
      (UnitStepsProse.clock_error_integrable 0 T)
  refine ⟨duhamel_bound ht hKr hGr hU hV, ?_, ?_⟩
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ht hi (hclock.const_mul (h / T))
    intro t hmem
    have hpoint := (rounded_hamiltonian_error_chain hd hbd hmem).1
    simpa only [norm_sub_rev, mul_div_right_comm] using hpoint
  · have hmean := Prose.rounded_clock_mean_quarter hT
    calc
      h / T * (∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) =
          h * ((∫ t in (0 : ℝ)..T, |t - (⌊t + 1 / 2⌋ : ℝ)|) / T) := by ring
      _ = h / 4 := by rw [hmean]; ring


/-- The first-order Hamiltonian difference has zero integral on a full cell
before conjugating into the evolution frame. -/
theorem unframed_linear_integral (D : 𝕄) :
    (∫ τ in (-1 / 2 : ℝ)..(1 / 2), τ • D) = 0 := by
  rw [intervalIntegral.integral_smul_const, integral_id]
  norm_num


end UnitaryProducts.PaperProof
