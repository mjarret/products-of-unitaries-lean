/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.Commutator
public import UnitaryProducts.Corrector.SeriesIdentity
public import UnitaryProducts.Evolution.Propagator
public import UnitaryProducts.Evolution.Simulation

/-!
# Analyticity of scalar power series in a Banach algebra

## Declarations

- `analyticOnNhd_tsum_coeff`
- `bernBound`
- `continuousOn_of_norm_sub_le`
- `unit_lipschitz_constant_nonneg`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Real

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- **A scalar power series is analytic on its disc of convergence.**  If `∑ |c n| rⁿ` converges
for every `0 ≤ r < R`, then `a ↦ ∑ c n aⁿ` is analytic on the ball of radius `R`. -/
theorem analyticOnNhd_tsum_coeff {c : ℕ → ℂ} {R : ℝ} (hR : 0 < R)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < R → Summable (fun n : ℕ ↦ ‖c n‖ * r ^ n)) :
    AnalyticOnNhd ℂ (fun a : A ↦ ∑' n : ℕ, c n • a ^ n) (Metric.ball 0 R) := by
  have hrad : ENNReal.ofReal R ≤ (FormalMultilinearSeries.ofScalars A c).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
    have hrR : (r : ℝ) < R := by simpa using (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hr
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
      (hsum r r.coe_nonneg hrR)
    rw [FormalMultilinearSeries.ofScalars_norm]
  have hball : HasFPowerSeriesOnBall (fun a : A ↦ ∑' n : ℕ, c n • a ^ n)
      (FormalMultilinearSeries.ofScalars A c) 0 (ENNReal.ofReal R) := by
    refine ⟨hrad, by simpa using hR, fun {y} hy ↦ ?_⟩
    simpa only [zero_add, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq] using
      (FormalMultilinearSeries.ofScalars A c).hasSum (Metric.eball_subset_eball hrad hy)
  simpa only [Metric.eball_ofReal] using hball.analyticOnNhd

end UnitaryProducts.Corrector

namespace UnitaryProducts

open UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The majorant of the Bernoulli series, `∑ |Bₙ| wⁿ/n! = w/2 + 2 - (w/2) cot(w/2)` for
$0 < w < 2\pi$ (`tsum_abs_bernoulli_eq`). It is the `tsum` junk value $0$ where the series
diverges. -/
noncomputable def bernBound (w : ℝ) : ℝ :=
  ∑' n : ℕ, |((bernoulli n : ℚ) : ℝ)| * w ^ n / (Nat.factorial n)

/-- A Lipschitz bound on the unit interval has a nonnegative constant. -/
theorem unit_lipschitz_constant_nonneg {H : ℝ → 𝕄} {L : ℝ}
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H t - H s‖ ≤ L * |t - s|) : 0 ≤ L := by
  simpa using (norm_nonneg _).trans (h 0 (left_mem_Icc.mpr zero_le_one)
    1 (right_mem_Icc.mpr zero_le_one))

/-- A real-parameter norm Lipschitz bound implies continuity on its domain. -/
theorem continuousOn_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    {H : ℝ → E} {S : Set ℝ} {L : ℝ}
    (h : ∀ s ∈ S, ∀ t ∈ S, ‖H t - H s‖ ≤ L * |t - s|) :
    ContinuousOn H S := by
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal L) fun x hx y hy ↦ ?_).continuousOn
  rw [dist_eq_norm, Real.dist_eq]
  exact (h y hy x hx).trans (by gcongr; exact Real.le_coe_toNNReal L)

end UnitaryProducts
