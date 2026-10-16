/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.Walks.FrameCubic
public import UnitaryProducts.PaperProof.MatrixSeries

/-! # Differentiation of the cell end value on a closed parameter interval

The frame series is differentiated in its Banach algebra before it is applied
in the matrix algebra. Within derivatives include both endpoints of the paper's
closed interval. The convergent derivative series is the error term in the product comparison bound.
-/
@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator Topology
open Complex Real Set Filter MeasureTheory
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper.UnitStepsProse

namespace UnitaryProducts.Corrector
section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- Differentiate the frame series along a curve, including a one-sided endpoint.
The directional derivative is the locally normally convergent series already
constructed in `hasDerivAt_cubic_frameSeries_line`. -/
theorem hasDerivWithinAt_frameSeries_comp {f : ℝ → A} {fd : A} {S : Set ℝ} {s : ℝ}
    (hf : HasDerivWithinAt f fd S s) (ha : ‖f s‖ < 2 * π) :
    HasDerivWithinAt (fun t ↦ frameSeries (f t))
      (cubicFrameSeriesDerivative (f s) fd) S s := by
  have hdiff : DifferentiableAt ℂ (frameSeries : A → A) (f s) :=
    (analyticOnNhd_cubic_frameSeries _ (mem_ball_zero_iff.mpr ha)).differentiableAt
  have hline : HasDerivAt (fun z : ℂ ↦ f s + z • fd) fd 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const fd).const_add (f s)
  have hbase : HasFDerivAt (frameSeries : A → A) (fderiv ℂ frameSeries (f s))
      (f s + (0 : ℂ) • fd) := by
    simpa only [zero_smul, add_zero] using hdiff.hasFDerivAt
  have hcomp := hbase.comp_hasDerivAt 0 hline
  have hvalue := hcomp.unique (hasDerivAt_cubic_frameSeries_line ha)
  simpa only [← hvalue] using
    (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivWithinAt s hf
omit [CompleteSpace A] [NormOneClass A] in
/-- The noncommutative power rule in a generic algebra, before instantiation
at the algebra of continuous linear operators. -/
theorem hasDerivWithinAt_cubic_pow {f : ℝ → A} {fd : A} {S : Set ℝ} {s : ℝ}
    (hf : HasDerivWithinAt f fd S s) (n : ℕ) :
    HasDerivWithinAt (fun t ↦ f t ^ n) (cubicPowDerivative (f s) fd n) S s := by
  simpa only [cubicPowDerivative, Nat.pred_eq_sub_one] using hf.fun_pow' n

end BanachAlgebra

section BanachSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Compose a real-parameter derivative with a complex-linear map. -/
theorem hasDerivWithinAt_complex_clm_comp (L : E →L[ℂ] F)
    {v : ℝ → E} {vd : E} {S : Set ℝ} {s : ℝ}
    (hv : HasDerivWithinAt v vd S s) :
    HasDerivWithinAt (fun t ↦ L (v t)) (L vd) S s :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s hv

/-- Evaluation of a complex-linear operator curve along a real parameter. -/
theorem hasDerivWithinAt_complex_clm_apply {L : ℝ → E →L[ℂ] F} {Ld : E →L[ℂ] F}
    {v : ℝ → E} {vd : E} {S : Set ℝ} {s : ℝ}
    (hL : HasDerivWithinAt L Ld S s) (hv : HasDerivWithinAt v vd S s) :
    HasDerivWithinAt (fun t ↦ L t (v t)) (Ld (v s) + L s vd) S s := by
  have hrestrict := (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).hasFDerivAt
    |>.comp_hasDerivWithinAt s hL
  exact hrestrict.clm_apply hv
end BanachSpace
end UnitaryProducts.Corrector

namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]
/-- The analytic frame series is smooth throughout its convergence ball. -/
theorem frameSeries_contDiffAt {a : A} (ha : ‖a‖ < 2 * π) :
    ContDiffAt ℂ ⊤ (frameSeries : A → A) a :=
  (analyticOnNhd_cubic_frameSeries a (mem_ball_zero_iff.mpr ha)).contDiffAt
end BanachAlgebra

section BanachSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
/-- Compose the analytic operator series with a linear map, then evaluate it. -/
theorem frameSeries_apply_contDiffAt (L : E →L[ℂ] (E →L[ℂ] E)) (a b : E)
    (h : ‖L a‖ < 2 * π) :
    ContDiffAt ℂ ⊤ (fun p : E × E ↦ frameSeries (L p.1) p.2) (a, b) := by
  have hs := frameSeries_contDiffAt h
  have hl : ContDiffAt ℂ ⊤ (fun p : E × E ↦ L p.1) (a, b) :=
    L.contDiff.contDiffAt.comp (a, b) contDiffAt_fst
  exact (hs.comp (a, b) hl).clm_apply contDiffAt_snd
end BanachSpace

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ


/-- The series expression for the variation in the generator, with the input held fixed. -/
def unifiedFrameError (Ω Ωd D : 𝕄) : 𝕄 :=
  cubicFrameSeriesDerivative (I • adL Ω) (I • adL Ωd) D

set_option maxHeartbeats 1200000 in
-- Elaboration composes real derivatives with complex operator-algebra derivatives.
/-- Termwise differentiation splits the input derivative from the generator derivative.
No derivative of an eigenbasis is used, and the assertion includes endpoints. -/
theorem hasDerivWithinAt_frameOp [NeZero d] {Ω D : ℝ → 𝕄} {Ωd Dd : 𝕄}
    {S : Set ℝ} {s : ℝ}
    (hΩ : HasDerivWithinAt Ω Ωd S s) (hD : HasDerivWithinAt D Dd S s)
    (ha : ‖I • adL (Ω s)‖ < 2 * π) :
    HasDerivWithinAt (fun t ↦ frameOp (Ω t) (D t))
      (unifiedFrameError (Ω s) Ωd (D s) + frameOp (Ω s) Dd) S s := by
  have hA := hasDerivWithinAt_complex_clm_comp (E := 𝕄) (F := 𝕄 →L[ℂ] 𝕄)
    (I • adLCLM d) hΩ
  simp only [ContinuousLinearMap.smul_apply,
    show ∀ X : 𝕄, adLCLM d X = adL X from fun _ ↦ rfl] at hA
  have hseries := hasDerivWithinAt_frameSeries_comp (A := 𝕄 →L[ℂ] 𝕄) hA ha
  exact hasDerivWithinAt_complex_clm_apply (E := 𝕄) (F := 𝕄) hseries hD

/-- Continuous differentiability of the end value follows locally from the
normally convergent analytic frame series. This uses only the width at each
parameter value and requires no continuous choice of midpoint or eigenbasis. -/
theorem contDiffOn_frameOp [NeZero d] {Ω D : ℝ → 𝕄} {S : Set ℝ} {w : ℝ}
    (hw : w < 2 * π) (hΩ : ∀ s ∈ S, (Ω s).IsHermitian)
    (hwidth : ∀ s (hs : s ∈ S), ∀ p q,
      |(hΩ s hs).eigenvalues p - (hΩ s hs).eigenvalues q| ≤ w)
    (hcΩ : ContDiffOn ℝ 1 Ω S) (hcD : ContDiffOn ℝ 1 D S) :
    ContDiffOn ℝ 1 (fun s ↦ frameOp (Ω s) (D s)) S := by
  intro s hs
  have ha : ‖I • adL (Ω s)‖ < 2 * π := by
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (show ‖adL (Ω s)‖ ≤ w by
      simpa only [pow_one] using ad_power_norm_le (hΩ s hs) (hwidth s hs) 1).trans_lt hw
  have hlocal := (frameSeries_apply_contDiffAt (I • adLCLM d) (Ω s) (D s) ha).restrict_scalars ℝ
  exact (hlocal.of_le (by norm_num)).comp_contDiffWithinAt s ((hcΩ.prodMk hcD) s hs)

set_option maxHeartbeats 1200000 in
-- The operator power rule requires both complex-linear composition and evaluation.
/-- Differentiate one nested commutator. The finite insertion sum is the
noncommutative power rule, with no assumption that the generator commutes
with its derivative. -/
theorem hasDerivWithinAt_nested_commutator {Ω D : ℝ → 𝕄} {Ωd Dd : 𝕄}
    {S : Set ℝ} {s : ℝ}
    (hΩ : HasDerivWithinAt Ω Ωd S s) (hD : HasDerivWithinAt D Dd S s) (n : ℕ) :
    HasDerivWithinAt (fun t ↦ (adL (Ω t) ^ n) (D t))
      (cubicPowDerivative (adL (Ω s)) (adL Ωd) n (D s) +
        (adL (Ω s) ^ n) Dd) S s := by
  have hA := hasDerivWithinAt_complex_clm_comp (E := 𝕄) (F := 𝕄 →L[ℂ] 𝕄)
    (adLCLM d) hΩ
  simp only [show ∀ X : 𝕄, adLCLM d X = adL X from fun _ ↦ rfl] at hA
  have hpower := hasDerivWithinAt_cubic_pow (A := 𝕄 →L[ℂ] 𝕄) hA n
  simpa only [cubicPowDerivative, Nat.pred_eq_sub_one] using
    hasDerivWithinAt_complex_clm_apply (E := 𝕄) (F := 𝕄) hpower hD


/-- Scaling both the base and direction gives the total degree of each insertion. -/
theorem cubicPowDerivative_smul_both {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (a b : A) (z : ℂ) (n : ℕ) :
    cubicPowDerivative (z • a) (z • b) n = z ^ n • cubicPowDerivative a b n := by
  simp only [cubicPowDerivative, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : (n - 1 - j) + 1 + j = n := by
    have := Finset.mem_range.mp hj
    omega
  simp only [smul_pow, smul_mul_smul]
  rw [← pow_succ, ← pow_add, he]


/-- The error series with the paper's nonnegative coefficients νₙ. -/
theorem unifiedFrameError_positive_series [NeZero d] (Ω Ωd D : 𝕄)
    (ha : ‖I • adL Ω‖ < 2 * π) :
    unifiedFrameError Ω Ωd D = ∑' n : ℕ,
      ((|((bernoulli (n + 2) : ℚ) : ℝ)| /
        (Nat.factorial (n + 2) : ℝ) : ℝ) : ℂ) •
        cubicPowDerivative (adL Ω) (adL Ωd) n D := by
  have hs := (summable_norm_cubicFrameSeriesDerivative (b := I • adL Ωd) ha).of_norm
  rw [unifiedFrameError, cubicFrameSeriesDerivative, tsum_apply_of_summable hs]
  apply tsum_congr
  intro n
  rw [cubicPowDerivative_smul_both, smul_smul,
    UnitaryProducts.Prose.frame_coefficient_mul_I_pow]
  rfl


end UnitaryProducts.PaperProof
