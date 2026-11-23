/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries
public import RoundedClocks.UnitSteps.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The steps of the proof of Example 4.3

Example 4.3 (`unit_sharp`) takes `Z = diag(1,-1)` and `H(s) = s²Z`. This file writes
`E u = e^{-iuZ}` and proves the steps of the example, in the paper's order:

* `H` satisfies the hypotheses of Theorem 4.2 with `L = 2` and `w = 2` (`regularity`);
* the values `H(s)` commute, so `U(T) = exp(-i∫_0^T H(t/T) dt)` (`evolution_end`) with
  `∫_0^T H(t/T) dt = TZ/3` (`integral_H`), and the `T`-step product is the exponential of `-i`
  times the left-endpoint sum `(T-1)(2T-1)Z/(6T)` (`left_sum`, `sharp_stepProduct`);
* for unitaries `A` and `B`, `‖A - B‖ = ‖AB† - 1‖` (`norm_reduction`), and
  `‖e^{iθZ} - 1‖ = 2|sin(θ/2)|`, as `Z` has eigenvalues `±1` (`norm_phase`);
* the asymptotic form of (i) and the limit of (ii) (`asymptotic`, `limit`).
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks.UnitSharp

/-- Example 4.3: `Z = diag(1,-1)`. -/
def Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]

/-- Example 4.3: the time-dependent Hamiltonian `H(s) = s²Z`. -/
def H (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (s ^ 2 : ℝ) • Z

/-- `E u = e^{-iuZ}`. -/
def E (u : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := exp (u • (-I • Z))

/-- The matrix `Z` is Hermitian. -/
theorem Z_isHermitian : IsHermitian Z := by
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; fin_cases i <;> simp)

/-- `H(s) = s²Z` is Hermitian. -/
theorem H_isHermitian (s : ℝ) : IsHermitian (H s) := by
  change (s ^ 2 • Z).IsHermitian
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  exact (IsSelfAdjoint.all (s ^ 2)).smul Z_isHermitian.isSelfAdjoint

/-- `e^{-i(u+v)Z} = e^{-iuZ} e^{-ivZ}`. -/
theorem E_add (u v : ℝ) : E (u + v) = E u * E v := by
  rw [E, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left _).smul_right _)

/-! ### The hypotheses of Theorem 4.2 -/

/-- The operator norm of `Z` is one. -/
theorem norm_Z : ‖Z‖ = 1 := by
  rw [Z, Matrix.l2_opNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_) ?_
  · fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![(1 : ℂ), -1] : Fin 2 → ℂ) 0

/-- The operator norm of `H(s)` is `s²`. -/
theorem norm_H (s : ℝ) : ‖H s‖ = s ^ 2 := by
  rw [H, norm_smul, norm_Z, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- The derivative of `H(s)` is `2sZ`. -/
theorem hasDerivAt_H (s : ℝ) :
    HasDerivAt H ((2 * s) • Z) s := by
  simpa [H] using (hasDerivAt_pow 2 s).smul_const Z

/-- The derivative `H'(s) = 2sZ` for `s ∈ [0,1]`, one-sided at `0` and `1`. -/
theorem deriv01_H {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∂H s = (2 * s) • Z :=
  (hasDerivAt_H s).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one s hs)

/-- `H(s) = s²Z` satisfies the hypotheses of Theorem 4.2 with `L = 2` and `w = 2`. -/
theorem regularity (T : ℕ) :
    IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H 2 ∧ HasSampleWidth H T 2 := by
  have hH : IsTimeDepHamiltonian H := fun {s} _ ↦ H_isHermitian s
  have hL : HasLipschitzDerivative H 2 := by
    refine ⟨fun s _ ↦
      (hasDerivAt_H s).differentiableAt.differentiableWithinAt, ?_⟩
    intro s₁ hs₁ s₂ hs₂
    rw [deriv01_H hs₁, deriv01_H hs₂, ← sub_smul,
      norm_smul, norm_Z, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_two]
  have hwidth : HasSampleWidth H T 2 := by
    intro j hj x hx y hy
    have hs : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
      exact unitInterval.div_mem (Nat.cast_nonneg j) (Nat.cast_nonneg T) (by exact_mod_cast hj)
    have hxnorm := spectrum.norm_le_norm_of_mem hx
    have hynorm := spectrum.norm_le_norm_of_mem hy
    rw [Real.norm_eq_abs, norm_H] at hxnorm hynorm
    have hsq : ((j : ℝ) / T) ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
    exact (abs_sub x y).trans (by linarith)
  exact ⟨hH, hL, hwidth⟩

/-! ### The evolution and the product -/

/-- The derivative of `e^{-iuZ}` in `u` is `-iZ e^{-iuZ}`. -/
theorem hasDerivAt_E (u : ℝ) : HasDerivAt E ((-I • Z) * E u) u :=
  hasDerivAt_exp_smul_const' (𝕂 := ℝ) _ _

/-- `U(t) = e^{-i t³/(3T²) Z}` satisfies `iU'(t) = H(t/T) U(t)`. -/
theorem hasDerivAt_evolution {T : ℝ} (hT : T ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ E (t ^ 3 / (3 * T ^ 2)))
      (-I • (H (t / T) * E (t ^ 3 / (3 * T ^ 2)))) t := by
  have hφ : HasDerivAt (fun t : ℝ ↦ t ^ 3 / (3 * T ^ 2)) ((t / T) ^ 2) t := by
    convert (hasDerivAt_pow 3 t).div_const (3 * T ^ 2) using 1
    field_simp
    ring
  convert (hasDerivAt_E (t ^ 3 / (3 * T ^ 2))).scomp t hφ using 1
  rw [H, smul_mul_assoc, smul_mul_assoc, smul_comm]

/-- The integral `∫_0^T H(t/T) dt = TZ/3`. -/
theorem integral_H (T : ℝ) (hT : 0 < T) :
    (∫ t in 0..T, H (t / T)) = (T / 3) • Z := by
  simp_rw [H, div_pow]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_div,
    integral_pow]
  congr 1
  simp only [Nat.reduceAdd, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    sub_zero]
  field_simp
  all_goals ring

/-- Assuming Dieudonné (10.5.4) and (10.6.3) with the remark (10.4.6),
`U(T) = exp(-i∫_0^T H(t/T) dt)`, as the values `H(s)` commute: `t ↦ e^{-i t³/(3T²) Z}` satisfies
`iU'(t) = H(t/T) U(t)` and `U(0) = 1`, the family `H(t/T)` generates exactly one evolution, and
`∫_0^T H(t/T) dt = TZ/3`. -/
theorem evolution_end (dieudonne_10_5_4 : Dieudonne_10_5_4)
    (dieudonne_10_6_3 : Dieudonne_10_6_3)
    (T : ℕ) (hT : 1 ≤ T) :
    evolution H T T = exp (-I • (∫ t in 0..(T : ℝ), H (t / T))) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let G : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t ↦ H (t / T)
  let U : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t ↦ E (t ^ 3 / (3 * (T : ℝ) ^ 2))
  have hGc : Continuous G := by
    dsimp [G, H]
    fun_prop
  have hreg : IsRegulated G 0 T := ContinuousOn.isRegulated hGc.continuousOn
  have hG : IsHermitianFamily G 0 T := fun t _ ↦ H_isHermitian _
  have hU : Generates G U 0 T := by
    refine ⟨?_, ?_, ?_, ∅, countable_empty, ?_⟩
    · exact fun t _ ↦
        (hasDerivAt_evolution hTr.ne' t).continuousAt.continuousWithinAt
    · simp [U, E]
    · exact fun t _ ↦ by
        simpa only [U, E, Complex.coe_smul] using
          exp_neg_I_smul_isUnitary Z_isHermitian (t ^ 3 / (3 * (T : ℝ) ^ 2))
    · exact fun t _ _ ↦ (hasDerivAt_evolution hTr.ne' t).hasDerivWithinAt
  have hcanon : Generates G (evolutionOf G T) 0 T :=
    generates_evolutionOf dieudonne_10_5_4 dieudonne_10_6_3
      hTr.le hreg hG
  have heq := generates_unique dieudonne_10_5_4 hreg hcanon hU
  have hphase : (T : ℝ) ^ 3 / (3 * (T : ℝ) ^ 2) = (T : ℝ) / 3 := by
    field_simp
  have hexp : exp (-I • (∫ t in 0..(T : ℝ), H (t / T))) = E ((T : ℝ) / 3) := by
    rw [integral_H (T : ℝ) hTr, E, smul_comm]
  change evolutionOf G T T = _
  rw [heq ⟨hTr.le, le_rfl⟩]
  dsimp [U]
  rw [hphase, hexp]

/-- The factors commute: `e^{-if(n-1)Z} ⋯ e^{-if(0)Z} = e^{-i(Σ_{j<n} f(j))Z}`. -/
theorem prod_E (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).reverse.map fun j ↦ E (f j)).prod =
      E (∑ j ∈ Finset.range n, f j) := by
  induction n with
  | zero => simp [E]
  | succ n ih =>
      rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append,
        List.map_reverse, List.map_singleton, List.reverse_singleton, List.prod_singleton, ih,
        Finset.sum_range_succ, add_comm, E_add]

/-- The left-endpoint sum `Σ_{j=0}^{T-1} (j/T)² = (T-1)(2T-1)/(6T)`. -/
theorem left_sum (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      ((T : ℝ) - 1) * (2 * T - 1) / (6 * T) := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have h6 : ∀ n : ℕ, 6 * ∑ j ∈ Finset.range n, (j : ℝ) ^ 2 =
      ((n : ℝ) - 1) * n * (2 * n - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        push_cast
        ring
  have hsum' : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (∑ j ∈ Finset.range T, (j : ℝ) ^ 2) / T ^ 2 := by
    simp [div_pow, Finset.sum_div]
  rw [hsum', show ∑ j ∈ Finset.range T, (j : ℝ) ^ 2 =
    ((T : ℝ) - 1) * T * (2 * T - 1) / 6 by linarith [h6 T]]
  have h6T2 : (6 : ℝ) * (T : ℝ) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hTr.ne')
  have h6T : (6 : ℝ) * T ≠ 0 := mul_ne_zero (by norm_num) hTr.ne'
  rw [div_div, div_eq_div_iff h6T2 h6T]
  ring

/-- The `T`-step product is the exponential of `-i` times the left-endpoint sum:
`W_T = e^{-i(T/3 - 1/2 + 1/(6T))Z}`. -/
theorem sharp_stepProduct (T : ℕ)
    (hsum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) :
    stepProduct H T = E ((T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) := by
  unfold stepProduct sampleProduct orderedProduct
  have hfactor (j : ℕ) : exp (-I • H (j / T)) =
      E (((j : ℝ) / T) ^ 2) := by
    simp only [H, E]
    congr 1
    exact smul_comm _ _ _
  simp_rw [hfactor]
  rw [prod_E, hsum]

/-! ### The norms -/

/-- `‖e^{-iuZ} - e^{-ivZ}‖ = ‖e^{-i(u-v)Z} - 1‖`: for unitaries `A` and `B`,
`‖A - B‖ = ‖AB† - 1‖`. -/
theorem norm_reduction (u v : ℝ) : ‖E u - E v‖ = ‖E (u - v) - 1‖ := by
  have hv : IsUnitary (E v) := by
    simpa only [E, Complex.coe_smul] using
      exp_neg_I_smul_isUnitary Z_isHermitian v
  rw [norm_sub_eq_norm_star_mul_sub_one hv (E u)]
  have hstar : (E v)† = E (-v) := by
    simp [E, NormedSpace.star_exp, star_smul, Z_isHermitian.isSelfAdjoint.star_eq,
      Complex.conj_I, neg_smul, smul_neg]
  rw [hstar, ← E_add]
  congr 2
  ring

/-- `‖e^{-iuZ} - 1‖ = 2|sin(u/2)|`, as `Z` has eigenvalues `±1`. -/
theorem norm_phase (u : ℝ) : ‖E u - 1‖ = 2 * |Real.sin (u / 2)| := by
  -- `e^{-iuZ}` is diagonal with entries `e^{-iu}` and `e^{iu}`.
  have hdiag : E u = Matrix.diagonal (fun i ↦
      Complex.exp ((u : ℂ) * (-I * ![(1 : ℂ), -1] i))) := by
    rw [E, Z, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul,
      Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (fun _ ↦ 1) :=
    Matrix.diagonal_one.symm
  -- `|e^{ix} - 1| = 2|sin(x/2)|` for real `x`.
  have hscalar (x : ℝ) : ‖Complex.exp (I * x) - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_two]
  have hentry : ∀ i : Fin 2,
      ‖Complex.exp ((u : ℂ) * (-I * ![(1 : ℂ), -1] i)) - 1‖ = 2 * |Real.sin (u / 2)| := by
    intro i
    fin_cases i
    · have h := hscalar (-u)
      rw [show -u / 2 = -(u / 2) by ring, Real.sin_neg, abs_neg] at h
      convert h using 1
      push_cast
      ring_nf
    · convert hscalar u using 1
      push_cast
      ring_nf
  rw [hdiag, hone, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ (hentry i).le) ?_
  exact (hentry 0).symm.le.trans (norm_le_pi_norm (fun i : Fin 2 ↦
    Complex.exp ((u : ℂ) * (-I * ![(1 : ℂ), -1] i)) - 1) 0)

/-! ### The asymptotic form and the limit -/

/-- Example 4.3(i): `2 sin(1/(12T))` is asymptotic to `1/(6T)`. -/
theorem asymptotic : (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * (N : ℝ)))) ~[atTop]
    (fun N : ℕ ↦ 1 / (6 * (N : ℝ))) := by
  have hinv : Tendsto (fun N : ℕ ↦ 1 / (12 * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)
  have h := (Asymptotics.IsEquivalent.refl (u := fun _ : ℕ ↦ (2 : ℝ)) (l := atTop)).mul
    (Real.isEquivalent_sin.comp_tendsto hinv)
  refine h.congr_right (Eventually.of_forall fun N ↦ ?_)
  simp only [Pi.mul_apply, Function.comp_apply, id]
  ring

/-- Example 4.3(ii): `2 sin(1/4 - 1/(12T))` has limit `2 sin(1/4)`. -/
theorem limit : Tendsto
    (fun N : ℕ ↦ 2 * Real.sin (1 / 4 - 1 / (12 * (N : ℝ)))) atTop
    (𝓝 (2 * Real.sin (1 / 4))) := by
  have hinv : Tendsto (fun N : ℕ ↦ 1 / (12 * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)
  have harg : Tendsto (fun N : ℕ ↦ 1 / 4 - 1 / (12 * (N : ℝ))) atTop
      (𝓝 (1 / 4)) := by
    simpa using tendsto_const_nhds.sub hinv
  exact ((Real.continuous_sin.tendsto _).comp harg).const_mul 2

end RoundedClocks.UnitSharp
