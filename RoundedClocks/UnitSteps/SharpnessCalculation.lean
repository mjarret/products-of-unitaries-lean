/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.UnitSteps.SharpnessEvolution

/-! # Sharpness calculation for unit steps

Example 4.3 evaluates the alternating two-level product and its continuous evolution to obtain the
sharp asymptotic error.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real Asymptotics
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks.UnitSharp

/-- Constant-Hamiltonian evolutions add their elapsed times. -/
theorem E_add (u v : ℝ) : E (u + v) = E u * E v := by
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  rw [E, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left _).smul_right _)

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

/-- The one-sided derivative used by the paper is also `2sZ`. -/
theorem deriv01_H {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∂H s = (2 * s) • Z :=
  (hasDerivAt_H s).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one s hs)

/-- Products of the commuting factors `e^{-if(j)Z}` add their phases. -/
theorem prod_E (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).reverse.map fun j ↦ E (f j)).prod =
      E (∑ j ∈ Finset.range n, f j) := by
  induction n with
  | zero => simp [E]
  | succ n ih =>
      rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append,
        List.map_reverse, List.map_singleton, List.reverse_singleton, List.prod_singleton, ih,
        Finset.sum_range_succ, add_comm, E_add]

/-- The left-endpoint sum of squares is the manuscript's quadrature coefficient. -/
theorem left_sum (T : ℕ) (hT : 1 ≤ T) :
    ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (T : ℝ) / 3 - 1 / 2 + 1 / (6 * T) := by
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
  field_simp
  ring

/-- The `T`-step product has the left-endpoint phase in the manuscript. -/
theorem sharp_stepProduct (T : ℕ)
    (hsum : ∑ j ∈ Finset.range T, ((j : ℝ) / T) ^ 2 =
      (T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) :
    stepProduct H T = E ((T : ℝ) / 3 - 1 / 2 + 1 / (6 * T)) := by
  unfold stepProduct sampleProduct
  have hfactor (j : ℕ) : exp (-I • H (j / T)) =
      E (((j : ℝ) / T) ^ 2) := by
    simp only [H, E]
    congr 1
    exact smul_comm _ _ _
  simp_rw [hfactor]
  rw [prod_E, hsum]

/-- The operator-norm distance between two phases of `Z`. -/
theorem norm_E_sub (u v : ℝ) :
    ‖E u - E v‖ = 2 * |Real.sin ((u - v) / 2)| := by
  have evol_diagonal (x : ℝ) : E x = Matrix.diagonal (fun i ↦
      Complex.exp ((x : ℂ) * (-I * ![(1 : ℂ), -1] i))) := by
    rw [E, Z, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul,
      Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, Complex.real_smul]
  have phase_dist (x y : ℝ) :
      ‖Complex.exp (I * x) - Complex.exp (I * y)‖ = 2 * |Real.sin ((x - y) / 2)| := by
    have h : Complex.exp (I * x) - Complex.exp (I * y) =
        Complex.exp (I * y) * (Complex.exp (I * (x - y)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
      ← Complex.ofReal_sub, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_two]
  rw [evol_diagonal, evol_diagonal, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  have hentry : ∀ i : Fin 2,
      ‖Complex.exp ((u : ℂ) * (-I * ![(1 : ℂ), -1] i)) -
          Complex.exp ((v : ℂ) * (-I * ![(1 : ℂ), -1] i))‖ =
        2 * |Real.sin ((u - v) / 2)| := by
    intro i
    fin_cases i
    · have h := phase_dist (-u) (-v)
      convert h using 1
      · push_cast
        ring_nf
      · rw [show (-u - -v) / 2 = -((u - v) / 2) by ring, Real.sin_neg, abs_neg]
    · convert phase_dist u v using 1
      push_cast
      ring_nf
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ (hentry i).le) ?_
  exact (hentry 0).symm.le.trans (norm_le_pi_norm (fun i : Fin 2 ↦
    Complex.exp ((u : ℂ) * (-I * ![(1 : ℂ), -1] i)) -
      Complex.exp ((v : ℂ) * (-I * ![(1 : ℂ), -1] i))) 0)

/-- The Hamiltonian, derivative and sample-width hypotheses of Example 4.3. -/
theorem regularity (T : ℕ) (hT : 1 ≤ T) :
    IsTimeDepHamiltonian H ∧ HasLipschitzDerivative H 2 ∧ HasSampleWidth H T 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hH : IsTimeDepHamiltonian H := fun s _ ↦ H_isHermitian s
  have hL : HasLipschitzDerivative H 2 := by
    refine ⟨fun s _ ↦
      (hasDerivAt_H s).differentiableAt.differentiableWithinAt, ?_⟩
    intro s₁ hs₁ s₂ hs₂
    rw [deriv01_H hs₁, deriv01_H hs₂, ← sub_smul,
      norm_smul, norm_Z, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_two]
  have hwidth : HasSampleWidth H T 2 := by
    intro j hj x hx y hy
    have hs : (j : ℝ) / T ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one hTr).2 (by exact_mod_cast hj)
    have hxnorm := spectrum.norm_le_norm_of_mem hx
    have hynorm := spectrum.norm_le_norm_of_mem hy
    rw [Real.norm_eq_abs, norm_H] at hxnorm hynorm
    have hsq : ((j : ℝ) / T) ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
    exact (abs_sub x y).trans (by linarith)
  exact ⟨hH, hL, hwidth⟩

/-- The asymptotic scalar assertion in Example 4.3. -/
theorem asymptotic : (fun N : ℕ ↦ 2 * Real.sin (1 / (12 * (N : ℝ)))) ~[atTop]
    (fun N : ℕ ↦ 1 / (6 * (N : ℝ))) := by
  have hinv : Tendsto (fun N : ℕ ↦ 1 / (12 * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)
  have hsinc : Tendsto (fun N : ℕ ↦ Real.sinc (1 / (12 * (N : ℝ))))
      atTop (𝓝 1) := by
    simpa only [Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hinv
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact_mod_cast hN
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).2
  · exact hsinc.congr' (by
      filter_upwards [hpos] with N hN
      rw [Real.sinc_of_ne_zero (by positivity)]
      dsimp
      field_simp
      ring)
  · filter_upwards [hpos] with N hN
    positivity

/-- The limit scalar assertion in Example 4.3. -/
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

/-- Right multiplication by the inverse unitary reduces the distance to the identity. -/
theorem norm_reduction (u v : ℝ) : ‖E u - E v‖ = ‖E (u - v) - 1‖ := by
  have hmem := Matrix.mem_unitaryGroup_iff'.mpr (E_isUnitary (-v))
  calc
    _ = ‖(E u - E v) * E (-v)‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ hmem]
    _ = ‖E (u - v) - 1‖ := by
      rw [sub_mul, ← E_add, ← E_add]
      simp [sub_eq_add_neg, E]

/-- The two diagonal entries give the sine formula for a single phase. -/
theorem norm_phase (u : ℝ) : ‖E u - 1‖ = 2 * |Real.sin (u / 2)| := by
  simpa [E] using norm_E_sub u 0

end RoundedClocks.UnitSharp
