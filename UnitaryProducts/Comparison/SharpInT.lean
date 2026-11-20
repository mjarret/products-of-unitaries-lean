/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.LogarithmDerivativeBounds
public import UnitaryProducts.Approximation.EntryRounding

/-!
# The unit-step comparison is sharp in `T`

## Declarations

- `sharpFamily`
- `sharpFamily_hypotheses`
- `sum_sq_div_eq`
- `derivWithin_sharpFamily`
- `localSteps_evol_smul_sharp`
- `localSteps_hasDerivAt_sharpEvolution`
- `hasDerivAt_sharpFamily`
- `localSteps_isHermitian_sharpFamily`
- `localSteps_isHermitian_sharpZ`
- `norm_sharpFamily`
- `norm_sharpZ`
- `localSteps_pieceProduct_sharpFamily`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real Matrix

noncomputable section

namespace UnitaryProducts.Paper

/-- The commuting family $H(s)=s^2Z$ with $Z=\mathrm{diag}(1,-1)$, a real multiple of one fixed
Hermitian matrix with eigenvalues $\pm1$. -/
def sharpFamily (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := s ^ 2 • Matrix.diagonal ![1, -1]

end UnitaryProducts.Paper

namespace UnitaryProducts.Prose
open UnitaryProducts.Paper

/-- Section 4.2: the fixed diagonal matrix is Hermitian. -/
theorem localSteps_isHermitian_sharpZ : (Matrix.diagonal ![(1 : ℂ), -1]).IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; fin_cases i <;> simp)

/-- Section 4.2: real scaling of the exponential phase. -/
theorem localSteps_evol_smul_sharp {d : ℕ} (c : ℝ) (G : Matrix (Fin d) (Fin d) ℂ) (u : ℝ) :
    UnitaryProducts.evol (c • G) u = UnitaryProducts.evol G (u * c) := by
  rw [UnitaryProducts.evol, UnitaryProducts.evol, smul_comm (-I) c G, smul_smul]

/-- Section 4.2: the quadratic example is Hermitian. -/
theorem localSteps_isHermitian_sharpFamily (s : ℝ) : (sharpFamily s).IsHermitian := by
  unfold sharpFamily
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, localSteps_isHermitian_sharpZ.eq]

/-- Section 4.2: derivative of the explicit quadratic-family evolution. -/
theorem localSteps_hasDerivAt_sharpEvolution {T : ℝ} (hT : T ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ UnitaryProducts.evol (Matrix.diagonal ![(1 : ℂ), -1]) (t ^ 3 / (3 * T ^ 2)))
      (-I • (sharpFamily (t / T) *
        UnitaryProducts.evol (Matrix.diagonal ![(1 : ℂ), -1]) (t ^ 3 / (3 * T ^ 2)))) t := by
  have hφ : HasDerivAt (fun t : ℝ ↦ t ^ 3 / (3 * T ^ 2)) ((t / T) ^ 2) t := by
    convert (hasDerivAt_pow 3 t).div_const (3 * T ^ 2) using 1
    field_simp
    ring
  convert (UnitaryProducts.hasDerivAt_evol (Matrix.diagonal ![(1 : ℂ), -1])
    (t ^ 3 / (3 * T ^ 2))).scomp t hφ using 1
  rw [sharpFamily, smul_mul_assoc, smul_mul_assoc, smul_comm]

/-- Section 4.2: the commuting sample product is the exponential of the sum. -/
theorem localSteps_pieceProduct_sharpFamily (T : ℝ) (N n : ℕ) :
    UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ (T / N) • sharpFamily (j / N)) n =
      UnitaryProducts.evol (Matrix.diagonal ![(1 : ℂ), -1])
        (∑ j ∈ Finset.range n, T / N * ((j : ℝ) / N) ^ 2) := by
  induction n with
  | zero => simp [UnitaryProducts.pieceProduct, UnitaryProducts.evol_zero]
  | succ n ih =>
    rw [UnitaryProducts.pieceProduct, ih, Finset.sum_range_succ, add_comm,
      UnitaryProducts.evol_add, sharpFamily, smul_smul, localSteps_evol_smul_sharp, one_mul]

end UnitaryProducts.Prose

namespace UnitaryProducts.Paper
open UnitaryProducts.Prose

/-- The sum of squares $\sum_{j<N}(j/N)^2=N/3-1/2+1/(6N)$: the trapezoid rule on $N$ steps
overestimates $\int_0^1s^2\,ds=1/3$ by exactly $1/(6N^2)$.

The proof is induction for $6\sum_{j<n}j^2=(n-1)n(2n-1)$, then division by $N^2$. -/
theorem sum_sq_div_eq {N : ℕ} (hN : 0 < N) :
    ∑ j ∈ Finset.range N, ((j : ℝ) / N) ^ 2 = N / 3 - 1 / 2 + 1 / (6 * N) := by
  have h6 : ∀ n : ℕ, 6 * ∑ j ∈ Finset.range n, (j : ℝ) ^ 2 = (n - 1) * n * (2 * n - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsum : ∑ j ∈ Finset.range N, ((j : ℝ) / N) ^ 2 =
      (∑ j ∈ Finset.range N, (j : ℝ) ^ 2) / N ^ 2 := by
    simp [div_pow, Finset.sum_div]
  rw [hsum, show ∑ j ∈ Finset.range N, (j : ℝ) ^ 2 = ((N : ℝ) - 1) * N * (2 * N - 1) / 6 by
    linarith [h6 N]]
  field_simp
  ring

/-- $\|Z\|=1$. -/
private theorem norm_sharpZ : ‖Matrix.diagonal ![(1 : ℂ), -1]‖ = 1 := by
  rw [Matrix.l2_opNorm_diagonal]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_) ?_
  · fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![(1 : ℂ), -1] : Fin 2 → ℂ) 0

/-- $\|H(s)\|=s^2$. -/
private theorem norm_sharpFamily (s : ℝ) : ‖sharpFamily s‖ = s ^ 2 := by
  rw [sharpFamily, norm_smul, norm_sharpZ, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

/-- $H'(s)=2sZ$. -/
private theorem hasDerivAt_sharpFamily (s : ℝ) :
    HasDerivAt sharpFamily ((2 * s) • Matrix.diagonal ![(1 : ℂ), -1]) s := by
  simpa using (hasDerivAt_pow 2 s).smul_const (Matrix.diagonal ![(1 : ℂ), -1])

private theorem derivWithin_sharpFamily {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    derivWithin sharpFamily (Icc (0 : ℝ) 1) s = (2 * s) • Matrix.diagonal ![(1 : ℂ), -1] :=
  (hasDerivAt_sharpFamily s).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one s hs)

/-- Example 4.3: the derivative norm of the quadratic diagonal path has
supremum exactly two, attained at the right endpoint. -/
theorem sharpFamily_derivative_supNorm :
    unitSupNorm (derivWithin sharpFamily (Icc (0 : ℝ) 1)) = 2 := by
  have hnorm (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖derivWithin sharpFamily (Icc (0 : ℝ) 1) s‖ = 2 * s := by
    rw [derivWithin_sharpFamily hs, norm_smul, norm_sharpZ, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs.1)]
  apply le_antisymm
  · exact csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
      (forall_mem_image.mpr fun s hs ↦ (hnorm s hs).trans_le (by linarith [hs.2]))
  · have hmem : (2 : ℝ) ∈ (fun s ↦ ‖derivWithin sharpFamily (Icc (0 : ℝ) 1) s‖) ''
        Icc (0 : ℝ) 1 := ⟨1, by norm_num, by simpa only [mul_one] using hnorm 1 (by norm_num)⟩
    exact le_csSup ⟨2, forall_mem_image.mpr fun s hs ↦
      (hnorm s hs).trans_le (by linarith [hs.2])⟩ hmem

/-- Supports the claim after Theorem 4.2 that the family $H(s)=s^2Z$, $Z=\mathrm{diag}(1,-1)$,
meets the hypotheses of Theorem 4.2: Hermitian, $C^1$ on $[0,1]$, $H'$ Lipschitz with $M=2$, at most
$2$ in norm ($L\le2$), samples with eigenvalue differences of modulus at most $2$ (so
$(T/N)H(j/N)$ has width at most $2T/N$, which is $2<2\pi$ at unit steps), and an evolution
$U$ generated by $H(t/T)$ on $[0,T]$.

Reading the statement against the paper:
* The clauses are the hypotheses `hH`, `hc`, `hlip` (with `M = 2`), and `hdiff` (with
  `w = 2 * T / N`) of `unit_step_comparison_of_lipschitz_derivative`, stated for every Hermitian
  proof `hj`, so they apply to the proof term used there.
* The last clause is the existence of `U`, so the hypothesis `hU` can be met.

The proof computes $H'(s)=2sZ$ and bounds each eigenvalue by the norm $s^2\|Z\|=s^2\le1$; the
evolution is $U(t)=e^{-i(t^3/(3T^2))Z}$. -/
theorem sharpFamily_hypotheses {T : ℝ} (hT : 0 < T) {N : ℕ} :
    (∀ s ∈ Icc (0 : ℝ) 1, (sharpFamily s).IsHermitian) ∧
    ContDiffOn ℝ 1 sharpFamily (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin sharpFamily (Icc (0 : ℝ) 1) t - derivWithin sharpFamily (Icc (0 : ℝ) 1) s‖ ≤
        2 * |t - s|) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ‖derivWithin sharpFamily (Icc (0 : ℝ) 1) s‖ ≤ 2) ∧
    (∀ j : ℕ, j ≤ N → ∀ hj : (sharpFamily (j / N)).IsHermitian, ∀ p q,
      (T / N) * |hj.eigenvalues p - hj.eigenvalues q| ≤ 2 * T / N) ∧
    ∃ U : ℝ → Matrix (Fin 2) (Fin 2) ℂ, IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T := by
  refine ⟨fun s _ ↦ localSteps_isHermitian_sharpFamily s, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((contDiff_id.pow 2).smul contDiff_const).contDiffOn
  · intro s hs t ht
    rw [derivWithin_sharpFamily ht, derivWithin_sharpFamily hs, ← sub_smul, norm_smul,
      norm_sharpZ, mul_one, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_two]
  · intro s hs
    rw [derivWithin_sharpFamily hs, norm_smul, norm_sharpZ, mul_one, Real.norm_eq_abs, abs_mul,
      abs_two, abs_of_nonneg hs.1]
    linarith [hs.2]
  · intro j hjN hj p q
    have hsq : ((j : ℝ) / N) ^ 2 ≤ 1 :=
      pow_le_one₀ (walkCubic_sample hjN).1 (walkCubic_sample hjN).2
    have heig : ∀ i, |hj.eigenvalues i| ≤ 1 := by
      intro i
      have hm := spectrum.norm_le_norm_of_mem (hj.eigenvalues_mem_spectrum_real i)
      rw [Real.norm_eq_abs] at hm
      exact (hm.trans_eq (norm_sharpFamily _)).trans hsq
    have hdiff : |hj.eigenvalues p - hj.eigenvalues q| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [heig p, heig q])
    exact (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_eq (by ring)
  · refine ⟨fun t ↦ UnitaryProducts.evol (Matrix.diagonal ![(1 : ℂ), -1]) (t ^ 3 / (3 * T ^ 2)),
      ?_, ?_, ?_, ∅, countable_empty, ?_⟩
    · exact fun t _ ↦
        (localSteps_hasDerivAt_sharpEvolution hT.ne' t).continuousAt.continuousWithinAt
    · simp [UnitaryProducts.evol_zero]
    · exact fun t _ ↦ UnitaryProducts.star_evol_mul_self localSteps_isHermitian_sharpZ _
    · exact fun t _ _ ↦ (localSteps_hasDerivAt_sharpEvolution hT.ne' t).hasDerivWithinAt

end UnitaryProducts.Paper
