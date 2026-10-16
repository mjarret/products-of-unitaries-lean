/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Walks.FrameSums
public import UnitaryProducts.Walks.LogHessian

/-!
# Block split for the walk corrector

## Declarations

- `analyticOnNhd_cubic_frameSeries`
- `cubicFrameSeriesDerivative`
- `cubicPowDerivative`
- `hasDerivAt_cubic_frameSeries_comp`
- `hasDerivAt_cubic_frameSeries_line`
- `norm_cubicFrameSeriesDerivative_term_le`
- `norm_cubicPowDerivative_le`
- `summable_norm_cubicFrameSeriesDerivative`
- `cubicDiag`
- `cubicDiagL`
- `cubicDiagL_apply`
- `cubicDiag_add_cubicOff`
- `cubicDiag_bernSeries`
- `cubicDiag_commute`
- `cubicFrameSeriesDerivative_apply`
- `cubicOff`
- `cubicOff_anticommute`
- `cubicPowDerivative_apply`
- `cubicSlopePair`
- `cubic_adL_shift_eq`
- `cubic_anticommute_I_adL_pow`
- `cubic_anticommute_adL`
- `cubic_bernSeries_shift_eq`
- `cubic_commute_I_adL_pow`
- `cubic_commute_adL`
- `cubic_commute_adL_of_anticommute`
- `cubic_commute_mul_of_anticommute`
- `cubic_frameLip_zero`
- `cubic_geometric_sum_le`
- `cubic_geometric_sum_reverse_le`
- `cubic_narrow_pow_le`
- `cubic_norm_commutator_le`
- `cubic_norm_pow_apply_le`
- `exists_cubic_spectral_split`
- `hasDerivAt_cubic_frameOp`
- `norm_adL_cubicDiag_le`
- `norm_cubicDiag_bernSeries_le`
- `norm_cubicDiag_bernSeries_le_block`
- `norm_cubicDiag_le`
- `norm_cubicOff_le`
- `norm_cubicSlopePair_off_off`
- `norm_cubic_conj_le`
- `summable_norm_cubicFrameSlope_terms`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real Complex UnitaryProducts.Corrector

noncomputable section

namespace UnitaryProducts

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The block-diagonal part $(X + JXJ)/2$ of $X$ for an involution $J$; for $X = \Lambda'$ it is the
paper's $B$ in the proof of the spectral comparison. The lemmas assume $J^2 = 1$. -/
def cubicDiag (J X : 𝕄) : 𝕄 := (1 / 2 : ℂ) • (X + J * X * J)

/-- The off-diagonal part $(X - JXJ)/2$ of $X$ for an involution $J$ (the paper's $E$ for
$X = \Lambda'$). -/
def cubicOff (J X : 𝕄) : 𝕄 := (1 / 2 : ℂ) • (X - J * X * J)

/-- The two parts add up to $X$. -/
theorem cubicDiag_add_cubicOff (J X : 𝕄) : cubicDiag J X + cubicOff J X = X := by
  rw [cubicDiag, cubicOff]
  module

/-- $\|JXJ\| \le \|X\|$ for $\|J\| \le 1$. -/
theorem norm_cubic_conj_le (J X : 𝕄) (hJ : ‖J‖ ≤ 1) : ‖J * X * J‖ ≤ ‖X‖ := by
  calc
    ‖J * X * J‖ ≤ ‖J‖ * ‖X‖ * ‖J‖ := norm_mul₃_le
    _ ≤ 1 * ‖X‖ * 1 := by gcongr
    _ = ‖X‖ := by ring

/-- The block-diagonal part has norm at most $\|X\|$. -/
theorem norm_cubicDiag_le (J X : 𝕄) (hJ : ‖J‖ ≤ 1) : ‖cubicDiag J X‖ ≤ ‖X‖ := by
  rw [cubicDiag, norm_smul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  linarith [norm_add_le X (J * X * J), norm_cubic_conj_le J X hJ]

/-- The off-diagonal part has norm at most $\|X\|$. -/
theorem norm_cubicOff_le (J X : 𝕄) (hJ : ‖J‖ ≤ 1) : ‖cubicOff J X‖ ≤ ‖X‖ := by
  rw [cubicOff, norm_smul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  linarith [norm_sub_le X (J * X * J), norm_cubic_conj_le J X hJ]

/-- The block-diagonal part commutes with $J$. -/
theorem cubicDiag_commute (J X : 𝕄) (hJ : J * J = 1) :
    J * cubicDiag J X = cubicDiag J X * J := by
  have hleft : J * (J * X * J) = X * J := by rw [← mul_assoc, ← mul_assoc, hJ, one_mul]
  have hright : J * X * J * J = J * X := by rw [mul_assoc (J * X), hJ, mul_one]
  simp only [cubicDiag, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, hleft, hright, add_comm]

/-- The off-diagonal part anticommutes with $J$. -/
theorem cubicOff_anticommute (J X : 𝕄) (hJ : J * J = 1) :
    J * cubicOff J X = -(cubicOff J X * J) := by
  have hleft : J * (J * X * J) = X * J := by rw [← mul_assoc, ← mul_assoc, hJ, one_mul]
  have hright : J * X * J * J = J * X := by rw [mul_assoc (J * X), hJ, mul_one]
  simp only [cubicOff, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, ← smul_neg, hleft, hright,
    neg_sub]

/-- The block split in the proof of the spectral comparison: for $h$ Hermitian with spectrum in
$[m, m + w]$, the
involution $J$ that is $-1$ on the eigenvectors of eigenvalues at most $m + w/2$ and $+1$ on the
others commutes with $h$, and $\|h - (m + w/2) - (w/4)J\| \le w/4$. -/
theorem exists_cubic_spectral_split {h : 𝕄} (hh : h.IsHermitian)
    {m w : ℝ} (hw : 0 ≤ w)
    (hev : ∀ i, hh.eigenvalues i ∈ Set.Icc m (m + w)) :
    ∃ J : 𝕄, J * J = 1 ∧ J.IsHermitian ∧ ‖J‖ ≤ 1 ∧
      Commute J h ∧
      ‖h - ((m + w / 2 : ℝ) : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4 := by
  let σ : Fin d → ℂ := fun i ↦ if hh.eigenvalues i ≤ m + w / 2 then -1 else 1
  let J₀ : 𝕄 := Matrix.diagonal σ
  let A : 𝕄 := Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues)
  let e : 𝕄 ≃⋆ₐ[ℂ] 𝕄 := Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary
  have hs : e A = h := hh.spectral_theorem.symm
  have henorm (X : 𝕄) : ‖e X‖ = ‖X‖ := by
    change ‖(hh.eigenvectorUnitary : 𝕄) * X * star (hh.eigenvectorUnitary : 𝕄)‖ = ‖X‖
    rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hh.eigenvectorUnitary.prop),
      CStarRing.norm_coe_unitary_mul]
  have hσ (i : Fin d) : σ i = -1 ∨ σ i = 1 := by dsimp [σ]; split_ifs <;> simp
  have hJ₀ : J₀ * J₀ = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; rcases hσ i with hi | hi <;> simp [hi]
    · simp [hij]
  have hsa : J₀.IsHermitian := Matrix.isHermitian_diagonal_iff.mpr fun i ↦ by
    rcases hσ i with hi | hi <;> simp [hi, IsSelfAdjoint]
  have hnorm : ‖J₀‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ by
      rcases hσ i with hi | hi <;> simp [hi]
  have hcomm : Commute J₀ A := by
    change J₀ * A = A * J₀
    simp only [J₀, A, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact mul_comm _ _
  refine ⟨e J₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hJ₀, map_one]
  · rw [Matrix.isHermitian_iff_isSelfAdjoint] at hsa ⊢
    change star (e J₀) = e J₀
    rw [← map_star, hsa]
  · rw [henorm]; exact hnorm
  · rw [← hs]; exact hcomm.map e
  · rw [← hs, ← map_one e, ← map_smul, ← map_sub, ← map_smul, ← map_sub,
      henorm]
    have hid : A - ((m + w / 2 : ℝ) : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J₀ =
        Matrix.diagonal (fun i ↦
          (hh.eigenvalues i : ℂ) - ((m + w / 2 : ℝ) : ℂ) - ((w / 4 : ℝ) : ℂ) * σ i) := by
      ext i j
      by_cases hij : i = j <;> simp [A, J₀, hij]
    rw [hid, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ w / 4)).mpr
    intro i
    have hi := hev i
    by_cases hmid : hh.eigenvalues i ≤ m + w / 2
    · have hσi : σ i = -1 := if_pos hmid
      rw [hσi]
      have heq : (hh.eigenvalues i : ℂ) - ((m + w / 2 : ℝ) : ℂ) -
          ((w / 4 : ℝ) : ℂ) * (-1) = ((hh.eigenvalues i - (m + w / 4) : ℝ) : ℂ) := by
        push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hi.1, hi.2]
    · have hσi : σ i = 1 := if_neg hmid
      rw [hσi]
      have heq : (hh.eigenvalues i : ℂ) - ((m + w / 2 : ℝ) : ℂ) -
          ((w / 4 : ℝ) : ℂ) * 1 = ((hh.eigenvalues i - (m + 3 * w / 4) : ℝ) : ℂ) := by
        push_cast; ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hi.1, hi.2]

/-- On block-diagonal $X$, $\mathrm{ad}_h X = \mathrm{ad}_{h - c - rJ}X$. -/
theorem cubic_adL_shift_eq {h J X : 𝕄} {c r : ℝ} (hX : Commute J X) :
    adL h X = adL (h - (c : ℂ) • 1 - (r : ℂ) • J) X := by
  simp only [adL_apply, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  rw [hX.eq]
  abel

/-- The narrow commutator estimate on the diagonal blocks. -/
theorem norm_adL_cubicDiag_le {h J X : 𝕄} {c r : ℝ}
    (hX : Commute J X)
    (hsmall : ‖h - (c : ℂ) • 1 - (r : ℂ) • J‖ ≤ r) :
    ‖adL h X‖ ≤ 2 * r * ‖X‖ := by
  rw [cubic_adL_shift_eq (c := c) (r := r) hX]
  have hb := norm_adL_apply_le (h - (c : ℂ) • 1 - (r : ℂ) • J) X 0
  simp only [zero_smul, sub_zero] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsmall (by norm_num)) (norm_nonneg _))

/-- $\mathrm{ad}_h$ preserves block-diagonal matrices when $J$ commutes with $h$. -/
theorem cubic_commute_adL {h J X : 𝕄} (hh : Commute J h) (hX : Commute J X) :
    Commute J (adL h X) := by
  rw [adL_apply]
  exact (hh.mul_right hX).sub_right (hX.mul_right hh)

/-- Diagonal compression as a continuous linear map. -/
def cubicDiagL (J : 𝕄) : 𝕄 →L[ℂ] 𝕄 :=
  (1 / 2 : ℂ) • (1 + mulL J * mulR J)

/-- `cubicDiagL J` is `cubicDiag J`. -/
theorem cubicDiagL_apply (J X : 𝕄) : cubicDiagL J X = cubicDiag J X := by
  simp only [cubicDiagL, cubicDiag, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply, mulL_apply, mulR_apply, mul_assoc]

/-- The compression to the block diagonal commutes with the inverse averaging operator
`bernSeries (I • adL h)`: in the proof of the spectral comparison, each diagonal block of
$\Lambda'$ is
determined by the same block of $W'$, as the Daleckii--Krein factors depend only on the
eigenvalues. -/
theorem cubicDiag_bernSeries [NeZero d] {J h : 𝕄} (hh : Commute J h)
    (ha : ‖I • adL h‖ < 2 * π) (X : 𝕄) :
    cubicDiag J (bernSeries (I • adL h) X) =
      bernSeries (I • adL h) (cubicDiag J X) := by
  have hc : Commute (cubicDiagL J) (I • adL h) := by
    ext X
    have hconj : adL h (J * X * J) = J * adL h X * J := by
      simp only [adL_apply, mul_sub, sub_mul]
      congr 1
      · simp only [← mul_assoc, hh.eq]
      · rw [mul_assoc (J * X) J h, hh.eq]
        simp only [mul_assoc]
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      map_smul, cubicDiagL_apply, cubicDiag, map_add]
    rw [← hconj]
    simp only [smul_add, smul_smul]
    ring_nf
  have hs := (summable_norm_bernSeries_term (I • adL h) ha).of_norm
  have hsX := ((ContinuousLinearMap.apply ℂ 𝕄 X).hasSum hs.hasSum).summable
  change Summable (fun n : ℕ ↦
    ((((bernoulli n : ℚ) : ℂ) / (Nat.factorial n : ℂ)) • (I • adL h) ^ n) X) at hsX
  rw [← cubicDiagL_apply, bernSeries, tsum_apply_of_summable hs,
    (cubicDiagL J).map_tsum hsX, tsum_apply_of_summable hs]
  refine tsum_congr fun n ↦ ?_
  simp only [ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  have heq := congrArg (fun T : 𝕄 →L[ℂ] 𝕄 ↦ T X) (hc.pow_right n).eq
  simpa only [ContinuousLinearMap.mul_apply, cubicDiagL_apply] using heq

/-- Commutator powers preserve the two fixed spectral blocks. -/
theorem cubic_commute_I_adL_pow {h J X : 𝕄}
    (hh : Commute J h) (hX : Commute J X) (n : ℕ) :
    Commute J (((I • adL h) ^ n) X) := by
  induction n with
  | zero => simpa using hX
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
    exact (cubic_commute_adL hh ih).smul_right I

/-- On a diagonal block the inverse averaging series may use the half-width
Hamiltonian. The norm hypotheses justify both operator series. -/
theorem cubic_bernSeries_shift_eq [NeZero d] {h J X : 𝕄} {c r : ℝ}
    (hh : Commute J h) (hX : Commute J X)
    (ha : ‖I • adL h‖ < 2 * π)
    (hb : ‖(I • adL (h - (c : ℂ) • 1 - (r : ℂ) • J) : 𝕄 →L[ℂ] 𝕄)‖ < 2 * π) :
    bernSeries (I • adL h) X =
      bernSeries (I • adL (h - (c : ℂ) • 1 - (r : ℂ) • J)) X := by
  unfold bernSeries
  have hsa := (summable_norm_bernSeries_term (I • adL h) ha).of_norm
  let b : 𝕄 →L[ℂ] 𝕄 := I • adL (h - (c : ℂ) • 1 - (r : ℂ) • J)
  have hsb := (summable_norm_bernSeries_term (A := 𝕄 →L[ℂ] 𝕄) b hb).of_norm
  rw [tsum_apply_of_summable hsa, tsum_apply_of_summable hsb]
  refine tsum_congr fun n ↦ ?_
  simp only [ContinuousLinearMap.smul_apply]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, ← ih,
      cubic_adL_shift_eq (c := c) (r := r) (cubic_commute_I_adL_pow hh hX n)]

/-- The blockwise bound in the proof of the spectral comparison: the block-diagonal part of
`bernSeries (I • adL h) X` has norm at most $\kappa = (w/4)/\sin(w/4)$ = `sinBound (w / 2)` times
the norm of the block-diagonal part of $X$. For $X = iW^\dagger W'$ with $W = e^{-ih}$, which
commutes with $J$, that part is $iW^\dagger$ times the block-diagonal part of $W'$, so this is
$\|\Lambda'_{jj}\| \le \kappa\|W'_{jj}\|$ for both blocks $j$.

The proof is the paper's: on block-diagonal input the series in $\mathrm{ad}_h$ equals the series in
$\mathrm{ad}_{h_0}$ for $h_0 = h - c - (w/4)J$, which subtracts from each block the midpoint of its
half of the window (`cubic_bernSeries_shift_eq`), and $h_0$ has spectrum in an interval of length
$w/2$, where the bound of Lemma A.2(i) is $\kappa$ (`norm_bernSeries_I_adL_le_sinBound`). -/
theorem norm_cubicDiag_bernSeries_le_block [NeZero d] {h J : 𝕄} {c w : ℝ}
    (hh : h.IsHermitian) (hJ : J.IsHermitian) (hJJ : J * J = 1) (hJh : Commute J h)
    (hw0 : 0 < w) (hw : w < 2 * π)
    (ha : ‖I • adL h‖ ≤ w)
    (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4)
    (X : 𝕄) :
    ‖cubicDiag J (bernSeries (I • adL h) X)‖ ≤ sinBound (w / 2) * ‖cubicDiag J X‖ := by
  let h₀ : 𝕄 := h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J
  have hh₀ : h₀.IsHermitian := by
    have hhs : star h = h := Matrix.isHermitian_iff_isSelfAdjoint.mp hh
    have hJs : star J = J := Matrix.isHermitian_iff_isSelfAdjoint.mp hJ
    change star h₀ = h₀
    simp only [h₀, star_sub, star_smul, star_one, Complex.star_def,
      Complex.conj_ofReal, hhs, hJs]
  have ha₀ : ‖I • adL h₀‖ ≤ w / 2 := (norm_I_smul_adL_le h₀ 0).trans (by
    rw [zero_smul, sub_zero]; linarith [show ‖h₀‖ ≤ w / 4 from hsmall])
  have hw₀ : w / 2 < 2 * π := by linarith
  rw [cubicDiag_bernSeries hJh (ha.trans_lt hw) X,
    cubic_bernSeries_shift_eq (c := c) (r := w / 4)
      hJh (cubicDiag_commute J X hJJ) (ha.trans_lt hw)
      (ha₀.trans_lt hw₀)]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_bernSeries_I_adL_le_sinBound hh₀ (by linarith) hw₀ ha₀) (norm_nonneg _))

/-- $\|B\| \le \kappa\|X\|$ in the proof of the spectral comparison: the block-diagonal part of
`bernSeries (I • adL h) X` has norm at most $(w/4)/\sin(w/4)$ = `sinBound (w / 2)` times $\|X\|$,
from the blockwise bound `norm_cubicDiag_bernSeries_le_block`, as a block-diagonal part has norm at
most the matrix's (`norm_cubicDiag_le`). -/
theorem norm_cubicDiag_bernSeries_le [NeZero d] {h J : 𝕄} {c w : ℝ}
    (hh : h.IsHermitian) (hJ : J.IsHermitian) (hJJ : J * J = 1)
    (hJn : ‖J‖ ≤ 1) (hJh : Commute J h)
    (hw0 : 0 < w) (hw : w < 2 * π)
    (ha : ‖I • adL h‖ ≤ w)
    (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4)
    (X : 𝕄) :
    ‖cubicDiag J (bernSeries (I • adL h) X)‖ ≤ sinBound (w / 2) * ‖X‖ :=
  (norm_cubicDiag_bernSeries_le_block hh hJ hJJ hJh hw0 hw ha hsmall X).trans
    (mul_le_mul_of_nonneg_left (norm_cubicDiag_le J X hJn)
      (sinBound_nonneg (by linarith) (by linarith)))

/-- $\mathrm{ad}_h$ preserves off-diagonal matrices when $J$ commutes with $h$. -/
theorem cubic_anticommute_adL {h J X : 𝕄} (hh : Commute J h)
    (hX : J * X = -(X * J)) : J * adL h X = -(adL h X * J) := by
  have h₁ : J * (h * X) = -(h * X * J) := by
    rw [← mul_assoc, hh.eq, mul_assoc h J X, hX, mul_neg, mul_assoc]
  have h₂ : J * (X * h) = -(X * h * J) := by
    rw [← mul_assoc, hX, neg_mul, mul_assoc X J h, hh.eq, ← mul_assoc]
  simp only [adL_apply, mul_sub, sub_mul, h₁, h₂]
  abel

/-- So do the powers of $i\,\mathrm{ad}_h$. -/
theorem cubic_anticommute_I_adL_pow {h J X : 𝕄}
    (hh : Commute J h) (hX : J * X = -(X * J)) (n : ℕ) :
    J * (((I • adL h) ^ n) X) = -((((I • adL h) ^ n) X) * J) := by
  induction n with
  | zero => simpa using hX
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      mul_smul_comm, smul_mul_assoc, cubic_anticommute_adL hh ih, smul_neg]

/-- Two off-diagonal factors have diagonal product. -/
theorem cubic_commute_mul_of_anticommute {J X Y : 𝕄}
    (hX : J * X = -(X * J)) (hY : J * Y = -(Y * J)) :
    Commute J (X * Y) := by
  change J * (X * Y) = X * Y * J
  rw [← mul_assoc, hX, neg_mul, mul_assoc X J Y, hY, mul_neg, neg_neg, ← mul_assoc]

/-- The commutator of two off-diagonal matrices is block-diagonal. -/
theorem cubic_commute_adL_of_anticommute {J X Y : 𝕄}
    (hX : J * X = -(X * J)) (hY : J * Y = -(Y * J)) :
    Commute J (adL X Y) := by
  rw [adL_apply]
  exact (cubic_commute_mul_of_anticommute hX hY).sub_right
    (cubic_commute_mul_of_anticommute hY hX)

/-- $\|C^nX\| \le w^n\|X\|$ for $\|C\| \le w$. -/
theorem cubic_norm_pow_apply_le {C : 𝕄 →L[ℂ] 𝕄} {w : ℝ} (hC : ‖C‖ ≤ w) (n : ℕ) (X : 𝕄) :
    ‖(C ^ n) X‖ ≤ w ^ n * ‖X‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    calc
      ‖C ((C ^ n) X)‖ ≤ ‖C‖ * ‖(C ^ n) X‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ w * (w ^ n * ‖X‖) :=
        mul_le_mul hC ih (norm_nonneg _) ((norm_nonneg C).trans hC)
      _ = w ^ (n + 1) * ‖X‖ := by rw [pow_succ']; ring

/-- $\|i[X, Y]\| \le 2\|X\|\|Y\|$. -/
theorem cubic_norm_commutator_le (X Y : 𝕄) :
    ‖(I • adL X) Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_I, one_mul]
  simpa using norm_adL_apply_le X Y 0

/-- The geometric sum that removes the derivative's factor `n` in the two
terms containing an off-diagonal perturbation. -/
theorem cubic_geometric_sum_le {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (w / 2) ^ j * w ^ (n - j)) ≤ 2 * w ^ n := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      (w / 2) ^ j * w ^ (n - j) = w ^ n * (1 / 2 : ℝ) ^ j := by
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [div_eq_mul_inv, mul_pow, show w ^ n = w ^ j * w ^ (n - j) by
      rw [← pow_add, Nat.add_sub_of_le hjn]]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (sum_geometric_two_le (n + 1)) (pow_nonneg hw n)).trans_eq
    (mul_comm _ _)

/-- The contribution of degree `n + 1` when the Hamiltonian is varied by `D` and the input slope is
held equal to `X`: $\sum_{j \le n}(i\,\mathrm{ad}_h)^j(i\,\mathrm{ad}_D)(i\,\mathrm{ad}_h)^{n-j}X$.
-/
def cubicSlopePair (h D X : 𝕄) (n : ℕ) : 𝕄 :=
  ∑ j ∈ Finset.range (n + 1),
    ((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))

/-- On block-diagonal input the powers are narrow: $\|(i\,\mathrm{ad}_h)^nX\| \le (w/2)^n\|X\|$
(the paper's "$\mathrm{ad}_\Lambda$ has norm at most $w/2$ on block-diagonal matrices"). -/
theorem cubic_narrow_pow_le {h J X : 𝕄} {c w : ℝ} (hh : Commute J h) (hX : Commute J X)
    (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4) (n : ℕ) :
    ‖((I • adL h) ^ n) X‖ ≤ (w / 2) ^ n * ‖X‖ := by
  have hr : 0 ≤ w / 4 := (norm_nonneg _).trans hsmall
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      norm_smul, Complex.norm_I, one_mul]
    calc
      ‖adL h (((I • adL h) ^ n) X)‖ ≤ 2 * (w / 4) * ‖((I • adL h) ^ n) X‖ :=
        norm_adL_cubicDiag_le (cubic_commute_I_adL_pow hh hX n) hsmall
      _ ≤ 2 * (w / 4) * ((w / 2) ^ n * ‖X‖) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg zero_le_two hr)
      _ = (w / 2) ^ (n + 1) * ‖X‖ := by rw [pow_succ']; ring

/-- $\sum_{j \le n} w^j(w/2)^{n-j} \le 2w^n$. -/
theorem cubic_geometric_sum_reverse_le {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), w ^ j * (w / 2) ^ (n - j)) ≤ 2 * w ^ n := by
  have heq : (∑ j ∈ Finset.range (n + 1), w ^ j * (w / 2) ^ (n - j)) =
      ∑ j ∈ Finset.range (n + 1), (w / 2) ^ j * w ^ (n - j) := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1), (w / 2) ^ (n - j) * w ^ (n - (n - j)) :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_comm]
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun j ↦ (w / 2) ^ j * w ^ (n - j)) (n + 1)
  rw [heq]
  exact cubic_geometric_sum_le hw n

/-- Two off-diagonal slopes give diagonal output, so the outer powers are narrow. -/
theorem norm_cubicSlopePair_off_off {h J D X : 𝕄} {c w : ℝ}
    (hh : Commute J h) (hD : J * D = -(D * J)) (hX : J * X = -(X * J))
    (ha : ‖I • adL h‖ ≤ w) (hsmall : ‖h - (c : ℂ) • 1 - ((w / 4 : ℝ) : ℂ) • J‖ ≤ w / 4) (n : ℕ) :
    ‖cubicSlopePair h D X n‖ ≤ 4 * ‖D‖ * ‖X‖ * w ^ n := by
  have hw : 0 ≤ w := (norm_nonneg (I • adL h)).trans ha
  unfold cubicSlopePair
  have hterm (j : ℕ) :
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
        (2 * ‖D‖ * ‖X‖) * ((w / 2) ^ j * w ^ (n - j)) := by
    have hcomm := (cubic_commute_adL_of_anticommute hD
      (cubic_anticommute_I_adL_pow hh hX (n - j))).smul_right I
    calc
      ‖((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))‖ ≤
          (w / 2) ^ j * ‖(I • adL D) (((I • adL h) ^ (n - j)) X)‖ :=
        cubic_narrow_pow_le hh hcomm hsmall j
      _ ≤ (w / 2) ^ j * (2 * ‖D‖ * ‖((I • adL h) ^ (n - j)) X‖) := by
        gcongr; exact cubic_norm_commutator_le _ _
      _ ≤ (w / 2) ^ j * (2 * ‖D‖ * (w ^ (n - j) * ‖X‖)) := by
        gcongr; exact cubic_norm_pow_apply_le ha _ _
      _ = _ := by ring
  refine (norm_sum_le_of_le _ (fun j _ ↦ hterm j)).trans ?_
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (cubic_geometric_sum_le hw n) (by positivity)).trans_eq
    (by ring)

end UnitaryProducts

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- The derivative of $a \mapsto a^n$ in direction $b$, $\sum_{j<n} a^{n-1-j}ba^j$ (`0` for
$n = 0$). -/
def cubicPowDerivative (a b : A) (n : ℕ) : A :=
  ∑ j ∈ Finset.range n, a ^ (n - 1 - j) * b * a ^ j

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- $\|\partial(a^n)[b]\| \le n r^{n-1}\|b\|$ for $\|a\| \le r$. -/
theorem norm_cubicPowDerivative_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (n : ℕ) :
    ‖cubicPowDerivative a b n‖ ≤ n * r ^ (n - 1) * ‖b‖ := by
  have hr : 0 ≤ r := (norm_nonneg (a)).trans ha
  unfold cubicPowDerivative
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤ r ^ (n - 1) * ‖b‖ := by
    have hjn := Finset.mem_range.mp hj
    have hp : (n - 1 - j) + j = n - 1 := by omega
    calc
      ‖a ^ (n - 1 - j) * b * a ^ j‖ ≤
          ‖a ^ (n - 1 - j)‖ * ‖b‖ * ‖a ^ j‖ := norm_mul₃_le
      _ ≤ r ^ (n - 1 - j) * ‖b‖ * r ^ j := by
        gcongr <;> exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
      _ = r ^ (n - 1) * ‖b‖ := by
        rw [mul_right_comm, ← pow_add, hp]
  refine (norm_sum_le_of_le _ hterm).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The directional derivative $\sum_n B_{n+2}/(n+2)!\,\partial(a^n)[b]$ of the corrector series
`frameSeries` at `a`. It converges absolutely for $\|a\| < 2\pi$, where every use takes it;
otherwise `tsum` may return `0`. -/
def cubicFrameSeriesDerivative (a b : A) : A :=
  ∑' n : ℕ, (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
    cubicPowDerivative a b n


omit [CompleteSpace A] in
/-- Termwise bound for `cubicFrameSeriesDerivative`. -/
theorem norm_cubicFrameSeriesDerivative_term_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (n : ℕ) :
    ‖(((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
        cubicPowDerivative a b n‖ ≤
      (|((bernoulli (n + 2) : ℚ) : ℝ)| * n * r ^ (n - 1) /
        (Nat.factorial (n + 2) : ℝ)) * ‖b‖ := by
  rw [norm_smul, norm_frame_coefficient]
  exact (mul_le_mul_of_nonneg_left (norm_cubicPowDerivative_le ha n) (by positivity)).trans_eq
    (by ring)

omit [CompleteSpace A] in
/-- The derivative series converges absolutely for $\|a\| < 2\pi$. -/
theorem summable_norm_cubicFrameSeriesDerivative {a b : A} (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      ‖(((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
        cubicPowDerivative a b n‖) := by
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_cubicFrameSeriesDerivative_term_le le_rfl)
    ((summable_frameLip_majorant (norm_nonneg a) ha).mul_right ‖b‖)

/-- Analyticity in the full operator algebra, rather than just on scalar arguments. -/
theorem analyticOnNhd_cubic_frameSeries :
    AnalyticOnNhd ℂ (frameSeries : A → A) (Metric.ball 0 (2 * π)) := by
  apply analyticOnNhd_tsum_coeff (by positivity)
  intro r hr0 hr
  refine (summable_frameBound_majorant hr0 hr).congr fun n ↦ ?_
  rw [norm_frame_coefficient]
  ring

/-- Differentiation of the operator series in a fixed direction. -/
theorem hasDerivAt_cubic_frameSeries_line {a b : A} (ha : ‖a‖ < 2 * π) :
    HasDerivAt (fun z : ℂ ↦ frameSeries (a + z • b))
      (cubicFrameSeriesDerivative a b) 0 := by
  let r : ℝ := (‖a‖ + 2 * π) / 2
  have hra : ‖a‖ < r := by dsimp [r]; linarith
  have hr : r < 2 * π := by dsimp [r]; linarith
  have hr0 : 0 ≤ r := (norm_nonneg a).trans hra.le
  let δ : ℝ := (r - ‖a‖) / (‖b‖ + 1)
  have hb1 : 0 < ‖b‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hra) hb1
  have hab (z : ℂ) (hz : z ∈ Metric.ball 0 δ) : ‖a + z • b‖ ≤ r := by
    have hzn : ‖z‖ < (r - ‖a‖) / (‖b‖ + 1) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hle : ‖z‖ * ‖b‖ ≤ ‖z‖ * (‖b‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg z)
    linarith [norm_add_le a (z • b), norm_smul z b, (lt_div_iff₀ hb1).mp hzn]
  have hline (z : ℂ) : HasDerivAt (fun y : ℂ ↦ a + y • b) b z := by
    simpa using ((hasDerivAt_id z).smul_const b).const_add a
  have hd := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ ↦
      (|((bernoulli (n + 2) : ℚ) : ℝ)| * n * r ^ (n - 1) /
        (Nat.factorial (n + 2) : ℝ)) * ‖b‖)
    (g := fun (n : ℕ) (z : ℂ) ↦
      (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
        (a + z • b) ^ n)
    (g' := fun (n : ℕ) (z : ℂ) ↦
      (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
        cubicPowDerivative (a + z • b) b n)
    ((summable_frameLip_majorant hr0 hr).mul_right ‖b‖)
    Metric.isOpen_ball (convex_ball (0 : ℂ) δ).isPreconnected
    (fun n z _ ↦ ?_)
    (fun n z hz ↦ norm_cubicFrameSeriesDerivative_term_le (hab z hz) n)
    (y₀ := (0 : ℂ)) (Metric.mem_ball_self hδ) ?_ (Metric.mem_ball_self hδ)
  · simpa only [zero_smul, add_zero, frameSeries, cubicFrameSeriesDerivative] using hd
  · simpa only [cubicPowDerivative, Nat.pred_eq_sub_one] using
      ((hline z).fun_pow' n).const_smul
        (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ))
  · simpa only [zero_smul, add_zero] using (summable_norm_frameSeries_terms a ha).of_norm

/-- Real-parameter composition, with scalar restriction performed in the abstract algebra. -/
theorem hasDerivAt_cubic_frameSeries_comp {f : ℝ → A} {fd : A} {s : ℝ}
    (hf : HasDerivAt f fd s) (ha : ‖f s‖ < 2 * π) :
    HasDerivAt (fun t ↦ frameSeries (f t)) (cubicFrameSeriesDerivative (f s) fd) s := by
  have hdiff : DifferentiableAt ℂ (frameSeries : A → A) (f s) :=
    (analyticOnNhd_cubic_frameSeries _ (mem_ball_zero_iff.mpr ha)).differentiableAt
  have hl : HasDerivAt (fun z : ℂ ↦ f s + z • fd) fd 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const fd).const_add (f s)
  have hf' : HasFDerivAt (frameSeries : A → A) (fderiv ℂ frameSeries (f s))
      (f s + (0 : ℂ) • fd) := by simpa only [zero_smul, add_zero] using hdiff.hasFDerivAt
  have hc := hf'.comp_hasDerivAt 0 hl
  have he := hc.unique (hasDerivAt_cubic_frameSeries_line ha)
  simpa only [← he] using (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hf

end UnitaryProducts.Corrector

namespace UnitaryProducts

variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- Applied to `X`, the derivative of $(i\,\mathrm{ad}_h)^{n+1}$ in direction $i\,\mathrm{ad}_D$ is
`cubicSlopePair h D X n`. -/
theorem cubicPowDerivative_apply (h D X : 𝕄) (n : ℕ) :
    (cubicPowDerivative (I • adL h) (I • adL D) (n + 1)) X =
      cubicSlopePair h D X n := by
  simp only [cubicPowDerivative, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.mul_apply, Nat.add_sub_cancel, cubicSlopePair]
  rw [← Finset.sum_range_reflect
    (fun j ↦ ((I • adL h) ^ j) ((I • adL D) (((I • adL h) ^ (n - j)) X))) (n + 1)]
  exact Finset.sum_congr rfl fun j hj ↦ by
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- The derivative of the corrector series as the series of `cubicSlopePair` terms (the
termwise differentiation in the proof of the spectral comparison). -/
theorem cubicFrameSeriesDerivative_apply (h D X : 𝕄)
    (ha : ‖I • adL h‖ < 2 * π) :
    cubicFrameSeriesDerivative (I • adL h) (I • adL D) X =
      ∑' n : ℕ, (((bernoulli (n + 3) : ℚ) : ℂ) / (Nat.factorial (n + 3) : ℂ)) •
        cubicSlopePair h D X n := by
  have hs := (summable_norm_cubicFrameSeriesDerivative (b := I • adL D) ha).of_norm
  have hsX := ((ContinuousLinearMap.apply ℂ 𝕄 X).hasSum hs.hasSum).summable
  change Summable (fun n : ℕ ↦
    ((((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) •
      cubicPowDerivative (I • adL h) (I • adL D) n) X) at hsX
  rw [cubicFrameSeriesDerivative, tsum_apply_of_summable hs, hsX.tsum_eq_zero_add]
  have hz : ((((bernoulli (0 + 2) : ℚ) : ℂ) / (Nat.factorial (0 + 2) : ℂ)) •
      cubicPowDerivative (I • adL h) (I • adL D) 0) X = 0 := by
    simp [cubicPowDerivative]
  rw [hz, zero_add]
  exact tsum_congr fun n ↦ by rw [ContinuousLinearMap.smul_apply, cubicPowDerivative_apply]

/-- That series converges absolutely. -/
theorem summable_norm_cubicFrameSlope_terms (h D X : 𝕄)
    (ha : ‖I • adL h‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      ‖(((bernoulli (n + 3) : ℚ) : ℂ) / (Nat.factorial (n + 3) : ℂ)) •
        cubicSlopePair h D X n‖) := by
  have hs := (summable_norm_cubicFrameSeriesDerivative (b := I • adL D) ha).mul_right ‖X‖
  have hs' := (summable_nat_add_iff 1).mpr hs
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hs'
  have hbound := ContinuousLinearMap.le_opNorm
    ((((bernoulli (n + 1 + 2) : ℚ) : ℂ) / (Nat.factorial (n + 1 + 2) : ℂ)) •
      cubicPowDerivative (I • adL h) (I • adL D) (n + 1)) X
  simpa only [ContinuousLinearMap.smul_apply, cubicPowDerivative_apply] using hbound

/-- The corrector along a differentiable Hamiltonian and slope path. -/
theorem hasDerivAt_cubic_frameOp {H D : ℝ → 𝕄} {Hd Dd : 𝕄} {s : ℝ}
    (hH : HasDerivAt H Hd s) (hD : HasDerivAt D Dd s)
    (ha : ‖I • adL (H s)‖ < 2 * π) :
    HasDerivAt (fun t ↦ frameOp (H t) (D t))
      (cubicFrameSeriesDerivative (I • adL (H s)) (I • adL Hd) (D s) +
        frameOp (H s) Dd) s := by
  have hA := hasDerivAt_clmC_comp (V := 𝕄) (W := 𝕄 →L[ℂ] 𝕄) (I • adLCLM d) hH
  simp only [ContinuousLinearMap.smul_apply,
    show ∀ X : 𝕄, adLCLM d X = adL X from fun _ ↦ rfl] at hA
  have hc := hasDerivAt_cubic_frameSeries_comp (A := 𝕄 →L[ℂ] 𝕄) hA ha
  exact hasDerivAt_clmC_apply (V := 𝕄) (W := 𝕄) hc hD

/-- $\mathcal N'(0) = 0$: `frameLip 0 = 0`, as $B_3 = 0$. -/
theorem cubic_frameLip_zero : frameLip 0 = 0 := by
  rw [← tsum_frameLip_shifted (show (0 : ℝ) ≤ 0 by rfl) (by positivity : (0 : ℝ) < 2 * π)]
  refine (tsum_congr fun n ↦ ?_).trans (tsum_zero (α := ℝ))
  cases n with
  | zero => norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_three]
  | succ n => simp

end UnitaryProducts
