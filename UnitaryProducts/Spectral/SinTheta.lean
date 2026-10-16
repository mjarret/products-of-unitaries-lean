/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.Sparse

/-!
# The Davis–Kahan $\sin\Theta$ bound for spectral projectors

## Declarations

- `HasGap`
- `IsDiag`
- `adjoint_proj`
- `ext_basis`
- `idx`
- `inner_basis_sum`
- `inner_proj`
- `inner_proj_left`
- `inner_shift`
- `inner_starProjection_complement_eq_zero`
- `isDiag_eigenvectorBasis`
- `isStarProjection_specProj`
- `le_norm_shift_proj`
- `norm_comp_compression`
- `norm_comp_sub_comm`
- `norm_compression_sub_comm`
- `norm_le_of_apply_le`
- `norm_one_sub_specProj_mul_specProj_le`
- `norm_proj_comp_proj_le_residual`
- `norm_proj_le`
- `norm_shift_proj_le`
- `norm_specProj_sub_le_widened`
- `norm_specProj_sub_le_widened_residual`
- `norm_sq_basis_sum`
- `norm_sq_proj`
- `norm_sq_proj_add_compl`
- `norm_sq_shift_proj`
- `norm_sub_le_max_of_isStarProjection`
- `proj`
- `proj_add_compl`
- `proj_apply`
- `proj_proj`
- `shift_proj`
- `specProj`
- `toEuclideanCLM_one_sub_specProj`
- `toEuclideanCLM_specProj`
- `windowProj`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator InnerProductSpace
open NormedSpace Set Finset Matrix

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
local notation "𝒯" => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)

section Projections

variable (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (ev : Fin d → ℝ)

open Classical in
/-- Coordinates of a finite combination of an orthonormal basis. -/
theorem inner_basis_sum (s : Finset (Fin d)) (l : Fin d → ℂ) (j : Fin d) :
    ⟪b j, ∑ i ∈ s, l i • b i⟫_ℂ = if j ∈ s then l j else 0 := by
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  simp [Finset.sum_ite_eq]

open Classical in
/-- Pythagoras for a finite combination of an orthonormal basis. -/
theorem norm_sq_basis_sum (s : Finset (Fin d)) (l : Fin d → ℂ) :
    ‖∑ i ∈ s, l i • b i‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, b.orthonormal.inner_sum l l s, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

open Classical in
/-- Two vectors with the same coordinates in an orthonormal basis are equal. -/
theorem ext_basis {x y : (EuclideanSpace ℂ (Fin d))} (h : ∀ j, ⟪b j, x⟫_ℂ = ⟪b j, y⟫_ℂ) : x = y :=
    by rw [← b.sum_repr' x, ← b.sum_repr' y]; simp only [h]

open Classical in
/-- The indices whose eigenvalue lies in `S`. -/
noncomputable def idx (S : Set ℝ) : Finset (Fin d) := univ.filter fun i ↦ ev i ∈ S

open Classical in
/-- The orthogonal projection onto the eigenvectors `b i` with `ev i ∈ S`. -/
noncomputable def proj (S : Set ℝ) : (EuclideanSpace ℂ (Fin d)) →L[ℂ] (EuclideanSpace ℂ (Fin d)) :=
  ∑ i ∈ idx ev S, InnerProductSpace.rankOne ℂ (b i) (b i)

open Classical in
/-- `proj b ev S x` is the sum of the coordinates of `x` along the selected basis vectors. -/
theorem proj_apply (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) :
    proj b ev S x = ∑ i ∈ idx ev S, ⟪b i, x⟫_ℂ • b i := by
  simp [proj, ContinuousLinearMap.sum_apply]

open Classical in
/-- `proj b ev S` keeps the coordinates with `ev j ∈ S` and zeroes the others. -/
theorem inner_proj (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) (j : Fin d) :
    ⟪b j, proj b ev S x⟫_ℂ = if ev j ∈ S then ⟪b j, x⟫_ℂ else 0 := by
  rw [proj_apply, inner_basis_sum]
  simp [idx]

open Classical in
/-- Pythagoras for `proj b ev S x`. -/
theorem norm_sq_proj (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) :
    ‖proj b ev S x‖ ^ 2 = ∑ i ∈ idx ev S, ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
  rw [proj_apply, norm_sq_basis_sum]

open Classical in
/-- Pythagoras for the splitting of `x` by `S` and its complement. -/
theorem norm_sq_proj_add_compl (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) :
    ‖proj b ev S x‖ ^ 2 + ‖proj b ev Sᶜ x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [norm_sq_proj, norm_sq_proj, ← b.sum_sq_norm_inner_right x, idx, idx]
  simp only [Set.mem_compl_iff]
  exact sum_filter_add_sum_filter_not _ _ _

open Classical in
/-- `proj b ev S` is a contraction. -/
theorem norm_proj_le (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) : ‖proj b ev S x‖ ≤ ‖x‖ := by
  have := norm_sq_proj_add_compl b ev S x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith [sq_nonneg ‖proj b ev Sᶜ x‖]

open Classical in
/-- The projectors of `S` and of its complement add up to the identity. -/
theorem proj_add_compl (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) :
    proj b ev S x + proj b ev Sᶜ x = x :=
  ext_basis b fun j ↦ by
    rw [inner_add_right, inner_proj, inner_proj]; by_cases h : ev j ∈ S <;> simp [h]

open Classical in
/-- `proj b ev S` is idempotent. -/
theorem proj_proj (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) : proj b ev S (proj b ev S x) =
    proj b ev S x :=
  ext_basis b fun j ↦ by rw [inner_proj, inner_proj]; by_cases h : ev j ∈ S <;> simp [h]

open Classical in
/-- `proj b ev S` is symmetric. -/
theorem inner_proj_left (S : Set ℝ) (x y : EuclideanSpace ℂ (Fin d)) :
    ⟪proj b ev S x, y⟫_ℂ = ⟪x, proj b ev S y⟫_ℂ := by
  rw [proj_apply, proj_apply, sum_inner, inner_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

open Classical in
/-- `proj b ev S` is self-adjoint. -/
theorem adjoint_proj (S : Set ℝ) :
    ContinuousLinearMap.adjoint (proj b ev S) = proj b ev S :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y ↦ inner_proj_left b ev S x y).symm

variable {T : (EuclideanSpace ℂ (Fin d)) →L[ℂ] (EuclideanSpace ℂ (Fin d))}

open Classical in
/-- `T` is diagonal in the orthonormal basis `b` with eigenvalues `ev`. -/
def IsDiag (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (ev : Fin d → ℝ) (T :
    (EuclideanSpace ℂ (Fin d)) →L[ℂ] (EuclideanSpace ℂ (Fin d))) : Prop :=
  ∀ j v, ⟪b j, T v⟫_ℂ = (ev j : ℂ) * ⟪b j, v⟫_ℂ

open Classical in
/-- Coordinates of `(T - m) v` for `T` diagonal in `b`. -/
theorem inner_shift {m : ℝ} (hT : IsDiag b ev T) (j : Fin d) (v : (EuclideanSpace ℂ (Fin d))) :
    ⟪b j, (T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) v⟫_ℂ = ((ev j - m :
      ℝ) : ℂ) * ⟪b j, v⟫_ℂ := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right, hT j v]
  push_cast; ring

open Classical in
/-- `T - m` commutes with `proj b ev S` when `T` is diagonal in `b`. -/
theorem shift_proj {m : ℝ} (hT : IsDiag b ev T) (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin d))) :
    (T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) (proj b ev S x)
      = proj b ev S ((T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) x) := by
  refine ext_basis b fun j ↦ ?_
  rw [inner_shift b ev hT, inner_proj, inner_proj, inner_shift b ev hT]
  by_cases h : ev j ∈ S <;> simp [h]

open Classical in
/-- `‖(T - m) P_S x‖² = ∑_{ev i ∈ S} (ev i - m)² |⟪b i, x⟫|²` for `T` diagonal in `b`. -/
theorem norm_sq_shift_proj {m : ℝ} (hT : IsDiag b ev T) (S : Set ℝ) (x : (EuclideanSpace ℂ (Fin
    d))) :
    ‖(T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) (proj b ev S x)‖ ^ 2
      = ∑ i ∈ idx ev S, (ev i - m) ^ 2 * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
  have hexp : (T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) (proj b ev S x)
      = ∑ i ∈ idx ev S, (((ev i - m : ℝ) : ℂ) * ⟪b i, x⟫_ℂ) • b i :=
    ext_basis b fun j ↦ by
      rw [inner_shift b ev hT, inner_proj, inner_basis_sum]; by_cases h : ev j ∈ S <;> simp [idx, h]
  rw [hexp, norm_sq_basis_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

open Classical in
/-- Eigenvalues in `S` within `c` of `m`: `‖(T - m) P_S x‖ ≤ c ‖P_S x‖`. -/
theorem norm_shift_proj_le {m c : ℝ} (hc : 0 ≤ c) (hT : IsDiag b ev T) {S : Set ℝ}
    (hS : ∀ i, ev i ∈ S → |ev i - m| ≤ c) (x : (EuclideanSpace ℂ (Fin d))) :
    ‖(T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) (proj b ev S x)‖ ≤ c *
      ‖proj b ev S x‖ := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
    norm_sq_shift_proj b ev hT, norm_sq_proj, mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact mul_le_mul_of_nonneg_right
    (by rw [← sq_abs (ev i - m)]; exact pow_le_pow_left₀ (abs_nonneg _) (hS i hi) 2) (sq_nonneg _)

open Classical in
/-- Eigenvalues in `S` at least `c` from `m`: `c ‖P_S x‖ ≤ ‖(T - m) P_S x‖`. -/
theorem le_norm_shift_proj {m c : ℝ} (hc : 0 ≤ c) (hT : IsDiag b ev T) {S : Set ℝ}
    (hS : ∀ i, ev i ∈ S → c ≤ |ev i - m|) (x : (EuclideanSpace ℂ (Fin d))) :
    c * ‖proj b ev S x‖ ≤ ‖(T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
      (proj b ev S x)‖ := by
  rw [← pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero, mul_pow,
    norm_sq_shift_proj b ev hT, norm_sq_proj, mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  simp only [idx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact mul_le_mul_of_nonneg_right
    (by rw [← sq_abs (ev i - m)]; exact pow_le_pow_left₀ hc (hS i hi) 2) (sq_nonneg _)

end Projections

set_option maxHeartbeats 800000 in
-- Operator-norm instance unification in the compressed Sylvester estimate exceeds the default limit.
open Classical in
/-- **Davis–Kahan, Sylvester form, residual numerator.**  `P` projects onto eigenvalues of `T`
within `c` of `m`, `Q'` onto eigenvalues of `T'` at least `c + δ` from `m`.  Then
`‖Q' P y‖ ≤ (‖Q' (T' - T) P‖ / δ) ‖y‖`: the perturbation `T' - T` enters only through its
compression between the two projectors.

The argument is the elementary shift-by-the-centre version of the proof of Bhatia's
Theorem VII.3.1, which the paper cites for the unnumbered Davis–Kahan estimate. -/
theorem norm_proj_comp_proj_le_residual
    {b b' : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))} {ev ev' : Fin d → ℝ}
    {T T' : (EuclideanSpace ℂ (Fin d)) →L[ℂ] (EuclideanSpace ℂ (Fin d))}
    (hT : IsDiag b ev T) (hT' : IsDiag b' ev' T') {S S' : Set ℝ}
    {m c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hS : ∀ i, ev i ∈ S → |ev i - m| ≤ c) (hS' : ∀ i, ev' i ∈ S' → c + δ ≤ |ev' i - m|)
    (y : (EuclideanSpace ℂ (Fin d))) :
    ‖proj b' ev' S' (proj b ev S y)‖
      ≤ ‖(proj b' ev' S').comp ((T' - T).comp (proj b ev S))‖ / δ * ‖y‖ := by
  set P := proj b ev S
  set Q := proj b' ev' S'
  set Sh := T - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))
  set Sh' := T' - (m : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))
  set K := ‖Q.comp P‖
  set R := ‖Q.comp ((T' - T).comp P)‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  -- Step 1: with `K = ‖QP‖` and `R = ‖Q(T' - T)P‖`, `(c + δ) ‖QPz‖ ≤ (cK + R) ‖z‖` for every `z`.
  have hstep : ∀ z : (EuclideanSpace ℂ (Fin d)), (c + δ) * ‖Q (P z)‖ ≤ (c * K + R) * ‖z‖ := by
    intro z
    -- The eigenvalues of `T'` selected by `Q` lie at least `c + δ` from `m`.
    have h1 := le_norm_shift_proj b' ev' (m := m) (by linarith) hT' hS' (P z)
    -- `T' - m` commutes with `Q`, and `(T' - m)P = (T - m)P + (T' - T)P`.
    have hcomm : Sh' (Q (P z)) = Q (Sh' (P z)) := shift_proj b' ev' hT' S' (P z)
    have hsplit : Sh' (P z) = Sh (P z) + (T' - T) (P z) := by
      simp only [Sh, Sh', ContinuousLinearMap.sub_apply]; abel
    have hPw : P (Sh (P z)) = Sh (P z) := by
      rw [← shift_proj b ev hT S (P z), proj_proj]
    -- The eigenvalues of `T` selected by `P` lie within `c` of `m`.
    have hw : ‖Q (Sh (P z))‖ ≤ K * (c * ‖z‖) := by
      calc ‖Q (Sh (P z))‖ = ‖Q.comp P (Sh (P z))‖ := by
            rw [ContinuousLinearMap.comp_apply, hPw]
        _ ≤ K * ‖Sh (P z)‖ := (Q.comp P).le_opNorm _
        _ ≤ K * (c * ‖P z‖) := by
            gcongr
            exact norm_shift_proj_le b ev hc hT hS z
        _ ≤ K * (c * ‖z‖) := by
            gcongr
            exact norm_proj_le b ev S z
    have hu : ‖Q ((T' - T) (P z))‖ ≤ R * ‖z‖ := by
      have h := (Q.comp ((T' - T).comp P)).le_opNorm z
      rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
    calc (c + δ) * ‖Q (P z)‖ ≤ ‖Sh' (Q (P z))‖ := h1
      _ = ‖Q (Sh (P z)) + Q ((T' - T) (P z))‖ := by rw [hcomm, hsplit, map_add]
      _ ≤ K * (c * ‖z‖) + R * ‖z‖ := (norm_add_le _ _).trans (add_le_add hw hu)
      _ = (c * K + R) * ‖z‖ := by ring
  -- Step 2: so `(c + δ) K ≤ cK + R`, that is `δ K ≤ R`.
  have hK : K ≤ (c * K + R) / (c + δ) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ by
      rw [ContinuousLinearMap.comp_apply, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith [hstep z]
  have hK' : K ≤ R / δ := by
    rw [le_div_iff₀ (by linarith)] at hK
    rw [le_div_iff₀ hδ]
    have hexp : K * (c + δ) = c * K + K * δ := by ring
    linarith
  -- Step 3: `‖QPy‖ ≤ K ‖y‖ ≤ (R/δ) ‖y‖`.
  calc ‖Q (P y)‖ = ‖Q.comp P y‖ := rfl
    _ ≤ K * ‖y‖ := (Q.comp P).le_opNorm y
    _ ≤ _ := by gcongr

open Classical in
/-- A Hermitian matrix is diagonal in its eigenvector basis, with its eigenvalues. -/
theorem isDiag_eigenvectorBasis {A : 𝕄} (hA : A.IsHermitian) :
    IsDiag hA.eigenvectorBasis hA.eigenvalues (𝒯 A) := by
  intro j v
  have hsa : IsSelfAdjoint (𝒯 A) := (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map 𝒯
  have hev : 𝒯 A (hA.eigenvectorBasis j) = ((hA.eigenvalues j : ℝ) : ℂ) • hA.eigenvectorBasis j :=
    by
    apply WithLp.ofLp_injective
    rw [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul, hA.mulVec_eigenvectorBasis j,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hsym := hsa.isSymmetric (hA.eigenvectorBasis j) v
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [← hsym, hev, inner_smul_left, Complex.conj_ofReal]

open Classical in
/-- The spectral projector $P_S(A)$ of a Hermitian matrix onto its eigenvalues in `S` (§2.2):
the matrix of `proj` in the eigenvector basis. As the indices with eigenvalue in `S` form whole
eigenspaces, it does not depend on the choice of that basis. -/
noncomputable def specProj {A : 𝕄} (hA : A.IsHermitian) (S : Set ℝ) : 𝕄 :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm (proj hA.eigenvectorBasis hA.eigenvalues S)

open Classical in
/-- The operator of `specProj hA S` is `proj` in the eigenvector basis. -/
theorem toEuclideanCLM_specProj {A : 𝕄} (hA : A.IsHermitian) (S : Set ℝ) :
    𝒯 (specProj hA S) = proj hA.eigenvectorBasis hA.eigenvalues S :=
  StarAlgEquiv.apply_symm_apply _ _

open Classical in
/-- `‖M‖` is the best constant in `‖𝒯 M x‖ ≤ C ‖x‖`. -/
theorem norm_le_of_apply_le {M : 𝕄} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖𝒯 M x‖ ≤ C * ‖x‖) :
    ‖M‖ ≤ C := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]; exact ContinuousLinearMap.opNorm_le_bound _ hC h

open Classical in
/-- `A` has no eigenvalues in the collar `c < |λ - m| < c + δ`: the window $[m - c, m + c]$ is
separated by at least $\delta$ from the rest of the spectrum. -/
def HasGap {A : 𝕄} (hA : A.IsHermitian) (m c δ : ℝ) : Prop :=
  ∀ i, |hA.eigenvalues i - m| ≤ c ∨ c + δ ≤ |hA.eigenvalues i - m|

open Classical in
/-- Spectral projectors are orthogonal projections. -/
theorem isStarProjection_specProj {A : 𝕄} (hA : A.IsHermitian) (S : Set ℝ) :
    IsStarProjection (specProj hA S) where
  isIdempotentElem := toEuclideanCLM_injective fun v ↦ by
    rw [map_mul, ContinuousLinearMap.mul_apply, toEuclideanCLM_specProj, proj_proj]
  isSelfAdjoint := toEuclideanCLM_injective fun v ↦ by
    rw [map_star, toEuclideanCLM_specProj, ContinuousLinearMap.star_eq_adjoint, adjoint_proj]

section Compressions

open Classical in
/-- Swapping the order of the difference inside a compression does not change its norm. -/
theorem norm_comp_sub_comm (Q P T T' : (EuclideanSpace ℂ (Fin d)) →L[ℂ]
    (EuclideanSpace ℂ (Fin d))) :
    ‖Q.comp ((T' - T).comp P)‖ = ‖Q.comp ((T - T').comp P)‖ := by
  rw [← norm_neg]
  congr 1; exact ContinuousLinearMap.ext fun x ↦ by simp

open Classical in
/-- The image under `𝒯` of `1 - P_S` is the projector onto the complementary group of
eigenvectors. -/
theorem toEuclideanCLM_one_sub_specProj {A : 𝕄} (hA : A.IsHermitian) (S : Set ℝ) :
    𝒯 (1 - specProj hA S) = proj hA.eigenvectorBasis hA.eigenvalues Sᶜ := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [map_sub, map_one, ContinuousLinearMap.sub_apply, toEuclideanCLM_specProj]
  have h := proj_add_compl hA.eigenvectorBasis hA.eigenvalues S x
  simp only [ContinuousLinearMap.one_apply]
  linear_combination (norm := module) -h

open Classical in
/-- The compression of `A - A'` between `P_S(A)` and the complement of `P_{S'}(A')`, read on
`EuclideanSpace`. -/
theorem norm_comp_compression {A A' : 𝕄} (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (S S' : Set ℝ) :
    ‖(proj hA'.eigenvectorBasis hA'.eigenvalues S'ᶜ).comp
        ((𝒯 A' - 𝒯 A).comp (proj hA.eigenvectorBasis hA.eigenvalues S))‖
      = ‖(1 - specProj hA' S') * (A - A') * specProj hA S‖ := by
  rw [norm_comp_sub_comm, ← Matrix.l2_opNorm_toEuclideanCLM]
  congr 1
  rw [map_mul, map_mul, toEuclideanCLM_one_sub_specProj, toEuclideanCLM_specProj, map_sub,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

open Classical in
/-- Swapping the order of the difference in a matrix compression does not change its norm. -/
theorem norm_compression_sub_comm (Q X Y P : 𝕄) : ‖Q * (X - Y) * P‖ = ‖Q * (Y - X) * P‖ := by
  rw [← norm_neg]; congr 1; noncomm_ring

open Classical in
/-- **Davis–Kahan, Sylvester form, for spectral projectors.**  If the eigenvalues of `A` in `S` lie
within `c` of `m` and those of `A'` outside `S'` lie at least `c + δ` from `m`, then
`‖(1 - P_{S'}(A')) P_S(A)‖ ≤ ‖(1 - P_{S'}(A')) (A - A') P_S(A)‖ / δ`: the matrix form of
`norm_proj_comp_proj_le_residual`. -/
theorem norm_one_sub_specProj_mul_specProj_le {A A' : 𝕄} (hA : A.IsHermitian)
    (hA' : A'.IsHermitian) {S S' : Set ℝ} {m c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (hS : ∀ i, hA.eigenvalues i ∈ S → |hA.eigenvalues i - m| ≤ c)
    (hS' : ∀ i, hA'.eigenvalues i ∈ S'ᶜ → c + δ ≤ |hA'.eigenvalues i - m|) :
    ‖(1 - specProj hA' S') * specProj hA S‖
      ≤ ‖(1 - specProj hA' S') * (A - A') * specProj hA S‖ / δ := by
  refine norm_le_of_apply_le (div_nonneg (norm_nonneg _) hδ.le) fun y ↦ ?_
  rw [map_mul, ContinuousLinearMap.mul_apply, toEuclideanCLM_one_sub_specProj,
    toEuclideanCLM_specProj, ← norm_comp_compression hA hA' S S']
  exact norm_proj_comp_proj_le_residual (isDiag_eigenvectorBasis hA)
    (isDiag_eigenvectorBasis hA') hc hδ hS hS' y

open Classical in
/-- A star projection has orthogonal range and complementary range. -/
theorem inner_starProjection_complement_eq_zero {P : 𝕄} (hP : IsStarProjection P)
    (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) P x)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) y) = 0 := by
  have hs := (hP.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℂ))).isSymmetric
  have he : inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) P x)
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) y) =
      inner ℂ x (Matrix.toEuclideanCLM (𝕜 := ℂ) P
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - P) y)) := hs _ _
  rw [he]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, hP.mul_one_sub_self, _root_.map_zero,
    ContinuousLinearMap.zero_apply, inner_zero_right]

open Classical in
/-- The distance of two orthogonal projections is bounded by the larger directed leakage. -/
theorem norm_sub_le_max_of_isStarProjection {P Q : 𝕄}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ‖P - Q‖ ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  let C := max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
  have hC : 0 ≤ C := (norm_nonneg _).trans (le_max_left _ _)
  have hstar : ‖Q * (1 - P)‖ = ‖(1 - P) * Q‖ := by
    rw [← norm_star (Q * (1 - P)), Matrix.star_mul, hP.one_sub.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq]
  apply norm_le_of_apply_le hC
  intro x
  have hPP : T P (T P x) = T P x := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hP.isIdempotentElem.eq]
  have hPcPc : T (1 - P) (T (1 - P) x) = T (1 - P) x := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, hP.one_sub.isIdempotentElem.eq]
  -- Split `(P - Q)x = (1 - Q)(Px) - Q((1 - P)x)`; each part is bounded by `C` times its input.
  have hdec : T (P - Q) x = T (1 - Q) (T P x) - T Q (T (1 - P) x) := by
    rw [show P - Q = (1 - Q) * P - Q * (1 - P) by noncomm_ring, map_sub,
      ContinuousLinearMap.sub_apply, map_mul, map_mul, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply]
  have hleft : ‖T (1 - Q) (T P x)‖ ≤ C * ‖T P x‖ := by
    calc ‖T (1 - Q) (T P x)‖ = ‖T ((1 - Q) * P) (T P x)‖ := by
            rw [map_mul, ContinuousLinearMap.mul_apply, hPP]
      _ ≤ ‖T ((1 - Q) * P)‖ * ‖T P x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖(1 - Q) * P‖ * ‖T P x‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
      _ ≤ C * ‖T P x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hright : ‖T Q (T (1 - P) x)‖ ≤ C * ‖T (1 - P) x‖ := by
    calc ‖T Q (T (1 - P) x)‖ = ‖T (Q * (1 - P)) (T (1 - P) x)‖ := by
            rw [map_mul, ContinuousLinearMap.mul_apply, hPcPc]
      _ ≤ ‖T (Q * (1 - P))‖ * ‖T (1 - P) x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Q * (1 - P)‖ * ‖T (1 - P) x‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
      _ ≤ C * ‖T (1 - P) x‖ := by
          rw [hstar]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  -- The two parts are orthogonal, and so are `Px` and `(1 - P)x`: Pythagoras on both sides.
  have horth : inner ℂ (T (1 - Q) (T P x)) (-T Q (T (1 - P) x)) = 0 := by
    rw [inner_neg_right, neg_eq_zero, inner_eq_zero_symm]
    exact inner_starProjection_complement_eq_zero hQ _ _
  have hpyth : ‖T (1 - Q) (T P x) - T Q (T (1 - P) x)‖ ^ 2 =
      ‖T (1 - Q) (T P x)‖ ^ 2 + ‖T Q (T (1 - P) x)‖ ^ 2 := by
    rw [sub_eq_add_neg, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
      norm_neg, sq, sq]
  have hsplit : ‖x‖ ^ 2 = ‖T P x‖ ^ 2 + ‖T (1 - P) x‖ ^ 2 := by
    rw [sq, sq, sq, ← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (inner_starProjection_complement_eq_zero hP x x), ← ContinuousLinearMap.add_apply,
      ← _root_.map_add, add_sub_cancel, map_one, ContinuousLinearMap.one_apply]
  change ‖T (P - Q) x‖ ≤ C * ‖x‖
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) two_ne_zero,
    hdec, hpyth, mul_pow, hsplit, mul_add]
  exact add_le_add
    (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hleft 2)
    (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hright 2)

end Compressions

open Classical in
/-- **Davis–Kahan, widened window, residual form.**  With the gap assumed for `A` only and the
window of `A'` widened by `δ/2`, only the compressions of `A - A'` between the band and the
complement of the widened band enter: the Sylvester bound in both directions with separation
`δ/2`, and the larger of the two directed leakages bounds the difference of the projectors. -/
theorem norm_specProj_sub_le_widened_residual {A A' : 𝕄} (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    {m c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hgap : HasGap hA m c δ) :
    ‖specProj hA (Metric.closedBall m c) - specProj hA' (Metric.closedBall m (c + δ / 2))‖
      ≤ 2 * max
          ‖(1 - specProj hA' (Metric.closedBall m (c + δ / 2))) * (A - A')
              * specProj hA (Metric.closedBall m c)‖
          ‖(1 - specProj hA (Metric.closedBall m c)) * (A - A')
              * specProj hA' (Metric.closedBall m (c + δ / 2))‖ / δ := by
  have hδ2 : 0 < δ / 2 := by linarith
  set M₁ := ‖(1 - specProj hA' (Metric.closedBall m (c + δ / 2))) * (A - A')
      * specProj hA (Metric.closedBall m c)‖ with hM₁
  set M₂ := ‖(1 - specProj hA (Metric.closedBall m c)) * (A - A')
      * specProj hA' (Metric.closedBall m (c + δ / 2))‖ with hM₂
  have heq : 2 * max M₁ M₂ / δ = max M₁ M₂ / (δ / 2) := by field_simp
  rw [heq]
  -- `A` within `c`, `A'` beyond `c + δ/2`
  have h₁ : ‖(1 - specProj hA' (Metric.closedBall m (c + δ / 2)))
      * specProj hA (Metric.closedBall m c)‖ ≤ M₁ / (δ / 2) :=
    norm_one_sub_specProj_mul_specProj_le (m := m) hA hA' hc hδ2
      (fun i h ↦ by simpa [Real.dist_eq] using h)
      (fun i h ↦ by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, not_le] at h
        exact h.le)
  -- `A'` within `c + δ/2`, `A` beyond `c + δ`
  have h₂ : ‖(1 - specProj hA (Metric.closedBall m c))
      * specProj hA' (Metric.closedBall m (c + δ / 2))‖ ≤ M₂ / (δ / 2) := by
    rw [hM₂, norm_compression_sub_comm _ A A']
    exact norm_one_sub_specProj_mul_specProj_le (m := m) (c := c + δ / 2) hA' hA
      (by positivity) hδ2
      (fun i h ↦ by simpa [Real.dist_eq] using h)
      (fun i h ↦ by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, not_le] at h
        rcases hgap i with h' | h'
        · exact absurd h' (not_le.mpr h)
        · linarith)
  exact (norm_sub_le_max_of_isStarProjection (isStarProjection_specProj hA _)
    (isStarProjection_specProj hA' _)).trans (_root_.max_le
      (h₁.trans (div_le_div_of_nonneg_right (le_max_left _ _) hδ2.le))
      (h₂.trans (div_le_div_of_nonneg_right (le_max_right _ _) hδ2.le)))

open Classical in
/-- **Davis–Kahan, widened window.**  With the gap assumed for `A` only, widening the window of
`A'` by `δ/2` gives `‖P_{[m-c, m+c]}(A) - P_{[m-c-δ/2, m+c+δ/2]}(A')‖ ≤ 2 ‖A - A'‖ / δ`: the
residual form, whose two compressions of `A - A'` are at most `‖A - A'‖` because projectors are
contractions. The proof of the unnumbered endpoint projector estimate uses it to get $\|P_t - \tilde
P_t\| < 1$. -/
theorem norm_specProj_sub_le_widened {A A' : 𝕄} (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    {m c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hgap : HasGap hA m c δ) :
    ‖specProj hA (Metric.closedBall m c) - specProj hA' (Metric.closedBall m (c + δ / 2))‖
      ≤ 2 * ‖A - A'‖ / δ :=
  (norm_specProj_sub_le_widened_residual hA hA' hc hδ hgap).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (_root_.max_le (norm_leak_le_norm (isStarProjection_specProj hA _)
          (isStarProjection_specProj hA' _) _)
        (norm_leak_le_norm (isStarProjection_specProj hA' _)
          (isStarProjection_specProj hA _) _))
      (by norm_num)) hδ.le)

open Classical in
/-- The spectral projector $P_{[m-c, m+c]}(A)$ onto `[m - c, m + c]` (§2.2), as a map on all
matrices. It is `0` off the Hermitian matrices; every use passes a Hermitian matrix. -/
noncomputable def windowProj (m c : ℝ) (A : 𝕄) : 𝕄 :=
  if h : A.IsHermitian then specProj h (Metric.closedBall m c) else 0

end UnitaryProducts
