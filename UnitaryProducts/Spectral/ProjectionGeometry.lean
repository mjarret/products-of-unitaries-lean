/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.SinTheta

/-!
# Directed distances between orthogonal projections

## Declarations

- `directed_le_of_orthogonal_inf_eq_bot`
- `norm_sub_le_directed_of_lt_one`
-/

@[expose] public section

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High

The subspace lemma below is adapted from Lean Pool's
LeanPool.UnitaryProducts.ForTauCeti.Analysis.InnerProductSpace.Projection.Gap,
`Submodule.directedProjectionGap_le_of_inf_orthogonal_eq_bot`.
Adapted to Mathlib v4.28.0; polynomial side goals use explicit monotonicity.
-/

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace UnitaryProducts
namespace ProjectionGeometry
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- If $U^\perp \cap V = 0$, then $\|P_{U^\perp} P_V\| \le \|P_{V^\perp} P_U\|$: the reverse
directed distance between the subspaces is at most the forward one. -/
theorem directed_le_of_orthogonal_inf_eq_bot (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : (U.orthogonal) ⊓ V = ⊥) :
    ‖(U.orthogonal).starProjection ∘L V.starProjection‖ ≤ ‖(V.orthogonal).starProjection ∘L
      U.starProjection‖ := by
  set t := ‖(V.orthogonal).starProjection ∘L U.starProjection‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    simpa only [one_mul, ContinuousLinearMap.comp_apply] using
      ((V.orthogonal).norm_starProjection_apply_le _).trans (U.norm_starProjection_apply_le x)
  have hk0 : (0 : ℝ) ≤ 1 - t ^ 2 :=
    sub_nonneg.mpr (by simpa using pow_le_pow_left₀ ht0 ht1 2)
  set c := Real.sqrt (1 - t ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hk0
  -- Pythagoras turns the directed bound into a lower bound for `P_V` on `U`.
  have hstep1 : ∀ u ∈ U, c * ‖u‖ ≤ ‖V.starProjection u‖ := by
    intro u hu
    have hperp : ‖(V.orthogonal).starProjection u‖ ≤ t * ‖u‖ := by
      simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hu]
        using ((V.orthogonal).starProjection ∘L U.starProjection).le_opNorm u
    have hpy : ‖u‖ ^ 2 = ‖V.starProjection u‖ ^ 2 + ‖(V.orthogonal).starProjection u‖ ^ 2 :=
      V.norm_sq_eq_add_norm_sq_starProjection u
    have hsq : (c * ‖u‖) ^ 2 ≤ ‖V.starProjection u‖ ^ 2 := by
      rw [mul_pow, hcsq]
      linarith [pow_le_pow_left₀ (norm_nonneg _) hperp 2]
    calc c * ‖u‖ = Real.sqrt ((c * ‖u‖) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg u))).symm
      _ ≤ Real.sqrt (‖V.starProjection u‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖V.starProjection u‖ := Real.sqrt_sq (norm_nonneg _)
  -- The same constant propagates to the image `P_V '' U` by Cauchy--Schwarz.
  set S : Submodule 𝕜 E := U.map (V.starProjection : E →ₗ[𝕜] E) with hS
  set T : Set E := {x : E | c * ‖x‖ ≤ ‖U.starProjection x‖} with hT
  have hTclosed : IsClosed T :=
    isClosed_le (continuous_const.mul continuous_norm)
      (continuous_norm.comp U.starProjection.continuous)
  have hST : (S : Set E) ⊆ T := by
    rintro x ⟨u, hu, rfl⟩
    change c * ‖V.starProjection u‖ ≤ ‖U.starProjection (V.starProjection u)‖
    rcases eq_or_ne (V.starProjection u) 0 with h0 | h0
    · rw [h0]; simp
    have hunorm : 0 < ‖u‖ := by
      refine norm_pos_iff.mpr fun huz ↦ h0 ?_
      rw [huz, map_zero]
    have hzero : ⟪V.starProjection u, u - V.starProjection u⟫_𝕜 = 0 :=
      inner_eq_zero_symm.mp
        (V.starProjection_inner_eq_zero u _ (V.starProjection_apply_mem u))
    have hself : ⟪V.starProjection u, u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      have hsub := inner_sub_right (𝕜 := 𝕜) (V.starProjection u) u (V.starProjection u)
      rw [hzero] at hsub
      exact sub_eq_zero.mp hsub.symm
    have hmove : ⟪U.starProjection (V.starProjection u), u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      rw [Submodule.inner_starProjection_left_eq_right U,
        Submodule.starProjection_eq_self_iff.mpr hu, hself]
    have hcs : ‖V.starProjection u‖ * ‖V.starProjection u‖
        ≤ ‖U.starProjection (V.starProjection u)‖ * ‖u‖ := by
      have hbound := norm_inner_le_norm (𝕜 := 𝕜)
        (U.starProjection (V.starProjection u)) u
      have hnormself : ‖⟪V.starProjection u, V.starProjection u⟫_𝕜‖
          = ‖V.starProjection u‖ * ‖V.starProjection u‖ :=
        (inner_self_re_eq_norm _).symm.trans (inner_self_eq_norm_mul_norm _)
      rwa [hmove, hnormself] at hbound
    have hlow : c * ‖u‖ * ‖V.starProjection u‖
        ≤ ‖V.starProjection u‖ * ‖V.starProjection u‖ :=
      mul_le_mul_of_nonneg_right (hstep1 u hu) (norm_nonneg _)
    exact le_of_mul_le_mul_right
      (by convert hlow.trans hcs using 1 ; ring) hunorm
  -- `P_V '' U` is dense in `V` precisely because `(U.orthogonal) ⊓ V = ⊥`.
  have hVle : V ≤ (S.orthogonal.orthogonal) := by
    intro v hv
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy' := (Submodule.mem_orthogonal S y).mp hy
    have hyV : V.starProjection y = 0 := by
      have hmem : V.starProjection y ∈ (U.orthogonal) ⊓ V :=
        ⟨(Submodule.mem_orthogonal _ _).mpr fun u hu ↦ by
          rw [← Submodule.inner_starProjection_left_eq_right]
          exact hy' _ (Submodule.mem_map_of_mem hu), V.starProjection_apply_mem y⟩
      rw [h] at hmem
      simpa using hmem
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal V y).mp
      ((Submodule.starProjection_apply_eq_zero_iff V).mp hyV) v hv)
  have hstep3 : ∀ v ∈ V, c * ‖v‖ ≤ ‖U.starProjection v‖ := by
    intro v hv
    have hmem : v ∈ closure (S : Set E) := by
      have hvv := hVle hv
      rwa [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hvv
    exact hTclosed.closure_subset_iff.mpr hST hmem
  -- Reversing Pythagoras on `V` is the reverse directed estimate.
  change ‖(U.orthogonal).starProjection ∘L V.starProjection‖ ≤ t
  refine ContinuousLinearMap.opNorm_le_bound _ ht0 fun x ↦ ?_
  rw [ContinuousLinearMap.comp_apply]
  have hv : V.starProjection x ∈ V := V.starProjection_apply_mem x
  have hpy : ‖V.starProjection x‖ ^ 2
      = ‖U.starProjection (V.starProjection x)‖ ^ 2
        + ‖(U.orthogonal).starProjection (V.starProjection x)‖ ^ 2 :=
    U.norm_sq_eq_add_norm_sq_starProjection _
  have hlow := hstep3 _ hv
  have hvx : ‖V.starProjection x‖ ≤ ‖x‖ := V.norm_starProjection_apply_le x
  have hsq : ‖(U.orthogonal).starProjection (V.starProjection x)‖ ^ 2 ≤ (t * ‖x‖) ^ 2 := by
    have hc2 := pow_le_pow_left₀ (mul_nonneg hc0 (norm_nonneg _)) hlow 2
    have hmono := pow_le_pow_left₀ (mul_nonneg ht0 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hvx ht0) 2
    rw [mul_pow, hcsq] at hc2
    linarith
  calc ‖(U.orthogonal).starProjection (V.starProjection x)‖
      = Real.sqrt (‖(U.orthogonal).starProjection (V.starProjection x)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((t * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = t * ‖x‖ := Real.sqrt_sq (mul_nonneg ht0 (norm_nonneg x))

end ProjectionGeometry
/-- Below distance one, the two directed projection errors agree: for orthogonal projectors with
$\|P - Q\| < 1$, $\|P - Q\| \le \|(1 - Q)P\|$. In the proof of the unnumbered endpoint projector
estimate
(`endpoint_projector_bound`) it replaces the paper's equal-rank identity
$\|P_t - \tilde P_t\| = \|(1 - \tilde P_t)P_t\|$. -/
theorem norm_sub_le_directed_of_lt_one {d : ℕ}
    {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hclose : ‖P - Q‖ < 1) :
    ‖P - Q‖ ≤ ‖(1 - Q) * P‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  have hPT : IsStarProjection (T P) := ⟨hP.isIdempotentElem.map T, hP.isSelfAdjoint.map T⟩
  have hQT : IsStarProjection (T Q) := ⟨hQ.isIdempotentElem.map T, hQ.isSelfAdjoint.map T⟩
  obtain ⟨hU, heP⟩ := isStarProjection_iff_eq_starProjection_range.mp hPT
  obtain ⟨hV, heQ⟩ := isStarProjection_iff_eq_starProjection_range.mp hQT
  let U := (T P).toLinearMap.range
  let V := (T Q).toLinearMap.range
  -- `‖P - Q‖ < 1` forces `ran(P)ᗮ ⊓ ran(Q) = ⊥`: there `(P - Q)x = -x`.
  have hi : U.orthogonal ⊓ V = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hPx : T P x = 0 := by
      rw [heP]; exact (Submodule.starProjection_apply_eq_zero_iff U).mpr hx.1
    have hQx : T Q x = x := by
      rw [heQ]
      exact Submodule.starProjection_eq_self_iff.mpr hx.2
    have hnorm : ‖x‖ ≤ ‖P - Q‖ * ‖x‖ := by
      have hv := (T (P-Q)).le_opNorm x
      rw [Matrix.l2_opNorm_toEuclideanCLM, map_sub, ContinuousLinearMap.sub_apply,
        hPx, hQx, zero_sub, norm_neg] at hv
      exact hv
    have hx0 : x = 0 := by
      by_contra hn
      have ht := mul_lt_mul_of_pos_right hclose (norm_pos_iff.mpr hn)
      rw [one_mul] at ht
      exact (not_lt_of_ge hnorm) ht
    exact hx0
  -- So `‖(1 - P)Q‖ ≤ ‖(1 - Q)P‖`, and `‖P - Q‖` is at most the larger of the two.
  have hrev := ProjectionGeometry.directed_le_of_orthogonal_inf_eq_bot U V hi
  rw [Submodule.starProjection_orthogonal', Submodule.starProjection_orthogonal',
    ← heP, ← heQ] at hrev
  have ht₁ : (1 - T P).comp (T Q) = T ((1-P)*Q) := by rw [map_mul, map_sub, map_one]; rfl
  have ht₂ : (1 - T Q).comp (T P) = T ((1-Q)*P) := by rw [map_mul, map_sub, map_one]; rfl
  rw [ht₁, ht₂, Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM] at hrev
  exact (norm_sub_le_max_of_isStarProjection hP hQ).trans (max_le le_rfl hrev)

end UnitaryProducts
