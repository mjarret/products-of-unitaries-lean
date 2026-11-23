/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Resolvent calculus

Lemma A.2 uses the segment resolvent from `1` to a unitary matrix; its inverse, derivative, and
commutation identities give the logarithm integral.
-/

@[expose] public section

open Set
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

namespace RoundedClocks.WalkLogCalculus

section Resolvent

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The resolvent $Z_u = (1 + u(V - 1))^{-1}$ of the proof of Lemma A.2, along the segment from
$1$ to $V$. `Ring.inverse` returns `0` when $1 + u(V - 1)$ is not invertible; every use proves
invertibility first. -/
def walkLogResolvent (V : A) (t : ℝ) : A := Ring.inverse (1 + t • (V - 1))

omit [CompleteSpace A] in
/-- Lemma A.2: the division-free resolvent identity, valid also at `u = 0`. -/
theorem walkLogResolvent_mul_sub (V : A) (u : ℝ)
    (hu : IsUnit (1 + u • (V - 1))) :
    u • ((V - 1) * walkLogResolvent V u) = 1 - walkLogResolvent V u := by
  have hsum : walkLogResolvent V u + u • ((V - 1) * walkLogResolvent V u) = 1 := by
    rw [show walkLogResolvent V u + u • ((V - 1) * walkLogResolvent V u) =
        (1 + u • (V - 1)) * walkLogResolvent V u by
      rw [add_mul, one_mul, smul_mul_assoc]]
    exact Ring.mul_inverse_cancel _ hu
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hsum)

/-- The inverse derivative in a form convenient for a real matrix path. -/
theorem hasDerivWithinAt_ringInverse_path {V : ℝ → A} {D : A} {s : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s) (hu : IsUnit (V s)) :
    HasDerivWithinAt (fun r ↦ Ring.inverse (V r))
      (-(Ring.inverse (V s) * D * Ring.inverse (V s))) S s := by
  obtain ⟨u, hu⟩ := hu
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u)
  rw [hu] at hi
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ← hu, Ring.inverse_unit] using hi.comp_hasDerivWithinAt s hV

/-- $\partial_s Z_u(V(s)) = -u\,Z_uV'Z_u$. -/
theorem hasDerivWithinAt_walkLogResolvent {V : ℝ → A} {D : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt (fun r ↦ walkLogResolvent (V r) t)
      (-t • (walkLogResolvent (V s) t * D * walkLogResolvent (V s) t)) S s := by
  simpa only [walkLogResolvent, mul_smul_comm, smul_mul_assoc, neg_smul] using
    hasDerivWithinAt_ringInverse_path (((hV.sub_const 1).const_smul t).const_add 1) hu

/-- The derivative of the logarithm integrand is $Z_uDZ_u$, as $u(V-1)Z_u = 1-Z_u$. -/
theorem hasDerivWithinAt_walkLogIntegrand {V : ℝ → A} {D : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V D S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt (fun r ↦ (V r - 1) * walkLogResolvent (V r) t)
      (walkLogResolvent (V s) t * D * walkLogResolvent (V s) t) S s := by
  let Z := walkLogResolvent (V s) t
  have hmul := walkLogResolvent_mul_sub (V s) t hu
  have hid : 1 - t • ((V s - 1) * Z) = Z := by
    change 1 - t • ((V s - 1) * walkLogResolvent (V s) t) = _
    rw [hmul, sub_sub_cancel]
  have hd := (hV.sub_const 1).mul (hasDerivWithinAt_walkLogResolvent hV hu)
  convert hd using 1
  change Z * D * Z = D * Z + (V s - 1) * (-t • (Z * D * Z))
  calc
    Z * D * Z = (1 - t • ((V s - 1) * Z)) * D * Z := by rw [hid]
    _ = _ := by
      simp only [add_mul, neg_mul, one_mul, smul_mul_assoc, mul_smul_comm, neg_smul,
        mul_neg,
        mul_assoc, sub_eq_add_neg]

/-- $(s, u) \mapsto Z_u(V(s))$ is jointly continuous where $1 + u(V(s) - 1)$ is invertible. -/
theorem continuousOn_walkLogResolvent {V : ℝ → A} {S : Set ℝ}
    (hV : ContinuousOn V S)
    (hu : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V s - 1))) :
    ContinuousOn (fun p : ℝ × ℝ ↦ walkLogResolvent (V p.1) p.2)
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hh : ContinuousOn (fun p : ℝ × ℝ ↦ 1 + p.2 • (V p.1 - 1))
      (S ×ˢ Icc (0 : ℝ) 1) :=
    continuousOn_const.add (continuous_snd.continuousOn.smul (hv.sub continuousOn_const))
  intro p hp
  have hi := (differentiableAt_inverse (𝕜 := ℝ) (hu p.1 hp.1 p.2 hp.2)).continuousAt
  exact hi.comp_continuousWithinAt
    (f := fun q : ℝ × ℝ ↦ 1 + q.2 • (V q.1 - 1)) (hh p hp)

/-- Differentiating the first resolvent sandwich gives the logarithm Hessian integrand. -/
theorem hasDerivWithinAt_walkLogSandwich {V D : ℝ → A} {Vd Dd : A} {s t : ℝ}
    {S : Set ℝ} (hV : HasDerivWithinAt V Vd S s)
    (hD : HasDerivWithinAt D Dd S s)
    (hu : IsUnit (1 + t • (V s - 1))) :
    HasDerivWithinAt
      (fun r ↦ walkLogResolvent (V r) t * D r * walkLogResolvent (V r) t)
      (walkLogResolvent (V s) t * Dd * walkLogResolvent (V s) t -
        t • (walkLogResolvent (V s) t * Vd * walkLogResolvent (V s) t *
          D s * walkLogResolvent (V s) t +
          walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t *
          Vd * walkLogResolvent (V s) t)) S s := by
  have hZ := hasDerivWithinAt_walkLogResolvent hV hu
  convert (hZ.mul hD).mul hZ using 1 ;
    simp only [Pi.mul_apply, add_mul, smul_mul_assoc, mul_smul_comm, neg_smul,
      neg_mul, mul_neg, smul_add, mul_assoc] ; abel

end Resolvent

/-- The integral representation in the first line of the logarithm display. -/
def walkLogIntegral {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :=
  ∫ t : ℝ in (0 : ℝ)..1, (V - 1) * walkLogResolvent V t

section CompactDifferentiation

open MeasureTheory Filter
open scoped Topology

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Differentiation on a compact rectangle supplies its own uniform majorant. -/
theorem hasDerivAt_integral_compact_rectangle {F F' : ℝ → ℝ → A} {a b s : ℝ}
    (hs : s ∈ Ioo a b)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hF' : ContinuousOn (Function.uncurry F') (Icc a b ×ˢ Icc (0 : ℝ) 1))
    (hd : ∀ x ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasDerivAt (fun x ↦ ∫ t : ℝ in (0 : ℝ)..1, F x t)
      (∫ t : ℝ in (0 : ℝ)..1, F' s t) s := by
  have hx (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (F x) (Icc (0 : ℝ) 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx, ht⟩)
  have hx' (x : ℝ) (hx : x ∈ Icc a b) : ContinuousOn (F' x) (Icc (0 : ℝ) 1) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'
  have hU : Set.uIoc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hK : Set.uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun _ ↦ C) (isOpen_Ioo.mem_nhds hs) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx0
    rw [hU]
    exact ((hx x ⟨hx0.1.le, hx0.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · exact (hK.symm ▸ hx s ⟨hs.1.le, hs.2.le⟩).intervalIntegrable
  · rw [hU]
    exact ((hx' s ⟨hs.1.le, hs.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · exact Filter.Eventually.of_forall fun t ht x hx0 ↦
      hC (x, t) ⟨⟨hx0.1.le, hx0.2.le⟩, Ioc_subset_Icc_self (hU ▸ ht)⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht x hx0 ↦
      hd x hx0 t (Ioc_subset_Icc_self (hU ▸ ht))

end CompactDifferentiation

section PathDerivatives

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The first logarithm derivative obtained by differentiating its compact integral. -/
theorem hasDerivAt_walkLogIntegral {V D : ℝ → 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (D x) x)
    (hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V x - 1))) :
    HasDerivAt (fun x ↦ walkLogIntegral (V x))
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t) s := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  apply hasDerivAt_integral_compact_rectangle
    (F := fun x t ↦ (V x - 1) * walkLogResolvent (V x) t)
    (F' := fun x t ↦ walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
    hs ((hv.sub continuousOn_const).mul hZ)
    ((hZ.mul hd').mul hZ)
  intro x hx t ht
  exact (hasDerivWithinAt_walkLogIntegrand (S := Set.univ) (hd x hx).hasDerivWithinAt
    (hu x ⟨hx.1.le, hx.2.le⟩ t ht)).hasDerivAt (by simp)

/-- The second logarithm derivative obtained from the differentiated resolvent sandwich. -/
theorem hasDerivAt_walkLogDerivativeIntegral {V D E : ℝ → 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (D x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt D (E x) x)
    (hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V x - 1))) :
    HasDerivAt
      (fun x ↦ ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * E s * walkLogResolvent (V s) t -
          (2 * t) • (walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t *
            D s * walkLogResolvent (V s) t)) s := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have he' : ContinuousOn (fun p : ℝ × ℝ ↦ E p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hE.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  apply hasDerivAt_integral_compact_rectangle
    (F := fun x t ↦ walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
    (F' := fun x t ↦ walkLogResolvent (V x) t * E x * walkLogResolvent (V x) t -
      (2 * t) • (walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t * D x *
        walkLogResolvent (V x) t))
    hs ((hZ.mul hd').mul hZ)
    (((hZ.mul he').mul hZ).sub
      ((continuousOn_const.mul continuous_snd.continuousOn).smul
        ((((hZ.mul hd').mul hZ).mul hd').mul hZ)))
  intro x hx t ht
  have hh := hasDerivWithinAt_walkLogSandwich (S := Set.univ) (hd x hx).hasDerivWithinAt
    (hdd x hx).hasDerivWithinAt (hu x ⟨hx.1.le, hx.2.le⟩ t ht)
  rw [← two_smul ℝ, smul_smul, mul_comm t 2] at hh
  exact hh.hasDerivAt (by simp)

end PathDerivatives

open Filter MeasureTheory

section CompactCalculus

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- Lemma A.2(ii), continuity under the integral: a continuous integrand on a
closed rectangle has a continuous parameter integral, including at its endpoints. -/
theorem continuousOn_integral_rectangle {F : ℝ → ℝ → A} {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun s ↦ ∫ u : ℝ in (0 : ℝ)..1, F s u) (Icc a b) := by
  by_cases hab : a ≤ b
  · let f : ℝ → ℝ → A := fun s u ↦ F (max a (min b s)) (max 0 (min 1 u))
    have hf : Continuous (Function.uncurry f) := by
      apply hF.comp_continuous (f := fun p : ℝ × ℝ ↦
        (max a (min b p.1), max 0 (min 1 p.2))) (by fun_prop)
      intro p
      exact ⟨⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩,
        ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
    have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hf 0 1
    apply hi.continuousOn.congr
    intro s hs
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    simp only [f, min_eq_right hs.2, max_eq_right hs.1,
      min_eq_right hu.2, max_eq_right hu.1]
  · simp only [Icc_eq_empty hab, continuousOn_empty]

/-- Lemma A.2(ii), endpoint differentiation: continuous interior derivatives extend
to derivatives within the closed interval. This is used for both integral derivatives. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {F G : ℝ → A} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s) {s : ℝ} (hs : s ∈ Icc a b) :
    HasDerivWithinAt F (G s) (Icc a b) s := by
  have ht : Tendsto (fun x ↦ deriv F x) (𝓝[Ioo a b] s) (𝓝 (G s)) := by
    apply ((hG s hs).mono Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hd x hx).deriv.symm
  have ht' : Tendsto (fun x ↦ fderiv ℝ F x) (𝓝[Ioo a b] s)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (G s))) := by
    simp only [← toSpanSingleton_deriv]
    exact (ContinuousLinearMap.toSpanSingletonCLE : A ≃L[ℝ] (ℝ →L[ℝ] A)).continuous
      |>.continuousAt |>.tendsto |>.comp ht
  have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo
    (fun x hx ↦ (hF x (by simpa [closure_Ioo hab.ne] using hx)).mono
      Ioo_subset_Icc_self) ht'
  rw [closure_Ioo hab.ne] at hh
  exact hh

/-- Lemma A.2(ii): two continuous derivatives obtained by integration imply `C²`
on a closed interval, using derivatives within that interval at both endpoints. -/
theorem contDiffOn_two_of_integral_derivatives {F G H : ℝ → A} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hH : ContinuousOn H (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt F (G s) s)
    (hdd : ∀ s ∈ Ioo a b, HasDerivAt G (H s) s) :
    ContDiffOn ℝ 2 F (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt F (G s) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt G (H s) (Icc a b) s) := by
  have hdw := fun (s : ℝ) (hs : s ∈ Icc a b) ↦
    hasDerivWithinAt_Icc_of_continuous_derivative hab hF hG hd hs
  have hddw := fun (s : ℝ) (hs : s ∈ Icc a b) ↦
    hasDerivWithinAt_Icc_of_continuous_derivative hab hG hH hdd hs
  have huniq := uniqueDiffOn_Icc hab
  have he : EqOn (derivWithin F (Icc a b)) G (Icc a b) :=
    fun s hs ↦ (hdw s hs).derivWithin (huniq s hs)
  have he' : EqOn (derivWithin G (Icc a b)) H (Icc a b) :=
    fun s hs ↦ (hddw s hs).derivWithin (huniq s hs)
  have hcG : ContDiffOn ℝ 1 G (Icc a b) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl, contDiffOn_succ_iff_derivWithin huniq]
    exact ⟨fun s hs ↦ (hddw s hs).differentiableWithinAt, by simp,
      contDiffOn_zero.mpr (hH.congr (fun s hs ↦ he' hs))⟩
  refine ⟨?_, hdw, hddw⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by rfl, contDiffOn_succ_iff_derivWithin huniq]
  exact ⟨fun s hs ↦ (hdw s hs).differentiableWithinAt, by simp,
    hcG.congr (fun s hs ↦ he hs)⟩

end CompactCalculus

section IntegralDerivatives

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Lemma A.2(ii), the first derivative integral following (log-integral), before
multiplication by `i` and addition of the fixed scalar center. -/
def walkLogFirstIntegral (V D : A) : A :=
  ∫ u : ℝ in (0 : ℝ)..1, walkLogResolvent V u * D * walkLogResolvent V u

/-- Lemma A.2(ii), the second derivative integral following (log-integral), before
multiplication by `i`; the two inverse derivatives give the coefficient `2u`. -/
def walkLogSecondIntegral (V D E : A) : A :=
  ∫ u : ℝ in (0 : ℝ)..1, walkLogResolvent V u * E * walkLogResolvent V u -
    (2 * u) • (walkLogResolvent V u * D * walkLogResolvent V u * D * walkLogResolvent V u)

/-- Lemma A.2(ii): the second differentiated integrand is jointly continuous on
the entire parameter rectangle, including its boundary. -/
theorem continuousOn_walkLogSecondIntegrand {V D E : ℝ → A} {S : Set ℝ}
    (hV : ContinuousOn V S) (hD : ContinuousOn D S) (hE : ContinuousOn E S)
    (hu : ∀ s ∈ S, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ContinuousOn (fun p : ℝ × ℝ ↦
      walkLogResolvent (V p.1) p.2 * E p.1 * walkLogResolvent (V p.1) p.2 -
        (2 * p.2) • (walkLogResolvent (V p.1) p.2 * D p.1 *
          walkLogResolvent (V p.1) p.2 * D p.1 * walkLogResolvent (V p.1) p.2))
      (S ×ˢ Icc (0 : ℝ) 1) := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hD' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hE' : ContinuousOn (fun p : ℝ × ℝ ↦ E p.1) (S ×ˢ Icc (0 : ℝ) 1) :=
    hE.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  exact ((hZ.mul hE').mul hZ).sub
    ((continuousOn_const.mul continuous_snd.continuousOn).smul
      ((((hZ.mul hD').mul hZ).mul hD').mul hZ))

end IntegralDerivatives

section IntegralCalculus

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Lemma A.2(ii): differentiating under the compact resolvent integral twice
produces continuous first and second derivatives and a `C²` integral on a closed
interval. The formulas use derivatives within the interval at both endpoints. -/
theorem walkLogIntegral_contDiffOn_two {V D E : ℝ → 𝕄} {a b : ℝ}
    (hab : a < b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt V (D s) s)
    (hdd : ∀ s ∈ Ioo a b, HasDerivAt D (E s) s)
    (hu : ∀ s ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    ContDiffOn ℝ 2 (fun s ↦ walkLogIntegral (V s)) (Icc a b) ∧
      ContinuousOn (fun s ↦ walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogIntegral (V t))
        (walkLogFirstIntegral (V s) (D s)) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogFirstIntegral (V t) (D t))
        (walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) s) := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hFint : ContinuousOn
      (fun p : ℝ × ℝ ↦ (V p.1 - 1) * walkLogResolvent (V p.1) p.2)
      (Icc a b ×ˢ Icc (0 : ℝ) 1) := (hv.sub continuousOn_const).mul hZ
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hF := continuousOn_integral_rectangle
    (F := fun s u ↦ (V s - 1) * walkLogResolvent (V s) u)
    hFint
  have hG := continuousOn_integral_rectangle
    (F := fun s u ↦ walkLogResolvent (V s) u * D s * walkLogResolvent (V s) u)
    ((hZ.mul hd').mul hZ)
  have hH := continuousOn_integral_rectangle
    (F := fun s u ↦ walkLogResolvent (V s) u * E s * walkLogResolvent (V s) u -
      (2 * u) • (walkLogResolvent (V s) u * D s * walkLogResolvent (V s) u *
        D s * walkLogResolvent (V s) u))
    (continuousOn_walkLogSecondIntegrand hV hD hE hu)
  obtain ⟨hc, hdw, hddw⟩ := contDiffOn_two_of_integral_derivatives hab hF hG hH
    (fun s hs ↦ hasDerivAt_walkLogIntegral hs hV hD hd hu)
    (fun s hs ↦ hasDerivAt_walkLogDerivativeIntegral hs hV hD hE hd hdd hu)
  exact ⟨hc, hH, hdw, hddw⟩

/-- Lemma A.2(ii): the only smoothness hypothesis needed for twice differentiating
the resolvent integral is `C²` of the walk; its within-derivatives supply `D` and `E`. -/
theorem walkLogIntegral_contDiffOn_of_contDiffOn {V : ℝ → 𝕄} {a b : ℝ}
    (hab : a < b) (hc : ContDiffOn ℝ 2 V (Icc a b))
    (hu : ∀ s ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V s - 1))) :
    let D := derivWithin V (Icc a b)
    let E := derivWithin D (Icc a b)
    ContDiffOn ℝ 2 (fun s ↦ walkLogIntegral (V s)) (Icc a b) ∧
      ContinuousOn (fun s ↦ walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogIntegral (V t))
        (walkLogFirstIntegral (V s) (D s)) (Icc a b) s) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt (fun t ↦ walkLogFirstIntegral (V t) (D t))
        (walkLogSecondIntegral (V s) (D s) (E s)) (Icc a b) s) := by
  intro D E
  have huniq := uniqueDiffOn_Icc hab
  have hD : ContDiffOn ℝ 1 D (Icc a b) := hc.derivWithin huniq (by norm_num)
  have hE : ContinuousOn E (Icc a b) := hD.continuousOn_derivWithin huniq (by norm_num)
  apply walkLogIntegral_contDiffOn_two hab hc.continuousOn hD.continuousOn hE _ _ hu
  · intro s hs
    exact ((hc.differentiableOn (by norm_num) s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  · intro s hs
    exact ((hD.differentiableOn (by norm_num) s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)

end IntegralCalculus

end RoundedClocks.WalkLogCalculus
