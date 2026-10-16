/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.ThmComparison

/-!
# The rotating-frame comparison

The frame primitive is constructed by integration. The proof integrates the
rotating path and its product with the primitive. The single-piece instance
`V S V†` of Theorem 2.2 identifies the same comparison identity.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts.Paper

noncomputable section
namespace UnitaryProducts.PaperProof

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Equation `eq:frame-integral`: the derivative representative of the frame integral. -/
def frameIntegrand (K G V : ℝ → 𝕄) (t : ℝ) : 𝕄 :=
  star (V t) * (K t - G t) * V t

/-- Equation `eq:frame-integral`: the frame primitive, with lower endpoint `a`. -/
def frameIntegral (K G V : ℝ → 𝕄) (a t : ℝ) : 𝕄 :=
  ∫ u in a..t, frameIntegrand K G V u

/-- The continuous unitary factors preserve regulatedness of the integrand. -/
theorem frameIntegrand_regulated {K G V : ℝ → 𝕄} {a b : ℝ}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hVc : ContinuousOn V (Icc a b)) : IsRegulated (frameIntegrand K G V) a b :=
  Prose.regulated_mul (Prose.regulated_mul (Prose.regulated_of_continuousOn hVc.star)
    (Prose.regulated_sub hKr hGr)) (Prose.regulated_of_continuousOn hVc)

/-- Regulated families are continuous away from a countable subset of the interior
of any compact interval. This translates the zero-based result. -/
theorem regulated_continuousAt_off_countable {H : ℝ → 𝕄} {a b : ℝ}
    (hab : a ≤ b) (hH : IsRegulated H a b) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ t ∈ Ioo a b, t ∉ E → ContinuousAt H t := by
  let F := fun t ↦ H (t + a)
  let D := {t ∈ Icc 0 (b - a) | ¬ ContinuousWithinAt F (Icc 0 (b - a)) t}
  have hD : D.Countable := hH.translate_to_zero.countable_not_continuousWithinAt
    (sub_nonneg.mpr hab)
  refine ⟨(fun t ↦ t + a) '' D, hD.image _, fun t ht hn ↦ ?_⟩
  have ht' : t - a ∈ Ioo 0 (b - a) := ⟨sub_pos.mpr ht.1, by linarith [ht.2]⟩
  have hnot : t - a ∉ D := fun h ↦ hn ⟨t - a, h, sub_add_cancel t a⟩
  have hc : ContinuousWithinAt F (Icc 0 (b - a)) (t - a) :=
    not_not.mp (fun h ↦ hnot ⟨Ioo_subset_Icc_self ht', h⟩)
  have hc' := hc.continuousAt (Icc_mem_nhds ht'.1 ht'.2)
  have hshift : ContinuousAt (fun x : ℝ ↦ x - a) t := continuousAt_id.sub continuousAt_const
  simpa only [F, Function.comp_def, sub_add_cancel] using ContinuousAt.comp (f := fun x : ℝ ↦ x -
    a) (x := t) hc' hshift

/-- The frame integral is continuous, starts at zero, and has the displayed
derivative outside a countable exceptional set. -/
theorem frameIntegral_regular {K G V : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b)
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hVc : ContinuousOn V (Icc a b)) :
    ContinuousOn (frameIntegral K G V a) (Icc a b) ∧ frameIntegral K G V a a = 0 ∧
      ∃ E : Set ℝ, E.Countable ∧ ∀ t ∈ Ioo a b, t ∉ E →
        HasDerivAt (frameIntegral K G V a) (frameIntegrand K G V t) t := by
  have hr := frameIntegrand_regulated hKr hGr hVc
  have hi := hr.intervalIntegrable_on hab
  obtain ⟨E, hE, hc⟩ := regulated_continuousAt_off_countable hab hr
  refine ⟨(intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc).mono
    Icc_subset_uIcc, by simp [frameIntegral], E, hE, fun t ht hn ↦ ?_⟩
  exact intervalIntegral.integral_hasDerivAt_right
    (hi.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioo_subset_Icc_self ht))))
    ⟨Ioc a b, Ioc_mem_nhds ht.1 ht.2, hi.1.aestronglyMeasurable⟩ (hc t ht hn)


/-- the rotating-frame estimate: the rotating path satisfies `Q' = i Q S'`. -/
theorem frame_path_hasDerivAt {K G U V : ℝ → 𝕄} {t : ℝ}
    (hK : (K t).IsHermitian)
    (hU : HasDerivAt U (-I • (K t * U t)) t)
    (hV : HasDerivAt V (-I • (G t * V t)) t)
    (hVV : V t * star (V t) = 1) :
    HasDerivAt (fun u ↦ star (U u) * V u)
      (I • (star (U t) * V t * frameIntegrand K G V t)) t := by
  have hcancel : star (U t) * V t * frameIntegrand K G V t =
      star (U t) * (K t - G t) * V t := by
    simp only [frameIntegrand, mul_assoc]
    rw [← mul_assoc (V t) (star (V t)), hVV, one_mul]
  rw [hcancel]
  convert (hasDerivAt_evolution_adjoint hK hU).mul hV using 1
  simp only [mul_smul_comm, smul_mul_assoc, neg_smul, mul_sub, sub_mul,
    smul_sub, mul_assoc, mul_neg]
  abel

/-- the rotating-frame estimate: the product rule for the rotating path and its primitive. -/
theorem frame_product_hasDerivAt {Q S : ℝ → 𝕄} {B : 𝕄} {t : ℝ}
    (hQ : HasDerivAt Q (I • (Q t * B)) t) (hS : HasDerivAt S B t) :
    HasDerivAt (fun u ↦ Q u * S u) (Q t * B + I • (Q t * B * S t)) t := by
  simpa only [Pi.mul_apply, smul_mul_assoc, add_comm] using hQ.mul hS

/-- The first line of the rotating-frame estimate, the fundamental theorem for `Q`.
This is the zero-correction instance of Theorem 2.2. -/
theorem frame_first_identity {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    star (U b) * V b - 1 =
      I • ∫ t in a..b, star (U t) * V t * frameIntegrand K G V t := by
  have hp : Monotone (fun j : ℕ ↦ if j = 0 then a else b) := by
    intro i j hij
    dsimp only
    split_ifs <;> first | exact le_rfl | exact hab | omega
  have hid := comparison_with_jumps 0 (fun j ↦ if j = 0 then a else b) hp
    (by simp) (by simp) K G U V (fun t ↦ K t - G t) (fun _ _ ↦ 0)
    ∅ countable_empty hU hV
    ((hKr.intervalIntegrable_on hab).sub (hGr.intervalIntegrable_on hab))
    (fun _ _ ↦ continuousOn_const)
    (by intro _ _ t _ _; simpa using hasDerivAt_const t (0 : 𝕄))
  simp only [smul_zero, mul_zero, zero_mul, sub_zero, add_zero,
    Finset.sum_const_zero] at hid
  rw [← intervalIntegral.integral_smul]
  refine hid.trans (intervalIntegral.integral_congr fun t ht ↦ ?_)
  have hVV : V t * star (V t) = 1 := Matrix.mem_unitaryGroup_iff.mp
    (Matrix.mem_unitaryGroup_iff'.mpr (hV.2.2.1 t (by simpa [uIcc_of_le hab] using ht)))
  simp only [frameIntegrand, mul_assoc]
  rw [← mul_assoc (V t) (star (V t)), hVV, one_mul]

/-- The second line of the rotating-frame estimate: integrate the product rule for `Q S`.
The exceptional sets for both evolutions and the primitive are countable. -/
theorem frame_product_integral {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    (∫ t in a..b, star (U t) * V t * frameIntegrand K G V t) +
      I • (∫ t in a..b, star (U t) * V t * frameIntegrand K G V t *
        frameIntegral K G V a t) = star (U b) * V b * frameIntegral K G V a b := by
  obtain ⟨hSc, hSa, ES, hES, hSd⟩ := frameIntegral_regular hab hKr hGr hV.1
  obtain ⟨EU, hEU, hUd⟩ := hU.2.2.2
  obtain ⟨EV, hEV, hVd⟩ := hV.2.2.2
  let Q := fun t ↦ star (U t) * V t
  let B := frameIntegrand K G V
  let S := frameIntegral K G V a
  have hQB : IsRegulated (fun t ↦ Q t * B t) a b := Prose.regulated_mul
    (Prose.regulated_of_continuousOn (hU.1.star.mul hV.1))
    (frameIntegrand_regulated hKr hGr hV.1)
  have hQBi := hQB.intervalIntegrable_on hab
  have hQBSi :=
    (Prose.regulated_mul hQB (Prose.regulated_of_continuousOn hSc)).intervalIntegrable_on hab
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t ↦ Q t * S t) (fun t ↦ Q t * B t + I • (Q t * B t * S t))
    hab ((hEU.union hEV).union hES) ((hU.1.star.mul hV.1).mul hSc) (fun t ht ↦ by
      have hu := (hUd t (Ioo_subset_Icc_self ht.1)
        (fun h ↦ ht.2 (Or.inl (Or.inl h)))).hasDerivAt (Icc_mem_nhds ht.1.1 ht.1.2)
      have hv := (hVd t (Ioo_subset_Icc_self ht.1)
        (fun h ↦ ht.2 (Or.inl (Or.inr h)))).hasDerivAt (Icc_mem_nhds ht.1.1 ht.1.2)
      have hk := isHermitian_of_unitary_solution hu
        (Filter.eventually_of_mem (Icc_mem_nhds ht.1.1 ht.1.2) hU.2.2.1)
      have hVV := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr
        (hV.2.2.1 t (Ioo_subset_Icc_self ht.1)))
      exact frame_product_hasDerivAt (frame_path_hasDerivAt hk hu hv hVV)
        (hSd t ht.1 (fun h ↦ ht.2 (Or.inr h))))
    (hQBi.add (hQBSi.smul I))
  have hISi : IntervalIntegrable (fun t ↦ I • (Q t * B t * S t)) volume a b := by
    simpa only [Pi.smul_apply] using hQBSi.smul I
  rw [intervalIntegral.integral_add hQBi hISi,
    intervalIntegral.integral_smul] at hFTC
  simpa only [Q, B, S, hSa, mul_zero, sub_zero] using hFTC

/-- the rotating-frame estimate: the two displayed integrations, followed by scalar algebra.
The same identity is the one-piece comparison `frame_comparison_from_piece`. -/
theorem frame_comparison_identity {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    star (U b) * V b - 1 =
      (∫ t in a..b, star (U t) * V t * frameIntegrand K G V t * frameIntegral K G V a t) +
        I • (star (U b) * V b * frameIntegral K G V a b) := by
  rw [frame_first_identity hab hKr hGr hU hV]
  have hparts := congrArg (fun X : 𝕄 ↦ I • X)
    (frame_product_integral hab hKr hGr hU hV)
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul] at hparts
  linear_combination (norm := abel) hparts

/-- Norm steps in the proof of the rotating-frame estimate: the rotating-frame bound, including the
norm of the unintegrated remainder between the two displayed bounds.
`frameIntegrand` is the regulated representative of `S'`, justified by
`frameIntegral_regular`; changing it on the countable exceptional set leaves
both integrals unchanged. No differentiability assumptions are added. -/
theorem frame_bound_representative {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    |‖V b - U b‖ - ‖frameIntegral K G V a b‖| ≤
      ‖∫ t in a..b, star (U t) * V t * frameIntegrand K G V t * frameIntegral K G V a t‖ ∧
    ‖∫ t in a..b, star (U t) * V t * frameIntegrand K G V t * frameIntegral K G V a t‖ ≤
      ∫ t in a..b, ‖frameIntegrand K G V t * frameIntegral K G V a t‖ := by
  have mem (W : 𝕄) := (Matrix.mem_unitaryGroup_iff' (A := W)).mpr
  have hUb := mem _ (hU.2.2.1 b ⟨hab, le_rfl⟩)
  have hVb := mem _ (hV.2.2.1 b ⟨hab, le_rfl⟩)
  have hnorm := Prose.unitary_difference_norm ⟨U b, hUb⟩ (V b)
  have hlast : ‖I • (star (U b) * V b * frameIntegral K G V a b)‖ =
      ‖frameIntegral K G V a b‖ := by
    rw [norm_smul, Complex.norm_I, one_mul, mul_assoc,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hUb),
      CStarRing.norm_mem_unitary_mul _ hVb]
  constructor
  · have hrev := abs_norm_sub_norm_le (star (U b) * V b - 1)
      (I • (star (U b) * V b * frameIntegral K G V a b))
    rw [← hnorm, hlast, frame_comparison_identity hab hKr hGr hU hV, add_sub_cancel_right] at hrev
    exact hrev
  · refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq
      (intervalIntegral.integral_congr fun t ht ↦ ?_)
    rw [uIcc_of_le hab] at ht
    rw [mul_assoc, mul_assoc, CStarRing.norm_mem_unitary_mul _
      (Unitary.star_mem (mem _ (hU.2.2.1 t ht))),
      CStarRing.norm_mem_unitary_mul _ (mem _ (hV.2.2.1 t ht))]

/-- The actual derivative of the frame integral agrees almost everywhere with
its regulated representative, including in interval integrals. -/
theorem frameIntegral_deriv_ae {a b : ℝ} (hab : a ≤ b) {K G V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hVc : ContinuousOn V (Icc a b)) :
    ∀ᵐ t ∂volume, t ∈ uIoc a b →
      deriv (frameIntegral K G V a) t = frameIntegrand K G V t := by
  obtain ⟨_, _, E, hE, hSd⟩ := frameIntegral_regular hab hKr hGr hVc
  have hex : (E ∪ {a, b}).Countable := hE.union (Set.toFinite _).countable
  filter_upwards [hex.ae_notMem volume] with t ht hti
  rw [uIoc_of_le hab] at hti
  have htb : t ≠ b := fun h ↦ ht (Or.inr (by simp [h]))
  exact (hSd t ⟨hti.1, lt_of_le_of_ne hti.2 htb⟩ (fun h ↦ ht (Or.inl h))).deriv

/-- General rotating-frame bound used by the rotating-frame estimate, with `S'` in both
integrals. Its proof integrates `Q` and `Q S`, then uses the reverse triangle
inequality and unitary invariance of the norm. -/
theorem rotating_frame_bound {a b : ℝ} (hab : a ≤ b) {K G U V : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b) :
    |‖V b - U b‖ - ‖frameIntegral K G V a b‖| ≤
      ‖∫ t in a..b, star (U t) * V t * deriv (frameIntegral K G V a) t * frameIntegral K G V a t‖ ∧
    ‖∫ t in a..b, star (U t) * V t * deriv (frameIntegral K G V a) t * frameIntegral K G V a t‖ ≤
      ∫ t in a..b, ‖deriv (frameIntegral K G V a) t * frameIntegral K G V a t‖ := by
  have hae := frameIntegral_deriv_ae hab hKr hGr hV.1
  have hleft : (∫ t in a..b, star (U t) * V t * deriv (frameIntegral K G V a) t *
      frameIntegral K G V a t) =
      ∫ t in a..b, star (U t) * V t * frameIntegrand K G V t * frameIntegral K G V a t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with t ht hti
    rw [ht hti]
  have hright : (∫ t in a..b, ‖deriv (frameIntegral K G V a) t * frameIntegral K G V a t‖) =
      ∫ t in a..b, ‖frameIntegrand K G V t * frameIntegral K G V a t‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with t ht hti
    rw [ht hti]
  rw [hleft, hright]
  exact frame_bound_representative hab hKr hGr hU hV

/-- Multiplication by a scalar phase preserves distances. This is the endpoint
norm step in equation `eq:centre`. -/
theorem phase_distance (θ : ℝ) (X Y : 𝕄) :
    ‖Complex.exp ((θ : ℂ) * I) • X - Complex.exp ((θ : ℂ) * I) • Y‖ = ‖X - Y‖ := by
  rw [← smul_sub, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- A scalar phase cancels from conjugation, so centering leaves the frame
unchanged, as stated immediately after equation `eq:centre`. -/
theorem phase_conjugation (θ : ℝ) (V X : 𝕄) :
    star (Complex.exp ((θ : ℂ) * I) • V) * X *
      (Complex.exp ((θ : ℂ) * I) • V) = star V * X * V := by
  simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have he : star (Complex.exp ((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  rw [mul_comm, he, one_smul]

/-- The displayed centered frame integrand: scalar phases cancel, and
conjugating a scalar identity leaves the same scalar identity. -/
theorem centered_frame_integrand (K G V : 𝕄) (f g θ : ℝ)
    (hV : star V * V = 1) :
    star (Complex.exp ((θ : ℂ) * I) • V) *
        ((K - (f : ℂ) • (1 : 𝕄)) - (G - (g : ℂ) • (1 : 𝕄))) *
        (Complex.exp ((θ : ℂ) * I) • V) =
      star V * (K - G) * V - ((f - g : ℝ) : ℂ) • (1 : 𝕄) := by
  rw [phase_conjugation]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    hV, Complex.ofReal_sub, sub_smul]
  abel

/-- Subtracting a scalar derivative from a generator multiplies its evolution by
the integrated scalar phase. Countably many exceptions include the endpoints. -/
theorem scalar_phase_evolution {a b : ℝ} {H U : ℝ → 𝕄} {φ f : ℝ → ℝ}
    (hU : IsEvolution H U a b) (hφc : ContinuousOn φ (Icc a b)) (hφa : φ a = 0)
    (E : Set ℝ) (hE : E.Countable)
    (hφd : ∀ t ∈ Ioo a b, t ∉ E → HasDerivAt φ (f t) t) :
    IsEvolution (fun t ↦ H t - (f t : ℂ) • (1 : 𝕄))
      (fun t ↦ Complex.exp ((φ t : ℂ) * I) • U t) a b := by
  have hphase : ContinuousOn (fun t ↦ Complex.exp ((φ t : ℂ) * I)) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn ((Complex.continuous_ofReal.comp_continuousOn
      hφc).mul continuousOn_const)
  refine ⟨hphase.smul hU.1, by simp [hφa, hU.2.1], ?_, ?_⟩
  · intro t ht
    simpa only [mul_one, hU.2.2.1 t ht] using phase_conjugation (φ t) (U t) (1 : 𝕄)
  obtain ⟨EU, hEU, hUd⟩ := hU.2.2.2
  refine ⟨E ∪ EU ∪ {a, b}, (hE.union hEU).union (Set.toFinite _).countable, fun t ht hn ↦ ?_⟩
  have hta : t ≠ a := fun h ↦ hn (Or.inr (by simp [h]))
  have htb : t ≠ b := fun h ↦ hn (Or.inr (by simp [h]))
  have hti : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
  have hpd := ((hφd t hti (fun h ↦ hn (Or.inl (Or.inl h)))).ofReal_comp.mul_const I).cexp
  have hud := (hUd t ht (fun h ↦ hn (Or.inl (Or.inr h)))).hasDerivAt
    (Icc_mem_nhds hti.1 hti.2)
  apply HasDerivAt.hasDerivWithinAt
  convert hpd.smul hud using 1
  simp only [sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, smul_sub, smul_smul]
  module

end UnitaryProducts.PaperProof
