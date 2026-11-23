/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic

/-!
# Regulated functions: closure properties

Restrictions, sums, differences, products, adjoints, and constant multiples of regulated functions
are regulated, and so are constants, continuous functions, and functions that are constant between
finitely many times. The paper uses these facts without comment, as when the proof of Theorem 2.2
says that `U†RV` agrees with a regulated function.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A regulated function is regulated on every subinterval. -/
theorem IsRegulated.mono {F : ℝ → 𝕄} {a b c e : ℝ}
    (hF : IsRegulated F a b) (hac : a ≤ c) (heb : e ≤ b) : IsRegulated F c e :=
  ⟨fun t ht ↦ hF.1 t ⟨hac.trans ht.1, ht.2.trans_le heb⟩,
    fun t ht ↦ hF.2 t ⟨hac.trans_lt ht.1, ht.2.trans heb⟩⟩

/-- A constant function is regulated. -/
theorem isRegulated_const (A : 𝕄) (a b : ℝ) : IsRegulated (fun _ ↦ A) a b :=
  ⟨fun _ _ ↦ ⟨A, tendsto_const_nhds⟩, fun _ _ ↦ ⟨A, tendsto_const_nhds⟩⟩

/-- A function continuous on a closed interval is regulated. -/
theorem ContinuousOn.isRegulated {F : ℝ → 𝕄} {a b : ℝ}
    (hF : ContinuousOn F (Icc a b)) : IsRegulated F a b := by
  constructor
  · intro t ht
    refine ⟨F t, (hF t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Icc_mem_nhdsGT ht.2) fun x hx ↦ ⟨ht.1.trans hx.1, hx.2⟩
  · intro t ht
    refine ⟨F t, (hF t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin ?_⟩
    exact mem_of_superset (Icc_mem_nhdsLT ht.1) fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩

/-- If `F` and `G` are regulated and `f` is continuous, then `t ↦ f(F(t), G(t))` is regulated:
continuous operations preserve one-sided limits. -/
theorem IsRegulated.map₂ {F G : ℝ → 𝕄} {a b : ℝ} (hF : IsRegulated F a b)
    (hG : IsRegulated G a b) (f : 𝕄 × 𝕄 → 𝕄) (hf : Continuous f) :
    IsRegulated (fun t ↦ f (F t, G t)) a b :=
  ⟨fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
      ((hF.1 t ht).choose_spec.prodMk_nhds (hG.1 t ht).choose_spec)⟩,
    fun t ht ↦ ⟨_, hf.continuousAt.tendsto.comp
      ((hF.2 t ht).choose_spec.prodMk_nhds (hG.2 t ht).choose_spec)⟩⟩

/-- The sum of two regulated functions is regulated. -/
theorem IsRegulated.add {F G : ℝ → 𝕄} {a b : ℝ} (hF : IsRegulated F a b)
    (hG : IsRegulated G a b) : IsRegulated (fun t ↦ F t + G t) a b :=
  hF.map₂ hG (fun p ↦ p.1 + p.2) (continuous_fst.add continuous_snd)

/-- The difference of two regulated functions is regulated. -/
theorem IsRegulated.sub {F G : ℝ → 𝕄} {a b : ℝ} (hF : IsRegulated F a b)
    (hG : IsRegulated G a b) : IsRegulated (fun t ↦ F t - G t) a b :=
  hF.map₂ hG (fun p ↦ p.1 - p.2) (continuous_fst.sub continuous_snd)

/-- The product of two regulated functions is regulated. -/
theorem IsRegulated.mul {F G : ℝ → 𝕄} {a b : ℝ} (hF : IsRegulated F a b)
    (hG : IsRegulated G a b) : IsRegulated (fun t ↦ F t * G t) a b :=
  hF.map₂ hG (fun p ↦ p.1 * p.2) (continuous_fst.mul continuous_snd)

/-- The adjoint of a regulated function is regulated. -/
theorem IsRegulated.adjoint {F : ℝ → 𝕄} {a b : ℝ} (hF : IsRegulated F a b) :
    IsRegulated (fun t ↦ (F t)†) a b :=
  hF.map₂ hF (fun p ↦ p.1†) continuous_fst.star

/-- A constant real or complex multiple of a regulated function is regulated. -/
theorem IsRegulated.const_smul {R : Type*} [SMul R 𝕄] [ContinuousConstSMul R 𝕄] {F : ℝ → 𝕄}
    {a b : ℝ} (c : R) (hF : IsRegulated F a b) : IsRegulated (fun t ↦ c • F t) a b :=
  hF.map₂ hF (fun p ↦ c • p.1) (continuous_fst.const_smul c)

/-- A function equal to `Aⱼ` for `tⱼ < x < tⱼ₊₁` is regulated; its values at the times `tⱼ` are
immaterial. -/
theorem isRegulated_of_piecewise_constant (H : ℝ → 𝕄) (t : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ)
    (hpiece : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), H x = A j) :
    IsRegulated H (t 0) (t n) := by
  -- A property that holds at index `0` and fails at index `m` fails for the first time somewhere.
  have first_failure : ∀ (P : ℕ → Prop) (m : ℕ), P 0 → ¬ P m →
      ∃ j < m, P j ∧ ¬ P (j + 1) := by
    intro P m h0 hm
    induction m with
    | zero => exact absurd h0 hm
    | succ m ih =>
      by_cases h : P m
      · exact ⟨m, m.lt_succ_self, h, hm⟩
      · obtain ⟨j, hj, hp⟩ := ih h
        exact ⟨j, hj.trans m.lt_succ_self, hp⟩
  constructor
  · -- Right limit at `x`: with `tⱼ ≤ x < tⱼ₊₁`, `H = Aⱼ` just to the right of `x`.
    intro x hx
    obtain ⟨j, hj, hlo, hhi⟩ :=
      first_failure (fun j ↦ t j ≤ x) n hx.1 (not_le.mpr hx.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (not_le.mp hhi)).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact (hpiece j hj y ⟨hlo.trans_lt hy, hyb⟩).symm
  · -- Left limit at `x`: with `tⱼ < x ≤ tⱼ₊₁`, `H = Aⱼ` just to the left of `x`.
    intro x hx
    obtain ⟨j, hj, hlo, hhi⟩ :=
      first_failure (fun j ↦ t j < x) n hx.1 (not_lt.mpr hx.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hlo).filter_mono nhdsWithin_le_nhds] with y hy hya
    exact (hpiece j hj y ⟨hya, hy.trans_le (not_lt.mp hhi)⟩).symm

end RoundedClocks
