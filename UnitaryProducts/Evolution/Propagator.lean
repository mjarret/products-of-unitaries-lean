/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Evolution.Simulation

/-!
# Propagators of continuous Hamiltonians

## Declarations

- `eqOn`
- `eq_mul`
- `exists_solvesSchrodinger`
- `exists_solvesSchrodinger_step`
- `solvesSchrodinger_glue`
- `solvesSchrodinger_self`
-/

@[expose] public section

namespace UnitaryProducts

open scoped Matrix.Norms.L2Operator
open Complex Set

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- On a degenerate interval every function solves the equation. -/
theorem solvesSchrodinger_self (K V : ℝ → 𝕄) (a : ℝ) : SolvesSchrodinger K V a a := fun s _ ↦
  HasFDerivWithinAt.of_subsingleton (by rw [Icc_self]; exact subsingleton_singleton)

/-- **Gluing two solutions.**  A solution on `[a, b]` and a solution on `[b, c]` with matching
value at `b` combine into a solution on `[a, c]`. -/
theorem solvesSchrodinger_glue {K U V : ℝ → 𝕄} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hU : SolvesSchrodinger K U a b) (hV : SolvesSchrodinger K V b c) (hVb : V b = U b) :
    SolvesSchrodinger K (fun t ↦ if t ≤ b then U t else V t) a c := by
  set W : ℝ → 𝕄 := fun t ↦ if t ≤ b then U t else V t with hW
  have hWU : ∀ t ∈ Icc a b, W t = U t := fun t ht ↦ if_pos ht.2
  have hWV : ∀ t ∈ Icc b c, W t = V t := fun t ht ↦ by
    by_cases hle : t ≤ b
    · simp only [hW, le_antisymm hle ht.1, hVb, ite_self]
    · simp only [hW, if_neg hle]
  have hleft : ∀ s ∈ Icc a b, HasDerivWithinAt W (-I • (K s * W s)) (Icc a b) s :=
    fun s hs ↦ by rw [hWU s hs]; exact (hU s hs).congr hWU (hWU s hs)
  have hright : ∀ s ∈ Icc b c, HasDerivWithinAt W (-I • (K s * W s)) (Icc b c) s :=
    fun s hs ↦ by rw [hWV s hs]; exact (hV s hs).congr hWV (hWV s hs)
  intro s hs
  rcases lt_trichotomy s b with hlt | heq | hgt
  · exact (hleft s ⟨hs.1, hlt.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, hlt, fun t ht ↦ ⟨ht.2.1, ht.1.le⟩⟩)
  · subst heq
    have := (hleft s ⟨hs.1, le_rfl⟩).union (hright s ⟨le_rfl, hbc⟩)
    rwa [Icc_union_Icc_eq_Icc hab hbc] at this
  · exact (hright s ⟨hgt.le, hs.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Ioi b, isOpen_Ioi, hgt, fun t ht ↦ ⟨ht.1.le, ht.2.2⟩⟩)

/-- **Local existence** on a short subinterval, from Picard–Lindelöf: the vector field
`(t, Y) ↦ -i K(t) Y` is `M`-Lipschitz in `Y` and bounded on balls. -/
theorem exists_solvesSchrodinger_step {K : ℝ → 𝕄} {a b M : ℝ}
    (hK : ContinuousOn K (Icc a b)) (hM : ∀ t ∈ Icc a b, ‖K t‖ ≤ M)
    {c e : ℝ} (hac : a ≤ c) (hce : c ≤ e) (heb : e ≤ b) (hlen : (2 * M + 2) * (e - c) ≤ 1) (X : 𝕄) :
    ∃ V : ℝ → 𝕄, SolvesSchrodinger K V c e ∧ V c = X := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c ⟨hac, hce.trans heb⟩)
  have hsub : Icc c e ⊆ Icc a b := Icc_subset_Icc hac heb
  have hR0 : (0 : ℝ) ≤ ‖X‖ + 1 := by positivity
  have hL0 : (0 : ℝ) ≤ M * (2 * ‖X‖ + 1) := by positivity
  have hPL : IsPicardLindelof (fun t (Y : 𝕄) ↦ -I • (K t * Y))
      (tmin := c) (tmax := e) ⟨c, ⟨le_rfl, hce⟩⟩ X ⟨_, hR0⟩ 0 ⟨_, hL0⟩ ⟨M, hM0⟩ := by
    constructor
    · intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ ↦ ?_
      simp only [dist_eq_norm, ← smul_sub, ← mul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul,
        NNReal.coe_mk]
      exact norm_mul_le_of_le (hM t (hsub ht)) le_rfl
    · exact fun x _ ↦ ((hK.mono hsub).mul continuousOn_const).const_smul _
    · intro t ht Y hY
      have hYn : ‖Y‖ ≤ 2 * ‖X‖ + 1 := by
        linarith [(norm_sub_norm_le Y X).trans (mem_closedBall_iff_norm.mp hY),
          NNReal.coe_mk (‖X‖ + 1) hR0]
      simp only [norm_smul, norm_neg, Complex.norm_I, one_mul, NNReal.coe_mk]
      exact norm_mul_le_of_le (hM t (hsub ht)) hYn
    · simp only [NNReal.coe_mk, NNReal.coe_zero, sub_zero, sub_self]
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ e - c)]
      have h2 : (2 * M + 2) * (e - c) * (‖X‖ + 1) ≤ 1 * (‖X‖ + 1) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      have h3 : 0 ≤ (e - c) * (M + 2 * ‖X‖ + 2) := mul_nonneg (by linarith) (by positivity)
      linarith
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, fun s hs ↦ hα s hs, hα0⟩

/-- **Existence.**  A Hamiltonian continuous on `[a, b]` has a propagator starting at `1`. -/
theorem exists_solvesSchrodinger {K : ℝ → 𝕄} {a b : ℝ}
    (hK : ContinuousOn K (Icc a b)) :
    ∃ V : ℝ → 𝕄, SolvesSchrodinger K V a b ∧ V a = 1 := by
  by_cases hab : a ≤ b
  swap
  · exact ⟨fun _ ↦ 1, fun t ht ↦ (hab (ht.1.trans ht.2)).elim, rfl⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a ⟨le_rfl, hab⟩)
  set s : ℝ := 1 / (2 * M + 2) with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hstep : (2 * M + 2) * s = 1 := by rw [hs]; exact mul_one_div_cancel (by positivity)
  -- solve on `[a, min b (a + n s)]` by induction on `n`
  have key : ∀ n : ℕ, ∃ V : ℝ → 𝕄, SolvesSchrodinger K V a (min b (a + n * s)) ∧ V a = 1 := by
    intro n
    induction n with
    | zero => exact ⟨fun _ ↦ 1, by simpa only [Nat.cast_zero, zero_mul, add_zero, min_eq_right hab]
        using solvesSchrodinger_self K (fun _ ↦ 1) a, rfl⟩
    | succ n ih =>
      obtain ⟨V, hV, hV1⟩ := ih
      have hn0 : (0 : ℝ) ≤ (n : ℝ) * s := by positivity
      have hac : a ≤ min b (a + (n : ℝ) * s) := le_min hab (by linarith)
      have hce : min b (a + (n : ℝ) * s) ≤ min b (a + ((n : ℕ) + 1 : ℕ) * s) :=
        min_le_min le_rfl (by push_cast; linarith [hs0.le])
      have heb : min b (a + ((n : ℕ) + 1 : ℕ) * s) ≤ b := min_le_left _ _
      have hdiff : min b (a + ((n : ℕ) + 1 : ℕ) * s) - min b (a + (n : ℝ) * s) ≤ s := by
        rw [sub_le_iff_le_add', ← min_add_add_right]
        exact min_le_min (le_add_of_nonneg_right hs0.le) (by push_cast; linarith)
      have hlen : (2 * M + 2) * (min b (a + ((n : ℕ) + 1 : ℕ) * s) - min b (a + (n : ℝ) * s))
          ≤ 1 := by
        rw [← hstep]; exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      obtain ⟨W, hW, hWc⟩ := exists_solvesSchrodinger_step hK hM hac hce heb hlen
        (V (min b (a + (n : ℝ) * s)))
      refine ⟨fun t ↦ if t ≤ min b (a + (n : ℝ) * s) then V t else W t, ?_, ?_⟩
      · have hglue := solvesSchrodinger_glue hac hce hV hW hWc
        push_cast at hglue ⊢
        exact hglue
      · simp only [if_pos hac, hV1]
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / s)
  have hbn : min b (a + (n : ℝ) * s) = b := min_eq_left (by linarith [(div_le_iff₀ hs0).mp hn])
  simpa only [hbn] using key n

/-- **Uniqueness.**  Two solutions for a Hamiltonian continuous on `[a, b]` that agree at `a`
agree on `[a, b]`. -/
theorem SolvesSchrodinger.eqOn {K U V : ℝ → 𝕄} {a b : ℝ} (hK : ContinuousOn K (Icc a b))
    (hU : SolvesSchrodinger K U a b) (hV : SolvesSchrodinger K V a b) (hUV : U a = V a) :
    EqOn U V (Icc a b) := by
  rcases le_or_gt a b with hab | hba
  · obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM a ⟨le_rfl, hab⟩)
    refine ODE_solution_unique_of_mem_Icc_right (v := fun t Y ↦ -I • (K t * Y))
      (s := fun _ ↦ univ) (K := ⟨M, hM0⟩) (fun t ht ↦ ?_)
      (fun t ht ↦ (hU t ht).continuousWithinAt) (fun t ht ↦ ?_) (fun _ _ ↦ mem_univ _)
      (fun t ht ↦ (hV t ht).continuousWithinAt) (fun t ht ↦ ?_) (fun _ _ ↦ mem_univ _) hUV
    · refine LipschitzOnWith.of_dist_le_mul fun x _ y _ ↦ ?_
      simp only [dist_eq_norm, ← smul_sub, ← mul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul,
        NNReal.coe_mk]
      exact norm_mul_le_of_le (hM t (Ico_subset_Icc_self ht)) le_rfl
    · exact (hU t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · exact (hV t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.mpr hba)

/-- Every solution is the propagator `V` (with `V a = 1`) applied to its initial value. -/
theorem SolvesSchrodinger.eq_mul {K U V : ℝ → 𝕄} {a b : ℝ} (hK : ContinuousOn K (Icc a b))
    (hU : SolvesSchrodinger K U a b) (hV : SolvesSchrodinger K V a b) (hV0 : V a = 1) :
    ∀ t ∈ Icc a b, U t = V t * U a := by
  have hVU : SolvesSchrodinger K (fun t ↦ V t * U a) a b := fun t ht ↦ by
    simpa [mul_assoc, smul_mul_assoc] using (hV t ht).mul_const (U a)
  exact hU.eqOn hK hVU (by simp [hV0])

end UnitaryProducts
