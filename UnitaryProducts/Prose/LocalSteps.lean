/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Comparison.SharpInT

/-!
# Standalone steps of the paper's prose arguments

## Declarations

- `exists_piecewise_recursive_evolution_from`
- `exists_piecewise_recursive_evolution`
- `frameOp_change_split`
- `frameOp_split_norm_bound`
- `sharp_evolution_endpoint`
- `sharp_unit_step_exponentials`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Complex Set MeasureTheory Filter
open UnitaryProducts.Paper UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ



/-- Section 4.1, proof of the periodic-corrector bounds: split the change in the frame
multiplier into its argument change and its operator change, before bounding each norm. -/
theorem frameOp_change_split (Ω Ω' D D' : 𝕄) :
    ‖frameOp Ω' D' - frameOp Ω D‖ ≤
      ‖frameOp Ω' (D' - D)‖ +
      ‖(positiveFrameSeries (adL Ω') - positiveFrameSeries (adL Ω)) D‖ := by
  have he : frameOp Ω' D' - frameOp Ω D = frameOp Ω' (D' - D) +
      (positiveFrameSeries (adL Ω') - positiveFrameSeries (adL Ω)) D := by
    rw [frameOp_sub]
    simp only [frameOp, ContinuousLinearMap.sub_apply]
    abel
  rw [he]
  exact norm_add_le _ _

/-- Section 4.2, sharpness example: the evolution endpoint is `exp(-i(T/3)Z)`. -/
theorem sharp_evolution_endpoint {T : ℝ} (hT : 0 < T)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / T)) U 0 T) :
    U T = evol (Matrix.diagonal ![(1 : ℂ), -1]) (T / 3) := by
  obtain ⟨hUc, hU0, -, S, hS, hUd⟩ := hU
  have hV := localSteps_hasDerivAt_sharpEvolution hT.ne'
  have heq := UnitaryProducts.evolution_eq_of_solves_off_countable (T := T) S ∅ hS
    countable_empty (fun t _ ↦ localSteps_isHermitian_sharpFamily (t / T)) hUc
    (fun t _ ↦ (hV t).continuousAt.continuousWithinAt) hU0
    (by simp [UnitaryProducts.evol_zero])
    (fun t ht htS ↦ hUd t (Ioo_subset_Icc_self ht) htS)
    (fun t _ _ ↦ (hV t).hasDerivWithinAt) ⟨hT.le, le_rfl⟩
  rw [heq]
  congr 1
  field_simp

/-- Section 4.2, sharpness display: at unit steps the product has both displayed phase
forms, and the half-step-processed endpoint has phase `T/3-1/2`. Here the positive integer
`N` is the paper's `T`. -/
theorem sharp_unit_step_exponentials {N : ℕ} (hN : 0 < N)
    {U : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsEvolution (fun t ↦ sharpFamily (t / N)) U 0 N) :
    (unitProduct sharpFamily N).1 = evol (Matrix.diagonal ![(1 : ℂ), -1])
      (∑ j ∈ Finset.range N, ((j : ℝ) / N)^2) ∧
    (unitProduct sharpFamily N).1 = evol (Matrix.diagonal ![(1 : ℂ), -1])
      (((N : ℝ) - 1) * (2 * N - 1) / (6 * N)) ∧
    evol (sharpFamily 1) (-(1 / 2)) * U N * evol (sharpFamily 0) (1 / 2) =
      evol (Matrix.diagonal ![(1 : ℂ), -1]) ((N : ℝ) / 3 - 1 / 2) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hprod : (unitProduct sharpFamily N).1 =
      evol (Matrix.diagonal ![(1 : ℂ), -1])
        (∑ j ∈ Finset.range N, ((j : ℝ) / N)^2) := by
    simpa only [div_self hn, one_smul, one_mul, unitProduct] using
      localSteps_pieceProduct_sharpFamily (N : ℝ) N N
  refine ⟨hprod, ?_, ?_⟩
  · rw [hprod, sum_sq_div_eq hN]
    congr 1
    field_simp
    ring
  · rw [sharp_evolution_endpoint (by exact_mod_cast hN) hU]
    have h1 : evol (sharpFamily 1) (-(1 / 2)) =
        evol (Matrix.diagonal ![(1 : ℂ), -1]) (-(1 / 2)) := by
      rw [sharpFamily, localSteps_evol_smul_sharp, one_pow, mul_one]
    have h0 : evol (sharpFamily 0) (1 / 2) = 1 := by
      rw [sharpFamily, localSteps_evol_smul_sharp, zero_pow two_ne_zero, mul_zero, evol_zero]
    rw [h1, h0, mul_one, ← evol_add]
    congr 1
    ring

/-- Section 2.1, piecewise-constant recursion: the joined curve has the displayed formula
on every closed cell, is continuous and unitary, ends at the product, and solves the equation
away from precisely the partition nodes. The initial time is translated to zero. -/
theorem exists_piecewise_recursive_evolution {H : ℝ → 𝕄} {τ : ℕ → ℝ} {G : ℕ → 𝕄}
    (hτ : ∀ j, 0 < τ j) (n : ℕ) (hG : ∀ j < n, (G j).IsHermitian)
    (hp : ∀ j < n, ∀ t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)), H t = G j) :
    ∃ U : ℝ → 𝕄, Continuous U ∧ U 0 = 1 ∧
      (∀ t, star (U t) * U t = 1) ∧ U (switchTime τ n) = pieceProduct τ G n ∧
      (∀ j < n, ∀ t ∈ Icc (switchTime τ j) (switchTime τ (j + 1)),
        U t = evol (G j) (t - switchTime τ j) * U (switchTime τ j)) ∧
      (∀ t ∈ Icc 0 (switchTime τ n),
        (∀ j ≤ n, t ≠ switchTime τ j) → HasDerivAt U (-I • (H t * U t)) t) := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ ↦ 1, continuous_const, rfl, ?_, rfl, ?_, ?_⟩
    · intro t; simp
    · intro j hj; omega
    · intro t ht hn
      exact False.elim (hn 0 le_rfl (le_antisymm ht.2 (by simpa using ht.1)))
  | succ n ih =>
    obtain ⟨U, hUc, hU0, hUu, hUn, hrec, hd⟩ :=
      ih (fun j hj ↦ hG j (Nat.lt_succ_of_lt hj))
        (fun j hj ↦ hp j (Nat.lt_succ_of_lt hj))
    let c := switchTime τ n
    let e := switchTime τ (n + 1)
    have hc0 : 0 ≤ c := by
      simpa only [switchTime_zero] using switchTime_mono (fun j ↦ (hτ j).le) (Nat.zero_le n)
    have hce : c < e := by dsimp [c, e]; rw [switchTime_succ]; exact lt_add_of_pos_right _ (hτ n)
    let W : ℝ → 𝕄 := fun t ↦ evol (G n) (t - c) * U c
    have hWd : ∀ t, HasDerivAt W (-I • (G n * W t)) t := by
      intro t
      have hh := ((hasDerivAt_evol (G n) (t - c)).scomp t
        ((hasDerivAt_id t).sub_const c)).mul_const (U c)
      simpa only [W, Function.comp_def, id_eq, one_smul, one_mul, mul_one, smul_mul_assoc,
        mul_assoc] using hh
    have hWc : Continuous W := continuous_iff_continuousAt.mpr (fun t ↦ (hWd t).continuousAt)
    have hjoin : U c = W c := by simp only [W, sub_self, evol_zero, one_mul]
    let V : ℝ → 𝕄 := fun t ↦ if t ≤ c then U t else W t
    have hVc : Continuous V := hUc.if (fun t ht ↦ by
      have htc : t = c := by simpa only [show {x : ℝ | x ≤ c} = Iic c from rfl,
        frontier_Iic, mem_singleton_iff] using ht
      exact htc ▸ hjoin) hWc
    have hV0 : V 0 = 1 := by simpa only [V, if_pos hc0] using hU0
    have hVe : V e = pieceProduct τ G (n + 1) := by
      have hec : e - c = τ n := by dsimp [e, c]; rw [switchTime_succ, add_sub_cancel_left]
      rw [show V e = W e from if_neg (not_le.mpr hce)]
      change evol (G n) (e - c) * U c = _
      rw [hec, hUn, pieceProduct]
    refine ⟨V, hVc, hV0, ?_, hVe, ?_, ?_⟩
    · intro t
      dsimp only [V]
      split_ifs with ht
      · exact hUu t
      · dsimp only [W]
        rw [star_mul, mul_assoc, ← mul_assoc (star (evol (G n) (t - c))),
          star_evol_mul_self (hG n (Nat.lt_succ_self n)), one_mul, hUu]
    · intro j hj t ht
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | rfl
      · have hjc : switchTime τ (j + 1) ≤ c :=
          switchTime_mono (fun k ↦ (hτ k).le) hjn
        have hj0 : switchTime τ j ≤ c :=
          switchTime_mono (fun k ↦ (hτ k).le) hjn.le
        simpa only [V, if_pos (ht.2.trans hjc), if_pos hj0] using hrec j hjn t ht
      · have hVc0 : V c = U c := if_pos le_rfl
        change V t = evol (G j) (t - c) * V c
        rw [hVc0]
        by_cases htc : t ≤ c
        · have heq : t = c := le_antisymm htc ht.1
          subst t
          simp only [V, if_pos le_rfl, sub_self, evol_zero, one_mul]
        · exact if_neg htc
    · intro t ht hn
      have htc : t ≠ c := hn n (Nat.le_succ n)
      have hte : t ≠ e := hn (n + 1) le_rfl
      rcases lt_or_gt_of_ne htc with hlt | hgt
      · have hEq : V =ᶠ[𝓝 t] U := Filter.eventually_of_mem (Iio_mem_nhds hlt)
          (fun x hx ↦ if_pos (le_of_lt hx))
        have hdt := hd t ⟨ht.1, hlt.le⟩ (fun j hj ↦ hn j (hj.trans (Nat.le_succ n)))
        rw [show V t = U t from if_pos hlt.le]
        exact hdt.congr_of_eventuallyEq hEq
      · have hEq : V =ᶠ[𝓝 t] W := Filter.eventually_of_mem (Ioi_mem_nhds hgt)
          (fun x hx ↦ if_neg (not_le.mpr hx))
        have hHt : H t = G n := hp n (Nat.lt_succ_self n) t ⟨hgt, lt_of_le_of_ne ht.2 hte⟩
        rw [hHt, show V t = W t from if_neg (not_le.mpr hgt)]
        exact (hWd t).congr_of_eventuallyEq hEq


/-- Section 2.1: the piecewise-constant recursion on an interval with any initial time.
The cell endpoints are `a + switchTime τ j`. -/
theorem exists_piecewise_recursive_evolution_from {H : ℝ → 𝕄} {τ : ℕ → ℝ}
    {G : ℕ → 𝕄} (a : ℝ) (hτ : ∀ j, 0 < τ j) (n : ℕ)
    (hG : ∀ j < n, (G j).IsHermitian)
    (hp : ∀ j < n, ∀ t ∈ Ioo (a + switchTime τ j) (a + switchTime τ (j + 1)),
      H t = G j) :
    ∃ U : ℝ → 𝕄, Continuous U ∧ U a = 1 ∧
      (∀ t, star (U t) * U t = 1) ∧
      U (a + switchTime τ n) = pieceProduct τ G n ∧
      (∀ j < n, ∀ t ∈ Icc (a + switchTime τ j) (a + switchTime τ (j + 1)),
        U t = evol (G j) (t - (a + switchTime τ j)) * U (a + switchTime τ j)) ∧
      (∀ t ∈ Icc a (a + switchTime τ n),
        (∀ j ≤ n, t ≠ a + switchTime τ j) → HasDerivAt U (-I • (H t * U t)) t) := by
  obtain ⟨V, hVc, hV0, hVu, hVn, hrec, hd⟩ :=
    exists_piecewise_recursive_evolution (H := fun t ↦ H (a + t)) hτ n hG
      (fun j hj t ht ↦ hp j hj (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  refine ⟨fun t ↦ V (t - a), hVc.comp (continuous_id.sub continuous_const), ?_,
    fun t ↦ hVu (t - a), ?_, ?_, ?_⟩
  · simpa only [sub_self] using hV0
  · simpa only [add_sub_cancel_left] using hVn
  · intro j hj t ht
    have ht' : t - a ∈ Icc (switchTime τ j) (switchTime τ (j + 1)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [add_sub_cancel_left, sub_sub] using hrec j hj (t - a) ht'
  · intro t ht hn
    have ht' : t - a ∈ Icc 0 (switchTime τ n) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hnodes : ∀ j ≤ n, t - a ≠ switchTime τ j := by
      intro j hj he
      exact hn j hj (by linarith)
    have hderiv := (hd (t - a) ht' hnodes).scomp t ((hasDerivAt_id t).sub_const a)
    simpa only [Function.comp_def, add_sub_cancel, one_smul, mul_one] using hderiv

/-- Section 4.1, the second inequality of the multiplier-splitting display: the sum of
the two individual multiplier norms satisfies the stated width bound. -/
theorem frameOp_split_norm_bound [NeZero d] {Ω Ω' D D' : 𝕄} {c c' w : ℝ}
    (hw : w < 2 * Real.pi) (hwidth : ‖Ω - (c : ℂ) • 1‖ ≤ w / 2)
    (hwidth' : ‖Ω' - (c' : ℂ) • 1‖ ≤ w / 2) :
    ‖frameOp Ω' (D' - D)‖ +
      ‖(positiveFrameSeries (adL Ω') - positiveFrameSeries (adL Ω)) D‖ ≤
      frameBound w * ‖D' - D‖ + 2 * frameLip w * ‖Ω' - Ω‖ * ‖D‖ := by
  have ha : ‖adL Ω‖ ≤ w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [(norm_nonneg _).trans hwidth])
    intro E
    exact (norm_adL_apply_le Ω E (c : ℂ)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg E))
  have ha' : ‖adL Ω'‖ ≤ w := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [(norm_nonneg _).trans hwidth'])
    intro E
    exact (norm_adL_apply_le Ω' E (c' : ℂ)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg E))
  have hd : ‖adL Ω' - adL Ω‖ ≤ 2 * ‖Ω' - Ω‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro E
    have he : (adL Ω' - adL Ω) E = adL (Ω' - Ω) E := by
      simp only [ContinuousLinearMap.sub_apply, adL_apply, sub_mul, mul_sub]
      abel
    rw [he]
    simpa only [zero_smul, sub_zero] using norm_adL_apply_le (Ω' - Ω) E 0
  have hL : ‖positiveFrameSeries (adL Ω') - positiveFrameSeries (adL Ω)‖ ≤
      frameLip w * (2 * ‖Ω' - Ω‖) :=
    (norm_positiveFrameSeries_sub_le (a := adL Ω') (b := adL Ω) ha' ha hw).trans
      (mul_le_mul_of_nonneg_left hd
        (frameLip_nonneg (by linarith [(norm_nonneg _).trans hwidth])))
  apply add_le_add (norm_frameOp_le hw hwidth')
  calc
    _ ≤ ‖positiveFrameSeries (adL Ω') - positiveFrameSeries (adL Ω)‖ * ‖D‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (frameLip w * (2 * ‖Ω' - Ω‖)) * ‖D‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg D)
    _ = _ := by ring

end UnitaryProducts.Prose
