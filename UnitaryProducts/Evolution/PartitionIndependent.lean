/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import UnitaryProducts.Evolution.Regulated

/-!
# Evolutions of piecewise-constant families

## Declarations

- `exists_piecewise_evolution`
-/

@[expose] public section

namespace UnitaryProducts
open scoped Matrix.Norms.L2Operator Topology
open Complex Set
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The evolution of a piecewise-constant family (the recursion after the existence-and-uniqueness
claim of §2.1): if $H = G_j$
on each open piece $(t_j, t_{j+1})$, $j < n$, of a partition with positive durations, there is a
continuous $U$ with $U(0) = 1$, $U(t_n)$ the product (2.5), and $iU' = HU$ on $[0, t_n]$ outside a
finite set (the switch times). $H$ is unconstrained at the switch times. -/
theorem exists_piecewise_evolution {H : ℝ → 𝕄} {τ : ℕ → ℝ} {G : ℕ → 𝕄}
    (hτ : ∀ j, 0 < τ j) (n : ℕ)
    (hp : ∀ j < n, ∀ t ∈ Ioo (switchTime τ j) (switchTime τ (j + 1)), H t = G j) :
    ∃ (U : ℝ → 𝕄) (S : Finset ℝ), Continuous U ∧ U 0 = 1 ∧
      U (switchTime τ n) = pieceProduct τ G n ∧
      (∀ t ∈ Icc 0 (switchTime τ n), t ∉ S → HasDerivAt U (-I • (H t * U t)) t) := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ ↦ 1, {0}, continuous_const, rfl, rfl, ?_⟩
    intro t ht hS
    have ht0 : t = 0 := le_antisymm (by simpa only [switchTime_zero] using ht.2) ht.1
    exact False.elim (hS (by simp only [ht0, Finset.mem_singleton]))
  | succ n ih =>
    -- Step 1: the evolution U on the first n pieces, by induction.
    obtain ⟨U, S, hUc, hU0, hUn, hd⟩ := ih (fun j hj ↦ hp j (Nat.lt_succ_of_lt hj))
    let c := switchTime τ n
    let e := switchTime τ (n + 1)
    have hc0 : 0 ≤ c := by
      simpa only [switchTime_zero] using switchTime_mono (fun j ↦ (hτ j).le) (Nat.zero_le n)
    have hce : c < e := by dsimp [c, e]; rw [switchTime_succ]; exact lt_add_of_pos_right _ (hτ n)
    -- Step 2 (paper, the recursion): on the new piece, W(t) = e^{-i(t - t_n)G_n} U(t_n).
    let W : ℝ → 𝕄 := fun t ↦ evol (G n) (t - c) * U c
    have hWd : ∀ t, HasDerivAt W (-I • (G n * W t)) t := fun t ↦ by
      simpa only [W, Function.comp_def, id_eq, one_smul, one_mul, mul_one, smul_mul_assoc,
        mul_assoc] using ((hasDerivAt_evol (G n) (t - c)).scomp t
          ((hasDerivAt_id t).sub_const c)).mul_const (U c)
    have hWc : Continuous W := continuous_iff_continuousAt.mpr (fun t ↦ (hWd t).continuousAt)
    have hjoin : U c = W c := by simp only [W, sub_self, evol_zero, one_mul]
    -- Step 3: glue U and W at t_n; the glued curve is continuous and ends at the product (2.5).
    let V : ℝ → 𝕄 := fun t ↦ if t ≤ c then U t else W t
    have hVc : Continuous V := hUc.if (fun t ht ↦ by
      have htc : t = c := by simpa only [show {x : ℝ | x ≤ c} = Iic c from rfl,
        frontier_Iic, mem_singleton_iff] using ht
      exact htc ▸ hjoin) hWc
    have hV0 : V 0 = 1 := by simpa only [V, if_pos hc0] using hU0
    have hVe : V e = pieceProduct τ G (n + 1) := by
      have hec : e - c = τ n := by dsimp [e, c]; rw [switchTime_succ, add_sub_cancel_left]
      rw [show V e = W e from if_neg (not_le.mpr hce)]
      change evol (G n) (e - c) * U c = _; rw [hec, hUn, pieceProduct]
    -- Step 4: away from t_n, t_{n+1} and the initial exceptional set, V agrees near t with U or W.
    refine ⟨V, insert c (insert e S), hVc, hV0, hVe, ?_⟩
    intro t ht hS
    have htc : t ≠ c := fun h ↦ hS (h ▸ Finset.mem_insert_self _ _)
    have hte : t ≠ e := fun h ↦ hS (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    rcases lt_or_gt_of_ne htc with hlt | hgt
    · rw [show V t = U t from if_pos hlt.le]
      exact (hd t ⟨ht.1, hlt.le⟩ fun hh ↦ hS (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hh))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Iio_mem_nhds hlt) fun x hx ↦ if_pos (le_of_lt hx))
    · rw [hp n (Nat.lt_succ_self n) t ⟨hgt, lt_of_le_of_ne ht.2 hte⟩,
        show V t = W t from if_neg (not_le.mpr hgt)]
      exact (hWd t).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioi_mem_nhds hgt) fun x hx ↦ if_neg (not_le.mpr hx))

end UnitaryProducts
