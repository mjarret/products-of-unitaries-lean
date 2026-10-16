/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Evolution.Simulation

/-!
# Cutting an interval at finitely many points

## Declarations

- `exists_switchTime_of_finset`
-/

@[expose] public section

namespace UnitaryProducts
open Set Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

/-- **Cutting `[0, T]` at finitely many points.**  A finite set `S` of points at most `T`,
containing `0` and `T`, cuts `[0, T]` into `n` consecutive pieces of positive length, with
`n + 1 ≤ #S`, whose open interiors contain no point of `S`.  Remove `T`, cut `[0, T']` at the
next largest point `T'`, and append the piece `(T', T)`. -/
theorem exists_switchTime_of_finset {S : Finset ℝ} {T : ℝ} (hT : 0 ≤ T) (h0 : 0 ∈ S)
    (hTS : T ∈ S) (hS : ∀ x ∈ S, x ≤ T) :
    ∃ (n : ℕ) (τ : ℕ → ℝ), (∀ j, 0 < τ j) ∧ switchTime τ n = T ∧
      (∀ j < n, ∀ x ∈ S, x ∉ Ioo (switchTime τ j) (switchTime τ (j + 1))) ∧ n + 1 ≤ #S := by
  obtain ⟨N, hN⟩ : ∃ N, #S = N := ⟨_, rfl⟩
  induction N generalizing S T with
  | zero => exact absurd hN (Finset.card_ne_zero_of_mem h0)
  | succ N ih =>
    rcases hT.eq_or_lt with rfl | hT
    · exact ⟨0, fun _ ↦ 1, fun _ ↦ one_pos, switchTime_zero _,
        fun j hj ↦ absurd hj (Nat.not_lt_zero j), by omega⟩
    -- the largest breakpoint `T'` below `T`
    set S' := S.erase T
    have h0' : (0 : ℝ) ∈ S' := Finset.mem_erase.mpr ⟨hT.ne, h0⟩
    set T' := S'.max' ⟨0, h0'⟩
    have hT'S : T' ∈ S' := S'.max'_mem _
    have hT'T : T' < T :=
      lt_of_le_of_ne (hS T' (Finset.mem_of_mem_erase hT'S)) (Finset.ne_of_mem_erase hT'S)
    have hS'card : #S' = N := by rw [Finset.card_erase_of_mem hTS, hN, Nat.add_sub_cancel]
    obtain ⟨n, τ, hτ, hsw, hgap, hcard⟩ := ih (S'.le_max' 0 h0') h0' hT'S
      (fun x hx ↦ S'.le_max' x hx) hS'card
    -- append the last piece `(T', T)`
    let τ' : ℕ → ℝ := fun j ↦ if j < n then τ j else T - T'
    have hτ' : ∀ j, 0 < τ' j := fun j ↦ by
      simp only [τ']; split_ifs; exacts [hτ j, sub_pos.mpr hT'T]
    have hsw' : ∀ j ≤ n, switchTime τ' j = switchTime τ j := fun j hj ↦
      Finset.sum_congr rfl fun i hi ↦ if_pos (by rw [Finset.mem_range] at hi; omega)
    have hlast : τ' n = T - T' := if_neg (lt_irrefl n)
    have hmono := switchTime_mono fun j ↦ (hτ j).le
    refine ⟨n + 1, τ', hτ', ?_, fun j hj x hx hxj ↦ ?_, by rw [hN]; omega⟩
    · rw [switchTime_succ, hsw' n le_rfl, hsw, hlast]; ring
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · -- a preceding piece: `x < T`, so `x` is a preceding breakpoint
      rw [hsw' j hj.le, hsw' (j + 1) hj] at hxj
      have hxT : x < T := hxj.2.trans_le (((hmono hj).trans_eq hsw).trans hT'T.le)
      exact hgap j hj x (Finset.mem_erase.mpr ⟨hxT.ne, hx⟩) hxj
    · -- the new piece `(T', T)`
      rw [hj, switchTime_succ, hsw' n le_rfl, hsw, hlast] at hxj
      exact not_le.mpr hxj.1
        (S'.le_max' x (Finset.mem_erase.mpr ⟨(by linarith [hxj.2] : x < T).ne, hx⟩))

end UnitaryProducts
