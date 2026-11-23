/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-!
# Evolutions of piecewise-constant Hamiltonians

This is the recursion immediately preceding equation (2.4) in the manuscript.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)
open NormedSpace (exp)

noncomputable section

namespace RoundedClocks

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A family constant on the open pieces of a finite partition is regulated; its values at the
partition points are immaterial. -/
theorem piecewise_regulated (H : ℝ → 𝕄) (t : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ)
    (hpiece : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), H x = A j) :
    IsRegulated H (t 0) (t n) := by
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
  · intro x hx
    obtain ⟨j, hj, hlo, hhi⟩ :=
      first_failure (fun j ↦ t j ≤ x) n hx.1 (not_le.mpr hx.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (not_le.mp hhi)).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact (hpiece j hj y ⟨hlo.trans_lt hy, hyb⟩).symm
  · intro x hx
    obtain ⟨j, hj, hlo, hhi⟩ :=
      first_failure (fun j ↦ t j < x) n hx.1 (not_lt.mpr hx.2)
    refine ⟨A j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hlo).filter_mono nhdsWithin_le_nhds] with y hy hya
    exact (hpiece j hj y ⟨hya, hy.trans_le (not_lt.mp hhi)⟩).symm

/-- The constant-Hamiltonian evolution `exp (-i u A)`. -/
noncomputable def frozenEvolution (A : 𝕄) (u : ℝ) : 𝕄 :=
  exp (u • (-I • A))

/-- The constant evolution in the scalar form used by the paper. -/
theorem frozenEvolution_eq (A : 𝕄) (u : ℝ) :
    frozenEvolution A u = exp ((-I * (u : ℂ)) • A) := by
  rw [frozenEvolution]
  congr 1
  simpa only [mul_smul] using (smul_comm u (-I) A)

/-- The derivative of the constant-Hamiltonian evolution. -/
private theorem hasDerivAt_frozenEvolution (A : 𝕄) (u : ℝ) :
    HasDerivAt (frozenEvolution A)
      (-I • (A * frozenEvolution A u)) u := by
  simpa only [frozenEvolution, smul_mul_assoc] using
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-I • A) u

/-- A constant Hermitian Hamiltonian has a unitary evolution. -/
private theorem frozenEvolution_unitary {A : 𝕄} (hA : IsHermitian A) (u : ℝ) :
    IsUnitary (frozenEvolution A u) := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  have hI : -I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff, star_neg, Complex.star_def, Complex.conj_I]
  exact Unitary.star_mul_self_of_mem (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem u (hA.isSelfAdjoint.smul_mem_skewAdjoint hI)))

/-- The recursive product of the first `n` constant-evolution factors. -/
noncomputable def recursiveProduct (t : ℕ → ℝ) (A : ℕ → 𝕄) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => frozenEvolution (A n) (t (n + 1) - t n) * recursiveProduct t A n

/-- The switch time after the first `n` durations. -/
def switchTime (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => switchTime σ n + σ n

/-- A recursive product parametrized by the durations of its pieces. -/
noncomputable def durationProduct (σ : ℕ → ℝ) (A : ℕ → 𝕄) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => frozenEvolution (A n) (σ n) * durationProduct σ A n

/-- Recursive products at switch times are duration products. -/
theorem recursiveProduct_switchTime (σ : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ) :
    recursiveProduct (switchTime σ) A n = durationProduct σ A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recursiveProduct, durationProduct, switchTime, ih]
    congr 2
    ring

/-- Splitting the first duration off as a correction gives the product with uniform durations. -/
theorem durationProduct_first_piece (σ : ℕ → ℝ) (A : ℕ → 𝕄) (a b : ℝ) (n : ℕ)
    (hσ0 : σ 0 = a) (hσ : ∀ j, 0 < j → j ≤ n → σ j = b) :
    durationProduct σ A (n + 1) =
      durationProduct (fun _ ↦ b) A (n + 1) * frozenEvolution (A 0) (a - b) := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  induction n with
  | zero =>
    change frozenEvolution (A 0) (σ 0) * 1 =
      frozenEvolution (A 0) b * 1 * frozenEvolution (A 0) (a - b)
    rw [mul_one, mul_one, hσ0]
    rw [frozenEvolution, frozenEvolution, frozenEvolution,
      ← NormedSpace.exp_add_of_commute
        (show Commute (b • (-I • A 0)) ((a - b) • (-I • A 0)) by
          exact (Commute.refl (-I • A 0)).smul_left b |>.smul_right (a - b))]
    congr 1
    module
  | succ n ih =>
    change frozenEvolution (A (n + 1)) (σ (n + 1)) * durationProduct σ A (n + 1) =
      frozenEvolution (A (n + 1)) b * durationProduct (fun _ ↦ b) A (n + 1) *
        frozenEvolution (A 0) (a - b)
    rw [ih (fun j hj hjn ↦ hσ j hj (Nat.le_succ_of_le hjn)),
      hσ (n + 1) (Nat.succ_pos n) le_rfl, mul_assoc]

/-- The rounded clock has half-length end cells and unit-length interior cells. -/
def roundedClockDuration (T j : ℕ) : ℝ :=
  if j = 0 ∨ j = T then 1 / 2 else 1

/-- The rounded-clock cells partition `[0,T]`, and the clock equals `j` on the `j`th cell. -/
theorem rounded_clock_partition (H : ℝ → 𝕄) (T : ℕ) (hT : 1 ≤ T) :
    switchTime (roundedClockDuration T) (T + 1) = T ∧
      ∀ j < T + 1, ∀ x ∈ Ioo
        (switchTime (roundedClockDuration T) j)
        (switchTime (roundedClockDuration T) (j + 1)),
        H ((⌊x + 1 / 2⌋ : ℝ) / T) = H (j / T) := by
  let σ := roundedClockDuration T
  have hmid : ∀ j, j ≠ 0 → j ≠ T → σ j = 1 := by
    intro j h0 hTj
    exact if_neg (by rintro (h | h) <;> contradiction)
  have hswitch : ∀ j, 1 ≤ j → j ≤ T → switchTime σ j = (j : ℝ) - 1 / 2 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [switchTime]
      change 0 + (if 0 = 0 ∨ 0 = T then 1 / 2 else 1) = _
      rw [if_pos (Or.inl rfl)]
      norm_num
    | succ j hj ih =>
      intro hjT
      rw [switchTime, ih (by omega), hmid j (by omega) (by omega)]
      push_cast
      ring
  have hend : switchTime σ (T + 1) = T := by
    rw [switchTime, hswitch T hT le_rfl]
    simp [σ, roundedClockDuration]
  refine ⟨hend, ?_⟩
  intro j hj x hx
  have hfloor : ⌊x + 1 / 2⌋ = (j : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · rcases Nat.eq_zero_or_pos j with rfl | hpos
      · rw [switchTime] at hx
        norm_num at hx ⊢
        linarith
      · have hlo := hx.1
        rw [hswitch j hpos (by omega)] at hlo
        linarith
    · rcases Nat.lt_or_ge j T with hjT | hjT
      · have hhi := hx.2
        rw [hswitch (j + 1) (by omega) (by omega)] at hhi
        push_cast at hhi
        linarith
      · have hjT' : j = T := by omega
        subst j
        rw [hswitch T hT le_rfl, hend] at hx
        calc
          x + (1 : ℝ) / 2 < (T : ℝ) + 1 / 2 := by
            simpa only [add_comm] using add_lt_add_right hx.2 ((1 : ℝ) / 2)
          _ < (T : ℝ) + 1 := by norm_num
  rw [hfloor, Int.cast_natCast]

/-- The rounded product is a final half step, `T` full steps, and a backward initial half step. -/
theorem rounded_durationProduct_split (H : ℝ → 𝕄) (T : ℕ) (hT : 1 ≤ T) :
    durationProduct (roundedClockDuration T) (fun j : ℕ ↦ H (j / T)) (T + 1) =
      frozenEvolution (H 1) (1 / 2) *
        durationProduct (fun _ ↦ 1) (fun j : ℕ ↦ H (j / T)) T *
        frozenEvolution (H 0) (-1 / 2) := by
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  let σ := roundedClockDuration T
  have hmid : ∀ j, j ≠ 0 → j ≠ T → σ j = 1 := by
    intro j h0 hTj
    exact if_neg (by rintro (h | h) <;> contradiction)
  obtain ⟨n, hn⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have hfirst := durationProduct_first_piece σ (fun j : ℕ ↦ H (j / T))
    (1 / 2) 1 n (if_pos (Or.inl rfl))
    (fun j hj hjn ↦ hmid j (by omega) (by omega))
  rw [← hn] at hfirst
  have hσT : σ T = 1 / 2 := if_pos (Or.inr rfl)
  have hHT : H ((T : ℝ) / T) = H 1 := by rw [div_self hT0.ne']
  have hH0 : H (((0 : ℕ) : ℝ) / T) = H 0 := by rw [Nat.cast_zero, zero_div]
  change frozenEvolution (H ((T : ℝ) / T)) (σ T) *
      durationProduct σ (fun j : ℕ ↦ H (j / T)) T = _
  rw [hfirst, hσT, hHT, ← mul_assoc]
  norm_num [hH0]

/-- Unit durations give exactly the step product of Definition 2.3. -/
theorem durationProduct_one_eq_stepProduct (H : ℝ → 𝕄) (T : ℕ) :
    durationProduct (fun _ ↦ 1) (fun j : ℕ ↦ H (j / T)) T = stepProduct H T := by
  have generic : ∀ (n : ℕ) (A : ℕ → 𝕄),
      durationProduct (fun _ ↦ 1) A n =
        ((List.range n).reverse.map fun j ↦ exp (-I • A j)).prod := by
    intro n A
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [durationProduct, List.range_succ, List.reverse_append, List.map_append,
        List.prod_append]
      simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton,
        frozenEvolution, one_smul, ih]
  simpa only [stepProduct] using generic T (fun j : ℕ ↦ H (j / T))

/-- The recursive product is the reverse-list product displayed in equation (2.4). -/
private theorem recursiveProduct_eq_list (t : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ) :
    recursiveProduct t A n = ((List.range n).reverse.map fun j ↦
      exp ((-I * (t (j + 1) - t j : ℝ)) • A j)).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recursiveProduct, ih, List.range_succ, List.reverse_append,
      List.map_append, List.prod_append, frozenEvolution_eq]
    simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton]

/-- Adjacent inequalities make the partition monotone up to its final index. -/
private theorem partition_mono {t : ℕ → ℝ} {n : ℕ}
    (ht : ∀ j < n, t j ≤ t (j + 1)) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    t i ≤ t j := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hij'
      · exact le_rfl
      · exact (ih (Nat.le_of_lt_succ hij') ((Nat.le_succ j).trans hjn)).trans
          (ht j (Nat.lt_of_succ_le hjn))

/-- The manuscript's recursive construction of a piecewise-constant evolution. -/
theorem exists_piecewise_evolution {n : ℕ} {t : ℕ → ℝ}
    (ht : ∀ j < n, t j ≤ t (j + 1)) {G : ℝ → 𝕄} {A : ℕ → 𝕄}
    (hA : ∀ j < n, IsHermitian (A j))
    (hG : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = A j) :
    ∃ V, Generates G V (t 0) (t n) ∧ V (t n) = recursiveProduct t A n := by
  classical
  induction n with
  | zero =>
      refine ⟨fun _ ↦ 1, ⟨continuousOn_const, rfl, fun _ _ ↦ ?_,
        ⟨{t 0}, Set.countable_singleton _, ?_⟩⟩, rfl⟩
      · change (1 : 𝕄)† * 1 = 1
        simp
      intro x hx hnot
      have hxt : x = t 0 := le_antisymm hx.2 hx.1
      exact False.elim (hnot (by simp [hxt]))
  | succ n ih =>
      have htn : t n ≤ t (n + 1) := ht n (Nat.lt_succ_self n)
      obtain ⟨U, hU, hUn⟩ := ih
        (fun j hj ↦ ht j (hj.trans (Nat.lt_succ_self n)))
        (fun j hj ↦ hA j (hj.trans (Nat.lt_succ_self n)))
        (fun j hj ↦ hG j (hj.trans (Nat.lt_succ_self n)))
      rcases htn.eq_or_lt with heq | hlt
      · refine ⟨U, ?_, ?_⟩
        · simpa only [heq] using hU
        · rw [recursiveProduct, ← heq, sub_self]
          simpa [frozenEvolution] using hUn
      · let W : ℝ → 𝕄 := fun x ↦
          frozenEvolution (A n) (x - t n) * U (t n)
        have hWd : ∀ x, HasDerivAt W (-I • (A n * W x)) x := by
          intro x
          simpa only [W, one_smul, one_mul, mul_one, smul_mul_assoc, mul_assoc] using
            ((hasDerivAt_frozenEvolution (A n) (x - t n)).scomp x
              ((hasDerivAt_id x).sub_const (t n))).mul_const (U (t n))
        have hWc : Continuous W :=
          continuous_iff_continuousAt.mpr fun x ↦ (hWd x).continuousAt
        have hjoin : U (t n) = W (t n) := by
          simp [W, frozenEvolution]
        let V : ℝ → 𝕄 := fun x ↦ if x ≤ t n then U x else W x
        have hVc : ContinuousOn V (Icc (t 0) (t (n + 1))) := by
          have hleft : ContinuousOn U
              (Icc (t 0) (t (n + 1)) ∩ closure {x : ℝ | x ≤ t n}) :=
            hU.1.mono (by
              intro x hx
              exact ⟨hx.1.1, by
                simpa only [show {y : ℝ | y ≤ t n} = Iic (t n) from rfl,
                  closure_Iic] using hx.2⟩)
          exact hleft.if
            (fun x hx ↦ by
              have hxn : x = t n := by
                simpa only [show {y : ℝ | y ≤ t n} = Iic (t n) from rfl,
                  frontier_Iic, mem_singleton_iff] using hx.2
              exact hxn ▸ hjoin)
            hWc.continuousOn
        have h0n : t 0 ≤ t n :=
          partition_mono ht (Nat.zero_le n) (Nat.le_succ n)
        have hV0 : V (t 0) = 1 := by
          simpa only [V, if_pos h0n] using hU.2.1
        have hVu : ∀ x ∈ Icc (t 0) (t (n + 1)), IsUnitary (V x) := by
          intro x hx
          by_cases hxn : x ≤ t n
          · rw [show V x = U x from if_pos hxn]
            exact hU.2.2.1 x ⟨hx.1, hxn⟩
          · rw [show V x = W x from if_neg hxn]
            have hleft := frozenEvolution_unitary (hA n (Nat.lt_succ_self n)) (x - t n)
            have hright := hU.2.2.1 (t n) ⟨?_, le_rfl⟩
            · exact Matrix.mem_unitaryGroup_iff'.mp
                (mul_mem (Matrix.mem_unitaryGroup_iff'.mpr hleft)
                  (Matrix.mem_unitaryGroup_iff'.mpr hright))
            · exact h0n
        obtain ⟨S, hS, hUd⟩ := hU.2.2.2
        let E : Set ℝ := insert (t 0) (insert (t n) (insert (t (n + 1)) S))
        refine ⟨V, ⟨hVc, hV0, hVu, E, ((hS.insert _).insert _).insert _, ?_⟩, ?_⟩
        · intro x hx hE
          have hx0 : x ≠ t 0 := fun h ↦ hE (h ▸ Set.mem_insert _ _)
          have hxn : x ≠ t n := fun h ↦ hE (by simp [E, h])
          have hxend : x ≠ t (n + 1) := fun h ↦ hE (by simp [E, h])
          rcases lt_or_gt_of_ne hxn with hbefore | hafter
          · rw [show V x = U x from if_pos hbefore.le]
            exact ((hUd x ⟨hx.1, hbefore.le⟩ fun h ↦
              hE (by simp [E, h])).hasDerivAt
                (Icc_mem_nhds (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hbefore)).congr_of_eventuallyEq
                  (Filter.eventually_of_mem (Iio_mem_nhds hbefore) fun y hy ↦
                    if_pos hy.le) |>.hasDerivWithinAt
          · rw [hG n (Nat.lt_succ_self n) x
                ⟨hafter, lt_of_le_of_ne hx.2 hxend⟩,
              show V x = W x from if_neg (not_le.mpr hafter)]
            exact (hWd x).congr_of_eventuallyEq
              (Filter.eventually_of_mem (Ioi_mem_nhds hafter) fun y hy ↦
                if_neg (not_le.mpr hy)) |>.hasDerivWithinAt
        · rw [show V (t (n + 1)) = W (t (n + 1)) from
              if_neg (not_le.mpr hlt)]
          change frozenEvolution (A n) (t (n + 1) - t n) * U (t n) =
            recursiveProduct t A (n + 1)
          rw [recursiveProduct, hUn]

/-- The recursive endpoint in `exists_piecewise_evolution` has the displayed list form. -/
theorem exists_piecewise_evolution_list {n : ℕ} {t : ℕ → ℝ}
    (ht : ∀ j < n, t j ≤ t (j + 1)) {G : ℝ → 𝕄} {A : ℕ → 𝕄}
    (hA : ∀ j < n, IsHermitian (A j))
    (hG : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = A j) :
    ∃ V, Generates G V (t 0) (t n) ∧
      V (t n) = ((List.range n).reverse.map fun j ↦
        exp ((-I * (t (j + 1) - t j : ℝ)) • A j)).prod := by
  obtain ⟨V, hV, hend⟩ := exists_piecewise_evolution ht hA hG
  exact ⟨V, hV, hend.trans (recursiveProduct_eq_list t A n)⟩

end RoundedClocks
