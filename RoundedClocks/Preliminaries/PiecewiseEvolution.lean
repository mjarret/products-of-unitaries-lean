/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Preliminaries.Basic

/-!
# Evolutions of piecewise-constant families: equations (2.4) and (2.5)

For (2.4): the recursion `V(a) = 1`, `V(t) = e^{-i(t - tⱼ)Gⱼ} V(tⱼ)` for `t ∈ [tⱼ, tⱼ₊₁]` defines a
continuous, unitary `V` that satisfies `i V'(t) = G(t) V(t)` for every `t ∉ {t₀, …, tₙ}`
(`exists_piecewise_evolution`), and its value at `tₙ` is the product (2.4)
(`recursiveProduct_eq_list`).

For (2.5): `⌊t + 1/2⌋ = j` for `t` in an interval of length `1` when `0 < j < T` and of length `1/2`
when `j ∈ {0, T}` (`rounded_clock_partition`), and writing `e^{-iH(0)/2} = e^{-iH(0)} e^{iH(0)/2}`
turns the resulting product into `e^{-iH(1)/2} W_T e^{iH(0)/2}` (`rounded_durationProduct_split`,
`durationProduct_one_eq_stepProduct`).
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

/-! ## Evolution under one fixed Hamiltonian -/

/-- The evolution `e^{-iuA}` under the fixed Hamiltonian `A` for time `u`. -/
noncomputable def frozenEvolution (A : 𝕄) (u : ℝ) : 𝕄 :=
  exp (u • (-I • A))

/-- The evolution under a fixed Hamiltonian in the form of the factors of (2.4): `e^{-iuA}` with
the complex scalar `-iu`. -/
theorem frozenEvolution_eq (A : 𝕄) (u : ℝ) :
    frozenEvolution A u = exp ((-I * (u : ℂ)) • A) := by
  rw [frozenEvolution]
  congr 1
  simpa only [mul_smul] using (smul_comm u (-I) A)

/-- The evolution under a fixed Hamiltonian satisfies `i (e^{-iuA})' = A e^{-iuA}`. -/
private theorem hasDerivAt_frozenEvolution (A : 𝕄) (u : ℝ) :
    HasDerivAt (frozenEvolution A)
      (-I • (A * frozenEvolution A u)) u := by
  simpa only [frozenEvolution, smul_mul_assoc] using
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-I • A) u

/-! ## The recursion before equation (2.4) -/

/-- The value at `tₙ` of the recursion before (2.4): `1` for `n = 0`, and `e^{-i(tₙ₊₁ - tₙ)Aₙ}`
times the value at `tₙ` for `n + 1`. -/
noncomputable def recursiveProduct (t : ℕ → ℝ) (A : ℕ → 𝕄) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => frozenEvolution (A n) (t (n + 1) - t n) * recursiveProduct t A n

/-- The value of the recursion at `tₙ` is the product displayed in equation (2.4),
`e^{-i(tₙ - tₙ₋₁)Aₙ₋₁} ⋯ e^{-i(t₁ - t₀)A₀}`. -/
theorem recursiveProduct_eq_list (t : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ) :
    recursiveProduct t A n = ((List.range n).reverse.map fun j ↦
      exp ((-I * (t (j + 1) - t j : ℝ)) • A j)).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recursiveProduct, ih, List.range_succ, List.reverse_append,
      List.map_append, List.prod_append, frozenEvolution_eq]
    simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton]

/-- The recursion before equation (2.4). For times `t₀ ≤ ⋯ ≤ tₙ` and Hermitian `Aⱼ`, let
`G(x) = Aⱼ` for `tⱼ < x < tⱼ₊₁`. The recursion `V(t₀) = 1`, `V(x) = e^{-i(x - tⱼ)Aⱼ} V(tⱼ)` for
`x ∈ [tⱼ, tⱼ₊₁]` defines a continuous, unitary `V` with `i V'(x) = G(x) V(x)` for every
`x ∉ {t₀, …, tₙ}`, so `G` generates `V`. -/
theorem exists_piecewise_evolution {n : ℕ} {t : ℕ → ℝ}
    (ht : ∀ j < n, t j ≤ t (j + 1)) {G : ℝ → 𝕄} {A : ℕ → 𝕄}
    (hA : ∀ j < n, IsHermitian (A j))
    (hG : ∀ j < n, ∀ x ∈ Ioo (t j) (t (j + 1)), G x = A j) :
    ∃ V, Generates G V (t 0) (t n) ∧ V (t n) = recursiveProduct t A n := by
  classical
  induction n with
  | zero =>
      -- No intervals: `V = 1` at the single time `t₀`.
      refine ⟨fun _ ↦ 1, ⟨continuousOn_const, rfl, fun _ _ ↦ ?_,
        ⟨{t 0}, Set.countable_singleton _, ?_⟩⟩, rfl⟩
      · exact one_mem (unitary 𝕄)
      intro x hx hnot
      have hxt : x = t 0 := le_antisymm hx.2 hx.1
      exact False.elim (hnot (by simp [hxt]))
  | succ n ih =>
      have htn : t n ≤ t (n + 1) := ht n (Nat.lt_succ_self n)
      -- The recursion up to `tₙ` gives the evolution `U` for `x ∈ [t₀, tₙ]`.
      obtain ⟨U, hU, hUn⟩ := ih
        (fun j hj ↦ ht j (hj.trans (Nat.lt_succ_self n)))
        (fun j hj ↦ hA j (hj.trans (Nat.lt_succ_self n)))
        (fun j hj ↦ hG j (hj.trans (Nat.lt_succ_self n)))
      rcases htn.eq_or_lt with heq | hlt
      · -- A repeated time `tₙ = tₙ₊₁` contributes the factor `1`.
        refine ⟨U, ?_, ?_⟩
        · simpa only [heq] using hU
        · rw [recursiveProduct, ← heq, sub_self]
          simpa [frozenEvolution] using hUn
      · -- The recursion for `x ∈ [tₙ, tₙ₊₁]`: `W(x) = e^{-i(x - tₙ)Aₙ} U(tₙ)`, with `i W' = Aₙ W`.
        let W : ℝ → 𝕄 := fun x ↦
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
        -- `V` is `U` up to `tₙ` and `W` after it. It is continuous, as `U(tₙ) = W(tₙ)`.
        let V : ℝ → 𝕄 := fun x ↦ if x ≤ t n then U x else W x
        have hVc : ContinuousOn V (Icc (t 0) (t (n + 1))) := by
          have hleft : ContinuousOn U
              (Icc (t 0) (t (n + 1)) ∩ closure {x : ℝ | x ≤ t n}) :=
            hU.continuousOn.mono (by
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
          simpa only [V, if_pos h0n] using hU.init
        -- `V` is unitary: `W(x)` is a product of two unitaries.
        have hVu : ∀ x ∈ Icc (t 0) (t (n + 1)), IsUnitary (V x) := by
          intro x hx
          by_cases hxn : x ≤ t n
          · rw [show V x = U x from if_pos hxn]
            exact hU.isUnitary x ⟨hx.1, hxn⟩
          · rw [show V x = W x from if_neg hxn]
            have hleft := exp_neg_I_smul_isUnitary (hA n (Nat.lt_succ_self n)) (x - t n)
            exact mul_mem hleft (hU.isUnitary (t n) ⟨h0n, le_rfl⟩)
        -- `i V' = G V` outside `t₀`, `tₙ`, `tₙ₊₁`, and the countable set where `i U' = G U` fails.
        obtain ⟨S, hS, hUd⟩ := hU.deriv
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
        · -- The value at `tₙ₊₁` has one more factor: `V(tₙ₊₁) = e^{-i(tₙ₊₁ - tₙ)Aₙ} U(tₙ)`.
          rw [show V (t (n + 1)) = W (t (n + 1)) from
              if_neg (not_le.mpr hlt)]
          change frozenEvolution (A n) (t (n + 1) - t n) * U (t n) =
            recursiveProduct t A (n + 1)
          rw [recursiveProduct, hUn]

/-! ## The rounded clock: the intervals and the product of equation (2.5) -/

/-- The time `tₙ = ℓ₀ + ⋯ + ℓₙ₋₁` at which the first `n` intervals end, for intervals of lengths
`ℓⱼ = len j`. -/
def switchTime (len : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => switchTime len n + len n

/-- The product `e^{-iℓₙ₋₁Aₙ₋₁} ⋯ e^{-iℓ₀A₀}` of (2.4), written with the interval lengths
`ℓⱼ = tⱼ₊₁ - tⱼ`. -/
noncomputable def durationProduct (len : ℕ → ℝ) (A : ℕ → 𝕄) : ℕ → 𝕄
  | 0 => 1
  | n + 1 => frozenEvolution (A n) (len n) * durationProduct len A n

/-- The product with interval lengths `ℓⱼ` is the displayed product
`e^{-iℓₙ₋₁Aₙ₋₁} ⋯ e^{-iℓ₀A₀}`. -/
theorem durationProduct_eq_list (len : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ) :
    durationProduct len A n = orderedProduct n fun j ↦ exp ((-I * (len j : ℝ)) • A j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [durationProduct, ih]
    change frozenEvolution (A n) (len n) *
      ((List.range n).reverse.map fun j ↦ exp ((-I * (len j : ℝ)) • A j)).prod =
        ((List.range (n + 1)).reverse.map fun j ↦ exp ((-I * (len j : ℝ)) • A j)).prod
    rw [List.range_succ, List.reverse_append,
      List.map_append, List.prod_append, frozenEvolution_eq]
    simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton]

/-- If the first interval has length `a` and the others have length `b`, the product is the one
with all lengths `b`, times `e^{-i(a - b)A₀}` on the right, as
`e^{-iaA₀} = e^{-ibA₀} e^{-i(a - b)A₀}`. -/
theorem durationProduct_first_piece (len : ℕ → ℝ) (A : ℕ → 𝕄) (a b : ℝ) (n : ℕ)
    (hlen0 : len 0 = a) (hlen : ∀ j, 0 < j → j ≤ n → len j = b) :
    durationProduct len A (n + 1) =
      durationProduct (fun _ ↦ b) A (n + 1) * frozenEvolution (A 0) (a - b) := by
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  induction n with
  | zero =>
    -- One factor: `e^{-iaA₀} = e^{-ibA₀} e^{-i(a - b)A₀}`, as the two exponents commute.
    change frozenEvolution (A 0) (len 0) * 1 =
      frozenEvolution (A 0) b * 1 * frozenEvolution (A 0) (a - b)
    rw [mul_one, mul_one, hlen0]
    rw [frozenEvolution, frozenEvolution, frozenEvolution,
      ← NormedSpace.exp_add_of_commute
        (show Commute (b • (-I • A 0)) ((a - b) • (-I • A 0)) by
          exact (Commute.refl (-I • A 0)).smul_left b |>.smul_right (a - b))]
    congr 1
    module
  | succ n ih =>
    -- Each later factor has length `b` in both products.
    change frozenEvolution (A (n + 1)) (len (n + 1)) * durationProduct len A (n + 1) =
      frozenEvolution (A (n + 1)) b * durationProduct (fun _ ↦ b) A (n + 1) *
        frozenEvolution (A 0) (a - b)
    rw [ih (fun j hj hjn ↦ hlen j hj (Nat.le_succ_of_le hjn)),
      hlen (n + 1) (Nat.succ_pos n) le_rfl, mul_assoc]

/-- The length of the interval of `[0,T]` on which the rounded clock `⌊t + 1/2⌋` equals `j`:
`1/2` when `j ∈ {0, T}` and `1` when `0 < j < T`. -/
def roundedClockDuration (T j : ℕ) : ℝ :=
  if j = 0 ∨ j = T then 1 / 2 else 1

/-- The rounded clock equals `j` on an interval of length `1` when `0 < j < T`. -/
theorem roundedClockDuration_interior {T j : ℕ} (h0 : j ≠ 0) (hjT : j ≠ T) :
    roundedClockDuration T j = 1 :=
  if_neg (by rintro (h | h) <;> contradiction)

/-- The intervals of the rounded clock fill `[0,T]`: the last one ends at `T`, and
`⌊x + 1/2⌋ = j` for `x` in the `j`th open interval, so that `H(⌊x + 1/2⌋/T) = H(j/T)` there. -/
theorem rounded_clock_partition (H : ℝ → 𝕄) (T : ℕ) (hT : 1 ≤ T) :
    switchTime (roundedClockDuration T) (T + 1) = T ∧
      ∀ j < T + 1, ∀ x ∈ Ioo
        (switchTime (roundedClockDuration T) j)
        (switchTime (roundedClockDuration T) (j + 1)),
        H ((⌊x + 1 / 2⌋ : ℝ) / T) = H (j / T) := by
  let len := roundedClockDuration T
  -- The `j`th interval starts at `j - 1/2` for `1 ≤ j ≤ T`: the first has length `1/2`, and the
  -- next `T - 1` have length `1`.
  have hswitch : ∀ j, 1 ≤ j → j ≤ T → switchTime len j = (j : ℝ) - 1 / 2 := by
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
      rw [switchTime, ih (by omega),
        show len j = 1 from roundedClockDuration_interior (by omega) (by omega)]
      push_cast
      ring
  -- The last interval, of length `1/2`, ends at `T`.
  have hend : switchTime len (T + 1) = T := by
    rw [switchTime, hswitch T hT le_rfl]
    simp [len, roundedClockDuration]
  refine ⟨hend, ?_⟩
  intro j hj x hx
  -- For `x` in the `j`th open interval, `j ≤ x + 1/2 < j + 1`.
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

/-- Second equality of (2.5). The product over the intervals of the rounded clock is
`e^{-iH(1)/2}`, then the `T` factors `e^{-iH((T-1)/T)} ⋯ e^{-iH(0)}` with all lengths `1`, then
`e^{iH(0)/2}`, as `e^{-iH(0)/2} = e^{-iH(0)} e^{iH(0)/2}`. -/
theorem rounded_durationProduct_split (H : ℝ → 𝕄) (T : ℕ) (hT : 1 ≤ T) :
    durationProduct (roundedClockDuration T) (fun j : ℕ ↦ H (j / T)) (T + 1) =
      frozenEvolution (H 1) (1 / 2) *
        durationProduct (fun _ ↦ 1) (fun j : ℕ ↦ H (j / T)) T *
        frozenEvolution (H 0) (-1 / 2) := by
  have hT0 : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  let len := roundedClockDuration T
  obtain ⟨n, hn⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  -- The first `T` factors: `e^{-iH(0)/2} = e^{-iH(0)} e^{iH(0)/2}` gives all lengths `1`.
  have hfirst := durationProduct_first_piece len (fun j : ℕ ↦ H (j / T))
    (1 / 2) 1 n (if_pos (Or.inl rfl))
    (fun j hj hjn ↦ roundedClockDuration_interior (by omega) (by omega))
  rw [← hn] at hfirst
  -- The last factor is `e^{-iH(1)/2}`.
  have hlenT : len T = 1 / 2 := if_pos (Or.inr rfl)
  have hHT : H ((T : ℝ) / T) = H 1 := by rw [div_self hT0.ne']
  have hH0 : H (((0 : ℕ) : ℝ) / T) = H 0 := by rw [Nat.cast_zero, zero_div]
  change frozenEvolution (H ((T : ℝ) / T)) (len T) *
      durationProduct len (fun j : ℕ ↦ H (j / T)) T = _
  rw [hfirst, hlenT, hHT, ← mul_assoc]
  norm_num [hH0]

/-- With all interval lengths `1`, the product is the `T`-step product of Definition 2.3. -/
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

end RoundedClocks
