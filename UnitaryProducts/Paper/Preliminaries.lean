/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.NaturalNormsEnds
public import UnitaryProducts.Evolution.EnergyRescale
public import UnitaryProducts.Evolution.UnitaryGenerators
public import UnitaryProducts.Spectral.SinTheta

/-!
# Preliminaries: evolutions, products of unitaries, Duhamel, Davis–Kahan

## Declarations

- `IsEvolution`
- `IsRegulated`
- `duhamel`
- `piecewiseData`
- `piecewise_regulated`
- `regulated_evolution`
- `stepProducts`
- `step_products_factors`
-/

@[expose] public section

namespace UnitaryProducts.Paper
open scoped Matrix.Norms.L2Operator Topology
open Complex Set Filter MeasureTheory
noncomputable section
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Equation (2.5)** (product of unitaries induced by a piecewise-constant family). `.1` says
that $G$ is piecewise constant on $[a,b]$, and `.2` is the induced product
$e^{-i(t_n-t_{n-1})G_{n-1}}\cdots e^{-i(t_1-t_0)G_0}$ of eq. (2.5).

Reading the statement against the paper:
* `.1` asks for $n>0$, nodes `t` with $t_0=a$, $t_n=b$, strictly increasing on $\{0,\dots,n\}$,
  and matrices `A` with $G(s)=A_j$ on each open piece $(t_j,t_{j+1})$. The values of $G$ at the
  nodes are free, as in the paper.
* `.2 t A n` takes the nodes and the matrices as arguments; nothing is chosen from `.1`, and a
  consumer passes the data that witness `.1`. It is `pieceProduct` with durations
  $t_{j+1}-t_j$, whose recursion puts the latest factor on the left. It is total, but only its
  value on data satisfying `.1` is the paper's product.
* That the product depends only on $G$ is not part of the definition. It follows from the last
  clause of `regulated_evolution`: the evolution at time $T$ equals the product for every
  admissible partition. -/
def piecewiseData (G : ℝ → 𝕄) (a b : ℝ) :
    Prop × ((ℕ → ℝ) → (ℕ → 𝕄) → ℕ → 𝕄) :=
  (∃ (n : ℕ) (t : ℕ → ℝ) (A : ℕ → 𝕄),
    0 < n ∧ t 0 = a ∧ t n = b ∧ StrictMonoOn t (Iic n) ∧
      ∀ j < n, ∀ s ∈ Ioo (t j) (t (j+1)), G s = A j,
   fun t A n ↦ UnitaryProducts.pieceProduct (fun j ↦ t (j+1) - t j) A n)

/-- The equal-step objects of the paper, bundled: the midpoint product, the $N$-step product
$W_N$ of **Definition 2.3**, and the rounded clock $q(t)=\lfloor t+1/2\rfloor$ (after
Definition 2.3).

* `.1 n t` is `heldProduct id H n t`, the midpoint product of Definition 3.5. It depends on neither
  `T` nor `N`; `midpoint_step_products` identifies it with `midpointProduct`.
* `.2.1` is $W_N=e^{-i(T/N)H((N-1)/N)}\cdots e^{-i(T/N)H(0)}$, encoded as `pieceProduct` with unit
  durations and generators $(T/N)H(j/N)$. This is the same encoding as `stepProduct H T N`, which
  is `(unitProduct (fun s ↦ (T/N) • H s) N).1`, an internal general-duration encoding.
  `step_products_factors` rewrites it with durations $T/N$ and generators $H(j/N)$, and
  `step_products_unit` identifies `(stepProducts H N N).2.1` with `(unitProduct H N).1`.
* `.2.2` is the rounded clock $q$, the integer floor cast to `ℝ`.

At $N=0$, `.2.1` is the empty product $1$; the paper takes $N\ge1$. -/
def stepProducts (H : ℝ → 𝕄) (T : ℝ) (N : ℕ) :
    (ℕ → (ℕ → ℝ) → 𝕄) × 𝕄 × (ℝ → ℝ) :=
  (fun n t ↦ UnitaryProducts.heldProduct id H n t,
   UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ (T/N) • H (j/N)) N,
   fun t ↦ (⌊t + 1/2⌋ : ℤ))

omit [NeZero d] in
/-- Supports "equal to $H(j/N)$ for $|s-j/N|<1/(2N)$, $0\le j\le N$" (the paragraph after
Definition 2.3, on the rounded clock): each factor $e^{-i(T/N)H(j/N)}$ of $W_N$ is the evolution
of $H(j/N)$ for time $T/N$.

Reading the statement against the paper:
* The left side is $W_N$ as `stepProducts` encodes it (unit durations, generators
  $(T/N)H(j/N)$); the right side is the same product with durations $T/N$ and generators $H(j/N)$.
* Stronger than the paper: no $d\ge1$, $T>0$, or $N\ge1$ is needed. Scalar actions
  commute directly, including zero scale and the empty product at $N=0$.

The proof rescales one factor, $e^{-i\cdot1\cdot(T/N)A}=e^{-i(T/N)A}$ by scalar commutation, and
inducts on the number of factors. -/
theorem step_products_factors (H : ℝ → 𝕄) {T : ℝ} {N : ℕ} :
    (stepProducts H T N).2.1 =
      UnitaryProducts.pieceProduct (fun _ ↦ T/N) (fun j ↦ H (j/N)) N := by
  change UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ (T/N) • H (j/N)) N = _
  have hp (n : ℕ) : UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ (T/N) • H (j/N)) n =
      UnitaryProducts.pieceProduct (fun _ ↦ T/N) (fun j ↦ H (j/N)) n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [UnitaryProducts.pieceProduct, ih, UnitaryProducts.evol, one_smul,
        smul_comm (-I) (T / (N : ℝ))]
  exact hp N

/-- **Definition 2.1** (regulated matrix-valued function). $H$ has a right limit at every
$t\in[a,b)$ and a left
limit at every $t\in(a,b]$.

Reading the statement against the paper:
* The body is `UnitaryProducts.Regulated H a b`, which is these two clauses literally, with
  `Tendsto H (𝓝[>] t)` and `Tendsto H (𝓝[<] t)` in the topology of matrices; every matrix norm
  gives this topology, so the choice of norm does not matter.
* This definition applies to every matrix-valued function, without a Hermitian hypothesis.
  Consumers that require Hermitian values assume them separately. -/
def IsRegulated (H : ℝ → 𝕄) (a b : ℝ) : Prop := UnitaryProducts.Regulated H a b

omit [NeZero d] in
/-- A family constant on the open pieces of a finite partition is regulated (Definition 2.1);
its values at the nodes are unrestricted. It makes piecewise-constant truncated families regulated
in `truncation_error` and `truncation_bits`, and the rounded clock's family regulated in the
rounded-clock identity. -/
theorem piecewise_regulated (H : ℝ → 𝕄) (a : ℕ → ℝ) (G : ℕ → 𝕄) (n : ℕ)
    (hc : ∀ j < n, ∀ x ∈ Ioo (a j) (a (j + 1)), H x = G j) :
    IsRegulated H (a 0) (a n) := by
  -- A predicate true at `0` and false at `m` fails for the first time at some `j + 1 ≤ m`.
  have piece : ∀ (P : ℕ → Prop) (m : ℕ), P 0 → ¬ P m → ∃ j < m, P j ∧ ¬ P (j+1) := by
    intro P m h0 hm
    induction m with
    | zero => exact absurd h0 hm
    | succ m ih =>
      by_cases h : P m
      · exact ⟨m, m.lt_succ_self, h, hm⟩
      · obtain ⟨j, hj, hp⟩ := ih h
        exact ⟨j, hj.trans m.lt_succ_self, hp⟩
  constructor
  · intro t ht
    obtain ⟨j, hj, hlo, hhi⟩ := piece (fun j ↦ a j ≤ t) n ht.1 (not_le.mpr ht.2)
    refine ⟨G j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (not_le.mp hhi)).filter_mono nhdsWithin_le_nhds] with x hx hxb
    exact (hc j hj x ⟨hlo.trans_lt hx,hxb⟩).symm
  · intro t ht
    obtain ⟨j, hj, hlo, hhi⟩ := piece (fun j ↦ a j < t) n ht.1 (not_lt.mpr ht.2)
    refine ⟨G j, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hlo).filter_mono nhdsWithin_le_nhds] with x hx hxa
    exact (hc j hj x ⟨hxa,hx.trans_le (not_lt.mp hhi)⟩).symm

/-- Generation (§2, the sentence with eq. (2.1)). `IsEvolution H U a b` reads: $H$ generates $U$
on $[a,b]$ (the paper: "A family $G$ on $[a,b]$ generates a continuous, unitary-valued $V$ on
$[a,b]$"): $U$ is continuous and unitary on $[a,b]$, $U(a)=1$, and $iU'=HU$ for all but
countably many $t$. The evolution of a path $H$ over time $T$ is the $U$ with
`IsEvolution (fun t ↦ H (t / T)) U 0 T`.

Reading the statement against the paper:
* $iU'=HU$ is written $U'=-iHU$ as a derivative within $[a,b]$ (`HasDerivWithinAt`), so
  one-sided derivatives count at $a$ and $b$; the exceptional set `S` is any countable set.
* Unitarity is $U^\dagger U=1$ (`star (U t) * U t = 1`), which for square matrices implies
  $UU^\dagger=1$.
* As in the paper, $H$ need not be regulated (by the existence-and-uniqueness claim of §2.1, a
regulated $H$ generates
  exactly one $U$). Hermiticity, the paper's standing convention, is not part of the predicate;
  a unitary solution implies it at interior times where the equation holds.

Existence and uniqueness are not part of the definition: they are the existence-and-uniqueness claim
of §2.1,
`exists_unique_evolution`. -/
def IsEvolution (H U : ℝ → 𝕄) (a b : ℝ) : Prop :=
  ContinuousOn U (Icc a b) ∧ U a = 1 ∧
    (∀ t ∈ Icc a b, star (U t) * U t = 1) ∧
    ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Icc a b, t ∉ S →
      HasDerivWithinAt U (-I • (H t * U t)) (Icc a b) t

omit [NeZero d] in
/-- Supports **equation (2.3)** (`eq:duhamel`), "$\|V(b)-U(b)\|\le\int_a^b\|K-G\|\,dt$", the case
$Y=0$ of the
comparison theorem (the paper’s derivation is `PaperProof.duhamel_bound`), for
$U$ and $V$ generated by regulated Hermitian families $H$ and $G$ on $[a,b]$.

Reading the statement against the paper:
* The paper's $K$ is `H`, and the conclusion is written $\|U(b)-V(b)\|$.
* Stronger than the paper: no separate Hermiticity premises are needed (unitarity
  is part of `IsEvolution`), and $d\ge1$ is not needed.

The proof follows the paper's: with $W=U^\dagger V$, off the union of the two countable exceptional
sets $W'=iU^\dagger(H-G)V$, so $\|W'\|\le\|H-G\|$ as $U$ and $V$ are unitary; the
fundamental theorem of calculus off a countable set and $W(a)=1$ give the bound
(`norm_sub_le_integral_sub_of_regulated`). -/
theorem duhamel {H G U V : ℝ → 𝕄} {a b : ℝ} (hab : a ≤ b)
    (hHr : IsRegulated H a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution H U a b) (hV : IsEvolution G V a b) :
    ‖U b - V b‖ ≤ ∫ t in a..b, ‖H t - G t‖ := by
  obtain ⟨hUc, hU0, hUU, S, hS, hUd⟩ := hU
  obtain ⟨hVc, hV0, hVV, R, hR, hVd⟩ := hV
  exact UnitaryProducts.norm_sub_le_integral_sub_of_regulated (S ∪ R) (hS.union hR) hab hUc hVc
    (fun t ht hn ↦ hUd t ht (fun hs ↦ hn (Or.inl hs)))
    (fun t ht hn ↦ hVd t ht (fun hr ↦ hn (Or.inr hr)))
    hUU hVV (hU0.trans hV0.symm) hHr hGr

omit [NeZero d] in
/-- A regulated Hermitian family on $[0,T]$ generates exactly one $U$ (the
argument for **the existence-and-uniqueness claim of §2.1**), with two further clauses: $U$ solves
$iU'=HU$ at every point
where $H$ is continuous within $[0,T]$, and if $H=A_j$ on the open pieces of a partition with
positive durations $\tau_j$ ending at $T$, then $U(T)$ is the induced product of eq. (2.5) (the
recursion after the existence-and-uniqueness claim of §2.1).

`exists_unique_evolution` states the existence-and-uniqueness claim of §2.1 by projecting the first
two clauses, through
`regulated_evolution_rounded`.

The proof differs from the paper's, which cites Dieudonné for the linear equation. Existence is
`exists_evolution_of_regulated`, built by hand as the uniform limit of evolutions of step
approximations of $H$. Uniqueness applies `duhamel` to two evolutions of the same $H$. The
piecewise clause identifies $U$ with the glued evolution of the pieces. -/
theorem regulated_evolution {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) (hHr : IsRegulated H 0 T) :
    ∃ U : ℝ → 𝕄, IsEvolution H U 0 T ∧
      (∀ V : ℝ → 𝕄, IsEvolution H V 0 T → EqOn V U (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, ContinuousWithinAt H (Icc 0 T) t →
        HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t) ∧
      ∀ (τ : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ), (∀ j, 0 < τ j) → UnitaryProducts.switchTime τ n = T →
        (∀ j < n, ∀ s ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ (j+1)),
          H s = A j) →
        U T = UnitaryProducts.pieceProduct τ A n := by
  -- Existence: `regulatedEvolution` is chosen from `exists_evolution_of_regulated`; the
  -- uniqueness clause below shows that the choice does not matter.
  let U := UnitaryProducts.regulatedEvolution hT.le hHr hH
  have hu := (UnitaryProducts.exists_evolution_of_regulated hT.le hHr hH).choose_spec
  -- `U` is an evolution; its exceptional set is the countable set of discontinuities of `H`.
  have he : IsEvolution H U 0 T :=
    ⟨hu.1, hu.2.1, fun t ht ↦ (hu.2.2.1 t ht).1,
      {t ∈ Icc 0 T | ¬ ContinuousWithinAt H (Icc 0 T) t},
      UnitaryProducts.Regulated.countable_not_continuousWithinAt hHr hT.le, fun t ht hn ↦
        UnitaryProducts.regulatedEvolution_hasDerivWithinAt hT.le hHr hH ht
          (not_not.mp fun hc ↦ hn ⟨ht, hc⟩)⟩
  refine ⟨U, he, ?_, fun t ht hc ↦
    UnitaryProducts.regulatedEvolution_hasDerivWithinAt hT.le hHr hH ht hc, ?_⟩
  -- Uniqueness: restrict both evolutions to `[0,t]`; `duhamel` with the same generator `H` gives
  -- `‖V t - U t‖ ≤ ∫ ‖H - H‖ = 0`.
  · intro V hV t ht
    have restrict_evolution : ∀ W, IsEvolution H W 0 T → IsEvolution H W 0 t := by
      intro W hW
      obtain ⟨hc, h0, hunit, S, hS, hd⟩ := hW
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
      exact ⟨hc.mono hsub, h0, fun x hx ↦ hunit x (hsub hx), S, hS,
        fun x hx hn ↦ (hd x (hsub hx) hn).mono hsub⟩
    have hr : IsRegulated H 0 t := ⟨fun x hx ↦ hHr.1 x ⟨hx.1, hx.2.trans_le ht.2⟩,
      fun x hx ↦ hHr.2 x ⟨hx.1, hx.2.trans ht.2⟩⟩
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by
      simpa only [sub_self, norm_zero, intervalIntegral.integral_zero] using
        duhamel ht.1 hr hr (restrict_evolution V hV) (restrict_evolution U he)))
  -- Piecewise-constant `H` (the recursion after the existence-and-uniqueness claim of §2.1): the
  -- glued evolution `V` of the
  -- pieces ends at the product, and it solves the same equation as `U` off a countable set, so
  -- `V = U` on `[0,T]` (`evolution_eq_of_solves_off_countable`).
  · intro τ A n hτ hTn hp
    obtain ⟨V, S, hVc, hV0, hend, hVd⟩ := UnitaryProducts.exists_piecewise_evolution hτ n hp
    obtain ⟨hUc, hU0, -, R, hR, hUd⟩ := he
    rw [hTn] at hend hVd
    have h := UnitaryProducts.evolution_eq_of_solves_off_countable (↑S) R S.countable_toSet hR hH
      hVc.continuousOn hUc hV0 hU0
      (fun t ht hn ↦ (hVd t (Ioo_subset_Icc_self ht) hn).hasDerivWithinAt)
      (fun t ht hn ↦ hUd t (Ioo_subset_Icc_self ht) hn)
    exact (h ⟨hT.le, le_rfl⟩).symm.trans hend


end
end UnitaryProducts.Paper
