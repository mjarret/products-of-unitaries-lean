/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.UnitSteps

/-!
# Products of unitaries, regulated evolutions and the rounded clock

## Declarations

- `regulated_evolution_rounded`
- `roundedClockDuration`
- `rounded_clock_normalized_piecewise_endpoint`
- `rounded_clock_partition`
- `rounded_clock_piecewise_endpoint`
- `rounded_clock_product_eq_unitProduct`
- `rounded_clock_product_split`
- `pieceProduct_first_piece`
- `rounded_clock_endpoint`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real Filter MeasureTheory
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A product whose first piece has length $a$ and whose other pieces have length $b$ is the
product with all pieces of length $b$, followed by the correction $e^{-i(a-b)A_0}$ on the right.
This moves the first half step of the rounded clock into the phase of (2.5) (`eq:rounded`). -/
private theorem pieceProduct_first_piece (σ : ℕ → ℝ) (A : ℕ → 𝕄) (a b : ℝ) (n : ℕ)
    (hσ0 : σ 0 = a) (hσ : ∀ j, 0 < j → j ≤ n → σ j = b) :
    UnitaryProducts.pieceProduct σ A (n+1) =
      UnitaryProducts.pieceProduct (fun _ ↦ b) A (n+1) * UnitaryProducts.evol (A 0) (a - b) := by
  induction n with
  | zero =>
    change UnitaryProducts.evol (A 0) (σ 0) * 1 =
      UnitaryProducts.evol (A 0) b * 1 * UnitaryProducts.evol (A 0) (a - b)
    rw [mul_one, mul_one, ← UnitaryProducts.evol_add, hσ0]; congr 1; ring
  | succ n ih =>
    change UnitaryProducts.evol (A (n+1)) (σ (n+1)) * UnitaryProducts.pieceProduct σ A (n+1) =
      UnitaryProducts.evol (A (n+1)) b * UnitaryProducts.pieceProduct (fun _ ↦ b) A (n+1) *
        UnitaryProducts.evol (A 0) (a - b)
    rw [ih (fun j hj hjn ↦ hσ j hj (Nat.le_succ_of_le hjn)),
      hσ (n+1) (Nat.succ_pos n) le_rfl, mul_assoc]

/-- Durations of the rounded-clock cells on $[0,T]$: $T/(2N)$ at both ends and
$T/N$ at each interior sample. Setting $T=1$ gives the normalized-time lengths used
in the explanation of the first line of (2.5) (`eq:rounded`). -/
def roundedClockDuration (T : ℝ) (N j : ℕ) : ℝ :=
  if j = 0 ∨ j = N then T/(2*N) else T/N

/-- The rounded-clock cells form a partition, and the clock equals $j$ on the
$j$th open cell. In normalized time ($T=1$) these are precisely the cells used
for $T H(q(Ns)/N)$ in the first line of (2.5) (`eq:rounded`). -/
theorem rounded_clock_partition (H : ℝ → 𝕄) (T : ℝ) (N : ℕ)
    (hT : 0 < T) (hN : 1 ≤ N) :
    (∀ j, 0 < roundedClockDuration T N j) ∧
    UnitaryProducts.switchTime (roundedClockDuration T N) (N+1) = T ∧
    ∀ j < N+1, ∀ s ∈ Ioo
      (UnitaryProducts.switchTime (roundedClockDuration T N) j)
      (UnitaryProducts.switchTime (roundedClockDuration T N) (j+1)),
      H ((⌊(N : ℝ) * s / T + 1 / 2⌋ : ℝ) / N) = H (j/N) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  -- Step 1 (paper, before (2.5) (`eq:rounded`)): the rounded clock holds the end samples for T/(2N)
  -- and the
  -- interior samples for T/N, so the durations are T/(2N), T/N, …, T/N, T/(2N).
  let τ := roundedClockDuration T N
  have hτ : ∀ j, 0 < τ j := fun j ↦ by
    dsimp only [τ, roundedClockDuration]; split_ifs <;> positivity
  have hτmid : ∀ j, j ≠ 0 → j ≠ N → τ j = T/N := fun j h0 hN' ↦
    if_neg (by rintro (h | h) <;> contradiction)
  -- The switch times are (2j - 1)T/(2N) for 1 ≤ j ≤ N, and the last one is T.
  have hsw : ∀ j, 1 ≤ j → j ≤ N →
      UnitaryProducts.switchTime τ j = (2*(j:ℝ)-1)*T/(2*N) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro _
      rw [UnitaryProducts.switchTime_succ, UnitaryProducts.switchTime_zero]
      change 0 + (if 0 = 0 ∨ 0 = N then T/(2*N) else T/N) = _
      rw [if_pos (Or.inl rfl)]; push_cast; ring
    | succ j hj ih =>
      intro hjN
      rw [UnitaryProducts.switchTime_succ, ih (by omega), hτmid j (by omega) (by omega)]
      push_cast; field_simp; ring
  have hswT : UnitaryProducts.switchTime τ (N+1) = T := by
    rw [UnitaryProducts.switchTime_succ, hsw N hN le_rfl]
    change _ + (if N = 0 ∨ N = N then T/(2*N) else T/N) = T
    rw [if_pos (Or.inr rfl)]; field_simp; ring
  -- Step 2: on the j-th open piece ⌊Ns/T + 1/2⌋ = j, so the rounded clock holds H(j/N); the
  -- three cases j = 0, 0 < j < N and j = N differ only in which end of the piece is special.
  have hp : ∀ j < N+1, ∀ s ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ
    (j+1)),
      (fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N)) s = H (j/N) := by
    intro j hj s hs
    have key : ⌊(N:ℝ)*s/T + 1 / 2⌋ = (j:ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0
          rw [UnitaryProducts.switchTime_zero] at hs
          have : 0 ≤ (N:ℝ)*s/T := div_nonneg (mul_nonneg hN0.le hs.1.le) hT.le
          push_cast
          linarith
        · have h1 := hs.1
          rw [hsw j hpos (by omega), div_lt_iff₀ (by positivity)] at h1
          have h2 : (2*(j:ℝ)-1)/2 < N*s/T := by rw [lt_div_iff₀ hT]; linarith
          linarith
      · rcases Nat.lt_or_ge j N with hjN | hjN
        · have h1 := hs.2
          rw [hsw (j+1) (by omega) (by omega), lt_div_iff₀ (by positivity)] at h1
          have h2 : (N:ℝ)*s/T < (2*(j:ℝ)+1)/2 := by rw [div_lt_iff₀ hT]; push_cast at h1; linarith
          linarith
        · have hjN' : j = N := by omega
          subst hjN'
          have h1 := hs.2
          rw [hswT] at h1
          have h2 : (j:ℝ)*s/T < j := by rw [div_lt_iff₀ hT]; exact mul_lt_mul_of_pos_left h1 hN0
          linarith
    change H ((⌊(N : ℝ)*s/T + 1 / 2⌋ : ℝ)/N) = H (j/N)
    rw [key, Int.cast_natCast]
  exact ⟨hτ, hswT, hp⟩

/-- The first line of (2.5) (`eq:rounded`): the endpoint is the product with a half step at
both ends and full steps in between, by the piecewise-product formula (2.4)
(`eq:piecewise-product`). -/
theorem rounded_clock_piecewise_endpoint (H : ℝ → 𝕄)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) (T : ℝ) (N : ℕ) (hT : 0 < T) (hN : 1 ≤ N)
    (V : ℝ → 𝕄) (hV : IsEvolution (fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N)) V 0 T) :
    V T = UnitaryProducts.pieceProduct (roundedClockDuration T N)
      (fun j : ℕ ↦ H (j/N)) (N+1) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  let τ := roundedClockDuration T N
  obtain ⟨hτ, hswT, hp⟩ := rounded_clock_partition H T N hT hN
  have hHerm : ∀ t ∈ Icc 0 T,
      ((fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N)) t).IsHermitian := by
    intro t ht
    apply hH
    have hr0 : 0 ≤ (N:ℝ) * t / T := div_nonneg (mul_nonneg hN0.le ht.1) hT.le
    have hr1 : (N:ℝ) * t / T ≤ N := by
      rw [div_le_iff₀ hT]; exact mul_le_mul_of_nonneg_left ht.2 hN0.le
    have hq0 : (0:ℤ) ≤ ⌊(N:ℝ) * t / T + 1 / 2⌋ := Int.floor_nonneg.mpr (by linarith)
    have hq1 : ⌊(N:ℝ) * t / T + 1 / 2⌋ ≤ (N:ℤ) := by rw [Int.floor_le_iff]; push_cast; linarith
    exact ⟨div_nonneg (Int.cast_nonneg hq0) hN0.le, (div_le_one hN0).mpr (by exact_mod_cast hq1)⟩
  have hreg := piecewise_regulated (fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N))
    (UnitaryProducts.switchTime τ) (fun j : ℕ ↦ H (j/N)) (N+1) hp
  rw [UnitaryProducts.switchTime_zero, hswT] at hreg
  obtain ⟨U, -, huniq, -, hpiece⟩ := regulated_evolution hT hHerm hreg
  exact (huniq V hV ⟨hT.le, le_rfl⟩).trans
    (hpiece τ (fun j : ℕ ↦ H (j/N)) (N+1) hτ hswT hp)

/-- The second line of (2.5) (`eq:rounded`): splitting the initial half step leaves $N$ full
steps and a backward half step, in addition to the final forward half step. -/
theorem rounded_clock_product_split (H : ℝ → 𝕄) (T : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    UnitaryProducts.pieceProduct (roundedClockDuration T N) (fun j : ℕ ↦ H (j/N)) (N+1) =
      UnitaryProducts.evol (H 1) (T/(2*N)) *
        UnitaryProducts.pieceProduct (fun _ ↦ T/N) (fun j : ℕ ↦ H (j/N)) N *
        UnitaryProducts.evol (H 0) (-(T/(2*N))) := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  let τ := roundedClockDuration T N
  have hτmid : ∀ j, j ≠ 0 → j ≠ N → τ j = T/N := fun j h0 hN' ↦
    if_neg (by rintro (h | h) <;> contradiction)
  obtain ⟨n, hn⟩ : ∃ n, N = n+1 := ⟨N-1, by omega⟩
  have hfirst := pieceProduct_first_piece τ (fun j : ℕ ↦ H (j/N)) (T/(2*N)) (T/N) n
    (if_pos (Or.inl rfl)) (fun j hj hjn ↦ hτmid j (by omega) (by omega))
  rw [← hn] at hfirst
  have hτN : τ N = T/(2*N) := if_pos (Or.inr rfl)
  have hHN : H ((N:ℝ)/N) = H 1 := by rw [div_self hN0.ne']
  have hH0 : H (((0:ℕ):ℝ)/N) = H 0 := by rw [Nat.cast_zero, zero_div]
  have hsub : T/(2*N) - T/N = -(T/(2*N)) := by field_simp; ring
  change UnitaryProducts.evol (H ((N:ℝ) / N)) (τ N) *
      UnitaryProducts.pieceProduct τ (fun j : ℕ ↦ H (j/N)) N = _
  rw [hfirst, hτN, hHN, hsub, ← mul_assoc]
  simp only [hH0]

/-- The third line of (2.5) (`eq:rounded`): the $N$ full factors are the $N$-step product of
Definition 2.3. -/
theorem rounded_clock_product_eq_unitProduct (H : ℝ → 𝕄) (T : ℝ) (N : ℕ) :
    UnitaryProducts.evol (H 1) (T/(2*N)) *
        UnitaryProducts.pieceProduct (fun _ ↦ T/N) (fun j : ℕ ↦ H (j/N)) N *
        UnitaryProducts.evol (H 0) (-(T/(2*N))) =
      UnitaryProducts.evol (H 1) (T/(2*N)) * (unitProduct (fun s ↦ (T/N) • H s) N).1 *
        UnitaryProducts.evol (H 0) (-(T/(2*N))) := by
  rw [show (unitProduct (fun s ↦ (T/N) • H s) N).1 = _ from step_products_factors H]

/-- The rounded-clock identity (2.5) (`eq:rounded`), following its three displayed equalities. -/
private theorem rounded_clock_endpoint (H : ℝ → 𝕄)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) (T : ℝ) (N : ℕ) (hT : 0 < T) (hN : 1 ≤ N)
    (V : ℝ → 𝕄) (hV : IsEvolution (fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N)) V 0 T) :
    V T = UnitaryProducts.evol (H 1) (T/(2*N)) * (unitProduct (fun s ↦ (T/N) • H s) N).1 *
      UnitaryProducts.evol (H 0) (-(T/(2*N))) :=
  (rounded_clock_piecewise_endpoint H hH T N hT hN V hV).trans
    ((rounded_clock_product_split H T N hN).trans (rounded_clock_product_eq_unitProduct H T N))

/-- Supports the existence-and-uniqueness claim of §2.1 ("Every regulated family $G$ on $[0,b]$
generates exactly one $V$", here with $H$, $U$, $T$) and the two paragraphs after it in §2.1: for
piecewise-constant $G$, "$V(b)$ is (2.4) (`eq:piecewise-product`)", and
the rounded-clock identity (2.5) (`eq:rounded`), $V(T) = e^{-iTH(1)/(2N)} W_N e^{iTH(0)/(2N)}$.

Reading the statement against the paper:
* Uniqueness is `EqOn V U (Icc 0 T)`: evolutions are compared on $[0,T]$ only, where they live.
* The clause `HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t` at every point where $H$ is
  continuous relative to $[0,T]$ is an addition to the paper's statement; it is one-sided at the
  ends.
* A piecewise-constant family is given by durations `τ j > 0`; `switchTime τ j` is
  $t_j = \tau_0 + \dots + \tau_{j-1}$, the last switch time is $T$, and $H$ is constrained only on
  the open pieces $(t_j, t_{j+1})$. `pieceProduct τ A n` is (2.4) (`eq:piecewise-product`).
* In the second conjunct, `⌊N * t / T + 1/2⌋` cast to `ℝ` is the rounded clock $q(Nt/T)$,
  `(unitProduct (fun s ↦ (T/N) • H s) N).1` is $W_N$ (Definition 2.3), and `evol A u` is
  $e^{-iuA}$.
* The rounded-clock conjunct assumes only $H$ Hermitian on $[0,1]$, $T > 0$ and $N \ge 1$: the
  rounded clock is piecewise constant, hence regulated, whatever $H$ is.

The proof follows the paper's: (1) the first conjunct is `regulated_evolution`, whose existence
half builds the evolution by hand (`exists_evolution_of_regulated`) instead of citing Dieudonné,
and whose piecewise clause glues the frozen evolutions (`exists_piecewise_evolution`); (2) the
rounded clock holds $H(j/N)$ on the piece around $jT/N$, with half pieces at the ends; (3) the
piecewise clause gives $V(T)$ as the induced product, and moving the first half step into a phase
gives (2.5) (`eq:rounded`). -/
theorem regulated_evolution_rounded :
    (∀ (H : ℝ → 𝕄) (T : ℝ), 0 < T → (∀ t ∈ Icc 0 T, (H t).IsHermitian) →
      IsRegulated H 0 T →
      ∃ U : ℝ → 𝕄, IsEvolution H U 0 T ∧
        (∀ V : ℝ → 𝕄, IsEvolution H V 0 T → EqOn V U (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, ContinuousWithinAt H (Icc 0 T) t →
          HasDerivWithinAt U (-I • (H t * U t)) (Icc 0 T) t) ∧
        ∀ (τ : ℕ → ℝ) (A : ℕ → 𝕄) (n : ℕ), (∀ j, 0 < τ j) → UnitaryProducts.switchTime τ n = T →
          (∀ j < n, ∀ s ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ (j+1)),
            H s = A j) →
          U T = UnitaryProducts.pieceProduct τ A n) ∧
    (∀ (H : ℝ → 𝕄), (∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) →
      ∀ (T : ℝ) (N : ℕ), 0 < T → 1 ≤ N →
      ∀ V : ℝ → 𝕄, IsEvolution (fun t ↦ H ((⌊(N : ℝ) * t / T + 1 / 2⌋ : ℝ) / N)) V 0 T →
        V T = UnitaryProducts.evol (H 1) (T/(2*N)) * (unitProduct (fun s ↦ (T/N) • H s) N).1 *
          UnitaryProducts.evol (H 0) (-(T/(2*N)))) :=
  ⟨fun _ _ ↦ regulated_evolution, rounded_clock_endpoint⟩

end UnitaryProducts.Paper
