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

- `exists_isHermitian_evol_eq_of_unitary`
- `regulated_evolution_rounded`
- `roundedClockDuration`
- `rounded_clock_cell_lengths`
- `rounded_clock_half_step_split`
- `rounded_clock_normalized_piecewise_endpoint`
- `rounded_clock_partition`
- `rounded_clock_piecewise_endpoint`
- `rounded_clock_product_eq_unitProduct`
- `rounded_clock_product_split`
- `unit_sample_mem`
- `unitary_product_evolution`
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

/-- The sample points $j/N$, $j < N$, lie in $[0,1]$; this lets the width hypotheses name the
eigenvalues of $H(j/N)$. -/
theorem unit_sample_mem {N j : ℕ} (hjN : j < N) : (j : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le j) hjN)
  exact ⟨div_nonneg (Nat.cast_nonneg j) hN.le, (div_le_one hN).mpr (Nat.cast_le.mpr hjN.le)⟩

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

/-- The normalized-time cell lengths in the explanation of (2.5) (`eq:rounded`): $1/(2N)$ at
$j=0,N$ and $1/N$ at $0<j<N$. -/
theorem rounded_clock_cell_lengths (N : ℕ) :
    roundedClockDuration 1 N 0 = 1/(2*N) ∧
    roundedClockDuration 1 N N = 1/(2*N) ∧
    ∀ j, 0 < j → j < N → roundedClockDuration 1 N j = 1/N :=
  ⟨if_pos (Or.inl rfl), if_pos (Or.inr rfl), fun j hj hjN ↦ if_neg (by omega)⟩

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

/-- The exponential identity used in the second line of (2.5) (`eq:rounded`): split the initial
half step as a full forward step followed by a backward half step. -/
theorem rounded_clock_half_step_split (A : 𝕄) (T : ℝ) (N : ℕ) :
    UnitaryProducts.evol A (T/(2*N)) =
      UnitaryProducts.evol A (T/N) * UnitaryProducts.evol A (-(T/(2*N))) := by
  rw [← UnitaryProducts.evol_add]; congr 1; ring

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

/-- Every unitary matrix is $e^{-iA}$ for a Hermitian $A$: its spectrum is finite, so it misses a
point $e^{i\beta}$ of the circle, and it lies in a closed arc of half-width $r < \pi$ about
$-e^{i\beta}$. Used by `unitary_product_evolution`. -/
theorem exists_isHermitian_evol_eq_of_unitary {U : 𝕄} (hU : star U * U = 1) :
    ∃ A : 𝕄, A.IsHermitian ∧ UnitaryProducts.evol A 1 = U := by
  -- `matrixCStarAlgebra` is the C*-algebra structure built from the `Matrix.Norms.L2Operator`
  -- instances, so its norm is the ℓ² operator norm used everywhere else; it is needed for
  -- `spectrum.subset_circle_of_unitary` and the continuous functional calculus.
  letI := UnitaryProducts.matrixCStarAlgebra d
  -- Step 1: the spectrum is finite, so some β ∈ (-π, π) is not the argument of an eigenvalue.
  have hfin : (spectrum ℂ U).Finite := Matrix.finite_spectrum U
  obtain ⟨β, hβ, hβs⟩ := ((Set.Ioo_infinite (by linarith [Real.pi_pos] : -π < π)).diff
    (hfin.image Complex.arg)).nonempty
  -- Step 2: each spectral point is `e^{i(α + ψ)}` with `|ψ| < π`, where `α = β - π`.
  have key : ∀ z ∈ spectrum ℂ U,
      z = Complex.exp ((((β - π) + (z * Complex.exp (-((β - π : ℝ) : ℂ) * I)).arg : ℝ) : ℂ) * I) ∧
        |(z * Complex.exp (-((β - π : ℝ) : ℂ) * I)).arg| < π := by
    intro z hz
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp
      (spectrum.subset_circle_of_unitary (𝕜 := ℂ) (Unitary.mem_iff.mpr ⟨hU, mul_eq_one_comm.mp hU⟩)
        hz)
    have hzexp : z = Complex.exp ((((β - π) + (z * Complex.exp (-((β - π : ℝ) : ℂ) * I)).arg : ℝ)
        : ℂ) * I) := by
      conv_lhs => rw [← UnitaryProducts.exp_neg_I_mul_argBranch (α := β - π) hz1]
      rw [UnitaryProducts.argBranch]; congr 1; push_cast; ring
    refine ⟨hzexp, abs_lt.mpr ⟨Complex.neg_pi_lt_arg _, lt_of_le_of_ne (Complex.arg_le_pi _) ?_⟩⟩
    intro hpi
    rw [hpi, show β - π + π = β by ring] at hzexp
    refine hβs ⟨z, hz, ?_⟩
    rw [hzexp, Complex.arg_exp_mul_I, UnitaryProducts.toIocMod_eq_of_abs_lt (abs_lt.mpr hβ)]
  -- Step 3: r, the largest |ψ| over the finite spectrum, is below π.
  set f : ℂ → ℝ := fun z ↦ |(z * Complex.exp (-((β - π : ℝ) : ℂ) * I)).arg| with hf
  set S : Finset ℝ := insert 0 (hfin.toFinset.image f) with hS
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  have hle : ∀ z ∈ spectrum ℂ U, f z ≤ S.max' hSne := fun z hz ↦
    S.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hz)))
  have hr0 : 0 ≤ S.max' hSne := S.le_max' _ (Finset.mem_insert_self _ _)
  have hr : S.max' hSne < π := by
    refine (Finset.max'_lt_iff _ _).mpr fun y hy ↦ ?_
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Real.pi_pos
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (key z (hfin.mem_toFinset.mp hz)).2
  -- Step 4: `exists_isHermitian_evol_eq` takes A = cfc (argBranch α) U, a Hermitian logarithm
  -- of U whose branch cut misses the spectrum.
  exact (UnitaryProducts.exists_isHermitian_evol_eq (α := β - π) hr0 hr hU fun z hz ↦
    ⟨_, ⟨by linarith [(abs_le.mp (hle z hz)).1], by linarith [(abs_le.mp (hle z hz)).2]⟩,
      (key z hz).1⟩).imp fun A h ↦ ⟨h.1, h.2.2⟩

/-- Supports "a finite product is the exact evolution of a piecewise-constant Hamiltonian" (§1,
first paragraph; the product is that of equation (2.4) (`eq:piecewise-product`)): unitaries $U_0,
\dots, U_{n-1}$ have
Hermitian generators $A_j$ with $e^{-iA_j} = U_j$, and the product (2.4) (`eq:piecewise-product`) of
the family equal to
$A_j$
on $(j,j+1)$ is $U_{n-1} \cdots U_0$.

Reading the statement against the paper:
* `evol (A j) 1` is $e^{-iA_j}$, `pieceProduct (fun _ ↦ 1) A n` is (2.4) (`eq:piecewise-product`)
with all durations $1$,
  and `((List.range n).map U).reverse.prod` is $U_{n-1} \cdots U_0$, latest factor on the left.
* Unitarity of $U_j$ is `star (U j) * U j = 1`.
* Only `A j` with `j < n` is constrained; the proof pads with `A j = 0` beyond.
* That (2.4) (`eq:piecewise-product`) is the end value of the evolution of the piecewise-constant
family is the piecewise
  clause of `regulated_evolution_rounded`.
* Stronger than the paper's setting: no $d \ge 1$.

The paper states this as a standard fact, without proof. The proof: (1) each $U_j$ has a Hermitian
logarithm (`exists_isHermitian_evol_eq_of_unitary`, by the continuous functional calculus with a
branch cut off the finite spectrum); (2) induction on $m \le n$ telescopes the product. -/
theorem unitary_product_evolution :
    ∀ (n : ℕ) (U : ℕ → 𝕄), (∀ j < n, star (U j) * U j = 1) →
      ∃ A : ℕ → 𝕄, (∀ j, (A j).IsHermitian) ∧ (∀ j < n, UnitaryProducts.evol (A j) 1 = U j) ∧
        UnitaryProducts.pieceProduct (fun _ ↦ 1) A n = ((List.range n).map U).reverse.prod := by
  intro n U hU
  -- Step 1: a Hermitian logarithm of each factor; `A j = 0` for `j ≥ n`. Every choice works.
  have hex : ∀ j, ∃ B : 𝕄, B.IsHermitian ∧ (j < n → UnitaryProducts.evol B 1 = U j) := fun j ↦
    if hj : j < n then
      (exists_isHermitian_evol_eq_of_unitary (hU j hj)).imp fun B h ↦ ⟨h.1, fun _ ↦ h.2⟩
    else ⟨0, Matrix.isHermitian_zero, fun h ↦ absurd h hj⟩
  choose A hA hAU using hex
  refine ⟨A, hA, hAU, ?_⟩
  -- Step 2: by induction, the first m unit pieces give U_{m-1} ⋯ U_0.
  have hprod : ∀ m ≤ n,
      UnitaryProducts.pieceProduct (fun _ ↦ 1) A m = ((List.range m).map U).reverse.prod := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      change UnitaryProducts.evol (A m) 1 * UnitaryProducts.pieceProduct (fun _ ↦ 1) A m = _
      rw [ih (Nat.le_of_succ_le hm), hAU m hm, List.range_succ, List.map_append,
        List.map_singleton, List.reverse_append, List.reverse_singleton, List.prod_append,
        List.prod_singleton]
  exact hprod n le_rfl


end UnitaryProducts.Paper
