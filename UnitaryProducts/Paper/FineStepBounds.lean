/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Preliminaries

/-!
# Fine steps: level truncation, total variation, midpoint products

## Declarations

- `levelFunctionData`
- `midpointProduct`
- `piecewise_product_error_le_integral`
- `sparsity`
- `truncation`
- `variationCheckpoints`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal
open Complex Set MeasureTheory Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Bit truncation, defined inline in **Example 3.2**:
$[x]_k=\operatorname{sgn}(x)\,2^{-k}\lfloor2^k|x|\rfloor$ for an integer $k\ge0$, and
$H^{(k)}=H^{([\cdot]_k)}$. The four forms are bundled.

* `.1` is `truncBits k`, $[x]_k$ on reals: `level k x / 2^k`, where `level k x` is
  $\lfloor2^kx\rfloor$ for $x\ge0$ and $\lceil2^kx\rceil$ for $x<0$; this is the paper's formula.
* `.2.1` is `truncBitsC k`, $[\cdot]_k$ on the real and imaginary parts of a complex number.
* `.2.2.1` is `truncHerm k`, the entrywise action $A\mapsto A^{(k)}$ on matrices. It is
  definitionally `(levelFunctionData (truncation k).1).1`, which lets `truncation_bits` reuse
  `truncation_error`.
* `.2.2.2` is the action $H\mapsto H^{(k)}$ on families, pointwise in $t$.

All four are total functions; there are no junk values. -/
def truncation (k : ℕ) :
    (ℝ → ℝ) × (ℂ → ℂ) × (𝕄 → 𝕄) × ((ℝ → 𝕄) → ℝ → 𝕄) :=
  (UnitaryProducts.truncBits k, UnitaryProducts.truncBitsC k, UnitaryProducts.truncHerm k,
    fun H t ↦ UnitaryProducts.truncHerm k (H t))

/-- **Definition 3.1**: entrywise action of any real function on matrices (`.1`)
and pointwise action on families (`.2`). The matrix entries are
$F(\operatorname{Re} A_{pq}) + i F(\operatorname{Im} A_{pq})$.
Oddness is assumed separately where Hermitian matrices are required. -/
def levelFunctionData (F : ℝ → ℝ) :
    (𝕄 → 𝕄) × ((ℝ → 𝕄) → ℝ → 𝕄) :=
  (UnitaryProducts.scalarEntryMap F,
   fun H t ↦ UnitaryProducts.scalarEntryMap F (H t))

/-- The $s$-sparse condition, paired with the max-entry norm.

* `.1` is `0 < s ∧ RowSparse s A`: $s$ is a positive integer and each row of $A$ has at most $s$
  nonzero entries. `IsSparse` (`Spectral/CircularBands.lean`) is this component. The paper's
  statements use `RowSparse` of the truncation error instead; `.1` is the hypothesis of the
  bridges `…_of_sparse`.
* `.2` is $\|A\|_{\max}=\max_{p,q}|A_{pq}|$ (`maxEntryNorm`, cast to `ℝ`); it does not depend on
  `s`. -/
def sparsity (s : ℕ) (A : 𝕄) : Prop × ℝ :=
  (0 < s ∧ UnitaryProducts.RowSparse s A, (UnitaryProducts.maxEntryNorm A : ℝ))

/-- The total variation, with the checkpoints and midpoints of §3.2. `.1` is the
total variation $\ell(t)$ of $H$ up to time $t$, `.2.1` says that `t` is a sequence of
checkpoints, and `.2.2` is the midpoint map $t_{j+1/2}=(t_j+t_{j+1})/2$.

Reading the statement against the paper:
* `.1 t` is `eVariationOn H (Icc 0 t)`, Mathlib's supremum of $\sum_r\|H(s_{r+1})-H(s_r)\|$ over
  finite monotone sequences in $[0,t]$, for the $\ell^2$ operator norm. Repeated points add $0$
  and adding the endpoints does not decrease a sum, so this is the paper's supremum over
  partitions $0=s_0<\dots<s_m=t$. For $t<0$ the interval is empty and `.1 t = 0`.
* `.1` is valued in `ℝ≥0∞` and depends on neither `T` nor `n`; statements read it as
  `(variationCheckpoints H T 0).1`, with the dummy `n = 0`. They convert it with
  `ENNReal.toReal`, whose junk value sends `⊤` to `0`. The bounded-variation support assumes
  `(variationCheckpoints H T 0).1 T < ⊤`, the paper's $\ell<\infty$, so that the real number is
  the variation.
* `.2.1 t` is `Monotone t ∧ t 0 = 0 ∧ t n = T`, nondecreasing times from $0$ to $T$. Monotonicity
  on all of `ℕ` asks more than $t_0\le\dots\le t_n$, harmlessly: a finite list extends constantly
  by $T$, as `inverseLevelTime` already does.
* `.2.2` is the midpoint map. No statement projects it; consumers write the midpoint
  $(t_j+t_{j+1})/2$ literally. The equal-variation checkpoints are not a component of this
  definition: they are `UnitaryProducts.inverseLevelTime`. -/
def variationCheckpoints (H : ℝ → 𝕄) (T : ℝ) (n : ℕ) :
    (ℝ → ℝ≥0∞) × ((ℕ → ℝ) → Prop) × ((ℕ → ℝ) → ℕ → ℝ) :=
  (fun t ↦ eVariationOn H (Icc 0 t),
    fun t ↦ Monotone t ∧ t 0 = 0 ∧ t n = T,
    fun t j ↦ (t j + t (j+1))/2)

/-- **Definition 3.5 in time** (midpoint products on checkpoints in time). The midpoint product of
a family $A$ on checkpoints $t_0,\dots,t_n$ is
$e^{-i(t_n-t_{n-1})A(t_{n-1/2})}\cdots e^{-i(t_1-t_0)A(t_{1/2})}$, where
$t_{j+1/2}=(t_j+t_{j+1})/2$. The paper's Definition 3.5, over time $T$ on checkpoints
$s_0,\dots,s_N$ in $[0,1]$, is `midpointProductOver A T N s`, which is
`midpointProduct (fun x ↦ T • A x) N s`; on the checkpoints $t_j=Ts_j$ it is also
`midpointProduct (fun t ↦ A (t / T)) N t` (`midpointProductOver_rescale`).

Reading the statement against the paper:
* The body `heldProduct id H n t` is `pieceProduct (scheduleDuration t n) G n` with
  $G_j=H(t_{j+1/2})$: the ordered product of $e^{-i(t_{j+1}-t_j)H(t_{j+1/2})}$, later factors on
  the left. `midpointProduct_zero` and `midpointProduct_succ` unfold it to the paper's product one
  factor at a time.
* The family argument `H` is the paper's $A$.
* Coinciding checkpoints $t_{j+1}=t_j$ give the factor $e^0=1$ (`midpointProduct_succ_of_eq`), so
  the product is that of the family equal to $H(t_{j+1/2})$ on each nonempty $(t_j,t_{j+1})$.
* The product is total: for non-monotone `t` the factors are backward evolutions. Every consumer
  passes checkpoints, which are nondecreasing.
* A truncated family is passed as `H` itself (for example `(truncation k).2.2.2 H`); the slot `Θ`
  of `heldProduct` is `id`. -/
def midpointProduct (H : ℝ → 𝕄) (n : ℕ) (t : ℕ → ℝ) : 𝕄 :=
  UnitaryProducts.heldProduct id H n t

omit [NeZero d] in
/-- The Duhamel bound for a product of exponentials, summed over the intervals (the proof of
Theorem 3.6): for checkpoints $t_0,\dots,t_n$ and Hermitian $G_j$,
$\|\prod_je^{-i(t_{j+1}-t_j)G_j}-U(T)\|\le\sum_j\int_{t_j}^{t_{j+1}}\|H(x)-G_j\|\,dx$.

The paper applies the Duhamel bound once, to the evolution of the piecewise-constant family $G$.
The proof instead
compares $U$ on each interval with the frozen evolution $V(x)=e^{-i(x-t_j)G_j}U(t_j)$ and
telescopes, using that each factor $e^{-i\tau G_j}$ is a contraction; the two bookkeepings agree.
-/
theorem piecewise_product_error_le_integral {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T)
    (hU : IsEvolution H U 0 T) (n : ℕ) (t : ℕ → ℝ)
    (ht : (variationCheckpoints H T n).2.1 t)
    (G : ℕ → 𝕄) (hG : ∀ j < n, (G j).IsHermitian) :
    ‖UnitaryProducts.pieceProduct (UnitaryProducts.scheduleDuration t n) G n-U T‖ ≤
      ∑ j ∈ Finset.range n, ∫ x in t j..t (j+1), ‖H x-G j‖ := by
  have hUi := hU.2.2.1
  obtain ⟨hUc,hU0,_,S,hS,hd⟩ := hU
  -- Step 1 (Duhamel on one interval): `V x = e^{-i(x-t_j)G_j} U(t_j)` is unitary, solves the
  -- frozen equation and starts at `U(t_j)`, so `U(t_{j+1})` is within `∫ ‖H - G_j‖` of
  -- `e^{-i(t_{j+1}-t_j)G_j} U(t_j)`.
  have local_bound : ∀ j < n,
      ‖U (t (j+1))-UnitaryProducts.evol (G j) (t (j+1)-t j)*U (t j)‖ ≤
        ∫ x in t j..t (j+1), ‖H x-G j‖ := by
    intro j hj
    have hab := ht.1 (Nat.le_succ j)
    have hsub : Icc (t j) (t (j+1)) ⊆ Icc 0 T :=
      Icc_subset_Icc (ht.2.1 ▸ ht.1 (Nat.zero_le j)) (ht.2.2 ▸ ht.1 hj)
    let V := fun x ↦ UnitaryProducts.evol (G j) (x-t j)*U (t j)
    have hV : ∀ x ∈ Icc (t j) (t (j+1)),
        HasDerivWithinAt V (-I • (G j*V x)) (Icc (t j) (t (j+1))) x := fun x _ ↦ by
      simpa only [V, Function.comp_def, id_eq, one_smul, one_mul, mul_one, smul_mul_assoc,
        mul_assoc] using (((UnitaryProducts.hasDerivAt_evol (G j) (x-t j)).scomp x
          ((hasDerivAt_id x).sub_const (t j))).mul_const (U (t j))).hasDerivWithinAt
    have hvu : ∀ x ∈ Icc (t j) (t (j+1)), star (V x)*V x=1 := fun x _ ↦ by
      dsimp [V]
      rw [star_mul, mul_assoc, ← mul_assoc (star (UnitaryProducts.evol _ _)),
        UnitaryProducts.star_evol_mul_self (hG j hj), one_mul]
      exact hUi _ (hsub ⟨le_rfl,hab⟩)
    have hi : IntervalIntegrable (fun x ↦ H x-G j) volume (t j) (t (j+1)) :=
      ((hreg.intervalIntegrable_on hT.le).mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hT.le]; exact hsub)).sub intervalIntegrable_const
    have hb := UnitaryProducts.norm_sub_le_integral_sub_off_countable S hS hab
      (hUc.mono hsub)
      (fun x hx ↦ (hV x hx).continuousWithinAt)
      (fun x hx hn ↦ (hd x (hsub hx) hn).mono hsub)
      (fun x hx _ ↦ hV x hx) (fun x hx ↦ hUi x (hsub hx)) hvu
      (by simp only [V, sub_self, UnitaryProducts.evol_zero, one_mul]) hi.norm
    exact hb
  -- Step 2 (telescoping): by induction on `m`, `U(t_m)` is within the sum of the first `m` local
  -- errors of the product of the first `m` factors; the new factor is a contraction.
  have acc : ∀ m ≤ n,
      ‖U (t m)-UnitaryProducts.pieceProduct (UnitaryProducts.scheduleDuration t n) G m‖ ≤
        ∑ j ∈ Finset.range m, ∫ x in t j..t (j+1), ‖H x-G j‖ := by
    intro m
    induction m with
    | zero => intro hm; simp only [ht.2.1,hU0,UnitaryProducts.pieceProduct,sub_self,norm_zero,
        Finset.range_zero,Finset.sum_empty,le_refl]
    | succ m ih =>
      intro hm
      have hmn : m < n := hm
      rw [Finset.sum_range_succ, UnitaryProducts.pieceProduct,
        show UnitaryProducts.scheduleDuration t n m = t (m+1)-t m by
          simp only [UnitaryProducts.scheduleDuration, if_pos hmn]]
      calc
        _ ≤ ‖U (t (m+1))-UnitaryProducts.evol (G m) (t (m+1)-t m)*U (t m)‖ +
            ‖UnitaryProducts.evol (G m) (t (m+1)-t m)*U (t m)-
              UnitaryProducts.evol (G m) (t (m+1)-t m)*
                UnitaryProducts.pieceProduct (UnitaryProducts.scheduleDuration t n) G m‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (∫ x in t m..t (m+1), ‖H x-G m‖) +
            ∑ j ∈ Finset.range m, ∫ x in t j..t (j+1), ‖H x-G j‖ := by
          apply add_le_add (local_bound m hmn)
          rw [← mul_sub]
          exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
            (UnitaryProducts.norm_evol_le (hG m hmn) _) (norm_nonneg _)).trans
            (by simpa only [one_mul] using ih hmn.le))
        _ = _ := add_comm _ _
  -- Step 3: take `m = n`, where `t_n = T`.
  rw [norm_sub_rev, ← ht.2.2]
  exact acc n le_rfl

/-- A band of a unitary family $W$ on $[0,1]$ cut out by the moving arcs
$\{e^{-i\theta}:\alpha(s)<\theta<\beta(s)\}$ (the unitary-family clause of Definition 2.5):
$\alpha$ and $\beta$ are continuous, $\alpha(s)<\beta(s)<\alpha(s)+2\pi$, the arc endpoints
$e^{-i\alpha(s)}$ and $e^{-i\beta(s)}$ lie outside the spectrum of $W(s)$, and the spectrum meets
both the open arc and the complementary arc $\{e^{-i\theta}:\beta(s)<\theta<\alpha(s)+2\pi\}$.
The predicate does not require $W$ to be unitary. -/
def circularBand (W : ℝ → 𝕄) (α β : ℝ → ℝ) : Prop :=
  ContinuousOn α (Icc (0:ℝ) 1) ∧ ContinuousOn β (Icc (0:ℝ) 1) ∧
  ∀ s ∈ Icc (0:ℝ) 1,
    α s<β s ∧ β s<α s+2*Real.pi ∧
    Complex.exp (-Complex.I*(α s:ℂ)) ∉ spectrum ℂ (W s) ∧
    Complex.exp (-Complex.I*(β s:ℂ)) ∉ spectrum ℂ (W s) ∧
    (∃ θ ∈ Ioo (α s) (β s), Complex.exp (-Complex.I*(θ:ℂ)) ∈ spectrum ℂ (W s)) ∧
    (∃ θ ∈ Ioo (β s) (α s+2*Real.pi), Complex.exp (-Complex.I*(θ:ℂ)) ∈ spectrum ℂ (W s))

end UnitaryProducts.Paper
