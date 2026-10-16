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

- `band`
- `entry_truncation_bounds`
- `inverse_level_variation_bound`
- `jrsCoefficient`
- `jrsCoefficientTracked`
- `jrs_coefficient_tracked_band`
- `levelFunctionData`
- `midpointProduct`
- `midpointProduct_succ`
- `piecewise_product_error_le_integral`
- `sparsity`
- `truncation`
- `truncation_bits`
- `truncation_error`
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

omit [NeZero d] in
/-- The facts of the paragraph before Example 3.2, bundled with a Duhamel bound:
(1) the Schur test $\|E\|\le s\|E\|_{\max}$ for a Hermitian $s$-sparse $E$; (2) for an odd
function $F$ and Hermitian $A$, $A^{(F)}$ is Hermitian, zero entries stay zero, and
$\|A-A^{(F)}\|\le s\|A-A^{(F)}\|_{\max}$ when $A$ is $s$-sparse; (3) if $H^{(F)}=G_j$ on the open
pieces of a partition of $[0,T]$ with positive durations $\tau_j$, the induced product is within
$\int_0^T\|H-H^{(F)}\|\,dt$ of $U(T)$ (equation (2.3)).

`truncation_sparse` is (1) and (2); `truncation_bits` uses all three. Only the oddness of $F$ is
used. -/
theorem truncation_error :
    (∀ (E : 𝕄) (s : ℕ), E.IsHermitian → (sparsity s E).1 →
      ‖E‖ ≤ s * (sparsity s E).2) ∧
    (∀ (F : ℝ → ℝ), (∀ x, F (-x) = -F x) →
      ∀ A : 𝕄, A.IsHermitian →
      ((levelFunctionData F).1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (levelFunctionData F).1 A i j = 0) ∧
      ∀ s : ℕ, (sparsity s A).1 →
        ‖A-(levelFunctionData F).1 A‖ ≤
          s * (sparsity s (A-(levelFunctionData F).1 A)).2) ∧
    (∀ (H U : ℝ → 𝕄) (τ : ℕ → ℝ) (G : ℕ → 𝕄) (n : ℕ) (F : ℝ → ℝ),
      (∀ x, F (-x) = -F x) → 0 < n → (∀ j, 0 < τ j) →
      IsRegulated H 0 (UnitaryProducts.switchTime τ n) →
      (∀ t ∈ Icc 0 (UnitaryProducts.switchTime τ n), (H t).IsHermitian) →
      IsEvolution H U 0 (UnitaryProducts.switchTime τ n) →
      (∀ j < n, ∀ t ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ (j+1)),
        (levelFunctionData F).1 (H t) = G j) →
      ‖UnitaryProducts.pieceProduct τ G n-U (UnitaryProducts.switchTime τ n)‖ ≤
        ∫ t in (0:ℝ)..UnitaryProducts.switchTime τ n, ‖H t-(levelFunctionData F).1 (H t)‖) := by
  -- (2): `F 0 = 0` keeps zero entries zero, conjugate symmetry keeps `A^{(F)}` Hermitian, and the
  -- error is then `s`-sparse, so the Schur test applies to it.
  have point : ∀ (F : ℝ → ℝ), (∀ x, F (-x) = -F x) →
      ∀ A : 𝕄, A.IsHermitian →
      ((levelFunctionData F).1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (levelFunctionData F).1 A i j = 0) ∧
      ∀ s : ℕ, (sparsity s A).1 →
        ‖A-(levelFunctionData F).1 A‖ ≤
          s * (sparsity s (A-(levelFunctionData F).1 A)).2 := by
    intro F hodd A hA
    have hzero : F 0 = 0 := Function.Odd.map_zero hodd
    have hh := UnitaryProducts.scalarEntryMap_isHermitian F hodd hA
    have hz : ∀ i j, A i j = 0 → (levelFunctionData F).1 A i j = 0 := fun i j hij ↦
      Complex.ext (by simp [levelFunctionData, UnitaryProducts.scalarEntryMap, hij, hzero])
        (by simp [levelFunctionData, UnitaryProducts.scalarEntryMap, hij, hzero])
    exact ⟨hh, hz, fun s hs ↦ UnitaryProducts.norm_sub_le_sparsity_mul_maxEntryNorm hA hh hs.2 hz⟩
  -- (1) is the Schur test: `‖E‖` is at most the largest absolute row sum, at most `s‖E‖_max`.
  refine ⟨fun E s hE hs ↦ UnitaryProducts.norm_le_sparsity_mul_maxEntryNorm hE hs.2, point, ?_⟩
  -- (3): the truncated family is piecewise constant, hence regulated, and Hermitian by (2); its
  -- evolution `V` ends at the product (`regulated_evolution`), and `duhamel` compares `V` with `U`.
  intro H U τ G n F hodd hn hτ hreg hH hU hc
  have hFr : IsRegulated ((levelFunctionData F).2 H) 0 (UnitaryProducts.switchTime τ n) := by
    simpa only [UnitaryProducts.switchTime_zero] using
      piecewise_regulated ((levelFunctionData F).2 H) (UnitaryProducts.switchTime τ) G n hc
  have hT : 0 < UnitaryProducts.switchTime τ n := by
    exact Finset.sum_pos (fun j _ ↦ hτ j) (Finset.nonempty_range_iff.mpr hn.ne')
  obtain ⟨V, hV, _, _, hv⟩ := regulated_evolution hT
    (fun t ht ↦ (point F hodd (H t) (hH t ht)).1) hFr
  have hb := duhamel hT.le hreg hFr hU hV
  rwa [hv τ G n hτ rfl hc, norm_sub_rev] at hb

omit [NeZero d] in
/-- Support for Example 3.2, bundled with a Duhamel bound for bits: oddness,
componentwise error bounds, preservation of Hermiticity and zero entries, an internal
max-entry bound, and the operator-norm bound for sparse Hermitian matrices. The product
induced by a piecewise-constant truncated path is within $\sqrt2\,s\,2^{-k}T$ of its evolution.
`entry_truncation_bounds` retains the pointwise estimates. -/
theorem truncation_bits (k : ℕ) :
    (∀ x, (truncation (d := d) k).1 (-x) = -(truncation (d := d) k).1 x) ∧
    (∀ (H : ℝ → 𝕄) (T : ℝ), ∀ t ∈ Icc 0 T, ∀ i j,
      |UnitaryProducts.truncBits k (H t i j).re-(H t i j).re| ≤ ((2:ℝ)^k)⁻¹ ∧
      |UnitaryProducts.truncBits k (H t i j).im-(H t i j).im| ≤ ((2:ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄), A.IsHermitian →
      ((truncation k).2.2.1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (truncation k).2.2.1 A i j = 0) ∧
      (sparsity 1 (A-(truncation k).2.2.1 A)).2 ≤
        Real.sqrt 2 * ((2 : ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄) (s : ℕ), A.IsHermitian → (sparsity s A).1 →
      ‖A-(truncation k).2.2.1 A‖ ≤ Real.sqrt 2*s*((2:ℝ)^k)⁻¹) ∧
    (∀ (H U : ℝ → 𝕄) (τ : ℕ → ℝ) (G : ℕ → 𝕄) (n s : ℕ), 0 < n →
      (∀ j, 0 < τ j) →
      IsRegulated H 0 (UnitaryProducts.switchTime τ n) →
      (∀ t ∈ Icc 0 (UnitaryProducts.switchTime τ n), (H t).IsHermitian) →
      (∀ t ∈ Icc 0 (UnitaryProducts.switchTime τ n), (sparsity s (H t)).1) →
      IsEvolution H U 0 (UnitaryProducts.switchTime τ n) →
      (∀ j < n, ∀ t ∈ Ioo (UnitaryProducts.switchTime τ j) (UnitaryProducts.switchTime τ (j+1)),
        (truncation k).2.2.1 (H t) = G j) →
      ‖(piecewiseData ((truncation k).2.2.2 H) 0 (UnitaryProducts.switchTime τ n)).2
        (UnitaryProducts.switchTime τ) G n-U (UnitaryProducts.switchTime τ n)‖ ≤
        Real.sqrt 2*s*((2 : ℝ)^k)⁻¹*UnitaryProducts.switchTime τ n) := by
  -- (i), oddness.
  have hodd : ∀ x, (truncation (d := d) k).1 (-x) = -(truncation (d := d) k).1 x :=
    UnitaryProducts.truncBits_neg k
  -- (ii), max norm: Hermitian and zero-preserving by `truncation_error` (2); an entry error with
  -- real and imaginary parts at most `2^{-k}` has modulus at most `√2·2^{-k}`.
  have hpoint : ∀ A : 𝕄, A.IsHermitian →
      ((truncation k).2.2.1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (truncation k).2.2.1 A i j = 0) ∧
      (sparsity 1 (A-(truncation k).2.2.1 A)).2 ≤ Real.sqrt 2*((2:ℝ)^k)⁻¹ := by
    intro A hA
    have hp := truncation_error.2.1 _ hodd A hA
    exact ⟨hp.1, hp.2.1, UnitaryProducts.maxEntryNorm_le_of_entry_components (by positivity)
      fun i j ↦ ⟨UnitaryProducts.abs_sub_truncBits_le k (A i j).re,
        UnitaryProducts.abs_sub_truncBits_le k (A i j).im⟩⟩
  -- (iii): the Schur test of `truncation_error` (2) and the max-norm bound.
  have hnorm : ∀ (A : 𝕄) (s : ℕ), A.IsHermitian → (sparsity s A).1 →
      ‖A-(truncation k).2.2.1 A‖ ≤ Real.sqrt 2*s*((2:ℝ)^k)⁻¹ := by
    intro A s hA hs
    exact ((truncation_error.2.1 _ hodd A hA).2.2 s hs).trans
      ((mul_le_mul_of_nonneg_left (hpoint A hA).2.2 (Nat.cast_nonneg s)).trans_eq (by ring))
  -- (ii), entrywise: `|[x]_k - x| ≤ 2^{-k}` for the real and imaginary parts.
  refine ⟨hodd, fun H T t ht i j ↦
    ⟨by simpa only [abs_sub_comm] using UnitaryProducts.abs_sub_truncBits_le k (H t i j).re,
      by simpa only [abs_sub_comm] using UnitaryProducts.abs_sub_truncBits_le k (H t i j).im⟩,
    hpoint, hnorm, ?_⟩
  -- The product bound: `truncation_error` (3), then (iii) integrated over `[0,T]`.
  intro H U τ G n s hn hτ hr hH hs hU hc
  have hFr : IsRegulated (fun t ↦ (truncation k).2.2.1 (H t))
      0 (UnitaryProducts.switchTime τ n) := by
    simpa only [UnitaryProducts.switchTime_zero] using
      piecewise_regulated (fun t ↦ (truncation k).2.2.1 (H t)) (UnitaryProducts.switchTime τ) G n hc
  have hT : 0 ≤ UnitaryProducts.switchTime τ n := Finset.sum_nonneg fun j _ ↦ (hτ j).le
  have hb := truncation_error.2.2 H U τ G n _ hodd hn hτ hr hH hU hc
  have hi := ((hr.intervalIntegrable_on hT).sub (hFr.intervalIntegrable_on hT)).norm
  have he := intervalIntegral.integral_mono_on hT hi intervalIntegrable_const
    (fun t ht ↦ hnorm (H t) s (hH t ht) (hs t ht))
  have hcst : (∫ _t in (0:ℝ)..UnitaryProducts.switchTime τ n, Real.sqrt 2*s*((2:ℝ)^k)⁻¹) =
      Real.sqrt 2*s*((2:ℝ)^k)⁻¹*UnitaryProducts.switchTime τ n := by
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm]
  simpa only [piecewiseData, UnitaryProducts.switchTime_succ, add_sub_cancel_left] using
    hb.trans (he.trans_eq hcst)

omit [NeZero d] in
/-- Supporting bounds for **Example 3.2** (bits). The numbered paper statement has
(i) oddness and (ii) the operator-norm bound. The componentwise and max-entry estimates
are intermediate steps in its proof, together with fixed-point and zero-entry facts.

`(truncation k).1` is the sign/floor bit map and `(truncation k).2.2.1 A` its entrywise
matrix action. The final conjunct bounds every Hermitian error with `RowSparse s`;
the paper uses the largest changed-entry count over the path for `s`, including `s = 0`.
The preceding max-entry bound is `(sparsity 1 (A - …)).2 ≤ √2 * (2^k)⁻¹`, independent
of the dummy `1`. Neither this auxiliary norm nor fixed-point classification is a
separate part of the current example. No positive-dimension hypothesis is needed.

Conjuncts in order: (1) oddness and fixed points x = m/2^k; dyadic entries are unchanged.
(2) At every t in [0,T], both components of each entry change by at most 2^(-k).
(3) Hermiticity, preservation of zero entries, and the max-entry error bound
(the second component of `sparsity` is the max-entry norm).
(4) The paper's operator-norm bound, with s nonzeros per row of the error matrix.

The scalar and entry estimates come from `truncation_bits`; the Schur test applied
to the Hermitian error gives the operator-norm bound. The paper-proof head
`PaperProof.ex_truncation_bits` follows the paper's proof directly. -/
theorem entry_truncation_bounds (k : ℕ) :
    ((∀ x, (truncation (d := d) k).1 (-x) = -(truncation (d := d) k).1 x) ∧
      ∀ x, (truncation (d := d) k).1 x = x ↔ ∃ m : ℤ, x = m / 2 ^ k) ∧
    (∀ (H : ℝ → 𝕄) (T : ℝ), ∀ t ∈ Icc 0 T, ∀ i j,
      |UnitaryProducts.truncBits k (H t i j).re-(H t i j).re| ≤ ((2:ℝ)^k)⁻¹ ∧
      |UnitaryProducts.truncBits k (H t i j).im-(H t i j).im| ≤ ((2:ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄), A.IsHermitian →
      ((truncation k).2.2.1 A).IsHermitian ∧
      (∀ i j, A i j = 0 → (truncation k).2.2.1 A i j = 0) ∧
      (sparsity 1 (A-(truncation k).2.2.1 A)).2 ≤
        Real.sqrt 2 * ((2 : ℝ)^k)⁻¹) ∧
    (∀ (A : 𝕄) (s : ℕ), A.IsHermitian →
      UnitaryProducts.RowSparse s (A-(truncation k).2.2.1 A) →
      ‖A-(truncation k).2.2.1 A‖ ≤ Real.sqrt 2*s*((2:ℝ)^k)⁻¹) := by
  obtain ⟨hodd, hcomp, hpoint, -, -⟩ := truncation_bits (d := d) k
  refine ⟨⟨hodd, UnitaryProducts.truncBits_eq_self_iff k⟩, hcomp, hpoint, fun A s hA hs ↦ ?_⟩
  -- (ii): the Schur test for the Hermitian error, whose rows have at most `s` nonzero entries,
  -- and the internal max-entry bound.
  exact (UnitaryProducts.norm_le_sparsity_mul_maxEntryNorm (hA.sub (hpoint A hA).1) hs).trans
    ((mul_le_mul_of_nonneg_left (hpoint A hA).2.2 (Nat.cast_nonneg s)).trans_eq (by ring))

/-- **Remark 3.9 (variation support)** (total variation), with the checkpoints and midpoints of
§3.2. `.1` is the
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
  definition: they are `UnitaryProducts.inverseLevelTime` (Remark 3.9). -/
def variationCheckpoints (H : ℝ → 𝕄) (T : ℝ) (n : ℕ) :
    (ℝ → ℝ≥0∞) × ((ℕ → ℝ) → Prop) × ((ℕ → ℝ) → ℕ → ℝ) :=
  (fun t ↦ eVariationOn H (Icc 0 t),
    fun t ↦ Monotone t ∧ t 0 = 0 ∧ t n = T,
    fun t j ↦ (t j + t (j+1))/2)

omit [NeZero d] in
/-- **Remark 3.9** (equal-variation checkpoints). Suppose $\ell<\infty$ and $n\ge1$. (i) The
equal-variation checkpoints are nondecreasing; (ii) for $t_j<x\le y<t_{j+1}$,
$\|H(y)-H(x)\|\le\ell/n$.

Reading the statement against the paper:
* `ℓ t` is the real total variation up to $t$, the `toReal` of `(variationCheckpoints H T 0).1 t`;
  under `hfin` it is finite, so `toReal` is faithful. The paper's $\ell$ is `ℓ T`.
* `t := inverseLevelTime ℓ T n` are the equal-variation checkpoints: $t_0=0$, $t_j=T$ for
  $j\ge n$, and an infimum for $0<j<n$. The second conjunct restates the paper's formula
  $t_j=\inf\{x\in[0,T]:\ell(x)\ge j\ell/n\}$; the set contains $T$ and is bounded below, so `sInf`
  is the infimum.
* (i) is `(variationCheckpoints H T n).2.1 t`: `t` is monotone with $t_0=0$ and $t_n=T$.
* Stronger than the paper: no $d\ge1$. Every explicit hypothesis is used.

The proof follows the paper's: (1) the superlevel sets contain $T$ and shrink as $j$ grows, so
their infima are nondecreasing (`inverseLevelTime_variation_mono`); (2) for $j>0$, $x>t_j$ puts a
point of the $j$th set below $x$, so $j\ell/n\le\ell(x)$, and for $j+1<n$, $y<t_{j+1}$ gives
$\ell(y)<(j+1)\ell/n$, with $0\le\ell(t)\le\ell$ at $j=0$ and $j+1=n$; (3)
$\|H(y)-H(x)\|\le\ell(y)-\ell(x)\le\ell/n$ (`inverseLevelTime_variation_norm_sub_le`). -/
theorem inverse_level_variation_bound {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hfin : (variationCheckpoints H T 0).1 T < ⊤) (n : ℕ) (hn : 1 ≤ n) :
    let ℓ := fun t ↦ ((variationCheckpoints H T 0).1 t).toReal
    let t := UnitaryProducts.inverseLevelTime ℓ T n
    (variationCheckpoints H T n).2.1 t ∧
    (∀ j, 0 < j → j < n →
      t j = sInf {x ∈ Icc 0 T | (j : ℝ)*ℓ T/n ≤ ℓ x}) ∧
    ∀ j < n, ∀ x y, t j < x → x ≤ y → y < t (j+1) →
      ‖H y-H x‖ ≤ ℓ T/n := by
  have hbv : BoundedVariationOn H (Icc 0 T) := ne_of_lt hfin
  have hn' : 0 < n := hn
  -- After unfolding, `(eVariationOn H (Icc 0 t)).toReal` is definitionally `variationGauge H 0 t`,
  -- the form in which the `inverseLevelTime_variation_*` lemmas below are stated.
  dsimp only [variationCheckpoints]
  refine ⟨⟨UnitaryProducts.inverseLevelTime_variation_mono H hT.le,
    UnitaryProducts.inverseLevelTime_zero _ T n, UnitaryProducts.inverseLevelTime_last _ T hn'⟩,
    ?_, ?_⟩
  · intro j hj hjn
    exact UnitaryProducts.inverseLevelTime_variation_eq H T (Nat.ne_of_gt hj) hjn
  · intro j hj x y hx hxy hy
    exact UnitaryProducts.inverseLevelTime_variation_norm_sub_le hbv hT.le hj
      ⟨hx.trans_le hxy, hy⟩ ⟨hx, hxy.trans_lt hy⟩

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
/-- The midpoint product (Definition 3.5) one factor at a time: on $t_0,\dots,t_{n+1}$ it is
$e^{-i(t_{n+1}-t_n)A(t_{n+1/2})}$, where $t_{n+1/2}=(t_n+t_{n+1})/2$, times the midpoint product on
$t_0,\dots,t_n$. With `midpointProduct_zero`, this is the explicit product of the paper. -/
theorem midpointProduct_succ (A : ℝ → 𝕄) (n : ℕ) (t : ℕ → ℝ) :
    midpointProduct A (n + 1) t =
      UnitaryProducts.evol (A ((t n + t (n + 1)) / 2)) (t (n + 1) - t n) *
        midpointProduct A n t := by
  -- The first `n` durations of the checkpoints `t₀, …, t_{n+1}` are those of `t₀, …, t_n`.
  have hcongr : ∀ k ≤ n,
      UnitaryProducts.pieceProduct (UnitaryProducts.scheduleDuration t (n + 1))
        (fun j ↦ id (A ((t j + t (j + 1)) / 2))) k =
      UnitaryProducts.pieceProduct (UnitaryProducts.scheduleDuration t n)
        (fun j ↦ id (A ((t j + t (j + 1)) / 2))) k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [UnitaryProducts.pieceProduct]
      rw [ih (Nat.le_of_succ_le hk), UnitaryProducts.scheduleDuration,
        UnitaryProducts.scheduleDuration, if_pos (show k < n + 1 by omega),
        if_pos (show k < n by omega)]
  unfold midpointProduct UnitaryProducts.heldProduct
  simp only [UnitaryProducts.pieceProduct]
  rw [hcongr n le_rfl, UnitaryProducts.scheduleDuration, if_pos (Nat.lt_succ_self n)]
  rfl

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

/-- The data of the Jansen–Ruskai–Seiler bound (§3.3) for a Hermitian family $F$ on $[0,1]$ with
a set $B(s)$ of $m$ eigenvalues and a gap lower bound $g$; the band itself is tracked by
`jrsCoefficientTracked`.

* `.1`: $F$ is $C^2$ on $[0,1]$, $g$ is continuous, and for every $s\in[0,1]$: $g(s)>0$, exactly
  $m$ eigenvalues of $F(s)$ lie in $B(s)$ (eigenvalue indices are filtered, so multiplicities
  count), and $g(s)$ is at most the distance from each eigenvalue in $B(s)$ to each eigenvalue
  outside it.
* `.2.1` is the pair of endpoint projectors $P=P_{B(0)}(F(0))$ and $Q=P_{B(1)}(F(1))$.
* `.2.2` is `jrsFunctional m ‖F'‖ ‖F''‖ g`, the coefficient $J_m(F)$ defined before
  Example 3.7 with the gap $\Gamma$ replaced by $g$:
  $\sum_{s\in\{0,1\}}m\|F'(s)\|/g(s)^2+\int_0^1\bigl(m\|F''\|/g^2+7m\sqrt m\,\|F'\|^2/g^3\bigr)$.

The derivatives are `derivWithin` on $[0,1]$, one-sided at the ends. `derivWithin` is $0$ where
$F$ is not differentiable and real division by $0$ is $0$, so `.2.2` is the paper's coefficient
only under `.1`. The paper's case is $g=\Gamma$ (`jrs_coefficient_tracked_exactGap`). -/
def jrsCoefficient (F : ℝ → 𝕄)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ) : Prop × (𝕄 × 𝕄) × ℝ := by
  classical
  exact
    (ContDiffOn ℝ 2 F (Icc 0 1) ∧ ContinuousOn g (Icc 0 1) ∧
      ∀ s (hs : s ∈ Icc (0 : ℝ) 1), 0 < g s ∧
        (Finset.univ.filter (fun i ↦ (hF s hs).eigenvalues i ∈ B s)).card = m ∧
        ∀ i j, (hF s hs).eigenvalues i ∈ B s →
          (hF s hs).eigenvalues j ∉ B s →
          g s ≤ |(hF s hs).eigenvalues i-(hF s hs).eigenvalues j|,
      (UnitaryProducts.specProj (hF 0 ⟨le_rfl,zero_le_one⟩) (B 0),
        UnitaryProducts.specProj (hF 1 ⟨zero_le_one,le_rfl⟩) (B 1)),
      UnitaryProducts.jrsFunctional m
        (fun s ↦ ‖derivWithin F (Icc (0 : ℝ) 1) s‖)
        (fun s ↦ ‖derivWithin (derivWithin F (Icc (0 : ℝ) 1)) (Icc 0 1) s‖) g)

/-- `jrsCoefficient` with the band tracked continuously. `.1` adds to the hypotheses of
`jrsCoefficient` that $m>0$ and that $B(s)=[a(s),b(s)]$ with $a\le b$ continuous on $[0,1]$ and
$a(s)$, $b(s)$ outside the spectrum of $F(s)$; `.2` is the data of `jrsCoefficient` (endpoint
projectors and coefficient). By `jrs_coefficient_tracked_band`, `.1` says exactly that $B$ is a
band of $m$ eigenvalues (`band`) of a $C^2$ family and $g$ is a positive continuous lower bound
on its gap: the hypothesis of the Jansen–Ruskai–Seiler consumers. -/
def jrsCoefficientTracked (F : ℝ → 𝕄)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ) : Prop × (𝕄 × 𝕄) × ℝ :=
  let data := jrsCoefficient F hF m g B
  (data.1 ∧ 0 < m ∧ ∃ a b : ℝ → ℝ,
    ContinuousOn a (Icc 0 1) ∧ ContinuousOn b (Icc 0 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, B s = Icc (a s) (b s) ∧ a s ≤ b s ∧
        a s ∉ spectrum ℝ (F s) ∧ b s ∉ spectrum ℝ (F s), data.2)

/-- A band of $m$ eigenvalues of a Hermitian family $F$ on $[0,1]$ (Definition 2.5 and the
paragraph after it), with its endpoint projectors.

* `.1`: $m>0$; for every $s$, exactly $m$ eigenvalues of $F(s)$ lie in $B(s)$, counted with
  multiplicity; and $B(s)=[a(s),b(s)]$ with $a\le b$ continuous on $[0,1]$ and $a(s)$, $b(s)$
  outside the spectrum of $F(s)$.
* `.2` is the pair of endpoint projectors $P_{B(0)}(F(0))$ and $P_{B(1)}(F(1))$.

Properness (some eigenvalue of $F(s)$ outside $B(s)$) is not part of `.1`; `bandData`
(Definition 2.5) adds it. The `classical` only supplies decidability for the eigenvalue
filter. -/
def band (F : ℝ → 𝕄)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (m : ℕ) (B : ℝ → Set ℝ) : Prop × (𝕄 × 𝕄) := by
  classical
  exact
    (0 < m ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (Finset.univ.filter (fun i ↦ (hF s hs).eigenvalues i ∈ B s)).card = m) ∧
      ∃ a b : ℝ → ℝ, ContinuousOn a (Icc 0 1) ∧ ContinuousOn b (Icc 0 1) ∧
        ∀ s ∈ Icc (0 : ℝ) 1, B s = Icc (a s) (b s) ∧ a s ≤ b s ∧
          a s ∉ spectrum ℝ (F s) ∧ b s ∉ spectrum ℝ (F s),
      (UnitaryProducts.specProj (hF 0 ⟨le_rfl,zero_le_one⟩) (B 0),
        UnitaryProducts.specProj (hF 1 ⟨zero_le_one,le_rfl⟩) (B 1)))


omit [NeZero d] in
/-- Unbundles `jrsCoefficientTracked`: its hypothesis is exactly a band of $m$ eigenvalues
(`band`, Definition 2.5) of a $C^2$ family together with a positive continuous lower bound $g$ on
its spectral gap, and its endpoint projectors are the band's. The Jansen–Ruskai–Seiler consumers
use it to translate between the two forms. -/
theorem jrs_coefficient_tracked_band (F : ℝ → 𝕄)
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, (F s).IsHermitian)
    (m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ) :
    ((jrsCoefficientTracked F hF m g B).1 ↔
      ContDiffOn ℝ 2 F (Icc 0 1) ∧ ContinuousOn g (Icc 0 1) ∧
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1), 0 < g s ∧
        ∀ i j, (hF s hs).eigenvalues i ∈ B s → (hF s hs).eigenvalues j ∉ B s →
          g s ≤ |(hF s hs).eigenvalues i-(hF s hs).eigenvalues j|) ∧
      (band F hF m B).1) ∧
    (jrsCoefficientTracked F hF m g B).2.1 = (band F hF m B).2 := by
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · rintro ⟨⟨hc, hg, hs⟩, hm, a, b, ha, hb, hab⟩
    exact ⟨hc, hg, fun s hs' ↦ ⟨(hs s hs').1, (hs s hs').2.2⟩, hm,
      fun s hs' ↦ (hs s hs').2.1, a, b, ha, hb, hab⟩
  · rintro ⟨hc, hg, hs, hm, hcard, a, b, ha, hb, hab⟩
    exact ⟨⟨hc, hg, fun s hs' ↦ ⟨(hs s hs').1, hcard s hs', (hs s hs').2⟩⟩, hm, a, b, ha, hb, hab⟩

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
