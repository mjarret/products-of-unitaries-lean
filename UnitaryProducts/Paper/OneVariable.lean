/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.EvolutionAndFineSteps

/-!
# Paths on the normalized interval

## Declarations

- `checkpoints_rescale`
- `checkpoints_unscale`
- `evol_smul_eq`
- `midpointProductOver`
- `midpointProductOver_eq`
- `midpointProductOver_rescale`
- `osc_rescale`
- `path_midpoint_product_error_and_infimum`
- `pieceProduct_congr_evol`
- `regulated_comp_mul`
- `regulated_rescale`
- `regulated_unscale`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology ENNReal Pointwise
open Complex Set MeasureTheory Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- Supports the substitution $t=Ts$ in §3: two ordered products whose factors agree are equal. -/
theorem pieceProduct_congr_evol {τ τ' : ℕ → ℝ} {G G' : ℕ → 𝕄}
    (h : ∀ j, UnitaryProducts.evol (G j) (τ j) = UnitaryProducts.evol (G' j) (τ' j)) (n : ℕ) :
    UnitaryProducts.pieceProduct τ G n = UnitaryProducts.pieceProduct τ' G' n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [UnitaryProducts.pieceProduct, h n, ih]

omit [NeZero d] in
/-- Supports Definition 3.5: $e^{-iu(TX)}=e^{-i(Tu)X}$. -/
theorem evol_smul_eq (X : 𝕄) (T u : ℝ) :
    UnitaryProducts.evol (T • X) u = UnitaryProducts.evol X (T * u) := by
  unfold UnitaryProducts.evol
  congr 1; rw [smul_comm (-I) T X, smul_smul, mul_comm]

/-- **Definition 3.5** (midpoint products over time $T$). The midpoint product of a family $A$
over time $T$ on checkpoints $s_0,\ldots,s_N$ is
$e^{-iT(s_N-s_{N-1})A(s_{N-1/2})}\cdots e^{-iT(s_1-s_0)A(s_{1/2})}$, where
$s_{j+1/2}=(s_j+s_{j+1})/2$.

Reading the statement against the paper:
* The body is `midpointProduct` of the family $TA$ on the checkpoints `s`: its factor $j$ is
  `evol (T • A s_{j+1/2}) (s_{j+1}-s_j)`, which is $e^{-iT(s_{j+1}-s_j)A(s_{j+1/2})}$
  (`midpointProductOver_eq` writes it out).
* The family argument `A` is the paper's $A$, and `n` is the paper's $N$.
* As for `midpointProduct`, the product is total, and coinciding checkpoints give the factor $1$. -/
def midpointProductOver (A : ℝ → 𝕄) (T : ℝ) (n : ℕ) (s : ℕ → ℝ) : 𝕄 :=  -- Easier-to-read statement (v1.1.0): https://github.com/mjarret/products-of-unitaries-lean/blob/v1.1.0/UnitaryProducts/Paper/OneVariable.lean#L65
  midpointProduct (fun x ↦ T • A x) n s

omit [NeZero d] in
/-- Supports **Definition 3.5**: the midpoint product over time $T$ is the ordered product of the
factors $e^{-i(Ts_{j+1}-Ts_j)A(s_{j+1/2})}$. -/
theorem midpointProductOver_eq (A : ℝ → 𝕄) (T : ℝ) (n : ℕ) (s : ℕ → ℝ) :
    midpointProductOver A T n s = UnitaryProducts.pieceProduct
      (UnitaryProducts.scheduleDuration (fun j ↦ T * s j) n)
      (fun j ↦ A ((s j + s (j + 1)) / 2)) n := by
  unfold midpointProductOver midpointProduct UnitaryProducts.heldProduct
  refine pieceProduct_congr_evol (fun j ↦ ?_) n
  simp only [id, UnitaryProducts.scheduleDuration, evol_smul_eq]
  split_ifs <;> simp [mul_sub]

omit [NeZero d] in
/-- Supports the substitution $t=Ts$ in §3: the midpoint product of $t\mapsto A(t/T)$ on the
checkpoints $Ts_j$ is the midpoint product of $A$ over time $T$ on the checkpoints $s_j$. -/
theorem midpointProductOver_rescale (A : ℝ → 𝕄) {T : ℝ} (hT : T ≠ 0) (n : ℕ) (s : ℕ → ℝ) :
    midpointProduct (fun t ↦ A (t / T)) n (fun j ↦ T * s j) = midpointProductOver A T n s := by
  rw [midpointProductOver_eq]
  unfold midpointProduct UnitaryProducts.heldProduct
  refine pieceProduct_congr_evol (fun j ↦ ?_) n
  simp only [id, show (T * s j + T * s (j + 1)) / 2 / T = (s j + s (j + 1)) / 2 by field_simp]

omit [NeZero d] in
/-- Supports the auxiliary integrated midpoint estimate: the substitution $t=Ts$ in its
oscillation term. -/
theorem osc_rescale (H : ℝ → 𝕄) {T : ℝ} (hT : 0 < T) (n : ℕ) (s : ℕ → ℝ) :
    ∑ j ∈ Finset.range n, ∫ x in T * s j..T * s (j + 1),
        ‖H (x / T) - H ((T * s j + T * s (j + 1)) / 2 / T)‖ =
      T * ∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1), ‖H x - H ((s j + s (j + 1)) / 2)‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hm : (T * s j + T * s (j + 1)) / 2 / T = (s j + s (j + 1)) / 2 := by field_simp
  have hc := intervalIntegral.integral_comp_div
    (fun y ↦ ‖H y - H ((s j + s (j + 1)) / 2)‖) hT.ne' (a := T * s j) (b := T * s (j + 1))
  simp only at hc
  rw [hm, hc, mul_div_cancel_left₀ _ hT.ne', mul_div_cancel_left₀ _ hT.ne', smul_eq_mul]

omit [NeZero d] in
/-- Supports the substitution $t=Ts$ in §3: a family regulated on $[a,b]$ stays regulated under
the linear change of variable $x\mapsto cx$, $c>0$, on $[a/c,b/c]$. -/
theorem regulated_comp_mul {H : ℝ → 𝕄} {a b c : ℝ} (hc : 0 < c) (h : IsRegulated H a b) :
    IsRegulated (fun x ↦ H (c * x)) (a / c) (b / c) := by
  have hcont : Continuous fun x : ℝ ↦ c * x := continuous_const.mul continuous_id
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨L, hL⟩ := h.1 (c * t) ⟨(div_le_iff₀' hc).mp ht.1, (lt_div_iff₀' hc).mp ht.2⟩
    exact ⟨L, hL.comp (hcont.continuousWithinAt.tendsto_nhdsWithin
      fun x hx ↦ mul_lt_mul_of_pos_left hx hc)⟩
  · obtain ⟨L, hL⟩ := h.2 (c * t) ⟨(div_lt_iff₀' hc).mp ht.1, (le_div_iff₀' hc).mp ht.2⟩
    exact ⟨L, hL.comp (hcont.continuousWithinAt.tendsto_nhdsWithin
      fun x hx ↦ mul_lt_mul_of_pos_left hx hc)⟩

omit [NeZero d] in
/-- Supports the auxiliary integrated midpoint estimate: a regulated path on $[0,1]$ gives a
regulated family $t\mapsto H(t/T)$
on $[0,T]$. -/
theorem regulated_rescale {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) (h : IsRegulated H 0 1) :
    IsRegulated (fun t ↦ H (t / T)) 0 T := by
  simpa only [zero_div, one_div, inv_inv, div_eq_inv_mul, mul_zero, mul_one] using
    regulated_comp_mul (inv_pos.mpr hT) h

omit [NeZero d] in
/-- Supports the bridge `midpoint_product_error_and_infimum_of_path`: a regulated family on
$[0,T]$ gives a regulated path $s\mapsto G(Ts)$ on $[0,1]$. -/
theorem regulated_unscale {G : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) (h : IsRegulated G 0 T) :
    IsRegulated (fun s ↦ G (T * s)) 0 1 := by
  simpa only [zero_div, div_self hT.ne'] using regulated_comp_mul hT h

omit [NeZero d] in
/-- Supports the auxiliary integrated midpoint estimate: checkpoints $s_j$ on $[0,1]$ scale to
checkpoints $Ts_j$ on $[0,T]$. -/
theorem checkpoints_rescale {H : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) {n : ℕ} {s : ℕ → ℝ}
    (hs : (variationCheckpoints H 1 n).2.1 s) (G : ℝ → 𝕄) :
    (variationCheckpoints G T n).2.1 (fun j ↦ T * s j) :=
  ⟨fun _ _ hab ↦ mul_le_mul_of_nonneg_left (hs.1 hab) hT.le,
    by simp only [hs.2.1, mul_zero], by simp only [hs.2.2, mul_one]⟩

omit [NeZero d] in
/-- Supports the bridge `midpoint_product_error_and_infimum_of_path`: checkpoints $t_j$ on $[0,T]$
scale to checkpoints $t_j/T$ on $[0,1]$. -/
theorem checkpoints_unscale {G : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) {n : ℕ} {t : ℕ → ℝ}
    (ht : (variationCheckpoints G T n).2.1 t) (H : ℝ → 𝕄) :
    (variationCheckpoints H 1 n).2.1 (fun j ↦ t j / T) :=
  ⟨fun _ _ hab ↦ div_le_div_of_nonneg_right (ht.1 hab) hT.le,
    by simp only [ht.2.1, zero_div], by simp only [ht.2.2, div_self hT.ne']⟩

omit [NeZero d] in
/-- **Auxiliary integrated midpoint estimate** (midpoint products over time $T$) and the claim
after it. Let $F$ be an odd
function, and let $H$ be a regulated path with evolution $U$ over time $T$. (i) The
midpoint product $W$ of $H^{(F)}$ over time $T$ on checkpoints $s_0,\ldots,s_N$ satisfies
$\|W-U(T)\|\le T\bigl(\sum_j\int_{s_j}^{s_{j+1}}\|H(s)-H(s_{j+1/2})\|\,ds
+\max_j\|H(s_{j+1/2})-H^{(F)}(s_{j+1/2})\|\bigr)$ (the auxiliary integrated midpoint estimate).
(ii) For every $\varepsilon>0$,
some checkpoints make the sum in (i) less than $\varepsilon$ (the paragraph after its proof).

Reading the statement against the paper:
* `H` is a path on $[0,1]$, regulated (`hreg`) and Hermitian (`hH`), and `U` is its evolution
  over time $T$: `IsEvolution (fun t ↦ H (t / T)) U 0 T`, generated by $H(t/T)$ on $[0,T]$.
* Stronger than the paper's setting: no $d\ge1$.
* "Checkpoints $s_0,\ldots,s_N$" is `(variationCheckpoints H 1 n).2.1 s`: `s` nondecreasing with
  $s_0=0$ and $s_n=1$; the paper's $N$ is `n`.
* `osc n s` is the sum in (i), $\sum_j\int_{s_j}^{s_{j+1}}\|H(x)-H(s_{j+1/2})\|\,dx$.
* "Odd function" is `∀ x, F (-x) = -F x`; $H^{(F)}$ is
  `(levelFunctionData F).2 H`, and at a sample it is `(levelFunctionData F).1`. The midpoint
  product over time $T$ is `midpointProductOver` (Definition 3.5).
* The maximum is `⨆ j : Fin n`. At $n=0$ this would be the junk value $0$, but $s_0=0<1=s_n$
  forces $n\ge1$, so it is a maximum over a nonempty finite set.
* (ii) is `sInf {…} = 0` over all $n$ and all checkpoints on $[0,1]$. The set is nonempty and
  bounded below by $0$, so this is the genuine infimum; it does not involve $T$ or $U$.

The proof is the substitution $t=Ts$. (i) is the auxiliary integrated midpoint estimate for a
family on $[0,T]$
(`midpoint_product_error_and_infimum`) applied to $t\mapsto H(t/T)$, which is regulated
(`regulated_rescale`), on the checkpoints $Ts_j$ (`checkpoints_rescale`): its midpoint product is
the midpoint product of $H^{(F)}$ over time $T$ on the $s_j$ (`midpointProductOver_rescale`), and
its oscillation term is $T$ times `osc n s` (`osc_rescale`). (ii) is (ii) of the same head: the
checkpoints $t_j$ on $[0,T]$ are the $Ts_j$ for the checkpoints $s_j=t_j/T$ on $[0,1]$
(`checkpoints_unscale`), so the set of oscillation sums on $[0,T]$ is $T$ times the set on
$[0,1]$, and its infimum $0$ is $T$ times the infimum here. The bridge back is
`midpoint_product_error_and_infimum_of_path`. -/
theorem path_midpoint_product_error_and_infimum {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let osc := fun (n : ℕ) (s : ℕ → ℝ) ↦
      ∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1), ‖H x - H ((s j + s (j + 1)) / 2)‖
    (∀ F : ℝ → ℝ, (∀ x, F (-x) = -F x) →
      ∀ (n : ℕ) (s : ℕ → ℝ), (variationCheckpoints H 1 n).2.1 s →
      ‖midpointProductOver ((levelFunctionData F).2 H) T n s - U T‖ ≤
        T * (osc n s + ⨆ j : Fin n, ‖H ((s j + s (j + 1)) / 2) -
          (levelFunctionData F).1 (H ((s j + s (j + 1)) / 2))‖)) ∧
    sInf {x : ℝ | ∃ (n : ℕ) (s : ℕ → ℝ), (variationCheckpoints H 1 n).2.1 s ∧
      x = osc n s} = 0 := by
  intro osc
  have hG := midpoint_product_error_and_infimum hT (regulated_rescale hT hreg)
    (fun t ht ↦ hH (t / T) ⟨div_nonneg ht.1 hT.le, (div_le_one hT).mpr ht.2⟩) hU
  dsimp only at hG
  refine ⟨fun F hodd n s hs ↦ ?_, ?_⟩
  · have hb := hG.1 F hodd n (fun j ↦ T * s j) (checkpoints_rescale hT hs _)
    have hW : midpointProduct ((levelFunctionData F).2 (fun t ↦ H (t / T))) n
        (fun j ↦ T * s j) = midpointProductOver ((levelFunctionData F).2 H) T n s :=
      midpointProductOver_rescale ((levelFunctionData F).2 H) hT.ne' n s
    have hm : ∀ j, (T * s j + T * s (j + 1)) / 2 / T = (s j + s (j + 1)) / 2 := fun j ↦ by
      field_simp
    rw [hW, osc_rescale H hT n s] at hb
    simpa only [hm, mul_add] using hb
  · have hset : {x : ℝ | ∃ (n : ℕ) (t : ℕ → ℝ),
        (variationCheckpoints (fun t ↦ H (t / T)) T n).2.1 t ∧
        x = ∑ j ∈ Finset.range n, ∫ x in t j..t (j + 1),
          ‖H (x / T) - H ((t j + t (j + 1)) / 2 / T)‖} =
        T • {x : ℝ | ∃ (n : ℕ) (s : ℕ → ℝ), (variationCheckpoints H 1 n).2.1 s ∧
          x = osc n s} := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨n, t, ht, rfl⟩
        refine ⟨osc n (fun j ↦ t j / T),
          ⟨n, fun j ↦ t j / T, checkpoints_unscale hT ht H, rfl⟩, ?_⟩
        simpa only [mul_div_cancel₀ _ hT.ne', smul_eq_mul] using
          (osc_rescale H hT n (fun j ↦ t j / T)).symm
      · rintro ⟨y, ⟨n, s, hs, rfl⟩, rfl⟩
        exact ⟨n, fun j ↦ T * s j, checkpoints_rescale hT hs _,
          by rw [smul_eq_mul]; exact (osc_rescale H hT n s).symm⟩
    have h2 := hG.2
    rw [hset, Real.sInf_smul_of_nonneg hT.le, smul_eq_mul] at h2
    exact (mul_eq_zero.mp h2).resolve_left hT.ne'

end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.levelFunctionData
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.truncation
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.variationCheckpoints
