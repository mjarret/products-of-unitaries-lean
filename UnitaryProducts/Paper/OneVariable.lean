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

- `evol_smul_eq`
- `midpointProductOver`
- `midpointProductOver_eq`
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
def midpointProductOver (A : ℝ → 𝕄) (T : ℝ) (n : ℕ) (s : ℕ → ℝ) : 𝕄 :=
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

end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.levelFunctionData
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.truncation
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.variationCheckpoints
