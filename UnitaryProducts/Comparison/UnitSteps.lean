/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import UnitaryProducts.Comparison.EndpointConstants
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import UnitaryProducts.Approximation.VariationMain
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.FinCases
public import UnitaryProducts.Approximation.JRSComparison
public import UnitaryProducts.Comparison.DiscreteAdiabatic
public import UnitaryProducts.Corrector.CommutatorRegularity
public import UnitaryProducts.Corrector.IntegratedComparison
public import UnitaryProducts.Corrector.PowerSeries
public import UnitaryProducts.Matrix.ExponentialEigenvectors
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Evolution.RoundedTransfer
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Spectral.Weyl
public import UnitaryProducts.Walks.Logarithm
public import UnitaryProducts.Walks.LogarithmBranch
public import Mathlib.Data.Matrix.Basis
public import UnitaryProducts.Corrector.SeparatedFrameBounds
public import UnitaryProducts.Evolution.PartitionIndependent
public import UnitaryProducts.Evolution.Pieces
public import UnitaryProducts.Evolution.PiecewiseDressedComparison
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogarithmDerivative
public import UnitaryProducts.Spectral.ProjectorDistance
public import UnitaryProducts.Evolution.UnitaryGenerators
public import UnitaryProducts.Paper.FineStepBounds
public import UnitaryProducts.Spectral.GapDistance
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# Unit-step products, the periodic corrector, and mesh norms

## Declarations

- `deriv_frameMult_eq_partialFractions`
- `meshInterval`
- `mesh_subset`
- `norm_le_unitSupNorm`
- `rescaled_evolution`
- `rescaled_evolution_steps`
- `step_products_unit`
- `unitProduct`
- `unitSupNorm`
- `walk`
- `walkCubic_sample`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Definition 2.3** (`def:unit-product`): the unit-step product of `H` with `T` factors,
together with the rounded clock. The first component is
$e^{-iH((T-1)/T)}\cdots e^{-iH(0)}$; the second is $q(t)=\lfloor t+1/2\rfloor$.
The empty product at `T = 0` is an internal convention; the paper assumes `T ≥ 1`. -/
def unitProduct (H : ℝ → 𝕄) (T : ℕ) : 𝕄 × (ℝ → ℝ) :=
  (UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ H (j / T)) T,
   fun t ↦ (⌊t + 1 / 2⌋ : ℤ))

/-- Internal specialization of the general-duration encoding to the unit-step product
of Definition 2.3. It also handles the empty product convention. -/
theorem step_products_unit (H : ℝ → 𝕄) {N : ℕ} :
    (stepProducts H N N).2.1 = (unitProduct H N).1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rfl
  have hNZ : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [stepProducts, unitProduct, div_self hNZ, one_smul]

/-- On $|w|<2\pi$ the derivative of the closed form `frameMult` is $\mathcal N'(w)$, the
derivative of the paper's series. -/
theorem deriv_frameMult_eq_partialFractions {w : ℝ} (hw : |w| < 2 * π) :
    deriv UnitaryProducts.Corrector.frameMult w =
      deriv (fun x : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)) w := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hw] with x hx
  exact frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt hx)

/-- The samples $j/N$, $j \le N$, lie in $[0, 1]$: the form of Mathlib's `unitInterval.div_mem`
that the statements of §4 use, including the zero denominator convention. -/
theorem walkCubic_sample {N j : ℕ} (hj : j ≤ N) :
    (j : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
  unitInterval.div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)

/-- Simultaneous energy and time scaling preserves the evolution endpoint. -/
theorem rescaled_evolution {H U : ℝ → 𝕄} {T : ℝ}
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) {c : ℝ} (hc : 0 < c) :
    IsEvolution (fun t ↦ c • H (t/(T/c))) (fun t ↦ U (c*t)) 0 (T/c) := by
  obtain ⟨hUc,hU0,hUU,S,hS,hUd⟩ := hU
  refine ⟨UnitaryProducts.continuousOn_energy_rescale hc hUc, ?_, ?_,
    (fun t : ℝ ↦ c*t) ⁻¹' S, hS.preimage (mul_right_injective₀ hc.ne'), ?_⟩
  · simpa only [mul_zero] using hU0
  · intro t ht
    apply hUU
    exact ⟨mul_nonneg hc.le ht.1, (mul_le_mul_of_nonneg_left ht.2 hc.le).trans_eq (by field_simp)⟩
  · intro t ht hn
    have h := UnitaryProducts.schrodinger_energy_rescale_off_set hc S hUd t ht hn
    convert h using 1 ; congr 2 ; field_simp

/-- Supports "Rescaling energy and time together meets it" and "it is also the final value of the
evolution of $(T/N)H$ over time $N$" (§4.2, before Theorem 4.2): if $U$ is the evolution of $H$
over time $T$, then $(T/N)H(t/N)$ generates $t\mapsto U((T/N)t)$ on $[0,N]$, so the evolution of
$(T/N)H$ over time $N$ is $t\mapsto U((T/N)t)$, whose value at $N$ is $U(T)$.

Reading the statement against the paper:
* The unit-step samples of $(T/N)H$ over time $N$ are $(T/N)H(j/N)$, so its unit-step product is
  the $N$-step product `unitProduct (fun s ↦ (T/N) • H s) N` of $H$ over time $T$, by definition.
* `IsEvolution G V 0 N` says that $G$ generates $V$ on $[0,N]$ (§2).

The proof is the time change $t\mapsto(T/N)t$ (`rescaled_evolution` with $c=T/N$), and
$T/(T/N)=N$. -/
theorem rescaled_evolution_steps {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) (N : ℕ) (hN : 0 < N)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    IsEvolution (fun t ↦ (T/N) • H (t/N)) (fun t ↦ U ((T/N)*t)) 0 N ∧ U ((T/N)*N) = U T := by
  have hN' : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := rescaled_evolution hU (div_pos hT (Nat.cast_pos.mpr hN))
  rw [show T/(T/N) = (N:ℝ) by field_simp] at h
  exact ⟨h, by rw [div_mul_cancel₀ T hN']⟩

/-- A walk and its sampled product (§4.3). The first component says that $W(s)$ is unitary for
$s\in[0,1]$; the second is the sampled product $W_T=W((T-1)/T)\cdots W(0)$. For `T = 0` the
product is the empty product `1`; every use has $T\ge1$. -/
def walk (W : ℝ → 𝕄) (T : ℕ) : Prop × 𝕄 :=
  (∀ s ∈ Icc (0 : ℝ) 1, star (W s) * W s = 1,
   UnitaryProducts.stepProduct W T T)

/-- The maximum $\max_{[0,1]}\|F\|$ of the norm of `F` on the parameter interval $[0,1]$.

It is an `sSup`: a genuine maximum when `F` is continuous on $[0,1]$ (a compact image), and the
junk value `0` when the norms are unbounded; every use assumes continuity. -/
def unitSupNorm {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) : ℝ :=
  sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1)

/-- Every value of a continuous `F` on $[0,1]$ is at most `unitSupNorm F`. -/
theorem norm_le_unitSupNorm {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → E} (hc : ContinuousOn F (Icc (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖F s‖ ≤ unitSupNorm F :=
  hc.norm.le_sSup_image_Icc hs

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The $i$-th step $[i/N,(i+1)/N]$ of the mesh of §4.2, as a closed interval.

The endpoints are written $\max(0,i)/N$ and $\min(N,i+1)/N$, so for $i<N$ the set is exactly
$[i/N,(i+1)/N]\subseteq[0,1]$. For $i\ge N$ it is $\{1\}$ or empty, and for $N=0$ it is $\{0\}$
(division by zero is `0`); every use has $0<N$ and $i<N$. -/
def meshInterval (N i : ℕ) : Set ℝ :=
  Icc (max 0 (i:ℝ)/N) (min (N:ℝ) ((i:ℝ)+1)/N)

/-- Each step lies in $[0,1]$. -/
theorem mesh_subset {N i : ℕ} : meshInterval N i ⊆ Icc (0 : ℝ) 1 := fun _ hs ↦
  ⟨(div_nonneg (le_max_left _ _) (Nat.cast_nonneg N)).trans hs.1,
    hs.2.trans (div_le_one_of_le₀ (min_le_left _ _) (Nat.cast_nonneg N))⟩

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts.Corrector UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.meshInterval
