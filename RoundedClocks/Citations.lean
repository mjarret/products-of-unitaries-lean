/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib
public import RoundedClocks.Definitions

/-!
# Results cited by the paper

Each declaration is a proposition, not an axiom. A theorem of the paper that uses a cited result
takes the corresponding proposition as an explicit hypothesis. Statements about Banach spaces are
specialized to finite-dimensional complex matrices when that is all the paper uses.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology Real
open Set Filter
open Complex (I)

noncomputable section

namespace RoundedClocks

/-- `f` has derivative `g t` on `[a,b]` outside a countable set of points. -/
def DerivativeOffCountable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (a b : ℝ) : Prop :=
  ∃ D : Set ℝ, D.Countable ∧
    ∀ t ∈ Icc a b, t ∉ D → HasDerivWithinAt f (g t) (Icc a b) t

/-- `f n` converges locally uniformly to `g` at every point of `[a,b]`. -/
def LocallyUniformlyConvergesOn {E : Type*} [PseudoMetricSpace E]
    (f : ℕ → ℝ → E) (g : ℝ → E) (a b : ℝ) : Prop :=
  ∀ x ∈ Icc a b, ∃ δ > 0, ∀ ε > 0, ∃ N, ∀ n, N ≤ n →
    ∀ y ∈ Icc a b, |y - x| < δ → dist (f n y) (g y) < ε

/-- `u` solves `u' = A u + B` on `[a,b]` with initial value `u t₀ = X₀`. -/
def SolvesLinearMatrixODE {d : ℕ}
    (A B : ℝ → Matrix (Fin d) (Fin d) ℂ) (X₀ : Matrix (Fin d) (Fin d) ℂ)
    (u : ℝ → Matrix (Fin d) (Fin d) ℂ) (t₀ a b : ℝ) : Prop :=
  ContinuousOn u (Icc a b) ∧ u t₀ = X₀ ∧
    DerivativeOffCountable u (fun t ↦ A t * u t + B t) a b

/-- Dieudonné, *Foundations of Modern Analysis* (Academic Press, 1960), (7.6.1).

Source statement, quoted verbatim: “In order that a mapping `f` of a compact interval
`I = [a,b]` into `F` be regulated, a necessary and sufficient condition is that `f` be the limit
of a uniformly convergent sequence of step-functions.”

The proposition below is the direction used by the paper, specialized to matrix-valued functions:
one sufficiently close step-function is extracted from the uniformly convergent sequence. The
paper uses it to choose the checkpoints in Lemma 3.4 and to obtain standard consequences of
regulatedness in Section 2. -/
def Dieudonne_7_6_1 : Prop :=
  ∀ (d : ℕ) (H : ℝ → Matrix (Fin d) (Fin d) ℂ) (a b ε : ℝ),
    a ≤ b → IsRegulated H a b → 0 < ε →
      ∃ G, IsPiecewiseConstant G a b ∧ ∀ t ∈ Icc a b, ‖H t - G t‖ < ε

/-- Dieudonné, *Foundations of Modern Analysis* (Academic Press, 1960), (8.6.4).

Source statement, quoted verbatim: “Let `(gₙ)` be a sequence of mappings of an interval `I ⊂ ℝ`
into `F`, and suppose that, for each `n`, `gₙ(t)` is the derivative of a continuous function `fₙ`
except for the points `t` of a denumerable subset `Dₙ ⊂ I`. Suppose in addition that: (1) there
exists a point `t₀` such that the sequence `(fₙ(t₀))` converges in `F`; (2) for every point `t ∈ I`,
there is a neighborhood `B(t)` with respect to `I` such that in `B(t)` the sequence `(gₙ)`
converges uniformly. Then for each `t ∈ I`, the sequence `(fₙ)` converges uniformly in `B(t)`; and
if we put `f(t) = lim fₙ(t)` and `g(t) = lim gₙ(t)`, then at every point of `I` not in `⋃ Dₙ`,
`f'(t) = g(t)`.”

This is specialized below to matrix-valued functions on a compact interval. The paper uses it to
differentiate the normally convergent commutator series in Appendix A. -/
def Dieudonne_8_6_4 : Prop :=
  ∀ (d : ℕ) (f g : ℕ → ℝ → Matrix (Fin d) (Fin d) ℂ)
    (gLim : ℝ → Matrix (Fin d) (Fin d) ℂ) (a b t₀ : ℝ),
    (∀ n, ContinuousOn (f n) (Icc a b) ∧ DerivativeOffCountable (f n) (g n) a b) →
    t₀ ∈ Icc a b → (∃ x, Tendsto (fun n ↦ f n t₀) atTop (𝓝 x)) →
    LocallyUniformlyConvergesOn g gLim a b →
      ∃ fLim, LocallyUniformlyConvergesOn f fLim a b ∧
        DerivativeOffCountable fLim gLim a b

/-- Dieudonné, *Foundations of Modern Analysis* (Academic Press, 1960), Section 8.7,
“Primitives and integrals.”

Source statements, quoted verbatim: “We say that a continuous mapping `g` of `I` into `F` is a
primitive of `f` in `I` if there exists a denumerable set `D ⊂ I` such that, for any `t ∈ I ∖ D`,
`g` is differentiable at `t` and `g'(t) = f(t)`.” “If `g₁`, `g₂` are two primitives of `f` in
`I`, then `g₁ - g₂` is constant in `I`.” The section then defines
`∫_a^b f(t) dt = g(b) - g(a)`.

The proposition is that fundamental-theorem consequence, specialized to matrices. The proof of
Theorem 2.2 uses it to integrate derivatives that fail on a countable set. -/
def Dieudonne_Section_8_7 : Prop :=
  ∀ (d : ℕ) (f g : ℝ → Matrix (Fin d) (Fin d) ℂ) (a b : ℝ),
    a ≤ b → ContinuousOn f (Icc a b) → IsRegulated g a b →
    DerivativeOffCountable f g a b → f b - f a = ∫ t in a..b, g t

/-- Dieudonné, *Foundations of Modern Analysis* (Academic Press, 1960), (10.5.4).

Source statement, quoted verbatim: “The uniqueness result (10.5.2) holds likewise (when `K = ℝ`)
under the only assumption that `f` is locally lipschitzian (10.4.6) in `I × H`, when one takes for
`J` an interval having `t₀` as origin or extremity, and one only requires that the relations
`u'(t)=f(t,u(t))`, `v'(t)=f(t,v(t))` hold in the complement of an at most denumerable subset of
`J`.”

The matrix-linear specialization below is the uniqueness statement used for evolutions in
Section 2: `f(t,x) = A(t)x + B(t)` with `A` and `B` regulated is locally lipschitzian in the
sense of (10.4.6) (`A` regulated is bounded), and
`J = [a,b]` has `t₀ = a` as origin. -/
def Dieudonne_10_5_4 : Prop :=
  ∀ (d : ℕ) (A B : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (X₀ : Matrix (Fin d) (Fin d) ℂ) (u v : ℝ → Matrix (Fin d) (Fin d) ℂ) (a b : ℝ),
    a ≤ b → IsRegulated A a b → IsRegulated B a b →
    SolvesLinearMatrixODE A B X₀ u a a b → SolvesLinearMatrixODE A B X₀ v a a b →
      EqOn u v (Icc a b)

/-- Dieudonné, *Foundations of Modern Analysis* (Academic Press, 1960), (10.6.3).

Source statement, quoted verbatim: “Let `I ⊂ K` be an open ball of center `t₀`. Suppose `A` and
`b` are regulated in `I` if `K = ℝ`, analytic in `I` if `K = ℂ`. Then, for every `x₀ ∈ E`, there
exists a unique solution `u` of (10.6.2), defined in `I` and such that `u(t₀)=x₀`.” Here (10.6.2)
is the linear equation `x' = A(t)·x + b(t)`.

Remark (10.4.6), quoted verbatim: “The proof of (10.4.5) shows that the result is still valid
when `K = ℝ` and when `f` satisfies the following weaker hypotheses: (a) for every continuous
mapping `t ↦ w(t)` of `I` into `H`, `t ↦ f(t,w(t))` is a regulated function in `I`; (b) for any
point `(t,x) ∈ I × H`, there is a ball `J` of center `t` in `I` and a ball `B` of center `x` in
`H` such that `f` is bounded in `J × B`, and there exists a constant `k` (depending on `J` and `B`)
such that `‖f(s,y₁)-f(s,y₂)‖ ≤ k‖y₁-y₂‖` for `s ∈ J`, `y₁,y₂ ∈ B`.” The remark
says the differential equation holds off an at most denumerable set and that the intervals may
have endpoints.

The proposition below is (10.6.3) in the regulated real case that (10.4.6) allows, specialized to
finite-dimensional matrices. The paper uses it to construct the evolution `U`. -/
def Dieudonne_10_6_3 : Prop :=
  ∀ (d : ℕ) (A B : ℝ → Matrix (Fin d) (Fin d) ℂ)
    (X₀ : Matrix (Fin d) (Fin d) ℂ) (a b t₀ : ℝ),
    a < b → t₀ ∈ Icc a b → IsRegulated A a b → IsRegulated B a b →
      ∃ u, SolvesLinearMatrixODE A B X₀ u t₀ a b ∧
        ∀ v, SolvesLinearMatrixODE A B X₀ v t₀ a b → EqOn u v (Icc a b)

/-- `e` lists the eigenvalues of the Hermitian matrix `A`, with multiplicity, in decreasing
order. This is source vocabulary for Bhatia, Corollary III.2.6. -/
def IsDecreasingEigenvalueList {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (e : Fin d → ℝ) : Prop :=
  Antitone e ∧ A.charpoly.roots = Finset.univ.val.map fun j ↦ (e j : ℂ)

/-- Bhatia, *Matrix Analysis* (Springer, 1997), Corollary III.2.6, p. 63.

Source statement, quoted verbatim: “Corollary III.2.6 (Weyl's Perturbation Theorem) Let `A` and `B`
be Hermitian matrices. Then `max_j |λ_j↓(A) - λ_j↓(B)| ≤ ‖A - B‖`.” Here `λ_j↓` lists the
eigenvalues in decreasing order and `‖·‖` is the operator norm. The paper uses it for endpoint
truncation, gap-adapted schedules, and continuity of extreme eigenvalues. -/
def Bhatia_Corollary_III_2_6 : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (eA eB : Fin d → ℝ),
    IsHermitian A → IsHermitian B → IsDecreasingEigenvalueList A eA →
    IsDecreasingEigenvalueList B eB → ∀ j, |eA j - eB j| ≤ ‖A - B‖

/-- Bhatia, *Matrix Analysis* (Springer, 1997), Exercise VII.1.11, p. 201, with the remark that
follows it on p. 202.

Source statements, quoted verbatim: “Exercise VII.1.11 Let `𝓔, 𝓕` and `E, F` be as above [subspaces
of `ℂⁿ` of the same dimension and the orthogonal projections with ranges `𝓔, 𝓕`]. Then the nonzero
singular values of `E - F` are the nonzero singular values of `E⊥F`, each counted twice” and “It is
natural to define the distance between the spaces `𝓔` and `𝓕` as `‖E - F‖`. In view of Exercise
VII.1.11, this is also the number `‖E⊥F‖`.” Below, `E = Q` and `F = P`. The paper uses it for the
original and truncated endpoint projectors. -/
def Bhatia_Exercise_VII_1_11 : Prop :=
  ∀ (d : ℕ) (P Q : Matrix (Fin d) (Fin d) ℂ),
    IsOrthogonalProjector P → IsOrthogonalProjector Q → HasEqualRank P Q →
      ‖P - Q‖ = ‖(1 - Q) * P‖

/-- Bhatia, *Matrix Analysis* (Springer, 1997), Theorem VII.3.1, p. 211.

Source statement, quoted verbatim: “Let `A`, `B` be normal operators. Let `S₁` and `S₂` be two
subsets of the complex plane that are separated by either an annulus of width `δ` or a strip of
width `δ`. Let `E = P_A(S₁)`, `F = P_B(S₂)`. Then, for every unitarily invariant norm,
`|||EF||| ≤ (1/δ)|||E(A - B)F||| ≤ (1/δ)|||A - B|||`.”

Below: Hermitian matrices, the operator norm, and `S₁ ⊆ [α,β]` separated from
`S₂ ⊆ ℝ ∖ (α-δ, β+δ)` by strips of width `δ` (Bhatia's Davis–Kahan special case, p. 212). `P` is the
spectral projector of `A` for `S`, all of whose eigenvalues lie in `[α,β]`, and `1 - Q` that of
`B` for the eigenvalues outside `T`, all of which lie outside `(α-δ, β+δ)`; since `P ≤ E` and
`1 - Q ≤ F`, `‖(1-Q)P‖ ≤ ‖EF‖`. This special case is the Davis--Kahan `sin Θ` theorem (Davis
and Kahan, *SIAM J. Numer. Anal.* 7 (1970), 1–46). The paper uses it for the endpoint projectors
in Remark 3.8. -/
def Bhatia_Theorem_VII_3_1 : Prop :=
  ∀ (d : ℕ) (A B P Q : Matrix (Fin d) (Fin d) ℂ) (S T : Set ℂ) (δ : ℝ),
    IsHermitian A → IsHermitian B → IsSpectralProjector P A S →
    IsSpectralProjector Q B T → 0 < δ → ∀ α β : ℝ,
    (∀ x ∈ spectrum ℂ A ∩ S, α ≤ x.re ∧ x.re ≤ β) →
    (∀ y ∈ spectrum ℂ B \ T, y.re ≤ α - δ ∨ β + δ ≤ y.re) →
      ‖(1 - Q) * P‖ ≤ ‖A - B‖ / δ

/-- NIST Digital Library of Mathematical Functions, §4.22, equation 4.22.5.

Source statement, quoted verbatim:
`csc z = 1/z + 2z ∑_{n=1}^∞ (-1)^n/(z²-n²π²)`.

The paper substitutes `z=x/2` to obtain the alternating partial-fraction series used in the proof
of Lemma A.1. -/
def DLMF_4_22_5 : Prop :=
  ∀ z : ℂ, (∀ n : ℤ, z ≠ n * (π : ℂ)) →
    (Complex.sin z)⁻¹ = 1 / z + 2 * z *
      ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) /
        (z ^ 2 - ((n + 1 : ℕ) : ℂ) ^ 2 * (π : ℂ) ^ 2)

end RoundedClocks
