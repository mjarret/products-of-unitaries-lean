/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.EndpointTransfer

/-!
# Supporting band-projector estimates

## Declarations

- `IsBand`
- `bandGap`
- `bandProj`
- `hull_windowProj_eq_bandProj`
- `leakage_le_of_endpoint_approximation_sharp`
- `windowProj_eq_bandProj`
- `band_endpoint`
- `band_hull`
- `band_tight_hull`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter
namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A band of a Hermitian matrix (Definition 2.5), in index-set form: a nonempty proper set `S`
of ordered eigenvalue indices whose eigenvalues are exactly those in some closed interval
$[m-r, m+r]$. A closed interval whose ends are eigenvalues cuts out the same part of the spectrum
as a slightly larger one with ends outside it, so the paper's "endpoints outside the spectrum"
is equivalent. -/
def IsBand {A : 𝕄} (hA : A.IsHermitian) (S : Finset (Fin d)) : Prop :=
  S.Nonempty ∧ Sᶜ.Nonempty ∧ ∃ m r : ℝ, ∀ i, i ∈ S ↔ |hA.eigenvalues i-m| ≤ r

/-- The spectral gap $\Gamma(A)$ of a band (paragraph after Definition 2.5): the distance
$\min_{i \in S,\, j \notin S} |\lambda_i - \lambda_j|$ from its eigenvalues to the rest of the
spectrum. It takes the proof `hS` that `S` is a band, so it is never evaluated off a band and
has no junk value. -/
noncomputable def bandGap {A : 𝕄} (hA : A.IsHermitian) {S : Finset (Fin d)} (hS : IsBand hA S) :
    ℝ :=
  UnitaryProducts.finiteSpectralDistance hA.eigenvalues hA.eigenvalues S Sᶜ hS.1 hS.2.1

/-- The orthogonal projector onto the eigenvectors of $A$ with ordered indices in `S`: the
paper's $P_t$ for a band $S_t$ of $H(t)$, and $\tilde P_t$ when applied to $D_t$ (the unnumbered
endpoint-transfer estimate).

It is `0` off the Hermitian matrices. It is built from Mathlib's `eigenvectorBasis`; when `S`
is a union of whole eigenspaces, as for a band and, under the unnumbered endpoint-transfer
estimate's half-gap hypothesis, for
the same indices of $D_t$, it does not depend on that choice. -/
noncomputable def bandProj (S : Finset (Fin d)) (A : 𝕄) : 𝕄 :=
  if h : A.IsHermitian then
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
      (∑ i ∈ S, InnerProductSpace.rankOne ℂ (h.eigenvectorBasis i) (h.eigenvectorBasis i))
  else 0

omit [NeZero d] in
/-- A window projector is the index-set projector of the indices it selects: the spectral
projector $P_{[m-c, m+c]}(A)$ is `bandProj S A` for `S` the indices with eigenvalue in the
interval. The proof of the unnumbered endpoint-transfer estimate uses it to move from intervals to
index sets. -/
theorem windowProj_eq_bandProj {A : 𝕄} (hA : A.IsHermitian) {S : Finset (Fin d)} {m c : ℝ}
    (hmem : ∀ i, i ∈ S ↔ |hA.eigenvalues i - m| ≤ c) :
    UnitaryProducts.windowProj m c A = bandProj S A := by
  classical
  have hidx : UnitaryProducts.idx hA.eigenvalues (Metric.closedBall m c) = S := by
    ext i; simp [UnitaryProducts.idx, Real.dist_eq, hmem i]
  unfold UnitaryProducts.windowProj bandProj UnitaryProducts.specProj UnitaryProducts.proj
  rw [dif_pos hA, dif_pos hA, hidx]

omit [NeZero d] in
/-- The convex hull $I=[a,b]$ of an interval-cut index set, written as the window $[m-r,m+r]$ with
$m=(a+b)/2$ and $r=(b-a)/2$, where $a$ and $b$ are its least and largest eigenvalues: the set is
exactly the indices with eigenvalue in $I$, and both ends of $I$ are eigenvalues of the set. -/
private theorem band_hull (ev : Fin d → ℝ) {S : Finset (Fin d)} (hS : S.Nonempty)
    {m r : ℝ} (hmem : ∀ i, i ∈ S ↔ |ev i - m| ≤ r) :
    0 ≤ (S.sup' hS ev - S.inf' hS ev) / 2 ∧
      (∀ i, i ∈ S ↔
        |ev i - (S.inf' hS ev + S.sup' hS ev) / 2| ≤ (S.sup' hS ev - S.inf' hS ev) / 2) ∧
      (∃ i ∈ S, ev i = (S.inf' hS ev + S.sup' hS ev) / 2 - (S.sup' hS ev - S.inf' hS ev) / 2) ∧
      (∃ i ∈ S, ev i = (S.inf' hS ev + S.sup' hS ev) / 2 + (S.sup' hS ev - S.inf' hS ev) / 2) := by
  obtain ⟨ia, ha, hea⟩ := S.exists_mem_eq_inf' hS ev
  obtain ⟨ib, hb, heb⟩ := S.exists_mem_eq_sup' hS ev
  have hab : S.inf' hS ev ≤ S.sup' hS ev := (S.inf'_le ev ha).trans (S.le_sup' ev ha)
  refine ⟨div_nonneg (sub_nonneg.mpr hab) zero_le_two, fun i ↦ ?_,
    ⟨ia, ha, by rw [← hea]; ring⟩, ⟨ib, hb, by rw [← heb]; ring⟩⟩
  rw [abs_le]
  refine ⟨fun hi ↦ ⟨by linarith [S.inf'_le ev hi], by linarith [S.le_sup' ev hi]⟩,
    fun ⟨h₁, h₂⟩ ↦ ?_⟩
  have hA := abs_le.mp ((hmem ia).mp ha)
  have hB := abs_le.mp ((hmem ib).mp hb)
  rw [hmem i, abs_le]
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

omit [NeZero d] in
/-- The tight hull of an interval-cut index set: its ends are the extreme band eigenvalues. This
is the convex hull $I$ of $S_t$ in the proof of the unnumbered endpoint-transfer estimate. -/
private theorem band_tight_hull (ev : Fin d → ℝ) {S : Finset (Fin d)} (hS : S.Nonempty)
    {m r : ℝ} (hmem : ∀ i, i ∈ S ↔ |ev i - m| ≤ r) :
    ∃ m' r' : ℝ, 0 ≤ r' ∧ (∀ i, i ∈ S ↔ |ev i-m'| ≤ r') ∧
      (∃ i ∈ S, ev i = m'-r') ∧ (∃ i ∈ S, ev i = m'+r') :=
  ⟨_, _, band_hull ev hS hmem⟩

omit [NeZero d] in
/-- One endpoint of the proof of the unnumbered endpoint-transfer estimate: for a band `S` of $A$
and $\|A - D\| < \Gamma/2$,
the convex hull $[m - r, m + r]$ of the band carries an eigenvalue-free collar of width
$\Gamma$, the widened window of $D$ has a nonempty complement, and both window projectors are
index-set projectors of `S`. By Weyl's inequality the indices of `S` are exactly those whose
eigenvalue of $D$ lies within $r + \Gamma/2$ of $m$. These are the interval data consumed by
`transfer_gap`. -/
private theorem band_endpoint {A D : 𝕄} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {S : Finset (Fin d)} (hS : IsBand hA S) (he : ‖A - D‖ < bandGap hA hS / 2) :
    ∃ m r : ℝ, 0 ≤ r ∧ 0 < bandGap hA hS ∧ UnitaryProducts.HasGap hA m r (bandGap hA hS) ∧
      (UnitaryProducts.endpointComplement hD m r (bandGap hA hS)).Nonempty ∧
      UnitaryProducts.windowProj m r A = bandProj S A ∧
      UnitaryProducts.windowProj m (r+bandGap hA hS/2) D = bandProj S D := by
  obtain ⟨hne, hR, m₀, r₀, hmem₀⟩ := id hS
  obtain ⟨m, r, hr, hmem, hleft, hright⟩ := band_tight_hull hA.eigenvalues hne hmem₀
  have hγ : 0 < bandGap hA hS := by linarith [norm_nonneg (A-D)]
  have hg : UnitaryProducts.HasGap hA m r (bandGap hA hS) :=
    UnitaryProducts.hasGap_of_exact_distance hA S hne hR hmem hleft hright
  have hp : ∃ i, r < |hA.eigenvalues i-m| :=
    Exists.imp (fun i hi ↦ lt_of_not_ge fun h ↦ (Finset.mem_compl.mp hi) ((hmem i).mpr h)) hR
  refine ⟨m, r, hr, hγ, hg, UnitaryProducts.endpointComplement_nonempty hA hD hg he hp,
    windowProj_eq_bandProj hA hmem, windowProj_eq_bandProj hD fun i ↦ ?_⟩
  exact (hmem i).trans (UnitaryProducts.same_band_indices_of_small_perturbation hA hD hg he i)

omit [NeZero d] in
/-- The projectors of the unnumbered endpoint-transfer estimate at one endpoint are spectral
projectors of intervals. Let `S` be
a band of $A$ with convex hull $I=[a,b]$, where $a$ and $b$ are its least and largest eigenvalues,
and let $D$ be Hermitian with $\varepsilon=\|A-D\|<\Gamma/2$. Then $P_I(A)$ projects onto the
eigenvectors with indices in `S`, and so does $P_J(D)$ for the closed $\varepsilon$-neighborhood
$J=[a-\varepsilon,b+\varepsilon]$ of $I$. Both intervals are windows about $m=(a+b)/2$, of
radii $r=(b-a)/2$ and $r+\varepsilon$.

The proof is the paper's: the exact gap is an eigenvalue-free collar of width $\Gamma$ around $I$
(`hasGap_of_exact_distance`), and Weyl's inequality moves each ordered eigenvalue by at most
$\varepsilon$, so the eigenvalues of $D$ with indices in `S` lie in $J$ and the others at distance
at least $\Gamma-\varepsilon>\varepsilon$ from $I$. -/
theorem hull_windowProj_eq_bandProj {A D : 𝕄} (hA : A.IsHermitian) (hD : D.IsHermitian)
    {S : Finset (Fin d)} (hS : IsBand hA S) (he : ‖A - D‖ < bandGap hA hS / 2) :
    UnitaryProducts.windowProj ((S.inf' hS.1 hA.eigenvalues + S.sup' hS.1 hA.eigenvalues) / 2)
        ((S.sup' hS.1 hA.eigenvalues - S.inf' hS.1 hA.eigenvalues) / 2) A = bandProj S A ∧
      UnitaryProducts.windowProj ((S.inf' hS.1 hA.eigenvalues + S.sup' hS.1 hA.eigenvalues) / 2)
        ((S.sup' hS.1 hA.eigenvalues - S.inf' hS.1 hA.eigenvalues) / 2 + ‖A - D‖) D =
          bandProj S D := by
  obtain ⟨hne, hR, m₀, r₀, hmem₀⟩ := id hS
  obtain ⟨-, hmem, hleft, hright⟩ := band_hull hA.eigenvalues hS.1 hmem₀
  set m := (S.inf' hS.1 hA.eigenvalues + S.sup' hS.1 hA.eigenvalues) / 2
  set r := (S.sup' hS.1 hA.eigenvalues - S.inf' hS.1 hA.eigenvalues) / 2
  have hg : UnitaryProducts.HasGap hA m r (bandGap hA hS) :=
    UnitaryProducts.hasGap_of_exact_distance hA S hS.1 hR hmem hleft hright
  refine ⟨windowProj_eq_bandProj hA hmem, windowProj_eq_bandProj hD fun i ↦ ?_⟩
  -- Weyl: the distances of `λ_i(A)` and `λ_i(D)` from `m` differ by at most `‖A - D‖`.
  have key : |(|hA.eigenvalues i - m|) - (|hD.eigenvalues i - m|)| ≤ ‖A - D‖ := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [sub_sub_sub_cancel_right]
    exact UnitaryProducts.abs_eigenvalues_sub_le hA hD i
  rw [abs_le] at key
  -- An index outside `S` has `λ_i(A)` beyond the collar, so `λ_i(D)` lies beyond
  -- `r + Γ - ‖A - D‖ > r + ‖A - D‖`, contradicting `hi`.
  refine ⟨fun hi ↦ by linarith [(hmem i).mp hi, key.1], fun hi ↦ (hmem i).mpr ?_⟩
  exact (hg i).resolve_right fun h ↦ by linarith [key.2]

omit [NeZero d] in
/-- Unnumbered support for Remark 3.8: endpoint projector bounds in index form,
with the leakage-operator comparison, for an evolution on `[0,T]`. -/
theorem leakage_le_of_endpoint_approximation_sharp {H U : ℝ → 𝕄} {T : ℝ}
    (hT : 0 < T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian) (hU : IsEvolution H U 0 T)
    {S₀ S₁ : Finset (Fin d)}
    (hS₀ : IsBand (hH 0 ⟨le_rfl, hT.le⟩) S₀) (hS₁ : IsBand (hH T ⟨hT.le, le_rfl⟩) S₁)
    {D₀ D₁ : 𝕄} (hd₀ : D₀.IsHermitian) (hd₁ : D₁.IsHermitian)
    (he₀ : ‖H 0 - D₀‖ < bandGap _ hS₀ / 2) (he₁ : ‖H T - D₁‖ < bandGap _ hS₁ / 2) (W : 𝕄) :
    let P₀ := bandProj S₀ (H 0)
    let P₁ := bandProj S₁ (H T)
    let P'₀ := bandProj S₀ D₀
    let P'₁ := bandProj S₁ D₁
    let ε₀ := ‖H 0-D₀‖
    let ε₁ := ‖H T-D₁‖
    let Γ₀ := bandGap _ hS₀
    let Γ₁ := bandGap _ hS₁
    ‖(1-P'₁)*W*P'₀-(1-P₁)*U T*P₀‖ ≤ ‖W-U T‖+‖P₀-P'₀‖+‖P₁-P'₁‖ ∧
    ‖P₀-P'₀‖ ≤ ε₀/(Γ₀-ε₀) ∧ ‖P₁-P'₁‖ ≤ ε₁/(Γ₁-ε₁) := by
  obtain ⟨m₀, r₀, hr₀, _, hg₀, hn₀, hP₀, hP'₀⟩ := band_endpoint _ hd₀ hS₀ he₀
  obtain ⟨m₁, r₁, hr₁, _, hg₁, hn₁, hP₁, hP'₁⟩ := band_endpoint _ hd₁ hS₁ he₁
  have hb := transfer_gap hT hH hU hr₀ hr₁ hg₀ hg₁ D₀ D₁ hd₀ hd₁ he₀ he₁ hn₀ hn₁ W
  dsimp only at hb ⊢
  rw [hP₀, hP'₀, hP₁, hP'₁] at hb
  exact ⟨hb.1, hb.2.1.1, hb.2.2.1⟩

end UnitaryProducts.Paper
