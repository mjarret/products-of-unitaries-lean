/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.CircularBands

/-!
# Bands of walks and their logarithms, with multiplicity

## Declarations

- `arcEigenvalueCount_evol`
- `charpoly_evol_roots`
- `walk_band_jrs_count`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Complex Set Real Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The characteristic roots of `e^{-iΛ}`, with multiplicity, are the `e^{-iλ_i}`. -/
theorem charpoly_evol_roots (Λ : 𝕄) (hΛ : Λ.IsHermitian) :
    (UnitaryProducts.evol Λ 1).charpoly.roots =
      Multiset.map (fun i ↦ Complex.exp (-I*(hΛ.eigenvalues i:ℂ))) Finset.univ.val := by
  let u : 𝕄ˣ := Unitary.toUnits hΛ.eigenvectorUnitary
  let D : 𝕄 := Matrix.diagonal (RCLike.ofReal ∘ hΛ.eigenvalues)
  have hs : Λ = (u:𝕄) * D * ((u⁻¹ : 𝕄ˣ) : 𝕄) := by
    have h := hΛ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [Unitary.val_toUnits_apply, Unitary.val_inv_toUnits_apply]
    exact h
  have hD : (-I) • D = Matrix.diagonal (fun i ↦ -I*(hΛ.eigenvalues i:ℂ)) := by
    rw [← Matrix.diagonal_smul]
    rfl
  have hexp : NormedSpace.exp (Matrix.diagonal (fun i ↦ -I*(hΛ.eigenvalues i:ℂ))) =
      Matrix.diagonal (fun i ↦ Complex.exp (-I*(hΛ.eigenvalues i:ℂ))) := by
    rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  have hev : UnitaryProducts.evol Λ 1 =
      (u:𝕄) * Matrix.diagonal (fun i ↦ Complex.exp (-I*(hΛ.eigenvalues i:ℂ))) *
      ((u⁻¹ : 𝕄ˣ) : 𝕄) := by
    have hc : (-I) • Λ = (u:𝕄) * ((-I) • D) * ((u⁻¹ : 𝕄ˣ) : 𝕄) := by
      rw [mul_smul_comm, smul_mul_assoc, ← hs]
    rw [UnitaryProducts.evol, one_smul, hc, hD, Matrix.exp_units_conj, hexp]
  have hr := Polynomial.roots_multiset_prod_X_sub_C
    (Multiset.map (fun i ↦ Complex.exp (-I*(hΛ.eigenvalues i:ℂ))) Finset.univ.val)
  rw [Multiset.map_map] at hr
  rw [hev, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod]
  exact hr

open Classical in
/-- The arc count of `e^{-iΛ}` is the number of indices `i` whose phase `e^{-iλ_i}` lies on
the open arc `{e^{-iθ} : α < θ < β}`. -/
theorem arcEigenvalueCount_evol (Λ : 𝕄) (hΛ : Λ.IsHermitian) (α β : ℝ) :
    arcEigenvalueCount (UnitaryProducts.evol Λ 1) α β =
      (Finset.univ.filter (fun i ↦ ∃ θ ∈ Ioo α β,
        Complex.exp (-I*(θ:ℂ)) = Complex.exp (-I*(hΛ.eigenvalues i:ℂ)))).card := by
  classical
  unfold arcEigenvalueCount
  rw [charpoly_evol_roots Λ hΛ, Multiset.filter_map, Multiset.card_map, Finset.card_def,
    Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ ↦
    ⟨fun ⟨θ, hθ, he⟩ ↦ ⟨θ, hθ, he.symm⟩, fun ⟨θ, hθ, he⟩ ↦ ⟨θ, hθ, he.symm⟩⟩

/-- Supports the walk paragraph of §4.3: a band of $m$ eigenvalues of a walk on
the arcs
$\{e^{-i\theta} : \alpha(s) < \theta < \beta(s)\}$, with gap $g \ge \vartheta > 0$,
puts the spectrum in a closed arc of length $2\pi-\vartheta$; the open complement has no eigenvalue.
The walk's
band is the band of its logarithm in $(\alpha,\beta)$, with spectral gap at least $g$.

Reading the statement against the paper:
* The walk need only be unitary and continuous here (`hW`, `hWc`); the paper's walk is $C^2$.
* `trackedCircularBand W α β g` is the band on moving arcs with a continuous positive lower bound
  `g` for its gap; any such bound is allowed, not only $\Gamma$ itself.
* `∃ a, spectrumAvoidsOpenArc W ϑ a` gives the closed-arc hypothesis of the walk comparison
  by `spectrumAvoidsOpenArc_iff_closedArc`.
* Every Hermitian $\Lambda$ with $e^{-i\Lambda} = W$, spectrum in $[a(s), a(s) + 2\pi - \vartheta]$
  and $C^2$ is covered, in particular the $\Lambda$ of Lemma A.2.
* `arcEigenvalueCount (W s) (α s) (β s) = m` counts the eigenvalues on the arc with multiplicity
  (Definition 2.5); `0 < m` already follows from the band hypotheses and is harmless.
* The conclusion `(jrsCoefficientTracked Λ hΛ m g (fun s ↦ Icc (α s) (β s))).1` says that $\Lambda$
  has a band of $m$ eigenvalues in $[\alpha(s), \beta(s)]$, with endpoints off its spectrum (so the
  closed and the open interval select the same band) and gap at least $g$: the hypotheses of the
  Jansen–Ruskai–Seiler coefficient for $\Lambda$.

The proof follows the paper's: (1) cut at $\alpha(s)$, take the continuous logarithm $G$ with
spectrum in $(\alpha, \alpha + 2\pi)$ and its least eigenvalue $a(s)$, which is continuous; the gap
puts the spectrum in $[a, a + 2\pi - \vartheta]$ (`walk_band_log`); (2) every $\Lambda$ in that
window equals $G$ (`eq_of_evol_eq`), so the band transfers; (3) the count of eigenvalues of
$e^{-i\Lambda}$ on the arc is the number of eigenvalues of $\Lambda$ in $[\alpha, \beta]$
(`arcEigenvalueCount_evol`). Lean uses the least eigenvalue and the gap directly instead of the
paper's arc through the cut; the inequality is the same. -/
theorem walk_band_jrs_count [NeZero d] (W : ℝ → 𝕄) (α β g : ℝ → ℝ) (ϑ : ℝ) (m : ℕ)
    (hW : (walk W 1).1) (hWc : ContinuousOn W (Icc (0 : ℝ) 1))
    (hband : trackedCircularBand W α β g) (hϑ : 0 < ϑ)
    (hϑg : ∀ s ∈ Icc (0 : ℝ) 1, ϑ ≤ g s) :
    ∃ a : ℝ → ℝ, spectrumAvoidsOpenArc W ϑ a ∧
      ∀ (Λ : ℝ → 𝕄) (hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian),
        (∀ s (hs : s ∈ Icc (0 : ℝ) 1), UnitaryProducts.evol (Λ s) 1 = W s ∧
          ∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s+(2*π-ϑ))) →
        ContDiffOn ℝ 2 Λ (Icc (0 : ℝ) 1) → 0 < m →
        (∀ s ∈ Icc (0 : ℝ) 1, arcEigenvalueCount (W s) (α s) (β s) = m) →
        (jrsCoefficientTracked Λ hΛ m g (fun s ↦ Icc (α s) (β s))).1 := by
  obtain ⟨a,hfree,h⟩ := walk_band_log W α β g ϑ hW hWc hband hϑ hϑg
  refine ⟨a,hfree,fun Λ hΛ hlog hC hm hcount ↦ ?_⟩
  have hB := h Λ hΛ hlog
  obtain ⟨hα,hβ,hg,hb⟩ := hband
  refine (jrs_coefficient_tracked_band Λ hΛ m g _).1.mpr
    ⟨hC,hg,fun s hs ↦ ⟨(hb s hs).1,(hB s hs).2.2.1⟩,hm,fun s hs ↦ ?_,α,β,hα,hβ,
      fun s hs ↦ ⟨rfl,(hb s hs).2.1.le,(hB s hs).1,(hB s hs).2.1⟩⟩
  rw [← hcount s hs, ← (hlog s hs).1, arcEigenvalueCount_evol (Λ s) (hΛ s hs)]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (hB s hs).2.2.2 i

end UnitaryProducts.Paper
