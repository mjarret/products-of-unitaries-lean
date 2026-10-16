/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogarithmBranch

/-!
# The continuous and smooth logarithm of a walk

## Declarations

- `arc_le_two_pi`
- `contDiffOn_log_of_continuous`
- `continuousOn_log_moving_window`
- `continuousWithinAt_log_of_local_window`
- `exists_log_moving_cut`
- `hasDerivWithinAt_log`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open NormedSpace Complex Set Real

namespace UnitaryProducts

open UnitaryProducts.Corrector

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A unitary whose spectrum lies on the closed arc from `e^{i(φ+γ/2)}` to `e^{i(φ+2π-γ/2)}` has
`γ ≤ 2π`, since its spectrum is nonempty. -/
theorem arc_le_two_pi {d : ℕ} [NeZero d] {γ φ : ℝ} (W : Matrix (Fin d) (Fin d) ℂ)
    (hspec : ∀ z ∈ spectrum ℂ W,
      ∃ θ ∈ Icc (φ + γ / 2) (φ + 2 * π - γ / 2), z = Complex.exp (θ * I)) :
    γ ≤ 2 * π := by
  obtain ⟨z, hz⟩ := spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ W
  obtain ⟨θ, ⟨hθ1, hθ2⟩, -⟩ := hspec z hz
  linarith

/-- Continuity of a logarithm only needs a fixed spectral window locally. -/
theorem continuousWithinAt_log_of_local_window [NeZero d]
    {G W : ℝ → 𝕄} {S₀ : Set ℝ} {s α r : ℝ} (hr : r < π)
    (hHerm : (G s).IsHermitian)
    (hnorm : ‖G s - ((-α : ℝ) : ℂ) • 1‖ ≤ r)
    (hGW : evol (G s) 1 = W s)
    (hlocal : ∀ᶠ t in nhdsWithin s S₀, (G t).IsHermitian ∧
      ‖G t - ((-α : ℝ) : ℂ) • 1‖ ≤ r ∧ evol (G t) 1 = W t)
    (hW : ContinuousWithinAt W S₀ s) : ContinuousWithinAt G S₀ s := by
  set c : ℂ := ((-α : ℝ) : ℂ) with hc
  set S : Set 𝕄 := {A : 𝕄 | A.IsHermitian ∧ ‖A - c • 1‖ ≤ r} with hSdef
  have hSclosed : IsClosed S := by
    have h1 : IsClosed {A : 𝕄 | A.IsHermitian} := isClosed_eq continuous_star continuous_id
    have h2 : IsClosed {A : 𝕄 | ‖A - c • 1‖ ≤ r} :=
      isClosed_le (by fun_prop) continuous_const
    exact h1.inter h2
  have hSbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := c • (1:𝕄)) (r := r)).subset ?_
    intro A hA
    simpa [Metric.mem_closedBall, dist_eq_norm] using hA.2
  have hScompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  change Filter.Tendsto G (nhdsWithin s (S₀)) (nhds (G s))
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hns.eventually hlocal)
  have hyS : ∀ n : ℕ, G (ns (n + N)) ∈ S := fun n ↦
    ⟨(hN (n + N) (by omega)).1, (hN (n + N) (by omega)).2.1⟩
  obtain ⟨A', hA'S, φ, hφ, hlim⟩ := hScompact.tendsto_subseq hyS
  have hsub : Filter.Tendsto (fun i ↦ ns (φ i + N)) Filter.atTop (nhdsWithin s (S₀)) := by
    refine hns.comp (Filter.tendsto_atTop_mono (fun i ↦ ?_) Filter.tendsto_id)
    exact le_trans hφ.le_apply (Nat.le_add_right _ _)
  have hWlim : Filter.Tendsto (fun i ↦ W (ns (φ i + N))) Filter.atTop (nhds (W s)) :=
    Filter.Tendsto.comp hW hsub
  have hElim : Filter.Tendsto (fun i ↦ evol (G (ns (φ i + N))) 1) Filter.atTop
      (nhds (evol A' 1)) :=
    (continuous_evol_one.tendsto A').comp hlim
  have heq : ∀ i, evol (G (ns (φ i + N))) 1 = W (ns (φ i + N)) := fun i ↦ (hN _ (by omega)).2.2
  have hlimW : evol A' 1 = W s := by
    refine tendsto_nhds_unique ?_ hWlim
    simpa [heq] using hElim
  have hA'eq : A' = G s := eq_of_evol_eq hr hA'S.1 hA'S.2 hHerm hnorm (hlimW.trans hGW.symm)
  exact ⟨fun i ↦ φ i + N, by rw [← hA'eq]; exact hlim⟩

/-- A continuous moving window of radius strictly less than π selects one continuous branch. -/
theorem continuousOn_log_moving_window [NeZero d]
    {G W : ℝ → 𝕄} {S : Set ℝ} {α r : ℝ → ℝ}
    (hα : ContinuousOn α S) (hr : ContinuousOn r S)
    (hrπ : ∀ s ∈ S, r s < π)
    (hHerm : ∀ s ∈ S, (G s).IsHermitian)
    (hnorm : ∀ s ∈ S, ‖G s - ((-α s : ℝ) : ℂ) • 1‖ ≤ r s)
    (hGW : ∀ s ∈ S, evol (G s) 1 = W s)
    (hW : ContinuousOn W S) : ContinuousOn G S := by
  intro s hs
  let R := (r s + π) / 2
  have hrR : r s < R := by dsimp [R]; linarith [hrπ s hs]
  have hRπ : R < π := by dsimp [R]; linarith [hrπ s hs]
  have hc : ContinuousWithinAt
      (fun t ↦ ((-α t : ℝ) : ℂ) • (1 : 𝕄)) S s :=
    ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hα s hs).neg).smul
      continuousWithinAt_const)
  have hf : ContinuousWithinAt
      (fun t ↦ r t + ‖((-α t : ℝ) : ℂ) • (1 : 𝕄) - ((-α s : ℝ) : ℂ) • 1‖) S s :=
    (hr s hs).add (hc.sub continuousWithinAt_const).norm
  have hfR : r s + ‖((-α s : ℝ) : ℂ) • (1 : 𝕄) - ((-α s : ℝ) : ℂ) • 1‖ < R := by
    simpa only [sub_self, norm_zero, add_zero] using hrR
  have hnear := hf.eventually (gt_mem_nhds hfR)
  apply continuousWithinAt_log_of_local_window (G := G) (W := W) (S₀ := S)
    (s := s) (α := α s) (r := R) hRπ (hHerm s hs)
    ((hnorm s hs).trans hrR.le) (hGW s hs) _ (hW s hs)
  filter_upwards [hnear, self_mem_nhdsWithin] with t ht htS
  refine ⟨hHerm t htS, ?_, hGW t htS⟩
  calc ‖G t - ((-α s : ℝ) : ℂ) • 1‖
      ≤ ‖G t - ((-α t : ℝ) : ℂ) • 1‖ +
        ‖((-α t : ℝ) : ℂ) • (1 : 𝕄) - ((-α s : ℝ) : ℂ) • 1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ r t + ‖((-α t : ℝ) : ℂ) • (1 : 𝕄) - ((-α s : ℝ) : ℂ) • 1‖ :=
        add_le_add (hnorm t htS) le_rfl
    _ ≤ R := ht.le

/-- A continuous cut angle and an avoided open arc of positive continuous length
select a single continuous Hermitian logarithm, with the pointwise width. -/
theorem exists_log_moving_cut [NeZero d]
    (W : ℝ → 𝕄) (φ γ : ℝ → ℝ) (S : Set ℝ)
    (hW : ContinuousOn W S) (hφ : ContinuousOn φ S) (hγ : ContinuousOn γ S)
    (hγ0 : ∀ s ∈ S, 0 < γ s)
    (hunit : ∀ s ∈ S, star (W s) * W s = 1)
    (hspec : ∀ s ∈ S, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (φ s + γ s / 2) (φ s + 2 * π - γ s / 2),
        z = Complex.exp (θ * I)) :
    ∃ G : ℝ → 𝕄, (∀ s, (G s).IsHermitian) ∧ ContinuousOn G S ∧
      ∀ s ∈ S, evol (G s) 1 = W s ∧
        ‖G s - ((-(φ s + π) : ℝ) : ℂ) • 1‖ ≤ (2 * π - γ s) / 2 := by
  classical
  let P := fun s (A : 𝕄) ↦ A.IsHermitian ∧
    ‖A - ((-(φ s + π) : ℝ) : ℂ) • 1‖ ≤ (2 * π - γ s) / 2 ∧ evol A 1 = W s
  have hex : ∀ s ∈ S, ∃ A, P s A := by
    intro s hs
    apply exists_isHermitian_evol_eq (by linarith [arc_le_two_pi (W s) (hspec s hs)])
      (by linarith [hγ0 s hs]) (hunit s hs)
    intro z hz
    obtain ⟨θ, hθ, hzθ⟩ := hspec s hs z hz
    exact ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hzθ⟩
  -- The choice is determined: the logarithm in the window is unique (`eq_of_evol_eq`). Off `S`,
  -- or without a logarithm in the window, `G s` is the junk value `0`, never read.
  let G := fun s ↦ if h : ∃ A, P s A then h.choose else 0
  have hG : ∀ s ∈ S, P s (G s) := fun s hs ↦ by
    dsimp [G]; rw [dif_pos (hex s hs)]; exact (hex s hs).choose_spec
  have hHerm : ∀ s, (G s).IsHermitian := fun s ↦ by
    dsimp [G]; split_ifs with h
    · exact h.choose_spec.1
    · exact Matrix.isHermitian_zero
  refine ⟨G, hHerm, ?_, fun s hs ↦ ⟨(hG s hs).2.2, (hG s hs).2.1⟩⟩
  exact continuousOn_log_moving_window (hφ.add continuousOn_const)
    ((continuousOn_const.sub hγ).div_const 2)
    (fun s hs ↦ by linarith [hγ0 s hs]) (fun s _ ↦ hHerm s)
    (fun s hs ↦ (hG s hs).2.1) (fun s hs ↦ (hG s hs).2.2) hW

/-- Lemma A.2(ii): a continuous Hermitian logarithm $G$ of a $C^2$ path $W$, with
$\|i\,\mathrm{ad}_{G(s)}\| < 2\pi$, is $C^2$, since near each point it is the local inverse of
$X \mapsto e^{-iX}$ composed with $W$ (inverse function theorem). Smoothness is local and needs no
differentiability of the cut. -/
theorem contDiffOn_log_of_continuous [NeZero d] {G W : ℝ → 𝕄} {S : Set ℝ}
    (hGcont : ContinuousOn G S) (hG : ∀ s ∈ S, (G s).IsHermitian)
    (hwidth : ∀ s ∈ S, ‖I • adL (G s)‖ < 2 * π)
    (hGW : ∀ s ∈ S, evol (G s) 1 = W s)
    (hW : ContDiffOn ℝ 2 W S) : ContDiffOn ℝ 2 G S := by
  intro s₀ hs₀
  have hX₀ : (G s₀).IsHermitian := hG s₀ hs₀
  have hw := hwidth s₀ hs₀
  -- the differential at `G s₀` is invertible
  set Lequiv : 𝕄 ≃L[ℂ] 𝕄 := ContinuousLinearEquiv.equivOfInverse (evolDeriv (G s₀))
    (evolDerivInv (G s₀)) (evolDerivInv_evolDeriv hX₀ hw) (evolDeriv_evolDerivInv hX₀ hw)
    with hLdef
  have hfd : HasFDerivAt (fun X : 𝕄 ↦ evol X 1) (Lequiv : 𝕄 →L[ℂ] 𝕄) (G s₀) :=
    hasFDerivAt_evol_one hX₀
  have hcd : ContDiffAt ℂ 2 (fun X : 𝕄 ↦ evol X 1) (G s₀) := contDiffAt_evol_one (G s₀)
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- the local inverse of the exponential is smooth
  have hψcd : ContDiffAt ℂ 2 (hcd.localInverse hfd hn) (evol (G s₀) 1) :=
    hcd.to_localInverse hfd hn
  have hψR : ContDiffAt ℝ 2 (hcd.localInverse hfd hn) (W s₀) := by
    rw [← hGW s₀ hs₀]; exact hψcd.restrict_scalars ℝ
  have hleft : ∀ᶠ X in nhds (G s₀), hcd.localInverse hfd hn (evol X 1) = X :=
    (hcd.hasStrictFDerivAt' hfd hn).eventually_left_inverse
  -- near `s₀` the logarithm is that local inverse composed with the walk
  have heq : ∀ᶠ s in nhdsWithin s₀ (S), (hcd.localInverse hfd hn ∘ W) s = G s := by
    filter_upwards [(hGcont s₀ hs₀).eventually hleft, self_mem_nhdsWithin] with s h1 h2
    change hcd.localInverse hfd hn (W s) = G s; rw [← hGW s h2]; exact h1
  have hcomp : ContDiffWithinAt ℝ 2 (hcd.localInverse hfd hn ∘ W) (S) s₀ :=
    hψR.comp_contDiffWithinAt s₀ (hW s₀ hs₀)
  exact hcomp.congr_of_eventuallyEq (heq.mono fun s h ↦ h.symm)
    (heq.self_of_nhdsWithin hs₀).symm

/-- **The derivative of a logarithm path.**  If `G` is continuous at `s` within `S`, `G(s)` is
Hermitian of spectral width below `2π`, and `e^{-iG} = W` on `S`, then `G` is differentiable at
`s` within `S` wherever `W` is, with derivative `Φ_{G(s)}⁻¹(i W(s)* Ẇ)`: near `s`, `G` is the
local inverse of the exponential composed with `W`. -/
theorem hasDerivWithinAt_log [NeZero d] {G W : ℝ → 𝕄} {S : Set ℝ} {s : ℝ} {Wd : 𝕄}
    (hs : s ∈ S) (hGcont : ContinuousWithinAt G S s) (hG : (G s).IsHermitian)
    (hwidth : ‖(I • adL (G s) : 𝕄 →L[ℂ] 𝕄)‖ < 2 * π)
    (hGW : ∀ t ∈ S, evol (G t) 1 = W t) (hW : HasDerivWithinAt W Wd S s) :
    HasDerivWithinAt G (bernSeries (I • adL (G s)) (I • (star (W s) * Wd))) S s := by
  set Lequiv : 𝕄 ≃L[ℂ] 𝕄 := ContinuousLinearEquiv.equivOfInverse (evolDeriv (G s))
    (evolDerivInv (G s)) (evolDerivInv_evolDeriv hG hwidth) (evolDeriv_evolDerivInv hG hwidth)
    with hLdef
  have hfd : HasFDerivAt (fun X : 𝕄 ↦ evol X 1) (Lequiv : 𝕄 →L[ℂ] 𝕄) (G s) :=
    hasFDerivAt_evol_one hG
  have hcd : ContDiffAt ℂ 2 (fun X : 𝕄 ↦ evol X 1) (G s) := contDiffAt_evol_one (G s)
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hstrict := hcd.hasStrictFDerivAt' hfd hn
  -- the local inverse of the exponential has differential `evolDerivInv (G s)` at `W s`
  have hψ : HasFDerivAt (hcd.localInverse hfd hn)
      ((Lequiv.symm : 𝕄 →L[ℂ] 𝕄).restrictScalars ℝ) (W s) := by
    rw [← hGW s hs]; exact hstrict.to_localInverse.hasFDerivAt.restrictScalars ℝ
  -- near `s` the logarithm is that local inverse composed with the walk
  have heq : ∀ᶠ t in nhdsWithin s S, G t = (hcd.localInverse hfd hn ∘ W) t := by
    filter_upwards [hGcont.eventually hstrict.eventually_left_inverse, self_mem_nhdsWithin]
      with t h1 h2
    change G t = hcd.localInverse hfd hn (W t); rw [← hGW t h2]; exact h1.symm
  rw [← hGW s hs]
  exact (hψ.comp_hasDerivWithinAt s hW).congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hs)

end UnitaryProducts
