/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Walks.LogHessian

/-!
# Derivative bounds for the walk logarithm on $[0,1]$

## Declarations

- `norm_walkLogHessian_interior_le`
- `norm_walkLogHessian_on_Icc_le`
- `norm_walkLogSlope_on_Icc_le`
- `Prose.evol_sub_scalar_one`
-/

@[expose] public section

open Real Set Complex Filter NormedSpace
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace UnitaryProducts
-- Installs `matrixCStarAlgebra`, built from the ℓ² operator-norm instances (same norm as the
-- statements); see its docstring in `Walks/LogarithmBranch.lean`.
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

namespace Prose

omit [NeZero d] in
/-- Section 4, the scalar shift identifying the fixed-turn integral with the
rotated walk in the logarithm and transfer arguments. -/
theorem evol_sub_scalar_one (H : 𝕄) (c : ℝ) :
    evol (H - (c : ℂ) • 1) 1 = Complex.exp (I * (c : ℂ)) • evol H 1 := by
  have he : -I • (H - (c : ℂ) • (1 : 𝕄)) =
      algebraMap ℂ 𝕄 (I * (c : ℂ)) + (-I) • H := by
    rw [Algebra.algebraMap_eq_smul_one]
    module
  let +nondep : NormedAlgebra ℚ 𝕄 := .restrictScalars ℚ ℂ 𝕄
  rw [evol, one_smul, he, NormedSpace.exp_add_of_commute (Algebra.commutes _ _)]
  rw [← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  simp only [evol, one_smul]

end Prose

/-- Lemma A.2(ii), with coefficient $\cos^{-2}(w/4)$, at an interior point $s$: freeze the centre
$c$ of the window at $s$, apply `norm_walkLogHessian_centered_le` to $H - c$ and $e^{ic}W$, and
undo the unimodular factor $e^{ic}$. -/
theorem norm_walkLogHessian_interior_le
    {H Hd Hdd W Wd Wdd : ℝ → 𝕄} {w s c : ℝ} (hw : w < 2 * π) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian) (hc : ContinuousOn H (Icc (0 : ℝ) 1))
    (hcenter : ‖H s - (c : ℂ) • 1‖ ≤ w / 2) (he : ∀ x ∈ Icc (0 : ℝ) 1, evol (H x) 1 = W x)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt H (Hd x) x) (hdd : HasDerivAt Hd (Hdd s) s)
    (hW : ContinuousOn W (Icc (0 : ℝ) 1)) (hWd : ContinuousOn Wd (Icc (0 : ℝ) 1))
    (hWdd : ContinuousOn Wdd (Icc (0 : ℝ) 1)) (hdW : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt W (Wd x) x)
    (hddW : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Wd (Wdd x) x) :
    ‖Hdd s‖≤walkLogSlope w*‖Wdd s‖+(Real.cos (w/4))⁻¹^2*‖Wd s‖^2 := by
  let z : ℂ := Complex.exp (I*(c:ℂ))
  let G : ℝ → 𝕄 := fun x ↦ H x-(c:ℂ) • 1
  have hnorm (M : 𝕄) : ‖z • M‖=‖M‖ := by
    rw [norm_smul,show ‖z‖=1 from Complex.norm_exp_I_mul_ofReal c,one_mul]
  have hcont : ContinuousAt (fun x ↦ ‖G x‖) s :=
    (((hc s ⟨hs.1.le,hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)).sub continuousAt_const).norm
  have hn : ∀ᶠ x in 𝓝 s, ‖G x‖<π :=
    hcont.eventually (gt_mem_nhds (hcenter.trans_lt (by linarith)))
  obtain ⟨a,b,_,habn,hab⟩ := exists_Icc_mem_subset_of_mem_nhds
    (Filter.inter_mem (isOpen_Ioo.mem_nhds hs) hn)
  have hsab : s ∈ Ioo a b := Icc_mem_nhds_iff.mp habn
  have hsub : Icc a b ⊆ Icc (0:ℝ) 1 := fun x hx ↦
    ⟨(hab hx).1.1.le,(hab hx).1.2.le⟩
  have hG : ∀ x ∈ Icc a b, (G x).IsHermitian := by
    intro x hx
    exact (hH x (hsub hx)).sub (by
      change star ((c:ℂ) • (1:𝕄))=(c:ℂ) • (1:𝕄)
      simp only [star_smul,star_one,Complex.star_def,Complex.conj_ofReal])
  have heG : ∀ x ∈ Icc a b, evol (G x) 1=z • W x := fun x hx ↦ by
    rw [Prose.evol_sub_scalar_one,he x (hsub hx)]
  have hb := norm_walkLogHessian_centered_le (H:=G) (Hd:=Hd) (V:=fun x ↦ z • W x)
    (Vd:=fun x ↦ z • Wd x) (Vdd:=fun x ↦ z • Wdd x)
    hsab hw hcenter hG (fun x hx ↦ (hab hx).2) heG
    (fun x hx ↦ (hd x (hab ⟨hx.1.le,hx.2.le⟩).1).sub_const _) hdd
    ((hW.mono hsub).const_smul z) ((hWd.mono hsub).const_smul z)
    ((hWdd.mono hsub).const_smul z)
    (fun x hx ↦ (hdW x (hab ⟨hx.1.le,hx.2.le⟩).1).const_smul z)
    (fun x hx ↦ (hddW x (hab ⟨hx.1.le,hx.2.le⟩).1).const_smul z)
  simpa only [hnorm] using hb

/-- Lemma A.2(ii), with coefficient $\cos^{-2}(w/4)$, on all of $[0, 1]$: the interior estimate
extends to both endpoints by continuity. -/
theorem norm_walkLogHessian_on_Icc_le
    {H W : ℝ → 𝕄} {w : ℝ} (hw : w < 2 * π) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1)) (hW : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖H s - (c : ℂ) • 1‖ ≤ w / 2)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, evol (H x) 1 = W x) :
    ∀ s ∈ Icc (0:ℝ) 1,
      ‖derivWithin (derivWithin H (Icc (0:ℝ) 1)) (Icc 0 1) s‖ ≤
        walkLogSlope w*‖derivWithin (derivWithin W (Icc (0:ℝ) 1)) (Icc 0 1) s‖+
        (Real.cos (w/4))⁻¹^2*‖derivWithin W (Icc (0:ℝ) 1) s‖^2 := by
  let Hd := derivWithin H (Icc (0:ℝ) 1)
  let Hdd := derivWithin Hd (Icc (0:ℝ) 1)
  let Wd := derivWithin W (Icc (0:ℝ) 1)
  let Wdd := derivWithin Wd (Icc (0:ℝ) 1)
  have hcd : ContDiffOn ℝ 1 Hd (Icc (0:ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcdd : ContDiffOn ℝ 0 Hdd (Icc (0:ℝ) 1) :=
    hcd.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWcd : ContDiffOn ℝ 1 Wd (Icc (0:ℝ) 1) :=
    hW.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hWcdd : ContDiffOn ℝ 0 Wdd (Icc (0:ℝ) 1) :=
    hWcd.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hb : ∀ s ∈ Ioo (0:ℝ) 1, ‖Hdd s‖≤
      walkLogSlope w*‖Wdd s‖+(Real.cos (w/4))⁻¹^2*‖Wd s‖^2 := by
    intro s hs
    obtain ⟨c,hc0⟩ := hcenter s ⟨hs.1.le,hs.2.le⟩
    exact norm_walkLogHessian_interior_le hw hs hH hc.continuousOn hc0 he
      (fun x hx ↦ ((hc.differentiableOn (by norm_num) x
        ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2))
      (((hcd.differentiableOn (by norm_num) s ⟨hs.1.le,hs.2.le⟩).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)) hW.continuousOn hWcd.continuousOn hWcdd.continuousOn
      (fun x hx ↦ ((hW.differentiableOn (by norm_num) x
        ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2))
      (fun x hx ↦ ((hWcd.differentiableOn (by norm_num) x
        ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2))
  have hcl : closure (Ioo (0:ℝ) 1)=Icc (0:ℝ) 1 := closure_Ioo (by norm_num)
  intro s hs
  exact le_on_closure hb (by rw [hcl]; exact hcdd.continuousOn.norm)
    (by
      rw [hcl]
      exact (continuousOn_const.mul hWcdd.continuousOn.norm).add
        (continuousOn_const.mul (hWcd.continuousOn.norm.pow 2))) (by rwa [hcl])

/-- Lemma A.2(i) on $[0, 1]$: $\Lambda' = \Phi_\Lambda^{-1}(iW^\dagger W')$
(`hasDerivWithinAt_log`), $\|iW^\dagger W'\| \le \|W'\|$ and $\|\Phi_\Lambda^{-1}\| \le S$
(`norm_inverse_le_walkLogSlope`). -/
theorem norm_walkLogSlope_on_Icc_le {H W : ℝ → 𝕄} {w : ℝ}
    (hw : w < 2 * π) (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hc : ContinuousOn H (Icc (0 : ℝ) 1)) (hW : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖H s - (c : ℂ) • 1‖ ≤ w / 2)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, evol (H x) 1 = W x) :
    ∀ s ∈ Icc (0:ℝ) 1, ‖derivWithin H (Icc (0:ℝ) 1) s‖ ≤
      walkLogSlope w*‖derivWithin W (Icc (0:ℝ) 1) s‖ := by
  intro s hs
  obtain ⟨c,hc0⟩ := hcenter s hs
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := by linarith [(norm_nonneg _).trans hc0]
  have ha : ‖I • adL (H s)‖≤w :=
    (norm_I_smul_adL_le (H s) (c:ℂ)).trans (by linarith)
  let Wd := derivWithin W (Icc (0:ℝ) 1)
  have hd := hasDerivWithinAt_log hs (hc s hs) (hH s hs) (ha.trans_lt hw) he
    ((hW.differentiableOn (by norm_num) s hs).hasDerivWithinAt)
  rw [hd.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) s hs)]
  have hu : star (W s)*W s=1 := by rw [← he s hs]; exact star_evol_mul_self (hH s hs) 1
  have hy : ‖I • (star (W s)*Wd s)‖≤‖Wd s‖ := by
    rw [norm_smul,Complex.norm_I,one_mul]
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _)
      (by rw [norm_star]; exact norm_le_one_of_star_mul_self hu))
  exact ((UnitaryProducts.Corrector.bernSeries (I • adL (H s))).le_opNorm _).trans
    (mul_le_mul (norm_inverse_le_walkLogSlope (hH s hs) hw ha) hy
      (norm_nonneg _) (walkLogSlope_nonneg hw0 hw))

end UnitaryProducts
