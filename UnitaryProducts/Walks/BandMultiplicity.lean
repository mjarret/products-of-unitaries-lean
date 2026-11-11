/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.TrackedBands

/-!
# Empty spectral arcs and phase coordinates

## Declarations

- `norm_of_mem_spectrum`
- `phase_inj`
- `phase_of_unit`
- `spectrumAvoidsOpenArc`
- `spectrumAvoidsOpenArc_iff_closedArc`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Pointwise
open Complex Set Real Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The complementary open arc of length $\vartheta$ contains no eigenvalue:
$\vartheta > 0$, `a` is continuous on $[0,1]$, and for $s \in [0,1]$ the open arc
$\{e^{-i\theta} : a(s) + 2\pi - \vartheta < \theta < a(s) + 2\pi\}$ avoids the spectrum of $W(s)$.
For $\vartheta > 2\pi$ the arc would be the whole circle, impossible for $d \ge 1$; consumers take
$0 < \vartheta \le 2\pi$. -/
def spectrumAvoidsOpenArc (W : ℝ → 𝕄) (ϑ : ℝ) (a : ℝ → ℝ) : Prop :=
  0 < ϑ ∧ ContinuousOn a (Icc (0 : ℝ) 1) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ θ ∈ Ioo (a s+2*π-ϑ) (a s+2 * π),
      Complex.exp (-I*(θ:ℂ)) ∉ spectrum ℂ (W s)

/-- Phases in one open turn $(\alpha, \alpha + 2\pi)$ with the same $e^{-i\theta}$ are equal. -/
theorem phase_inj {α x y : ℝ}
    (hx : x ∈ Ioo α (α + 2 * π)) (hy : y ∈ Ioo α (α + 2 * π))
    (he : Complex.exp (-I * (x : ℂ)) = Complex.exp (-I * (y : ℂ))) : x=y := by
  have hx' : |(-x)-(-(α+π))|<π := abs_lt.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hy' : |(-y)-(-(α+π))|<π := abs_lt.mpr ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have he' : Complex.exp (((-x:ℝ) : ℂ)*I)=Complex.exp (((-y:ℝ) : ℂ)*I) := by
    convert he using 1 <;> congr 1 <;> push_cast <;> ring
  have hb := congrArg (UnitaryProducts.argBranch (-(α+π))) he'
  rw [UnitaryProducts.argBranch_exp_mul_I hx',UnitaryProducts.argBranch_exp_mul_I hy'] at hb
  simpa only [Complex.ofReal_neg,neg_neg,Complex.ofReal_inj] using hb

/-- Every unit complex number is $e^{-i\theta}$ for some $\theta \in [a, a + 2\pi)$. -/
theorem phase_of_unit {z : ℂ} (hz : ‖z‖ = 1) (a : ℝ) :
    ∃ θ ∈ Ico a (a+2 * π), z=Complex.exp (-I*(θ:ℂ)) := by
  have h1 : z=Complex.exp (-I*((-arg z:ℝ) : ℂ)) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [hz,Complex.ofReal_one,one_mul]
    congr 1; push_cast; ring
  refine ⟨toIcoMod two_pi_pos a (-arg z),toIcoMod_mem_Ico _ _ _,h1.trans ?_⟩
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-toIcoDiv two_pi_pos a (-arg z),?_⟩
  rw [toIcoMod,zsmul_eq_mul]
  push_cast
  ring

/-- The eigenvalues of a unitary matrix have modulus one. -/
theorem norm_of_mem_spectrum {U : 𝕄} (hU : star U * U = 1) {z : ℂ}
    (hz : z ∈ spectrum ℂ U) : ‖z‖=1 :=
  mem_sphere_zero_iff_norm.mp (spectrum.subset_circle_of_unitary (𝕜 := ℂ)
    (Matrix.mem_unitaryGroup_iff'.mpr hU) hz)

/-- Avoiding the complementary open arc is equivalent to the spectral hypothesis of Lemma A.2
and the walk comparison, spectrum on the closed arc $[a(s), a(s) + w]$, with $w = 2\pi -
\vartheta$. -/
theorem spectrumAvoidsOpenArc_iff_closedArc (W : ℝ → 𝕄) (ϑ : ℝ) (a : ℝ → ℝ)
    (hW : (walk W 1).1) (hϑ : ϑ ≤ 2 * π) :
    spectrumAvoidsOpenArc W ϑ a ↔ 0 < ϑ ∧ ContinuousOn a (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
        ∃ θ ∈ Icc (a s) (a s+(2*π-ϑ)), z=Complex.exp (-Complex.I*(θ:ℂ)) := by
  constructor
  · rintro ⟨h0,hc,h⟩
    refine ⟨h0,hc,fun s hs z hz ↦ ?_⟩
    obtain ⟨θ,hθ,rfl⟩ := phase_of_unit (norm_of_mem_spectrum (hW s hs) hz) (a s)
    refine ⟨θ,⟨hθ.1,?_⟩,rfl⟩
    by_contra hlt
    push_neg at hlt
    exact h s hs θ ⟨by linarith,by linarith [hθ.2]⟩ hz
  · rintro ⟨h0,hc,h⟩
    refine ⟨h0,hc,fun s hs θ hθ hz ↦ ?_⟩
    obtain ⟨θ',hθ',he⟩ := h s hs _ hz
    have hpos : 0 < a s+2*π-θ := by linarith [hθ.2]
    have hθθ := phase_inj (α := a s-(a s+2*π-θ)/2) (x := θ) (y := θ')
      ⟨by linarith [hθ.1],by linarith⟩ ⟨by linarith [hθ'.1],by linarith [hθ'.2,hθ.1]⟩ he
    linarith [hθ'.2,hθ.1]

private theorem spectrum_turn [NeZero d] {A : 𝕄} {α : ℝ}
    (hn : ‖A - ((α + π : ℝ) : ℂ) • 1‖ < π) :
    ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π) := by
  intro x hx
  have hm : x-(α+π) ∈ spectrum ℝ (A-algebraMap ℝ 𝕄 (α+π)) := by
    rw [← spectrum.sub_singleton_eq]
    exact ⟨x,hx,α+π,Set.mem_singleton _,rfl⟩
  have hh : |x-(α+π)|<π := (spectrum.norm_le_norm_of_mem hm).trans_lt
    (by simpa only [Algebra.algebraMap_eq_smul_one,Complex.coe_smul] using hn)
  exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩

/-- Spectral data of a Hermitian logarithm with spectrum in one open turn `(α, α+2π)`:
its least eigenvalue `a` is a band phase, and its spectrum fits in `[a, a+2π-ϑ]`. -/
private theorem turn_bottom [NeZero d] {A U : 𝕄} (hA : A.IsHermitian) {α β g ϑ : ℝ}
    (hU : spectrum ℂ U = (fun θ : ℝ ↦ Complex.exp (-I*(θ:ℂ))) '' spectrum ℝ A)
    (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π)) (hβ2 : β < α+2 * π)
    (hband : ∃ θ ∈ Ioo α β, Complex.exp (-I*(θ:ℂ)) ∈ spectrum ℂ U)
    (hcomp : ∃ θ ∈ Ioo β (α + 2 * π), Complex.exp (-I*(θ:ℂ)) ∈ spectrum ℂ U)
    (hgap : ∀ x y, x ∈ Ioo α β → y ∈ Ioo β (α + 2 * π) →
      Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U → Complex.exp (-I * (y:ℂ)) ∈ spectrum ℂ U →
      g ≤ min (y-x) (2*π-(y-x)))
    (hϑ : ϑ ≤ g) :
    ϑ < 2*π ∧ ∀ x ∈ spectrum ℝ A,
      x ∈ Icc (UnitaryProducts.spectralBottom A) (UnitaryProducts.spectralBottom A+(2*π-ϑ)) := by
  have himg : ∀ x ∈ spectrum ℝ A, Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U :=
    fun x hx ↦ hU ▸ ⟨x,hx,rfl⟩
  have hphase : ∀ θ ∈ Ioo α (α + 2 * π),
      Complex.exp (-I*(θ:ℂ)) ∈ spectrum ℂ U → θ ∈ spectrum ℝ A := by
    intro θ hθ hs
    rw [hU] at hs
    obtain ⟨x,hx,hex⟩ := hs
    exact (phase_inj (hopen x hx) hθ hex) ▸ hx
  have hmin := UnitaryProducts.isLeast_spectralBottom hA
  obtain ⟨b,hb,hbs⟩ := hband
  obtain ⟨c,hc,hcs⟩ := hcomp
  have hbm := hphase b ⟨hb.1,hb.2.trans hβ2⟩ hbs
  have hcm := hphase c ⟨hb.1.trans (hb.2.trans hc.1),hc.2⟩ hcs
  set a := UnitaryProducts.spectralBottom A with ha
  have hab : a < β := (hmin.2 hbm).trans_lt hb.2
  have hal : α < a := (hopen _ hmin.1).1
  have htop : ∀ y ∈ spectrum ℝ A, y ∈ Ioo β (α + 2 * π) → y ≤ a+2*π-ϑ := by
    intro y hy hy'
    have hgy := (hgap a y ⟨hal,hab⟩ hy' (himg _ hmin.1) (himg _ hy)).trans (min_le_right _ _)
    linarith
  have hc' := htop c hcm hc
  refine ⟨by linarith [hc.1],fun x hx ↦ ⟨hmin.2 hx,?_⟩⟩
  rcases le_or_gt x β with h | h
  · linarith [hc.1]
  · have hx' := htop x hx ⟨h,(hopen x hx).2⟩
    linarith

/-- The band of a Hermitian logarithm with spectrum in one open turn `(α, α+2π)`. -/
private theorem turn_band [NeZero d] {A U : 𝕄} (hA : A.IsHermitian) {α β g : ℝ}
    (hU : spectrum ℂ U = (fun θ : ℝ ↦ Complex.exp (-I*(θ:ℂ))) '' spectrum ℝ A)
    (hopen : ∀ x ∈ spectrum ℝ A, x ∈ Ioo α (α + 2 * π)) (hβ2 : β < α+2 * π)
    (hβ : Complex.exp (-I*(β:ℂ)) ∉ spectrum ℂ U)
    (hgap : ∀ x y, x ∈ Ioo α β → y ∈ Ioo β (α + 2 * π) →
      Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U → Complex.exp (-I * (y:ℂ)) ∈ spectrum ℂ U →
      g ≤ min (y-x) (2*π-(y-x))) :
    α ∉ spectrum ℝ A ∧ β ∉ spectrum ℝ A ∧
    (∀ i j, hA.eigenvalues i ∈ Icc α β → hA.eigenvalues j ∉ Icc α β →
      g ≤ |hA.eigenvalues i-hA.eigenvalues j|) ∧
    (∀ i, hA.eigenvalues i ∈ Icc α β ↔
      ∃ θ ∈ Ioo α β, Complex.exp (-I*(θ:ℂ)) = Complex.exp (-I*(hA.eigenvalues i:ℂ))) := by
  have himg : ∀ x ∈ spectrum ℝ A, Complex.exp (-I * (x : ℂ)) ∈ spectrum ℂ U :=
    fun x hx ↦ hU ▸ ⟨x,hx,rfl⟩
  have hβs : β ∉ spectrum ℝ A := fun h ↦ hβ (himg β h)
  have hαs : α ∉ spectrum ℝ A := fun h ↦ lt_irrefl α (hopen α h).1
  have hin : ∀ x ∈ spectrum ℝ A, x ∈ Icc α β → x ∈ Ioo α β := fun x hx h ↦
    ⟨(hopen x hx).1,lt_of_le_of_ne h.2 (fun e ↦ hβs (e ▸ hx))⟩
  have hout : ∀ x ∈ spectrum ℝ A, x ∉ Icc α β → x ∈ Ioo β (α + 2 * π) := fun x hx h ↦
    ⟨lt_of_not_ge fun hle ↦ h ⟨(hopen x hx).1.le,hle⟩,(hopen x hx).2⟩
  have hmem := hA.eigenvalues_mem_spectrum_real
  refine ⟨hαs,hβs,fun i j hi hj ↦ ?_,fun i ↦ ⟨fun hi ↦ ⟨_,hin _ (hmem i) hi,rfl⟩,?_⟩⟩
  · have hi' := hin _ (hmem i) hi
    have hj' := hout _ (hmem j) hj
    have h := (hgap _ _ hi' hj' (himg _ (hmem i)) (himg _ (hmem j))).trans (min_le_left _ _)
    rw [abs_sub_comm,abs_of_pos (sub_pos.mpr (hi'.2.trans hj'.1))]
    exact h
  · rintro ⟨θ,hθ,he⟩
    rw [← phase_inj ⟨hθ.1,hθ.2.trans hβ2⟩ (hopen _ (hmem i)) he]
    exact ⟨hθ.1.le,hθ.2.le⟩

/-- The walk paragraph in §4.3: a band of a walk on moving arcs with spectral gap
at least `g ≥ ϑ` puts the spectrum in a closed arc of length `2π - ϑ`, whose complementary
open arc contains no eigenvalue. Every Hermitian logarithm with spectrum in
the complementary closed arc $[a, a + 2\pi - \vartheta]$ (in particular the $\Lambda$ of Lemma A.2
and the walk comparison) has the walk's band as its band in $[\alpha, \beta]$, with gap at least
`g`. -/
theorem walk_band_log [NeZero d] (W : ℝ → 𝕄) (α β g : ℝ → ℝ) (ϑ : ℝ)
    (hW : (walk W 1).1) (hWc : ContinuousOn W (Icc (0 : ℝ) 1))
    (hband : trackedCircularBand W α β g) (hϑ : 0 < ϑ)
    (hϑg : ∀ s ∈ Icc (0 : ℝ) 1, ϑ ≤ g s) :
    ∃ a : ℝ → ℝ, spectrumAvoidsOpenArc W ϑ a ∧
      ∀ (Λ : ℝ → 𝕄) (hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian),
        (∀ s (hs : s ∈ Icc (0 : ℝ) 1), UnitaryProducts.evol (Λ s) 1 = W s ∧
          ∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s+(2*π-ϑ))) →
        ∀ s (hs : s ∈ Icc (0 : ℝ) 1),
          α s ∉ spectrum ℝ (Λ s) ∧ β s ∉ spectrum ℝ (Λ s) ∧
          (∀ i j, (hΛ s hs).eigenvalues i ∈ Icc (α s) (β s) →
            (hΛ s hs).eigenvalues j ∉ Icc (α s) (β s) →
            g s ≤ |(hΛ s hs).eigenvalues i-(hΛ s hs).eigenvalues j|) ∧
          (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (α s) (β s) ↔
            ∃ θ ∈ Ioo (α s) (β s), Complex.exp (-I*(θ:ℂ)) =
              Complex.exp (-I*((hΛ s hs).eigenvalues i:ℂ))) := by
  obtain ⟨hα,-,-,hb⟩ := hband
  let S := Icc (0 : ℝ) 1
  let V : S → unitary 𝕄 := fun s ↦ ⟨W s,Matrix.mem_unitaryGroup_iff'.mpr (hW s s.2)⟩
  have hV : Continuous V := Continuous.subtype_mk hWc.restrict _
  obtain ⟨G,hGc,hG,he⟩ := UnitaryProducts.continuous_log_of_cut V (fun s : S ↦ α s) hV hα.restrict
    (fun s ↦ (hb s s.2).2.2.2.1)
  -- The paper's `a = l`: the least eigenvalue of the cut logarithm (junk `0` off [0, 1],
  -- never read).
  let a : ℝ → ℝ := fun s ↦ if hs : s ∈ S then UnitaryProducts.spectralBottom (G ⟨s,hs⟩) else 0
  have key : ∀ s (hs : s ∈ S), a s = UnitaryProducts.spectralBottom (G ⟨s,hs⟩) :=
    fun s hs ↦ dif_pos hs
  have hac : ContinuousOn a S := by
    rw [continuousOn_iff_continuous_restrict]
    have hr : S.restrict a = fun s : S ↦ UnitaryProducts.spectralBottom (G s) :=
      funext fun s ↦ dif_pos s.2
    rw [hr]
    exact UnitaryProducts.continuous_spectralBottom.comp hGc
  have hGW : ∀ s (hs : s ∈ S), UnitaryProducts.evol (G ⟨s,hs⟩) 1 = W s :=
    fun s hs ↦ (he ⟨s,hs⟩).1
  have hspec : ∀ s (hs : s ∈ S), spectrum ℂ (W s) =
      (fun θ : ℝ ↦ Complex.exp (-I*(θ:ℂ))) '' spectrum ℝ (G ⟨s,hs⟩) := fun s hs ↦ by
    rw [← hGW s hs,UnitaryProducts.spectrum_evol_image (hG _)]
  have hopen : ∀ s (hs : s ∈ S), ∀ x ∈ spectrum ℝ (G ⟨s,hs⟩), x ∈ Ioo (α s) (α s+2 * π) :=
    fun s hs ↦ spectrum_turn (he ⟨s,hs⟩).2
  have hbot : ∀ s (hs : s ∈ S), ϑ < 2*π ∧
      ∀ x ∈ spectrum ℝ (G ⟨s,hs⟩), x ∈ Icc (a s) (a s+(2*π-ϑ)) := by
    intro s hs
    obtain ⟨-,-,hβ2,-,-,hbandW,hcompW,hgapW⟩ := hb s hs
    rw [key s hs]
    exact turn_bottom (hG ⟨s,hs⟩) (hspec s hs) (hopen s hs) hβ2 hbandW hcompW hgapW (hϑg s hs)
  have hϑ2 : ϑ ≤ 2*π := (hbot 0 ⟨le_rfl,zero_le_one⟩).1.le
  refine ⟨a,(spectrumAvoidsOpenArc_iff_closedArc W ϑ a hW hϑ2).mpr ⟨hϑ,hac,fun s hs z hz ↦ ?_⟩,?_⟩
  · rw [hspec s hs] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    exact ⟨x,(hbot s hs).2 x hx,rfl⟩
  · intro Λ hΛ hlog s hs
    have hΛG : Λ s = G ⟨s,hs⟩ := by
      have hw0 : 0 ≤ 2*π-ϑ := by linarith
      have hwπ : (2*π-ϑ)/2 < π := by linarith
      have hGe : ∀ i, (hG ⟨s,hs⟩).eigenvalues i ∈ Icc (a s) (a s+(2*π-ϑ)) :=
        fun i ↦ (hbot s hs).2 _ ((hG _).eigenvalues_mem_spectrum_real i)
      have n1 := UnitaryProducts.norm_sub_smul_one_le_of_eigenvalues (hΛ s hs) hw0 (hlog s hs).2
      have n2 := UnitaryProducts.norm_sub_smul_one_le_of_eigenvalues (hG ⟨s,hs⟩) hw0 hGe
      apply UnitaryProducts.eq_of_evol_eq (α := -(a s+(2*π-ϑ)/2)) (r := (2*π-ϑ)/2) hwπ (hΛ s hs)
        (by simpa only [neg_neg] using n1) (hG _) (by simpa only [neg_neg] using n2)
      rw [(hlog s hs).1,hGW s hs]
    obtain ⟨-,-,hβ2,-,hβW,-,-,hgapW⟩ := hb s hs
    exact turn_band (hΛ s hs) (by rw [hΛG]; exact hspec s hs) (by rw [hΛG]; exact hopen s hs)
      hβ2 hβW hgapW

end UnitaryProducts.Paper
