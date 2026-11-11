/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.PrincipalLog
public import UnitaryProducts.Paper.SpectralWindow

/-! # Principal logarithms and periodic spectral gaps

Backing for the spectral translation paragraph of Section 4.3 and its
introduction counterpart. The principal-log formula uses continuous functional
calculus on the centered spectral window.
-/

@[expose] public section
open Real Complex Set Filter
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
noncomputable section
namespace UnitaryProducts.PaperProof
attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- A centered width bound puts the exponential on the fixed arc about `1`
and makes the Hermitian matrix `i` times its principal logarithm. -/
theorem centered_log_principal {H : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw : w < 2 * π) (hn : ‖H‖ ≤ w / 2) :
    H = I • cfc Complex.log (evol H 1) ∧
      ∀ z ∈ spectrum ℂ (evol H 1),
        ∃ θ ∈ Icc (-w / 2) (-w / 2 + w), z = Complex.exp (-I * (θ : ℂ)) := by
  have hspec (x : ℝ) (hx : x ∈ spectrum ℝ H) : |x| ≤ w / 2 := by
    exact (spectrum.norm_le_norm_of_mem hx).trans hn
  have hopen : ∀ x ∈ spectrum ℝ H, x ∈ Ioo (-π) (-π + 2 * π) := by
    intro x hx
    have h := abs_le.mp (hspec x hx)
    constructor <;> linarith [h.1, h.2]
  have hprincipal := (cut_log_eq_principal hH rfl hopen).2
  constructor
  · simpa using hprincipal
  · intro z hz
    rw [spectrum_evol_image hH] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have h := abs_le.mp (hspec x hx)
    exact ⟨x, ⟨by linarith [h.1], by linarith [h.2]⟩, rfl⟩

/-- Conversely, the logarithm in the centered prescribed window is the
principal logarithm and has norm at most half the width. -/
theorem centered_window_log_principal {H W : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw0 : 0 ≤ w) (hw : w < 2 * π) (he : evol H 1 = W)
    (hwin : ∀ i, hH.eigenvalues i ∈ Icc (-w / 2) (-w / 2 + w)) :
    H = I • cfc Complex.log W ∧ ‖H‖ ≤ w / 2 := by
  have hn := norm_sub_smul_one_le_of_eigenvalues hH hw0 hwin
  have hnorm : ‖H‖ ≤ w / 2 := by
    simpa only [neg_div, neg_add_cancel, Complex.ofReal_zero, zero_smul, sub_zero] using hn
  exact ⟨he ▸ (centered_log_principal hH hw hnorm).1, hnorm⟩

omit [NeZero d] in
/-- The inverse image of the exponential spectrum is exactly the real
spectrum repeated with period `2π`. -/
theorem periodic_phase_spectrum {H : 𝕄} (hH : H.IsHermitian) (θ : ℝ) :
    Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ (evol H 1) ↔
      ∃ x ∈ spectrum ℝ H, ∃ n : ℤ, θ = x + n * (2 * π) := by
  rw [spectrum_evol_image hH]
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    have hi := congrArg Complex.im hn
    norm_num [Complex.mul_re, Complex.mul_im] at hi
    exact ⟨x, hx, n, by linarith⟩
  · rintro ⟨x, hx, n, rfl⟩
    refine ⟨x, hx, Complex.exp_eq_exp_iff_exists_int.mpr ⟨n, ?_⟩⟩
    push_cast
    ring

/-- The width condition bounds the distance between the extreme eigenvalues. -/
theorem spectral_span_le {H : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hwidth : ∀ i j, |hH.eigenvalues i - hH.eigenvalues j| ≤ w) :
    (-spectralBottom (-H)) - spectralBottom H ≤ w := by
  obtain ⟨i, hi⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ (isGreatest_spectralTop hH).1
  obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ (isLeast_spectralBottom hH).1
  have h := (abs_le.mp (hwidth i j)).2
  simpa only [hi, hj] using h

/-- Inside one spectral span shorter than a full turn, no nonzero translate
of a spectral point lies in that span. -/
theorem phase_spectrum_in_span {H : 𝕄} (hH : H.IsHermitian) {w θ : ℝ}
    (hw : w < 2 * π)
    (hwidth : ∀ i j, |hH.eigenvalues i - hH.eigenvalues j| ≤ w)
    (hθ : θ ∈ Icc (spectralBottom H) ((-spectralBottom (-H)))) :
    Complex.exp (-I * (θ : ℂ)) ∈ spectrum ℂ (evol H 1) ↔ θ ∈ spectrum ℝ H := by
  rw [periodic_phase_spectrum hH]
  constructor
  · rintro ⟨x, hx, n, he⟩
    have hxlo := (isLeast_spectralBottom hH).2 hx
    have hxhi := (isGreatest_spectralTop hH).2 hx
    have hspan := spectral_span_le hH hwidth
    by_cases hn : n = 0
    · rw [he]
      simpa only [hn, Int.cast_zero, zero_mul, add_zero] using hx
    · rcases lt_or_gt_of_ne hn with hn | hn
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        have hp := mul_le_mul_of_nonneg_right hn' two_pi_pos.le
        exfalso
        linarith [hθ.1]
      · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hp := mul_le_mul_of_nonneg_right hn' two_pi_pos.le
        exfalso
        linarith [hθ.2]
  · intro h
    exact ⟨θ, h, 0, by simp⟩

/-- Between two real spectral points, the eigenphase-free open intervals
are exactly the spectrum-free intervals of the Hermitian logarithm. Thus
consecutive eigenvalues give the same internal gaps on the circle. -/
theorem internal_phase_gap {H : 𝕄} (hH : H.IsHermitian) {w x y : ℝ}
    (hw : w < 2 * π)
    (hwidth : ∀ i j, |hH.eigenvalues i - hH.eigenvalues j| ≤ w)
    (hx : x ∈ spectrum ℝ H) (hy : y ∈ spectrum ℝ H) :
    (∀ θ ∈ Ioo x y, Complex.exp (-I * (θ : ℂ)) ∉ spectrum ℂ (evol H 1)) ↔
      ∀ θ ∈ Ioo x y, θ ∉ spectrum ℝ H := by
  have hlocal (θ : ℝ) (hθ : θ ∈ Ioo x y) := phase_spectrum_in_span hH hw hwidth
    (show θ ∈ Icc (spectralBottom H) ((-spectralBottom (-H))) from
      ⟨((isLeast_spectralBottom hH).2 hx).trans hθ.1.le,
        hθ.2.le.trans ((isGreatest_spectralTop hH).2 hy)⟩)
  exact ⟨fun h θ hθ ↦ (hlocal θ hθ).not.mp (h θ hθ),
    fun h θ hθ ↦ (hlocal θ hθ).not.mpr (h θ hθ)⟩

/-- The remaining circular gap runs from the greatest eigenvalue to the
least eigenvalue in the next period; its length is at least `2π - w`. -/
theorem between_periods_phase_gap {H : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw : w < 2 * π)
    (hwidth : ∀ i j, |hH.eigenvalues i - hH.eigenvalues j| ≤ w) :
    Complex.exp (-I * ((-spectralBottom (-H) : ℝ) : ℂ)) ∈ spectrum ℂ (evol H 1) ∧
    Complex.exp (-I * ((spectralBottom H + 2 * π : ℝ) : ℂ)) ∈ spectrum ℂ (evol H 1) ∧
    (∀ θ ∈ Ioo ((-spectralBottom (-H))) (spectralBottom H + 2 * π),
      Complex.exp (-I * (θ : ℂ)) ∉ spectrum ℂ (evol H 1)) ∧
    0 < spectralBottom H + 2 * π - (-spectralBottom (-H)) ∧
    2 * π - w ≤ spectralBottom H + 2 * π - (-spectralBottom (-H)) := by
  have hspan := spectral_span_le hH hwidth
  refine ⟨(periodic_phase_spectrum hH _).mpr
      ⟨_, (isGreatest_spectralTop hH).1, 0, by simp⟩,
    (periodic_phase_spectrum hH _).mpr
      ⟨_, (isLeast_spectralBottom hH).1, 1, by simp⟩, ?_, by linarith, by linarith⟩
  intro θ hθ hmem
  obtain ⟨x, hx, n, he⟩ := (periodic_phase_spectrum hH θ).mp hmem
  have hxlo := (isLeast_spectralBottom hH).2 hx
  have hxhi := (isGreatest_spectralTop hH).2 hx
  by_cases hn : n ≤ 0
  · have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have hp := mul_le_mul_of_nonneg_right hn' two_pi_pos.le
    linarith [hθ.1]
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hp := mul_le_mul_of_nonneg_right hn' two_pi_pos.le
    linarith [hθ.2]

/-- Section 1: a real band gap survives exponentiation with lower bound
`min (2π - w) γ`. This pointwise form applies to each band/complement pair;
`spectrum_evol_image` identifies those pairs with the exponential eigenvalues. -/
theorem band_phase_gap_lower {x y w γ : ℝ}
    (hwidth : |x - y| ≤ w) (hgap : γ ≤ |x - y|) :
    min (2 * π - w) γ ≤ angularDistance x y := by
  obtain ⟨k, hk⟩ := (angularDistance_isLeast x y).1
  rw [← hk]
  by_cases hz : k = 0
  · simpa only [hz, Int.cast_zero, mul_zero, add_zero] using
      (min_le_right (2 * π - w) γ).trans hgap
  · have hb := abs_le.mp hwidth
    rcases lt_or_gt_of_ne hz with hn | hp
    · have hn' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hm := mul_le_mul_of_nonneg_left hn' two_pi_pos.le
      have hroute : 2 * π - w ≤ -(x - y + 2 * π * k) := by linarith [hb.2]
      exact (min_le_left _ _).trans (hroute.trans (neg_le_abs _))
    · have hp' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hm := mul_le_mul_of_nonneg_left hp' two_pi_pos.le
      have hroute : 2 * π - w ≤ x - y + 2 * π * k := by linarith [hb.1]
      exact (min_le_left _ _).trans (hroute.trans (le_abs_self _))

/-- The band/complement minimum of the pointwise angular-gap estimate in §1. -/
theorem finite_band_phase_gap_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (S : Finset ι) (hS : S.Nonempty) (hR : Sᶜ.Nonempty)
    {w γ : ℝ} (hwidth : ∀ i j, |θ i - θ j| ≤ w)
    (hgap : ∀ i ∈ S, ∀ j ∈ Sᶜ, γ ≤ |θ i - θ j|) :
    min (2 * π - w) γ ≤ S.inf' hS (fun i ↦ Sᶜ.inf' hR
      (fun j ↦ angularDistance (θ i) (θ j))) := by
  apply Finset.le_inf'
  intro i hi
  apply Finset.le_inf'
  intro j hj
  exact band_phase_gap_lower (hwidth i j) (hgap i hi j hj)

/-- Section 1.2: the image of a Hermitian band under exponentiation is a band
of the unitary matrix. The original real interval may extend beyond the spectral
span; cropping its endpoints inside one open turn preserves exactly the selected
eigenvalues. The resulting arc has nonempty selected and complementary spectra,
and neither endpoint is a unitary eigenvalue. -/
theorem hermitian_band_exponential_image {H : 𝕄} (hH : H.IsHermitian)
    {w a b : ℝ} (hw : w < 2 * π)
    (hwidth : ∀ i j, |hH.eigenvalues i - hH.eigenvalues j| ≤ w)
    (hin : (spectrum ℝ H ∩ Ioo a b).Nonempty)
    (hout : (spectrum ℝ H \ Ioo a b).Nonempty)
    (ha : a ∉ spectrum ℝ H) (hb : b ∉ spectrum ℝ H) :
    ∃ α β : ℝ, spectralWindowBand true (evol H 1) α β ∧
      spectrum ℂ (evol H 1) ∩ spectralWindowSet true α β =
        (fun x : ℝ ↦ Complex.exp (-I * (x : ℂ))) '' (spectrum ℝ H ∩ Ioo a b) := by
  let L := spectralBottom H
  let q := (2 * π - w) / 4
  let c := L - q
  let α := max a (L - q / 2)
  let β := min b (L + w + q / 2)
  have hq : 0 < q := by dsimp [q]; linarith
  have hbounds (x : ℝ) (hx : x ∈ spectrum ℝ H) : L ≤ x ∧ x ≤ L + w := by
    have hlo := (isLeast_spectralBottom hH).2 hx
    have hhi := (UnitaryProducts.Prose.isGreatest_spectralTop hH).2 hx
    have hspan := spectral_span_le hH hwidth
    exact ⟨hlo, by dsimp [L]; linarith⟩
  have hturn (x : ℝ) (hx : x ∈ spectrum ℝ H) : x ∈ Ioo c (c + 2 * π) := by
    have hx' := hbounds x hx
    dsimp [c, q]
    constructor <;> linarith [hx'.1, hx'.2]
  obtain ⟨x₀, hx₀, hx₀ab⟩ := hin
  have hαx : α < x₀ := by
    apply max_lt hx₀ab.1
    linarith [(hbounds x₀ hx₀).1]
  have hxβ : x₀ < β := by
    apply lt_min hx₀ab.2
    linarith [(hbounds x₀ hx₀).2]
  have hαturn : α ∈ Ioo c (c + 2 * π) := by
    refine ⟨?_, hαx.trans (hturn x₀ hx₀).2⟩
    have hlo : L - q / 2 ≤ α := le_max_right _ _
    dsimp [c]
    linarith
  have hβturn : β ∈ Ioo c (c + 2 * π) := by
    refine ⟨(hturn x₀ hx₀).1.trans hxβ, ?_⟩
    have hhi : β ≤ L + w + q / 2 := min_le_right _ _
    dsimp [c, q] at *
    linarith
  have hcrop (x : ℝ) (hx : x ∈ spectrum ℝ H) :
      x ∈ Ioo α β ↔ x ∈ Ioo a b := by
    constructor
    · intro h
      exact ⟨(le_max_left _ _).trans_lt h.1, h.2.trans_le (min_le_left _ _)⟩
    · intro h
      have hbd := hbounds x hx
      exact ⟨max_lt h.1 (by linarith [hbd.1]),
        lt_min h.2 (by linarith [hbd.2])⟩
  have hαnot : α ∉ spectrum ℝ H := by
    intro hs
    by_cases h : a ≤ L - q / 2
    · have he : α = L - q / 2 := max_eq_right h
      have hbd := (hbounds α hs).1
      rw [he] at hbd
      linarith
    · have he : α = a := max_eq_left (le_of_not_ge h)
      exact ha (he ▸ hs)
  have hβnot : β ∉ spectrum ℝ H := by
    intro hs
    by_cases h : b ≤ L + w + q / 2
    · have he : β = b := min_eq_left h
      exact hb (he ▸ hs)
    · have he : β = L + w + q / 2 := min_eq_right (le_of_not_ge h)
      have hbd := (hbounds β hs).2
      rw [he] at hbd
      linarith
  have hphase (x : ℝ) (hx : x ∈ spectrum ℝ H) :
      Complex.exp (-I * (x : ℂ)) ∈ spectralWindowSet true α β ↔ x ∈ Ioo a b := by
    constructor
    · rintro ⟨y, hy, he⟩
      change Complex.exp (-I * (y : ℂ)) = Complex.exp (-I * (x : ℂ)) at he
      have hyturn : y ∈ Ioo c (c + 2 * π) :=
        ⟨hαturn.1.trans hy.1, hy.2.trans hβturn.2⟩
      have hyx := phase_inj hyturn (hturn x hx) he
      exact (hcrop x hx).mp (hyx ▸ hy)
    · intro hi
      exact ⟨x, (hcrop x hx).mpr hi, rfl⟩
  have hendpoint (t : ℝ) (ht : t ∈ Ioo c (c + 2 * π))
      (htnot : t ∉ spectrum ℝ H) :
      Complex.exp (-I * (t : ℂ)) ∉ spectrum ℂ (evol H 1) := by
    rw [spectrum_evol_image hH]
    rintro ⟨x, hx, he⟩
    have hxt := phase_inj (hturn x hx) ht he
    exact htnot (hxt ▸ hx)
  refine ⟨α, β, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hendpoint α hαturn hαnot, hendpoint β hβturn hβnot⟩
    · exact star_evol_mul_self hH 1
    · refine ⟨Complex.exp (-I * (x₀ : ℂ)), ?_, (hphase x₀ hx₀).mpr hx₀ab⟩
      rw [spectrum_evol_image hH]
      exact ⟨x₀, hx₀, rfl⟩
    · obtain ⟨x, hx, hxnot⟩ := hout
      refine ⟨Complex.exp (-I * (x : ℂ)), ?_, ?_⟩
      · rw [spectrum_evol_image hH]
        exact ⟨x, hx, rfl⟩
      · intro hi
        exact hxnot ((hphase x hx).mp hi)
  · ext z
    constructor
    · rintro ⟨hz, hzband⟩
      rw [spectrum_evol_image hH] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, ⟨hx, (hphase x hx).mp hzband⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxab⟩, rfl⟩
      refine ⟨?_, (hphase x hx).mpr hxab⟩
      rw [spectrum_evol_image hH]
      exact ⟨x, hx, rfl⟩

end UnitaryProducts.PaperProof
