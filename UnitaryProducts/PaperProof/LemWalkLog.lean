/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary

public import UnitaryProducts.Prose.WalkLogLocal
public import UnitaryProducts.Prose.FinalSteps
public import UnitaryProducts.PaperProof.SpectralProofSteps
public import UnitaryProducts.PaperProof.ResolventQuadratures

/-!
# The walk logarithm lemma and its principal-log derivative formula

## Declarations

- `lem_walk_log`
- `walk_log_interior_bounds`
- `walk_log_pointwise`
- `bounds_on_Icc`
- `centered_bounds`
- `centered_integral`
- `centered_log_derivatives`
- `centered_resolvent_le`
- `chord_quadratures`
- `integral_derivative`
-/

@[expose] public section

open Real Complex Set Filter MeasureTheory Matrix
open scoped Topology Matrix.Norms.L2Operator
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Prose
open UnitaryProducts.Corrector

noncomputable section
namespace UnitaryProducts.PaperProof

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The spectral projector at `z`, defined by the characteristic function of its
singleton on the finite spectrum. -/
def finiteSpectralProjector (U : 𝕄) (z : ℂ) : 𝕄 :=
  cfc (fun ζ : ℂ ↦ if ζ = z then 1 else 0) U

omit [NeZero d] in
/-- The finite-dimensional spectral theorem written as the sum of its named
spectral projectors. Any scalar function is continuous on the finite spectrum. -/
theorem finite_spectral_expansion (U : 𝕄) (f : ℂ → ℂ) :
    cfc f U = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
      f z • finiteSpectralProjector U z := by
  classical
  let S := (Matrix.finite_spectrum U).toFinset
  have hsum : cfc f U = cfc (fun ζ ↦ ∑ z ∈ S,
      f z • (if ζ = z then (1 : ℂ) else 0)) U := by
    apply cfc_congr
    intro ζ hζ
    have hmem : ζ ∈ S := (Matrix.finite_spectrum U).mem_toFinset.mpr hζ
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ζ]
    · simp
    · intro z _ hz
      simp [Ne.symm hz]
    · exact fun hz ↦ (hz hmem).elim
  rw [hsum]
  have hmap := cfc_sum (fun z ζ : ℂ ↦ f z • (if ζ = z then (1 : ℂ) else 0))
    U S (fun _ _ ↦ (Matrix.finite_spectrum U).continuousOn _)
  simp only [Finset.sum_fn] at hmap
  rw [hmap]
  apply Finset.sum_congr rfl
  intro z _
  exact cfc_smul (f z) _ U ((Matrix.finite_spectrum U).continuousOn _)

omit [NeZero d] in
/-- The characteristic functions give self-adjoint idempotent projectors. -/
theorem finiteSpectralProjector_properties (U : 𝕄) (z : ℂ) :
    (finiteSpectralProjector U z).IsHermitian ∧
    finiteSpectralProjector U z * finiteSpectralProjector U z =
      finiteSpectralProjector U z := by
  classical
  let e : ℂ → ℂ := fun ζ ↦ if ζ = z then 1 else 0
  have hc := (Matrix.finite_spectrum U).continuousOn e
  constructor
  · change star (cfc e U) = cfc e U
    rw [← cfc_star]
    apply cfc_congr
    intro ζ _
    simp [e]
  · change cfc e U * cfc e U = cfc e U
    rw [← cfc_mul e e U hc hc]
    apply cfc_congr
    intro ζ _
    by_cases h : ζ = z <;> simp [e, h]

omit [NeZero d] in
/-- Lemma A.2: a unitary matrix is the sum of its eigenvalues times the
spectral projectors. Replacing each eigenvalue by its chosen phase constructs its logarithm. -/
theorem unitary_spectral_decomposition (U : 𝕄) (hu : star U * U = 1) :
    U = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
      z • finiteSpectralProjector U z := by
  letI : IsStarNormal U :=
    ⟨by change star U * U = U * star U; rw [hu, mul_eq_one_comm.mp hu]⟩
  simpa only [cfc_id, id_eq] using finite_spectral_expansion U id

omit [NeZero d] in
/-- Pointwise spectral construction in Lemma A.2. Choose each phase in the
prescribed interval, then sum those phases times the spectral projectors. The
functional calculus proves Hermiticity, the spectral window, and exponentiation. -/
theorem walk_log_pointwise (a w : ℝ)
    (U : 𝕄) (hu : star U * U = 1)
    (harc : ∀ z ∈ spectrum ℂ U,
      ∃ θ ∈ Icc a (a + w), z = Complex.exp (-I * (θ : ℂ))) :
    ∃ H : 𝕄, ∃ hH : H.IsHermitian,
      (∀ i, hH.eigenvalues i ∈ Icc a (a + w)) ∧ evol H 1 = U := by
  classical
  letI : IsStarNormal U :=
    ⟨by change star U * U = U * star U; rw [hu, mul_eq_one_comm.mp hu]⟩
  let θ : ℂ → ℝ := fun z ↦ if hz : z ∈ spectrum ℂ U then (harc z hz).choose else a
  have hθ (z : ℂ) (hz : z ∈ spectrum ℂ U) :
      θ z ∈ Icc a (a + w) ∧ z = Complex.exp (-I * (θ z : ℂ)) := by
    simpa only [θ, dif_pos hz] using (harc z hz).choose_spec
  let f : ℂ → ℂ := fun z ↦ (θ z : ℂ)
  let H := ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
    f z • finiteSpectralProjector U z
  have hHcfc : H = cfc f U := (finite_spectral_expansion U f).symm
  have hc := (Matrix.finite_spectrum U).continuousOn f
  have hH : H.IsHermitian := by
    change star H = H
    simp only [H, star_sum, star_smul]
    apply Finset.sum_congr rfl
    intro z _
    rw [show star (finiteSpectralProjector U z) = finiteSpectralProjector U z from
      (finiteSpectralProjector_properties U z).1]
    simp only [f, Complex.star_def, Complex.conj_ofReal]
  refine ⟨H, hH, ?_, ?_⟩
  · intro i
    have hspec : (hH.eigenvalues i : ℂ) ∈ spectrum ℂ H :=
      (spectrum.algebraMap_mem_iff ℂ).mpr (hH.eigenvalues_mem_spectrum_real i)
    have hmap : spectrum ℂ H = f '' spectrum ℂ U := by
      rw [hHcfc, cfc_map_spectrum f U (inferInstance : IsStarNormal U) hc]
    rw [hmap] at hspec
    obtain ⟨z, hz, heq⟩ := hspec
    have he : θ z = hH.eigenvalues i := Complex.ofReal_injective heq
    rw [← he]
    exact (hθ z hz).1
  · rw [hHcfc, evol, one_smul, ← cfc_smul (-I) f U hc,
      ← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I • f z) U
        (inferInstance : IsStarNormal U) Complex.continuous_exp.continuousOn (hc.const_smul (-I))]
    calc
      _ = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
          Complex.exp (-I * f z) • finiteSpectralProjector U z :=
        finite_spectral_expansion U (fun z ↦ Complex.exp (-I * f z))
      _ = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
          z • finiteSpectralProjector U z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← (hθ z ((Matrix.finite_spectrum U).mem_toFinset.mp hz)).2]
      _ = U := (unitary_spectral_decomposition U hu).symm

/-- Lemma A.2: the principal logarithm integral evaluates to `-iφ` on every
phase in the principal turn. This is the scalar verification used by the matrix
functional calculus below. -/
theorem walk_log_integral_eigenvalue {φ : ℝ} (hφ : |φ| < π) :
    (∫ u : ℝ in (0 : ℝ)..1,
      (Complex.exp (-I * (φ : ℂ)) - 1) /
        (1 + (u : ℂ) * (Complex.exp (-I * (φ : ℂ)) - 1))) = -I * (φ : ℂ) := by
  rw [integral_log_chord (exp_neg_I_mem_slitPlane (abs_lt.mp hφ))]
  simpa only [Complex.ofReal_neg, mul_neg, neg_mul] using
    log_exp_I_mul (θ := -φ) (by simpa using hφ)

/-- The centered integral is the selected branch, using the principal scalar
identity `Log(exp(iθ)) = iθ` on `|θ| < π`. -/
theorem centered_integral {H : 𝕄} (hH : H.IsHermitian) (hn : ‖H‖ < π)
    (hcut : spectrum ℂ (evol H 1) ⊆ Complex.slitPlane) :
    walkLogIntegral (evol H 1) = (-I) • H := by
  have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hH
  letI : IsStarNormal H := hsa.isStarNormal
  letI : IsStarNormal (evol H 1) := ⟨by
    change star (evol H 1) * evol H 1 = evol H 1 * star (evol H 1)
    rw [star_evol_mul_self hH 1, mul_eq_one_comm.mpr (star_evol_mul_self hH 1)]⟩
  rw [walkLogIntegral_eq_cfc _ hcut,
    evol_one_eq_cfc_exp H hH]
  have hc : ContinuousOn Complex.log
      ((fun z : ℂ ↦ Complex.exp (-I * z)) '' spectrum ℂ H) := by
    apply (show ContinuousOn Complex.log Complex.slitPlane from
      fun z hz ↦ (continuousAt_clog hz).continuousWithinAt).mono
    rw [← cfc_map_spectrum (fun z : ℂ ↦ Complex.exp (-I * z)) H
      hsa.isStarNormal (by fun_prop), ← evol_one_eq_cfc_exp H hH]
    exact spectrum_evol_one_subset_slitPlane hH hn
  rw [← cfc_comp (R := ℂ) Complex.log (fun z : ℂ ↦ Complex.exp (-I * z)) H
    hsa.isStarNormal hc (by fun_prop)]
  have he : cfc (Complex.log ∘ fun z : ℂ ↦ Complex.exp (-I * z)) H =
      cfc (fun z : ℂ ↦ -I * z) H := by
    refine cfc_congr fun z hz ↦ ?_
    have hzreal : z = (z.re : ℂ) := IsSelfAdjoint.mem_spectrum_eq_re hsa hz
    have hb := (spectrum.norm_le_norm_of_mem hz).trans_lt hn
    rw [hzreal, Complex.norm_real, Real.norm_eq_abs] at hb
    change Complex.log (Complex.exp (-I * z)) = -I * z
    rw [hzreal]
    rw [← integral_log_chord (exp_neg_I_mem_slitPlane (abs_lt.mp hb))]
    exact walk_log_integral_eigenvalue hb
  rw [he, cfc_const_mul_id (-I) H]

/-- Lemma A.2 after removal of the constant phase: the centered formula
`H = i ∫ (W - 1) S_u` is verified on each eigenvalue in the principal turn.
The shifted theorem below applies this identity to `H - μ` and `exp(iμ) W`. -/
theorem walk_log_centered_integral {H W : 𝕄}
    (hH : H.IsHermitian) (hn : ‖H‖ < π) (he : evol H 1 = W)
    (hcut : spectrum ℂ (evol H 1) ⊆ Complex.slitPlane) :
    H = I • (∫ u : ℝ in (0 : ℝ)..1, (W - 1) * walkLogResolvent W u) := by
  have hi := centered_integral hH hn hcut
  rw [he] at hi
  change H = I • walkLogIntegral W
  rw [hi, smul_smul, show I * (-I) = (1 : ℂ) by simp, one_smul]

/-- Lemma A.2: the shifted integral formula for `H`, verified by the
principal-turn eigenvalue calculation in `centered_integral`. -/
theorem walk_log_integral {H W : 𝕄} (μ : ℝ)
    (hH : (H - (μ : ℂ) • 1).IsHermitian)
    (hn : ‖H - (μ : ℂ) • 1‖ < π)
    (he : evol H 1 = W)
    (hcut : spectrum ℂ (evol (H - (μ : ℂ) • 1) 1) ⊆ Complex.slitPlane) :
    H = (μ : ℂ) • 1 + I •
      (∫ u : ℝ in (0 : ℝ)..1,
        (Complex.exp (I * (μ : ℂ)) • W - 1) *
          walkLogResolvent (Complex.exp (I * (μ : ℂ)) • W) u) := by
  have hphase : evol (H - (μ : ℂ) • 1) 1 =
      Complex.exp (I * (μ : ℂ)) • W := by
    rw [evol_sub_scalar_one, he]
  have hi := walk_log_centered_integral hH hn hphase hcut
  rw [← hi]
  abel

/-- The paper's quadratures use `v=2u-1`, then the arctangent primitive,
odd cancellation, and the inverse-cube primitive, as in the displayed proof. -/
theorem chord_quadratures {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    (∫ u : ℝ in (0 : ℝ)..1,
      ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 2) =
        walkLogSlope w ∧
    (∫ u : ℝ in (0 : ℝ)..1, (2 * u) *
      ((Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹) ^ 3) =
        (Real.cos (w / 4))⁻¹ ^ 2 :=
  resolvent_chord_quadratures hw0 hw


omit [NeZero d] in
/-- The first differentiated integral, with the inverse derivative and product
rule derived here; the paper cites Dieci--Morini--Papini for this formula. -/
theorem integral_derivative {V D : ℝ → 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b) (hV : ContinuousOn V (Icc a b))
    (hD : ContinuousOn D (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (D x) x)
    (hu : ∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, IsUnit (1 + t • (V x - 1))) :
    HasDerivAt (fun x ↦ walkLogIntegral (V x))
      (∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * D s * walkLogResolvent (V s) t) s := by
  have hZ := continuousOn_walkLogResolvent hV hu
  have hv : ContinuousOn (fun p : ℝ × ℝ ↦ V p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hV.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hd' : ContinuousOn (fun p : ℝ × ℝ ↦ D p.1) (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hD.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  apply hasDerivAt_integral_compact_rectangle
    (F := fun x t ↦ (V x - 1) * walkLogResolvent (V x) t)
    (F' := fun x t ↦ walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)
    hs ((hv.sub continuousOn_const).mul hZ)
    ((hZ.mul hd').mul hZ)
  intro x hx t ht
  have hden := hasDerivAt_log_denominator (u := t) (hd x hx)
  have hinv := hasDerivWithinAt_ringInverse_path (S := Set.univ)
    hden.hasDerivWithinAt (hu x ⟨hx.1.le, hx.2.le⟩ t ht)
  have hres : HasDerivAt (fun y ↦ walkLogResolvent (V y) t)
      (-t • (walkLogResolvent (V x) t * D x * walkLogResolvent (V x) t)) x := by
    simpa only [walkLogResolvent, mul_smul_comm, smul_mul_assoc, neg_smul] using
      hinv.hasDerivAt (by simp)
  have hprod := ((hd x hx).sub_const 1).mul hres
  simpa only [log_product_rule_eq_sandwich (V x) (D x) t
    (hu x ⟨hx.1.le, hx.2.le⟩ t ht)] using hprod

/-- The resolvent bound `‖Z_u‖ ≤ 1/r_u` of the proof of Lemma A.2, at a centered point
`e^{-iH}` with `‖H‖ ≤ w/2`: normality gives the spectral maximum, and on the phase interval
the squared chord decreases with the absolute angle, as in the display. -/
theorem centered_resolvent_le {H : 𝕄} (hH : H.IsHermitian) {w : ℝ} (hw : w < 2 * π)
    (hHs : ‖H‖ ≤ w / 2) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖walkLogResolvent (evol H 1) u‖ ≤
      (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ := by
  have hw0 : 0 ≤ w := by linarith [(norm_nonneg _).trans hHs]
  have hc0 : -1 < Real.cos (w / 2) := by
    simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith : 0 ≤ w / 2) le_rfl (by linarith : w / 2 < π)
  letI : IsStarNormal (evol H 1) := ⟨by
    change star (evol H 1) * evol H 1 = evol H 1 * star (evol H 1)
    rw [star_evol_mul_self hH 1, mul_eq_one_comm.mpr (star_evol_mul_self hH 1)]⟩
  have hcut : spectrum ℂ (evol H 1) ⊆ Complex.slitPlane :=
    spectrum_evol_one_subset_slitPlane hH (by linarith)
  -- Normality gives the spectral maximum. On the phase interval, the
  -- squared chord decreases with the absolute angle, as in the display.
  have hmax : IsGreatest
      ((fun φ : ℝ ↦ ‖(1 + u • (Complex.exp ((φ : ℂ) * I) - 1))⁻¹‖) ''
        Icc (-w / 2) (w / 2))
      (1 / ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖) := by
    refine ⟨(isGreatest_inv_chord_phase_radius hw0 hw hu).1, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hφabs : |φ| ≤ w / 2 := abs_le.mpr ⟨by linarith [hφ.1], hφ.2⟩
    have hnegative : |(-φ)| ≤ w / 2 := by simpa only [abs_neg] using hφabs
    have hm := chord_radius_lower hw hnegative hu
    rw [← chord_norm_sq (-φ) u] at hm
    have heφ : -I * ((-φ : ℝ) : ℂ) = (φ : ℂ) * I := by push_cast; ring
    rw [heφ] at hm
    have hew : ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖ ^ 2 =
        radius w (2 * u - 1) := by
      rw [norm_chord_endpoint_eq_sqrt, radius_substitution,
        Real.sq_sqrt (radius_pos hw0 hw _).le]
    have hnorm : ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖ ≤
        ‖1 + u • (Complex.exp ((φ : ℂ) * I) - 1)‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [hew]
      exact hm
    have hpos : 0 < ‖1 + u • (Complex.exp (((w / 2 : ℝ) : ℂ) * I) - 1)‖ := by
      rw [norm_chord_endpoint_eq_sqrt]
      exact Real.sqrt_pos.mpr (walkLogDenom_pos (t := u) hc0 (Real.cos_le_one _))
    simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hpos hnorm
  obtain ⟨z, hz, hez⟩ := (isGreatest_norm_walkLogResolvent (evol H 1) hcut hu).1
  rw [← hez]
  rw [spectrum_evol_image hH] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  have hθnorm : |θ| ≤ w / 2 := by
    simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hθ).trans hHs
  have hp : Complex.exp (-I * (θ : ℂ)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    congr 1
    push_cast
    ring
  dsimp only at ⊢
  rw [hp]
  have hb := hmax.2 ⟨-θ, by constructor <;> linarith [(abs_le.mp hθnorm).1,
    (abs_le.mp hθnorm).2], rfl⟩
  simpa only [norm_chord_endpoint_eq_sqrt, one_div] using hb

/-- The second and third lines of the paper's display (A.3): at a point of a centered
principal branch, `Λ' = i ∫₀¹ B_u Ũ' B_u du` and
`Λ'' = i ∫₀¹ (B_u Ũ'' B_u - 2u B_u Ũ' B_u Ũ' B_u) du`, obtained by differentiating the
first line under the integral (`integral_derivative`, `walkLogHessian_identity`). -/
theorem centered_log_derivatives {H Hd V Vd Vdd : ℝ → 𝕄} {Hdd : 𝕄} {a b s : ℝ}
    (hs : s ∈ Ioo a b)
    (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
    (hwindow : ∀ x ∈ Icc a b, ‖H x‖ < π)
    (he : ∀ x ∈ Icc a b, evol (H x) 1 = V x)
    (hHd : ∀ x ∈ Ioo a b, HasDerivAt H (Hd x) x)
    (hHdd : HasDerivAt Hd Hdd s)
    (hV : ContinuousOn V (Icc a b))
    (hVd : ContinuousOn Vd (Icc a b))
    (hVdd : ContinuousOn Vdd (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (Vd x) x)
    (hdd : ∀ x ∈ Ioo a b, HasDerivAt Vd (Vdd x) x) :
    Hd s = I • ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * Vd s * walkLogResolvent (V s) t ∧
      Hdd = I • ∫ t : ℝ in (0 : ℝ)..1,
        walkLogResolvent (V s) t * Vdd s * walkLogResolvent (V s) t -
          (2 * t) • (walkLogResolvent (V s) t * Vd s * walkLogResolvent (V s) t *
            Vd s * walkLogResolvent (V s) t) := by
  have hnormal (x : ℝ) (hx : x ∈ Icc a b) : IsStarNormal (V x) := by
    rw [← he x hx]
    refine ⟨?_⟩
    change star (evol (H x) 1) * evol (H x) 1 = evol (H x) 1 * star (evol (H x) 1)
    rw [star_evol_mul_self (hH x hx) 1,
      mul_eq_one_comm.mpr (star_evol_mul_self (hH x hx) 1)]
  have hcut (x : ℝ) (hx : x ∈ Icc a b) : spectrum ℂ (V x) ⊆ Complex.slitPlane := by
    rw [← he x hx]
    exact spectrum_evol_one_subset_slitPlane (hH x hx) (hwindow x hx)
  have hu : ∀ x ∈ Icc a b, ∀ u ∈ Icc (0 : ℝ) 1, IsUnit (1 + u • (V x - 1)) := by
    intro x hx u hu
    letI := hnormal x hx
    rw [← cfc_unit_chord (V x) u]
    apply isUnit_cfc (p := IsStarNormal) (fun z : ℂ ↦ 1 + u • (z - 1))
      (V x) (by fun_prop) inferInstance
    exact fun z hz ↦ Complex.slitPlane_ne_zero (chord_mem_slitPlane (hcut x hx hz) hu)
  -- The first line of (A.3) on the window, then its two differentiated integrals.
  have hi (x : ℝ) (hx : x ∈ Icc a b) : walkLogIntegral (V x) = (-I) • H x := by
    rw [← he x hx]
    exact centered_integral (hH x hx) (hwindow x hx)
      (spectrum_evol_one_subset_slitPlane (hH x hx) (hwindow x hx))
  have hder := integral_derivative hs hV hVd hd hu
  have heq : (fun x ↦ (-I) • H x) =ᶠ[𝓝 s] (fun x ↦ walkLogIntegral (V x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx using (hi x ⟨hx.1.le, hx.2.le⟩).symm
  have hfirst := (hder.congr_of_eventuallyEq heq).unique ((hHd s hs).const_smul (-I))
  have hsecond := walkLogHessian_identity hs hH hwindow he hHd hHdd hV hVd hVdd hd hdd
  have hI (M : 𝕄) : I • ((-I) • M) = M := by
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  constructor
  · rw [← hI (Hd s), ← hfirst]
  · rw [← hI Hdd, hsecond]

/-- Both derivative estimates at a point of a centered principal branch.
The first uses the product-rule norm chain; the second uses the Hessian identity. -/
private theorem centered_bounds {H Hd V Vd Vdd : ℝ → 𝕄}
   {Hdd : 𝕄}
    {a b s w : ℝ}
   (hs : s ∈ Ioo a b)
   (hw : w < 2 * π)
   (hHs : ‖H s‖ ≤ w / 2)
    (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
   (hwindow : ∀ x ∈ Icc a b, ‖H x‖ < π)
    (he : ∀ x ∈ Icc a b, evol (H x) 1 = V x)
   (hHd : ∀ x ∈ Ioo a b, HasDerivAt H (Hd x) x)
    (hHdd : HasDerivAt Hd Hdd s)
   (hV : ContinuousOn V (Icc a b))
    (hVd : ContinuousOn Vd (Icc a b))
   (hVdd : ContinuousOn Vdd (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt V (Vd x) x)
   (hdd : ∀ x ∈ Ioo a b, HasDerivAt Vd (Vdd x) x) :
    ‖Hd s‖ ≤ walkLogSlope w * ‖Vd s‖ ∧
      ‖Hdd‖ ≤ walkLogSlope w * ‖Vdd s‖ + (Real.cos (w / 4))⁻¹ ^ 2 * ‖Vd s‖ ^ 2 := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := by linarith [(norm_nonneg _).trans hHs]
  have hs' : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hc0 : -1 < Real.cos (w / 2) := by
    simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith : 0 ≤ w / 2) le_rfl (by linarith : w / 2 < π)
  have hnormal (x : ℝ) (hx : x ∈ Icc a b) : IsStarNormal (V x) := by
    rw [← he x hx]
    refine ⟨?_⟩
    change star (evol (H x) 1) * evol (H x) 1 = evol (H x) 1 * star (evol (H x) 1)
    rw [star_evol_mul_self (hH x hx) 1,
      mul_eq_one_comm.mpr (star_evol_mul_self (hH x hx) 1)]
  letI := hnormal s hs'
  have hZ (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ‖walkLogResolvent (V s) u‖ ≤
      (Real.sqrt (1 - 2 * u * (1 - u) * (1 - Real.cos (w / 2))))⁻¹ := by
    rw [← he s hs']
    exact centered_resolvent_le (hH s hs') hw hHs hu
  -- The two differentiated integrals of (A.3) use the same resolvent.
  obtain ⟨hfirst, hsecond⟩ :=
    centered_log_derivatives hs hH hwindow he hHd hHdd hV hVd hVdd hd hdd
  -- Apply the common chord bound to each integral, then the exact quadratures.
  have hfirstBound := norm_sandwich_integral_le (walkLogResolvent (V s)) (Vd s)
    hw0 hw hZ
  rw [(chord_quadratures hw0 hw).1, mul_comm ‖Vd s‖] at hfirstBound
  have hsecondBound := norm_walkLogHessian_integral_le (V s) (Vd s) (Vdd s)
    hc0 (Real.cos_le_one _) hZ
  rw [(chord_quadratures hw0 hw).1, (chord_quadratures hw0 hw).2] at hsecondBound
  simp only [hfirst, hsecond, norm_smul, Complex.norm_I, one_mul]
  exact ⟨hfirstBound, hsecondBound⟩

/-- Freeze the scalar center, localize the principal branch, and undo the phase. -/
theorem walk_log_interior_bounds
    {H Hd Hdd W Wd Wdd : ℝ → 𝕄}
   {w s c : ℝ}
   (hw : w < 2 * π)
   (hs : s ∈ Ioo (0 : ℝ) 1)
    (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
   (hc : ContinuousOn H (Icc (0 : ℝ) 1))
    (hcenter : ‖H s - (c : ℂ) • 1‖ ≤ w / 2)
   (he : ∀ x ∈ Icc (0 : ℝ) 1, evol (H x) 1 = W x)
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt H (Hd x) x)
   (hdd : HasDerivAt Hd (Hdd s) s)
    (hW : ContinuousOn W (Icc (0 : ℝ) 1))
   (hWd : ContinuousOn Wd (Icc (0 : ℝ) 1))
    (hWdd : ContinuousOn Wdd (Icc (0 : ℝ) 1))
   (hdW : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt W (Wd x) x)
    (hddW : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Wd (Wdd x) x) :
    ‖Hd s‖ ≤ walkLogSlope w * ‖Wd s‖ ∧
      ‖Hdd s‖ ≤ walkLogSlope w * ‖Wdd s‖ + (Real.cos (w/4))⁻¹^2*‖Wd s‖^2 := by
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
    exact fun x hx ↦ (hH x (hsub hx)).sub (by
      change star ((c:ℂ) • (1:𝕄))=(c:ℂ) • (1:𝕄)
      simp only [star_smul,star_one,Complex.star_def,Complex.conj_ofReal])
  have heG : ∀ x ∈ Icc a b, evol (G x) 1=z • W x := fun x hx ↦ by
    rw [evol_sub_scalar_one,he x (hsub hx)]
  have hb := centered_bounds (H:=G) (Hd:=Hd) (V:=fun x ↦ z • W x)
    (Vd:=fun x ↦ z • Wd x) (Vdd:=fun x ↦ z • Wdd x)
    hsab hw hcenter hG (fun x hx ↦ (hab hx).2) heG
    (fun x hx ↦ (hd x (hab ⟨hx.1.le,hx.2.le⟩).1).sub_const _) hdd
    ((hW.mono hsub).const_smul z) ((hWd.mono hsub).const_smul z)
    ((hWdd.mono hsub).const_smul z)
    (fun x hx ↦ (hdW x (hab ⟨hx.1.le,hx.2.le⟩).1).const_smul z)
    (fun x hx ↦ (hddW x (hab ⟨hx.1.le,hx.2.le⟩).1).const_smul z)
  simpa only [hnorm] using hb

/-- Extend both interior inequalities to the endpoints by continuity of the derivatives. -/
private theorem bounds_on_Icc
    {H W : ℝ → 𝕄}
   {w : ℝ}
   (hw : w < 2 * π)
   (hH : ∀ x ∈ Icc (0 : ℝ) 1, (H x).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
   (hW : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1))
    (hcenter : ∀ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, ‖H s - (c : ℂ) • 1‖ ≤ w / 2)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, evol (H x) 1 = W x) :
    ∀ s ∈ Icc (0:ℝ) 1,
      ‖derivWithin H (Icc (0:ℝ) 1) s‖ ≤
        walkLogSlope w * ‖derivWithin W (Icc (0:ℝ) 1) s‖ ∧
      ‖derivWithin (derivWithin H (Icc (0:ℝ) 1))
   (Icc 0 1) s‖ ≤
        walkLogSlope w*‖derivWithin (derivWithin W (Icc (0:ℝ) 1))
   (Icc 0 1) s‖+
        (Real.cos (w/4))⁻¹^2*‖derivWithin W (Icc (0:ℝ) 1) s‖^2 := by
  let Hd := derivWithin H (Icc (0:ℝ) 1)
  let Hdd := derivWithin Hd (Icc (0:ℝ) 1)
  let Wd := derivWithin W (Icc (0:ℝ) 1)
  let Wdd := derivWithin Wd (Icc (0:ℝ) 1)
  have hcd : ContDiffOn ℝ 1 Hd (Icc (0:ℝ) 1) :=
    hc.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (by norm_num)
  have hcdd : ContDiffOn ℝ 0 Hdd (Icc (0:ℝ) 1) :=
    hcd.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (by norm_num)
  have hWcd : ContDiffOn ℝ 1 Wd (Icc (0:ℝ) 1) :=
    hW.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (by norm_num)
  have hWcdd : ContDiffOn ℝ 0 Wdd (Icc (0:ℝ) 1) :=
    hWcd.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)) (by norm_num)
  have hder {F : ℝ → 𝕄} {n : WithTop ℕ∞} (hF : ContDiffOn ℝ n F (Icc (0:ℝ) 1)) (hn : n ≠ 0) :
      ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F (derivWithin F (Icc (0:ℝ) 1) x) x := fun x hx ↦
    ((hF.differentiableOn hn x ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
  have hb : ∀ s ∈ Ioo (0:ℝ) 1, ‖Hd s‖ ≤ walkLogSlope w * ‖Wd s‖ ∧
      ‖Hdd s‖≤
      walkLogSlope w*‖Wdd s‖+(Real.cos (w/4))⁻¹^2*‖Wd s‖^2 := by
    intro s hs
    obtain ⟨c,hc0⟩ := hcenter s ⟨hs.1.le,hs.2.le⟩
    exact walk_log_interior_bounds hw hs hH hc.continuousOn hc0 he (hder hc (by norm_num))
      (hder hcd one_ne_zero s hs) hW.continuousOn hWcd.continuousOn hWcdd.continuousOn
      (hder hW (by norm_num)) (hder hWcd one_ne_zero)
  have hcl : closure (Ioo (0:ℝ) 1)=Icc (0:ℝ) 1 := closure_Ioo (by norm_num)
  intro s hs
  constructor
  · exact le_on_closure (fun x hx ↦ (hb x hx).1)
      (by rw [hcl]; exact hcd.continuousOn.norm)
      (by rw [hcl]; exact continuousOn_const.mul hWcd.continuousOn.norm) (by rwa [hcl])
  · exact le_on_closure (fun x hx ↦ (hb x hx).2) (by rw [hcl]; exact hcdd.continuousOn.norm)
      (by
        rw [hcl]
        exact (continuousOn_const.mul hWcdd.continuousOn.norm).add
          (continuousOn_const.mul (hWcd.continuousOn.norm.pow 2))) (by rwa [hcl])

omit [NeZero d] in
/-- **Lemma A.2** (`lem:walk-log`): construct the prescribed-window Hermitian logarithm
pointwise and prove uniqueness. Local principal-log integral representatives give C²
regularity; the first- and second-derivative bounds then extend to the closed interval.
The width hypotheses are exactly `0 ≤ w < 2 * π`. -/
theorem lem_walk_log [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw0 : 0 ≤ w) (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ)))
    (hc : ContDiffOn ℝ 2 W (Icc (0 : ℝ) 1)) :
    let S : ℝ → ℝ := fun x ↦ if x=0 then 1 else (x/2)/Real.sin (x/2)
    ∃ H : ℝ → 𝕄, ∃ hH : IsTimeDepHamiltonian H,
      (∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hH s hs).eigenvalues i ∈ Icc (a s) (a s+w)) ∧ evol (H s) 1=W s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ (B : 𝕄) (hB : B.IsHermitian),
        (∀ i, hB.eigenvalues i ∈ Icc (a s) (a s+w)) → evol B 1=W s → B=H s) ∧
      ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ S w*‖derivWithin W (Icc (0 : ℝ) 1) s‖ ∧
        ‖derivWithin (derivWithin H (Icc (0 : ℝ) 1)) (Icc 0 1) s‖ ≤
          S w*‖derivWithin (derivWithin W (Icc (0 : ℝ) 1)) (Icc 0 1) s‖+
            ‖derivWithin W (Icc (0 : ℝ) 1) s‖^2/Real.cos (w/4)^2 := by
  classical
  intro S
  have hex : ∀ s : ℝ, ∃ H : 𝕄, ∃ hH : H.IsHermitian,
      s ∈ Icc (0 : ℝ) 1 →
        (∀ i, hH.eigenvalues i ∈ Icc (a s) (a s + w)) ∧ evol H 1 = W s := by
    intro s
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · obtain ⟨H, hH, hwin, he⟩ := walk_log_pointwise (a s) w (W s)
        (hunit s hs) (harc s hs)
      exact ⟨H, hH, fun _ ↦ ⟨hwin, he⟩⟩
    · exact ⟨0, Matrix.isHermitian_zero, fun h ↦ (hs h).elim⟩
  choose H hH he using hex
  have hherm : IsTimeDepHamiltonian H := fun s _ ↦ hH s
  have hevol := fun s hs ↦ (he s hs).2
  have hwindow := fun s hs ↦ (he s hs).1
  have hcenter := fun s hs ↦ norm_sub_smul_one_le_of_eigenvalues (hH s) hw0 (hwindow s hs)
  have hunique : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (B : 𝕄) (hB : B.IsHermitian),
      (∀ i, hB.eigenvalues i ∈ Icc (a s) (a s + w)) → evol B 1 = W s → B = H s := by
    intro s hs B hB hwin hBexp
    apply eq_of_evol_eq (α := -(a s + w / 2)) (r := w / 2) (by linarith) hB
      (by simpa only [neg_neg] using norm_sub_smul_one_le_of_eigenvalues hB hw0 hwin)
      (hH s) (by simpa only [neg_neg] using hcenter s hs)
    exact hBexp.trans (hevol s hs).symm
  -- The local representatives differentiate the principal logarithm integral twice.
  have hcd : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1) := by
    intro s hs
    obtain ⟨δ, _, hmem, hsK, hF, _, _⟩ :=
      exists_local_walkLogIntegral_contDiffOn hw ha hc hherm hevol hwindow hs
    obtain ⟨ρ, hρ, ε, _, C, hsep⟩ :=
      exists_uniform_walkLog_distance_and_bound a w W hw ha hc.continuousOn hunit harc hs
    let μ := a s + w / 2
    let F := fun t ↦ (μ : ℂ) • (1 : 𝕄) +
      I • walkLogIntegral (Complex.exp (I * (μ : ℂ)) • W t)
    have hF' : ContDiffWithinAt ℝ 2 F (Icc (0 : ℝ) 1) s :=
      (hF s hsK).mono_of_mem_nhdsWithin hmem
    have hnear := eventually_window_in_principal_turn (ha s hs)
      (show 0 < 2 * π - w by linarith)
    simp only [sub_sub_cancel] at hnear
    have heq : H =ᶠ[𝓝[Icc (0 : ℝ) 1] s] F := by
      filter_upwards [hnear, self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds s hρ)] with t ht htI htρ
      have hnorm : ‖H t - (μ : ℂ) • 1‖ < π := by
        have hn := norm_center_lt_pi_of_open_turn (hH t) (α := μ - π) (by
          intro i
          have hh := ht.2 _ (hwindow t htI i)
          dsimp [μ]
          constructor <;> linarith [hh.1, hh.2])
        simpa only [sub_add_cancel] using hn
      have hG : (H t - (μ : ℂ) • 1).IsHermitian := by
        apply (hH t).sub
        change star ((μ : ℂ) • (1 : 𝕄)) = (μ : ℂ) • 1
        simp only [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]
      have hev : evol (H t - (μ : ℂ) • 1) 1 =
          Complex.exp (I * (μ : ℂ)) • W t := by
        rw [evol_sub_scalar_one, hevol t htI]
      have hcut : spectrum ℂ (evol (H t - (μ : ℂ) • 1) 1) ⊆ Complex.slitPlane := by
        rw [hev]
        exact (hsep t htI (by simpa only [Metric.mem_closedBall, Real.dist_eq] using htρ)).2.1
      exact walk_log_integral μ hG hnorm (hevol t htI) hcut
    exact hF'.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hs)
  have hb := bounds_on_Icc hw hherm hcd hc
    (fun s hs ↦ ⟨a s + w / 2, hcenter s hs⟩) hevol
  have hS : S w = walkLogSlope w := by
    rcases eq_or_lt_of_le hw0 with h | h
    · subst w; simp only [S, if_pos rfl, walkLogSlope_zero]
    · simp only [S, if_neg h.ne']
      rw [walkLogSlope_eq_sinBound h hw, sinBound]
  refine ⟨H, hherm, he, hunique, hcd, fun s hs ↦ ?_⟩
  simpa only [hS, inv_pow, inv_mul_eq_div] using hb s hs

end UnitaryProducts.PaperProof
