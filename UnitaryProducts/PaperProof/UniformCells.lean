/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.Vocabulary
public import UnitaryProducts.PaperProof.LocalCell
public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.PaperProof.ThmUnitStepsMax
public import UnitaryProducts.PaperProof.UniformCellGeometry
public import UnitaryProducts.PaperProof.UniformCellIntegrals
public import UnitaryProducts.Prose.ResidualPointwise
public import UnitaryProducts.Prose.FinalSteps
/-!
# Uniform correctors on all rounded cells

## Declarations

- `AllSampleWidth`
- `allSampleCorrectorFamily`
- `allSampleCorrectorFamily_center_norm_le`
- `allSampleCorrectorFamily_end_values`
- `allSampleCorrectorFamily_ode`
- `contDiff_uniformCorrectionPiece`
- `uniformCorrectionPiece`
- `uniformCorrectionPiece_derivative`
- `uniformCorrectionPiece_jump_frame`
- `uniformPieceResidual`
- `uniformResidual_norm_le`
- `uniformResidual_profile_bound`
- `uniform_aestronglyMeasurable_pieceResidual`
- `uniform_clock_integral_continuous`
- `uniform_corrector_norm_LM`
- `uniform_even_integral`
- `uniform_local_bounds`
- `uniform_residual_integral`
- `uniform_clock_profile_integral`
- `unit_residual_integral`
- `unitPhysicalResidual_integral_formula`
- `unitPhysicalResidual_integral_product_bound`
- `uniform_residual_moments`
- `uniform_residual_profile_integral`
- `uniform_residual_step`
- `unitPhysicalResidual`
- `uniform_physical_residual_integral`
- `unitPhysicalResidual_integral`
- `unitPhysicalResidual_local`
- `unitPhysicalResidual_profile_bound`
-/
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Dressed
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse
noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
/-- Borel measurable structure for matrices equipped with the operator norm. -/
local instance uniformMeasurableSpace : MeasurableSpace 𝕄 := borel 𝕄
/-- The measurable structure used by the uniform residual is the Borel structure. -/
local instance uniformBorelSpace : BorelSpace 𝕄 := ⟨rfl⟩

/-- Width of every sample, including indices 0 and N. -/
def AllSampleWidth (T : ℝ) (N : ℕ) (H : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) (w : ℝ) : Prop :=
  ∀ (r : ℤ) (hr : 0 ≤ r ∧ r ≤ (N : ℤ)), ∀ p q,
    let hΩ := Separation.isHermitian_real_smul (hH _ (all_grid_mem hr)) (T / N)
    |hΩ.eigenvalues p - hΩ.eigenvalues q| ≤ w

/-- The periodic corrector at each inclusive sample. -/
def allSampleCorrectorFamily (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) (r : ℤ) : ℝ → 𝕄 :=
  if hr : 0 ≤ r ∧ r ≤ (N : ℤ) then
    (periodicCorrectorData ((T / N) • H ((r : ℝ) / N))
      (Separation.isHermitian_real_smul (hH _ (all_grid_mem hr)) (T / N))
      ((T / (N : ℝ) ^ 2) • Hd ((r : ℝ) / N))).2.2
  else fun _ ↦ 0

/-- The correction on the closed cell of sample j; no global correction is glued. -/
def uniformCorrectionPiece (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) (j : ℤ) (s : ℝ) : 𝕄 :=
  allSampleCorrectorFamily T N H Hd hH j ((N : ℝ) * s - j)

/-- The residual selects the derivative of the current piece, including at switches.
Only its values on open cells matter to the comparison and its integral. -/
def uniformPieceResidual (T : ℝ) (N : ℕ) (H : ℝ → 𝕄) (Y : ℤ → ℝ → 𝕄)
    (s : ℝ) : 𝕄 :=
  globalResidual T N H (Y (clock (N * s))) s

/-- Supporting identity for uniform sample cells. -/
theorem allSampleCorrectorFamily_ode (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) {r : ℤ}
    (hr : 0 ≤ r ∧ r ≤ (N : ℤ)) (t : ℝ) :
    HasDerivAt (allSampleCorrectorFamily T N H Hd hH r)
      (t • ((T / (N : ℝ) ^ 2) • Hd ((r : ℝ) / N)) -
        I • (((T / N) • H ((r : ℝ) / N)) * allSampleCorrectorFamily T N H Hd hH r t -
          allSampleCorrectorFamily T N H Hd hH r t * ((T / N) • H ((r : ℝ) / N)))) t := by
  simp only [allSampleCorrectorFamily, dif_pos hr]
  exact hasDerivAt_periodic_corrector _ _ _ _

/-- Every closed correction piece is continuously differentiable. -/
theorem contDiff_uniformCorrectionPiece (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) (j : ℤ) :
    ContDiff ℝ 1 (uniformCorrectionPiece T N H Hd hH j) := by
  refine ContDiff.comp ?_ ((contDiff_const.mul contDiff_id).sub contDiff_const)
  by_cases hj : 0 ≤ j ∧ j ≤ (N : ℤ)
  · have hd := allSampleCorrectorFamily_ode T N H Hd hH hj
    refine contDiff_one_iff_deriv.mpr ⟨fun t ↦ (hd t).differentiableAt, ?_⟩
    rw [funext fun t ↦ (hd t).deriv]
    have hc := (show Differentiable ℝ _ from fun t ↦ (hd t).differentiableAt).continuous
    fun_prop
  · simpa only [allSampleCorrectorFamily, dif_neg hj] using contDiff_const (c := (0 : 𝕄))

/-- Supporting identity for uniform sample cells. -/
theorem allSampleCorrectorFamily_end_values (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) {w : ℝ} (hw : w < 2 * π)
    (hwidth : AllSampleWidth T N H hH w) {r : ℤ} (hr : 0 ≤ r ∧ r ≤ (N : ℤ)) :
    let hΩ := Separation.isHermitian_real_smul (hH _ (all_grid_mem hr)) (T / N)
    let E := (periodicCorrectorData ((T / N) • H ((r : ℝ) / N)) hΩ
      ((T / (N : ℝ) ^ 2) • Hd ((r : ℝ) / N))).2.1
    allSampleCorrectorFamily T N H Hd hH r (-(1 / 2)) = E ∧
      allSampleCorrectorFamily T N H Hd hH r (1 / 2) = E := by
  rcases Nat.eq_zero_or_pos d with rfl | hdim
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, and_self]
  letI : NeZero d := ⟨hdim.ne'⟩
  have hw₀ : 0 ≤ w := by simpa using hwidth r hr 0 0
  simp only [allSampleCorrectorFamily, dif_pos hr]
  have hb := canonical_cell_endpoints hw₀ hw
    (Separation.isHermitian_real_smul (hH _ (all_grid_mem hr)) (T / N))
    (hwidth r hr) ((T / (N : ℝ)^2) • Hd ((r : ℝ) / N))
  simpa only [neg_div] using hb

/-- The quadratic corrector profile at every sample cell. -/
theorem uniform_corrector_norm_LM [NeZero d] {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    {L : ℝ}
    {w : ℝ} (hw : w < 2 * π)
    (hwidth : AllSampleWidth T N H hH w) {j : ℤ} (hr : 0 ≤ j ∧ j ≤ (N : ℤ))
    (hbd : ‖Hd ((j : ℝ) / N)‖ ≤ L)
    {t : ℝ} :
    ‖allSampleCorrectorFamily T N H Hd hH j t‖ ≤
      (frameBound w - frameBound (w / 2) / 2 + t ^ 2 / 2) *
        (T / (N : ℝ) ^ 2) * L := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw₀ : 0 ≤ w := by simpa using hwidth 0 (by omega) 0 0
  let hΩ := Separation.isHermitian_real_smul (hH _ (all_grid_mem hr)) (T / N)
  have hb := canonical_cell_norm hw₀ hw hΩ (hwidth _ hr)
    ((T / (N : ℝ) ^ 2) • Hd ((j : ℝ) / N)) t
  simp only [allSampleCorrectorFamily, dif_pos hr]
  rw [norm_smul_of_nonneg (by positivity : 0 ≤ T / (N : ℝ) ^ 2), ← mul_assoc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hbd
    (mul_nonneg (add_nonneg (center_bound_nonneg hw₀ hw) (by positivity)) (by positivity)))

/-- Supporting identity for uniform sample cells. -/
theorem allSampleCorrectorFamily_center_norm_le {T : ℝ} (hT : 0 ≤ T)
    (N : ℕ) (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w)
    {r : ℤ} (hr : 0 ≤ r ∧ r ≤ (N : ℤ)) :
    ‖allSampleCorrectorFamily T N H Hd hH r 0‖ ≤
      (frameBound w - frameBound (w / 2) / 2) * T / (N : ℝ) ^ 2 *
        ‖Hd ((r : ℝ) / N)‖ := by
  -- In dimension zero every matrix vanishes; handle this before choosing an eigenvalue.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, mul_zero, le_refl]
  letI : NeZero d := ⟨hd.ne'⟩
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero, mul_div_assoc] using
    uniform_corrector_norm_LM hT N H Hd hH hw hwidth hr le_rfl (t := 0)

/-- The residual of the pieces is measurable; no derivative crosses a jump. -/
theorem uniform_aestronglyMeasurable_pieceResidual (T : ℝ) (N : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hcH : ContinuousOn H (Icc (0 : ℝ) 1)) :
    AEStronglyMeasurable
      (uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hmH := hcH.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hm (f : ℤ → ℝ → 𝕄) (hf : ∀ j, Continuous (f j)) :
      AEStronglyMeasurable (fun s ↦ f (clock (N * s)) s)
        (volume.restrict (Icc (0 : ℝ) 1)) :=
    ((measurable_from_prod_countable_left (f := fun p ↦ f p.2 p.1)
      (fun j ↦ (hf j).measurable)).comp (measurable_id.prodMk (Int.measurable_floor.comp
        (by fun_prop : Measurable (fun s : ℝ ↦ (N : ℝ) * s + 1 / 2))))).aestronglyMeasurable
  have hq := hm (fun j _ ↦ H ((j : ℝ) / N)) (fun _ ↦ continuous_const)
  have hc := contDiff_uniformCorrectionPiece T N H Hd hH
  have hy := hm _ (fun j ↦ (hc j).continuous)
  have hdy := hm _ (fun j ↦ (hc j).continuous_deriv le_rfl)
  exact ((hmH.const_smul T).sub (hq.const_smul T)).sub hdy |>.sub
    (((hmH.mul hy).sub (hy.mul hq)).const_smul T |>.const_smul I)

/-- The ODE differentiated along a fixed correction piece, including its endpoints. -/
theorem uniformCorrectionPiece_derivative (T : ℝ) {N : ℕ}
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    {j : ℤ} (hj : 0 ≤ j ∧ j ≤ (N : ℤ)) (s : ℝ) :
    HasDerivAt (uniformCorrectionPiece T N H Hd hH j)
      (((N : ℝ) * s - j) • ((T / N) • Hd ((j : ℝ) / N)) -
        I • (T • (H ((j : ℝ) / N) * uniformCorrectionPiece T N H Hd hH j s -
          uniformCorrectionPiece T N H Hd hH j s * H ((j : ℝ) / N)))) s := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · change HasDerivAt (fun u ↦ uniformCorrectionPiece T 0 H Hd hH j u) _ s
    simpa [uniformCorrectionPiece, allSampleCorrectorFamily, dite_apply,
      periodicCorrector_zero] using hasDerivAt_const s (0 : 𝕄)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  convert (allSampleCorrectorFamily_ode T N H Hd hH hj ((N : ℝ) * s - j)).scomp s
    (((hasDerivAt_id s).const_mul (N : ℝ)).sub_const (j : ℝ)) using 1
  simp only [uniformCorrectionPiece, mul_one, smul_sub, smul_mul_assoc, mul_smul_comm,
    smul_comm (N : ℝ) I, smul_smul, pow_two, div_mul_eq_div_div,
    mul_left_comm (N : ℝ), mul_div_cancel₀ _ hn]

/-- The cell residual used in the global bound is the Section 4 residual identity,
with the local-time interval restricted to the physical Hamiltonian domain. -/
theorem uniformPieceResidual_local_cell (T : ℝ) {N : ℕ} (hN : 0 < N)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    :
    let Y := uniformCorrectionPiece T N H Hd hH
    let r : ℝ := clock (N * s)
    let K := fun σ : ℝ ↦ (T / N) • H ((r + σ) / N)
    let Kd := fun σ : ℝ ↦ (T / (N : ℝ) ^ 2) • Hd ((r + σ) / N)
    uniformPieceResidual T N H Y s = (N : ℝ) •
      ((∫ σ in (0 : ℝ)..((N : ℝ) * s - clock (N * s)), Kd σ - Kd 0) -
        I • ((K (((N : ℝ) * s - clock (N * s))) - K 0) * Y (clock (N * s)) s)) := by
  intro Y r K Kd
  let τ := (N : ℝ) * s - clock (N * s)
  let Z := allSampleCorrectorFamily T N H Hd hH (clock (N * s))
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr := clock_bounds (N := N) hs
  have he : (r + τ) / N = s := by dsimp [r, τ]; field_simp; ring
  have hsample : r / N ∈ Icc (0 : ℝ) 1 := sample_mem (N := N) hs
  let f := fun σ : ℝ ↦ (r + σ) / N
  have hf : Monotone f := fun a b hab ↦
    div_le_div_of_nonneg_right (by simpa only [add_comm] using add_le_add_left hab r) hn.le
  have hmap : MapsTo f (uIcc (0 : ℝ) τ) (Icc (0 : ℝ) 1) := by
    intro σ hσ
    apply uIcc_subset_Icc hsample (he.symm ▸ hs)
    simpa only [f, add_zero] using hf.image_uIcc_subset ⟨σ, hσ, rfl⟩
  have hK : ∀ σ ∈ uIcc (0 : ℝ) τ, (K σ).IsHermitian := fun σ hσ ↦
    Separation.isHermitian_real_smul (hH _ (hmap hσ)) (T / N)
  have hKd : ∀ σ ∈ uIcc (0 : ℝ) τ,
      HasDerivWithinAt K (Kd σ) (uIcc 0 τ) σ := fun σ hσ ↦
    hasDerivWithinAt_local_hamiltonian T N r σ (hd _ (hmap hσ)) hmap
  have hcont : ContinuousOn Kd (uIcc (0 : ℝ) τ) :=
    (hc.comp ((continuous_const.add continuous_id).div_const (N : ℝ)).continuousOn
      hmap).const_smul _
  let hΩ := hK 0 left_mem_uIcc
  have hres := canonical_cell_residual hΩ (Kd 0)
    (uIcc 0 τ) ordConnected_uIcc left_mem_uIcc K Kd hKd hcont rfl rfl
    right_mem_uIcc
  have hsame : (periodicCorrectorData (K 0) hΩ (Kd 0)).2.2 = Z := by
    simp only [Z, allSampleCorrectorFamily, dif_pos hr, K, Kd, add_zero, r]
  rw [hsame] at hres
  have hZd := (allSampleCorrectorFamily_ode T N H Hd hH hr τ).deriv
  change deriv Z τ = _ at hZd
  calc
    uniformPieceResidual T N H Y s =
        (N : ℝ) • (K τ - K 0 - deriv Z τ - I • (K τ * Z τ - Z τ * K 0)) := by
      unfold uniformPieceResidual globalResidual
      rw [(uniformCorrectionPiece_derivative T H Hd hH hr s).deriv, hZd]
      simp only [K, he, add_zero, Y, uniformCorrectionPiece, Z, r, τ,
        smul_sub, smul_mul_assoc, mul_smul_comm, smul_comm (N : ℝ) I,
        smul_smul, pow_two, div_mul_eq_div_div, mul_div_cancel₀ _ hn.ne',
        mul_left_comm (N : ℝ), sample]
    _ = _ := by rw [hres]; rfl

/-- the proof of Theorem 4.2: derivative bounds and their two local-time rescalings.
For `a=j/N`, `b=(j+σ)/N`, the local difference `N*(b-a)` is exactly `σ`. -/
theorem uniform_local_bounds {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (H Hd : ℝ → 𝕄)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖H b-H a‖ ≤ L*|b-a| ∧
    ‖(T/N) • H b-(T/N) • H a‖ ≤ (T/(N:ℝ)^2)*L*|(N:ℝ)*(b-a)| ∧
    ‖(T/(N:ℝ)^2) • Hd b-(T/(N:ℝ)^2) • Hd a‖ ≤
      (T/(N:ℝ)^3)*M*|(N:ℝ)*(b-a)| := by
  have hh := norm_sub_le_of_derivWithin_le hd hbd a ha b hb
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa using hh
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨hh, ?_, ?_⟩ <;>
    rw [← smul_sub, norm_smul_of_nonneg (by positivity), abs_mul, abs_of_pos hn]
  · convert mul_le_mul_of_nonneg_left hh (div_nonneg hT hn.le) using 1; field_simp
  · convert mul_le_mul_of_nonneg_left (hl a ha b hb)
      (div_nonneg hT (sq_nonneg _)) using 1; field_simp

/-- The residual pointwise bound, using only the current sample. -/
theorem uniformResidual_norm_le {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0 < N)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ}
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    :
    let Y := uniformCorrectionPiece T N H Hd hH
    ‖uniformPieceResidual T N H Y s‖ ≤
      T / (N : ℝ) ^ 2 * |((N : ℝ) * s - clock (N * s))| *
        (M * |((N : ℝ) * s - clock (N * s))| / 2 + N * L * ‖Y (clock (N * s)) s‖) := by
  intro Y
  have hc := continuousOn_of_norm_sub_le hl
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let r : ℝ := clock (N * s)
  -- The local clock τ = Ns - q(Ns) measures time from the rounded sample.
  let τ := ((N : ℝ) * s - clock (N * s))
  let K := fun u : ℝ ↦ (T / N) • H ((r + u) / N)
  let Kd := fun u : ℝ ↦ (T / (N : ℝ)^2) • Hd ((r + u) / N)
  have hq := sample_mem (N := N) hs
  change r/N ∈ Icc (0 : ℝ) 1 at hq
  have he : (r + τ)/N = s := by
    dsimp only [r, τ]
    field_simp
    ring
  have hi : ‖∫ u in (0 : ℝ)..τ, Kd u-Kd 0‖ ≤ (T/(N:ℝ)^3)*M*(τ^2/2) := by
    have hb := local_taylor_chain hT hn hd hl hq (he.symm ▸ hs)
    simp only [Kd, add_zero]
    exact (hb.1.symm.trans_le (hb.2.1.trans_eq hb.2.2)).trans_eq (by ring)
  have hK : ‖K τ-K 0‖ ≤ (T/(N:ℝ)^2)*L*|τ| := by
    have hb := (uniform_local_bounds (N := N) hT H Hd hd hbd hl hq hs).2.1
    simpa only [K, he, add_zero, mul_sub, mul_div_cancel₀ _ hn.ne', τ] using hb
  rw [uniformPieceResidual_local_cell T hN H Hd hH hd hc hs,
    norm_smul_of_nonneg hn.le]
  have hprod := norm_mul_le_of_le hK (le_refl ‖Y (clock (N * s)) s‖)
  refine (mul_le_mul_of_nonneg_left (norm_sub_le_of_le hi
    (by simpa only [norm_smul, Complex.norm_I, one_mul] using hprod)) hn.le).trans_eq ?_
  dsimp [τ]
  rw [← sq_abs (((N : ℝ) * s - clock (N * s)))]
  field_simp

/-- the proof of Theorem 4.2: the integral-term bound and its exact even residual profile. -/
theorem uniformResidual_profile_bound [NeZero d] {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0 < N)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ}
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let Y := uniformCorrectionPiece T N H Hd hH
    let τ := ((N : ℝ) * s - clock (N * s))
    let c₀ := frameBound w-frameBound (w/2)/2
    ‖uniformPieceResidual T N H Y s‖ ≤
      N*(T*M/(N:ℝ)^3)*|(∫ u in (0 : ℝ)..τ, |u|)| +
        N*(T*L/(N:ℝ)^2)*|τ| *(c₀+τ^2/2)*(T*L/(N:ℝ)^2) ∧
    N*(T*M/(N:ℝ)^3)*|(∫ u in (0 : ℝ)..τ, |u|)| +
        N*(T*L/(N:ℝ)^2)*|τ| *(c₀+τ^2/2)*(T*L/(N:ℝ)^2) =
      T/(N:ℝ)^2 * (M*τ^2/2+|τ| *(c₀+τ^2/2)*(T/N)*L^2) := by
  intro Y τ c₀
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have habs : |(∫ u in (0 : ℝ)..τ, |u|)| = τ ^ 2 / 2 := abs_integral_abs_zero τ
  rw [habs]
  -- Clear only the mesh denominators; the even profile and its coefficients stay explicit.
  have hprofile :
      N * (T * M / (N : ℝ) ^ 3) * (τ ^ 2 / 2) +
        N * (T * L / (N : ℝ) ^ 2) * |τ| * (c₀ + τ ^ 2 / 2) *
          (T * L / (N : ℝ) ^ 2) =
      T / (N : ℝ) ^ 2 * (M * τ ^ 2 / 2 + |τ| * (c₀ + τ ^ 2 / 2) * (T / N) * L ^ 2) := by
    field_simp
  refine ⟨?_, hprofile⟩
  have hL : 0 ≤ L := (norm_nonneg _).trans (hbd 0 ⟨le_rfl, zero_le_one⟩)
  have hp := uniformResidual_norm_le hT hN H Hd hH hd hbd hl hs
  have hy := uniform_corrector_norm_LM hT N H Hd hH hw hwidth (clock_bounds (N := N) hs)
    (hbd _ (sample_mem (N := N) hs)) (t := (N : ℝ) * s - clock (N * s))
  have hscaled := scaled_corrector_bound_LM hL hy
  apply hp.trans
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (M*|((N : ℝ) * s - clock (N * s))|/2)) (hscaled.1.trans_eq hscaled.2))
    (show 0 ≤ T/(N:ℝ)^2*|((N : ℝ) * s - clock (N * s))| by positivity)
  -- Replace τ² by |τ|² to identify the Taylor and corrector-product contributions.
  exact hb.trans_eq (by
    dsimp [τ, c₀]; rw [← sq_abs (((N : ℝ) * s - clock (N * s)))]; field_simp)

/-- The integral of a continuous even function over a symmetric cell. -/
theorem uniform_even_integral {f : ℝ → ℝ} (hc : Continuous f)
    (he : ∀ t, f (-t) = f t) :
    (∫ t in (-(1/2) : ℝ)..(1/2), f t) = 2 * ∫ t in (0 : ℝ)..(1/2), f t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-(1/2)) 0) (hc.intervalIntegrable 0 (1/2)),
    ← neg_zero, ← intervalIntegral.integral_comp_neg]
  simp only [he, neg_zero]
  ring

/-- Shift a full mesh step to the centered cell using clock-error periodicity.
The centered-cell change of variables includes both endpoint halves. -/
theorem uniform_clock_integral_continuous {N j : ℕ} {f : ℝ → ℝ}
    (hc : Continuous f) :
    (∫ s in (j : ℝ)/N..((j : ℝ)+1)/N, f |((N : ℝ) * s - clock (N * s))|) =
      (2/N)*(∫ t in (0 : ℝ)..(1/2), f t) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let g := fun t : ℝ ↦ f |t|
  have hgc : Continuous g := hc.comp continuous_abs
  have hge : ∀ t, g (-t) = g t := fun t ↦ congrArg f (abs_neg t)
  have hp := (clock_error_periodic.comp f).intervalIntegral_add_eq (j : ℝ) (-(1 / 2))
  norm_num only [Function.comp_apply, abs_sub_comm, neg_div, neg_add_eq_sub] at hp
  have hfull := (uniform_clock_integral_full (N := 1) (by omega) 0 hgc hge).1
  have hg : (∫ t in (0 : ℝ)..(1 / 2), g t) = ∫ t in (0 : ℝ)..(1 / 2), f t :=
    intervalIntegral.integral_congr fun t ht ↦
      congrArg f (abs_of_nonneg ((uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)) ▸ ht).1)
  rw [intervalIntegral.integral_comp_mul_left
    (fun t : ℝ ↦ f |t - clock t|) hn]
  simp only [mul_div_cancel₀ _ hn, hp]
  norm_num only [Nat.cast_one, Int.cast_zero, zero_sub, zero_add, div_one, one_mul] at hfull
  rw [hfull, uniform_even_integral hgc hge, hg]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- the proof of Theorem 4.2: the three moments of the full centered cell. -/
theorem uniform_residual_moments :
    (∫ t in (-(1/2) : ℝ)..(1/2), t ^ 2) = 1/12 ∧
    (∫ t in (-(1/2) : ℝ)..(1/2), |t|) = 1/4 ∧
    (∫ t in (-(1/2) : ℝ)..(1/2), |t| ^ 3) = 1/32 := by
  have ha (f : ℝ → ℝ) : (∫ t in (0 : ℝ)..(1/2), f |t|) =
      ∫ t in (0 : ℝ)..(1/2), f t :=
    intervalIntegral.integral_congr fun t ht ↦ congrArg f
      (abs_of_nonneg ((uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)) ▸ ht).1)
  refine ⟨by norm_num [integral_pow], ?_, ?_⟩
  · rw [uniform_even_integral (by fun_prop) (fun t ↦ abs_neg t), ha (fun t ↦ t)]
    norm_num [integral_id]
  · rw [uniform_even_integral (by fun_prop) (fun t ↦ by rw [abs_neg]), ha (· ^ 3)]
    norm_num [integral_pow]

/-- the proof of Theorem 4.2: the even residual profile integrates to the stated sharp constants. -/
theorem uniform_residual_profile_integral (M c₀ q : ℝ) :
    (∫ t in (-(1/2) : ℝ)..(1/2), M*t^2/2 + |t| *(c₀+t^2/2)*q) =
      M/24 + (c₀/4+1/64)*q := by
  have he : (fun t : ℝ ↦ M*t^2/2 + |t| *(c₀+t^2/2)*q) =
      (fun t ↦ (M/2)*t^2 + (c₀*q)*|t| + (q/2)*|t| ^3) := by
    funext t
    rw [← sq_abs t]
    ring
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [he, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      uniform_residual_moments.1, uniform_residual_moments.2.1, uniform_residual_moments.2.2]
  ring

/-- Integrate a supplied residual profile over one mesh interval. -/
theorem uniform_residual_step_of_profile {T : ℝ} {N j : ℕ} (hj : j < N)
    (R : ℝ → 𝕄) (hmR : AEStronglyMeasurable R (volume.restrict (Icc (0 : ℝ) 1)))
    (L M c₀ : ℝ)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1,
      (N : ℝ) * s + 1 / 2 ≠ (clock (N * s) : ℝ) →
      ‖R s‖ ≤ T / (N : ℝ) ^ 2 *
        (M * ((N : ℝ) * s - clock (N * s)) ^ 2 / 2 +
          |(N : ℝ) * s - clock (N * s)| *
            (c₀ + ((N : ℝ) * s - clock (N * s)) ^ 2 / 2) * (T / N) * L ^ 2)) :
    IntervalIntegrable R volume ((j : ℝ)/N) (((j : ℝ)+1)/N) ∧
    (∫ s in (j : ℝ)/N..((j : ℝ)+1)/N, ‖R s‖) ≤
      T/(N:ℝ)^3 * (M/24+(c₀/4+1/64)*(T/N)*L^2) := by
  let a : ℝ := (j:ℝ)/N
  let b : ℝ := ((j:ℝ)+1)/N
  let f := fun t : ℝ ↦ M*t^2/2 + |t| *(c₀+t^2/2)*((T/N)*L^2)
  let B := fun s ↦ f |((N : ℝ) * s - clock (N * s))|
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hj)
  have hab : a ≤ b := by dsimp [a,b]; gcongr; linarith
  have hsub : Icc a b ⊆ Icc (0:ℝ) 1 := by
    rw [← meshInterval_eq hj]; exact mesh_subset
  have hf : IntervalIntegrable f volume 0 (1/2) :=
    (by fun_prop : Continuous f).intervalIntegrable _ _
  have hiB : IntervalIntegrable B volume a b := local_clock_weight_integrable hf
  have hmR' := AEStronglyMeasurable.mono_set
    (uIoc_subset_uIcc.trans ((uIcc_of_le hab).subset.trans hsub)) hmR
  have hbound : ∀ᵐ s ∂volume.restrict (Icc a b), ‖R s‖ ≤ T/(N:ℝ)^2*B s := by
    have hreg := (clock_switches_countable N).ae_notMem volume
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hreg] with s hs hreg
    exact (hp s (hsub hs) hreg).trans_eq (by simp only [B, f, abs_abs, sq_abs, mul_assoc])
  have hiR := (hiB.const_mul (T/(N:ℝ)^2)).mono_fun' hmR'
    (ae_restrict_of_ae_restrict_of_subset
      (uIoc_subset_uIcc.trans (uIcc_of_le hab).subset) hbound)
  refine ⟨hiR, ?_⟩
  have hh := intervalIntegral.integral_mono_ae_restrict hab hiR.norm
    (hiB.const_mul (T/(N:ℝ)^2)) hbound
  rw [intervalIntegral.integral_const_mul,
    uniform_clock_integral_continuous (j := j) (f := f) (by fun_prop)] at hh
  apply hh.trans_eq
  have hp := uniform_residual_profile_integral M c₀ ((T/N)*L^2)
  rw [uniform_even_integral (by fun_prop)
    (fun t ↦ by simp only [neg_sq, abs_neg])] at hp
  convert congrArg (fun x ↦ T/(N:ℝ)^3 * x) hp using 1 <;> ring

/-- Every mesh interval has the same sharp residual integral, including the first and last. -/
theorem uniform_residual_step [NeZero d] {T : ℝ} (hT : 0 ≤ T) {N j : ℕ}
    (hj : j < N) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ}
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let R := uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH)
    let c₀ := frameBound w-frameBound (w/2)/2
    IntervalIntegrable R volume ((j : ℝ)/N) (((j : ℝ)+1)/N) ∧
    (∫ s in (j : ℝ)/N..((j : ℝ)+1)/N, ‖R s‖) ≤
      T/(N:ℝ)^3 * (M/24+(c₀/4+1/64)*(T/N)*L^2) := by
  intro R c₀
  exact uniform_residual_step_of_profile hj R
    (uniform_aestronglyMeasurable_pieceResidual T N H Hd hH (HasDerivWithinAt.continuousOn hd)) L
      M c₀
    (fun s hs _hr ↦ (uniformResidual_profile_bound hT (Nat.zero_lt_of_lt hj)
      H Hd hH hd hbd hl hs hw hwidth).elim fun hb he ↦ hb.trans_eq he)

/-- Normalize Theorem 4.2's explicit two-half-cell and `N-1`-full-cell split.
Adding the two endpoint integrals gives exactly one full centered cell. -/
theorem uniform_clock_profile_integral {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ}
    (hf : Continuous f) :
    IntervalIntegrable (fun s ↦ f ((N : ℝ) * s - clock (N * s))) volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, f ((N : ℝ) * s - clock (N * s))) =
      ∫ u in (-(1/2) : ℝ)..(1/2), f u := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcells := clock_profile_cell_split N hf
  have hi := hcells.1.comp_mul_left (c := (N : ℝ))
  simp only [zero_div, div_self hn] at hi
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_comp_mul_left
    (fun t ↦ f (t - clock t)) hn]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [hcells.2.2]
  field_simp


/-- Sum a supplied residual profile, pairing the two endpoint half cells. -/
theorem uniform_residual_integral_of_profile {T : ℝ} {N : ℕ} (hN : 0 < N)
    (R : ℝ → 𝕄) (hmR : AEStronglyMeasurable R (volume.restrict (Icc (0 : ℝ) 1)))
    (L M c₀ : ℝ)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1,
      (N : ℝ) * s + 1 / 2 ≠ (clock (N * s) : ℝ) →
      ‖R s‖ ≤ T / (N : ℝ) ^ 2 *
        (M * ((N : ℝ) * s - clock (N * s)) ^ 2 / 2 +
          |(N : ℝ) * s - clock (N * s)| *
            (c₀ + ((N : ℝ) * s - clock (N * s)) ^ 2 / 2) * (T / N) * L ^ 2)) :
    IntervalIntegrable R volume 0 1 ∧
    IntervalIntegrable (fun s ↦ ‖R s‖) volume 0 1 ∧
    (∫ s in (0:ℝ)..1, ‖R s‖) ≤
      T/(N:ℝ)^2 * (M/24+(c₀/4+1/64)*(T/N)*L^2) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hi (j : ℕ) (hj : j < N) : IntervalIntegrable R volume
      ((j:ℝ)/N) (((j+1:ℕ):ℝ)/N) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (uniform_residual_step_of_profile hj R hmR L M c₀ hp).1
  have hiR := IntervalIntegrable.trans_iterate (a := fun j : ℕ ↦ (j:ℝ)/N) hi
  simp only [Nat.cast_zero, zero_div, div_self hn] at hiR
  refine ⟨hiR, hiR.norm, ?_⟩
  let f := fun u : ℝ ↦ M*u^2/2 + |u| * (c₀+u^2/2)*((T/N)*L^2)
  have hf : Continuous f := by fun_prop
  have hcells := uniform_clock_profile_integral hN hf
  have hbound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖R s‖ ≤ T/(N:ℝ)^2 * f ((N : ℝ)*s-clock (N*s)) := by
    have hreg := (clock_switches_countable N).ae_notMem volume
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hreg] with s hs hreg
    exact (hp s hs hreg).trans_eq (by dsimp only [f]; ring)
  have hmono := intervalIntegral.integral_mono_ae_restrict zero_le_one hiR.norm
    (hcells.1.const_mul (T/(N:ℝ)^2)) hbound
  rw [intervalIntegral.integral_const_mul, hcells.2,
    uniform_residual_profile_integral M c₀ ((T/N)*L^2)] at hmono
  simpa only [mul_assoc] using hmono

/-- Uniform-cell the proof of Theorem 4.2, with sharp constants and no endpoint correction. -/
theorem uniform_residual_integral [NeZero d] {T : ℝ} (hT : 0 ≤ T) {N : ℕ}
    (hN : 0 < N) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ}
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hd t - Hd s‖ ≤ M * |t - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w) :
    let R := uniformPieceResidual T N H (uniformCorrectionPiece T N H Hd hH)
    let c₀ := frameBound w-frameBound (w/2)/2
    IntervalIntegrable R volume 0 1 ∧
    IntervalIntegrable (fun s ↦ ‖R s‖) volume 0 1 ∧
    (∫ s in (0:ℝ)..1, ‖R s‖) ≤
      T/(N:ℝ)^2 * (M/24+(c₀/4+1/64)*(T/N)*L^2) := by
  intro R c₀
  exact uniform_residual_integral_of_profile hN R
    (uniform_aestronglyMeasurable_pieceResidual T N H Hd hH (HasDerivWithinAt.continuousOn hd)) L
      M c₀
    (fun s hs _hr ↦ (uniformResidual_profile_bound hT hN H Hd hH hd hbd hl hs hw hwidth).1.trans_eq
      (uniformResidual_profile_bound hT hN H Hd hH hd hbd hl hs hw hwidth).2)

/-- The residual of the assembled correction in physical time at unit steps. -/
def unitPhysicalResidual (T : ℕ) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) (t : ℝ) : 𝕄 :=
  (1 / T : ℝ) • uniformPieceResidual T T H
    (uniformCorrectionPiece T T H Hd hH) (t / T)

/-- Equation (4.2) in physical time, for the periodic piece at the rounded sample. -/
theorem unitPhysicalResidual_local {T : ℕ} (hT : 0 < T) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    let j : ℤ := clock t
    let τ := t - j
    let K := fun σ : ℝ ↦ H (((j : ℝ) + σ) / T)
    let Kd := fun σ : ℝ ↦ (1 / T : ℝ) • Hd (((j : ℝ) + σ) / T)
    unitPhysicalResidual T H Hd hH t =
      (∫ σ in (0 : ℝ)..τ, Kd σ - Kd 0) -
        I • ((K τ - K 0) * allSampleCorrectorFamily T T H Hd hH j τ) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hs : t / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩
  rw [unitPhysicalResidual, uniformPieceResidual_local_cell T hT H Hd hH hd hc hs]
  simp only [smul_smul, one_div_mul_cancel hTr.ne', one_smul, div_self hTr.ne',
    pow_two, div_mul_eq_div_div, mul_div_cancel₀ _ hTr.ne', uniformCorrectionPiece]

/-- Theorem 4.2's third line, before taking norms: the derivative-difference
integral starts at the actual rounded sample in physical time. -/
theorem unitPhysicalResidual_integral_formula {T : ℕ} (hT : 0 < T) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    unitPhysicalResidual T H Hd hH t =
      (∫ σ in (clock t : ℝ)..t, (1 / T : ℝ) • Hd (σ / T) -
        (1 / T : ℝ) • Hd ((clock t : ℝ) / T)) -
      I • ((H (t / T) - H ((clock t : ℝ) / T)) *
        allSampleCorrectorFamily T T H Hd hH (clock t) (t - clock t)) := by
  rw [unitPhysicalResidual_local hT H Hd hH hd hc ht]
  dsimp only
  have hshift := intervalIntegral.integral_comp_add_right
    (fun σ ↦ (1 / T : ℝ) • Hd (σ / T) - (1 / T : ℝ) • Hd ((clock t : ℝ) / T))
    (clock t : ℝ) (a := 0) (b := t - clock t)
  simp only [zero_add, sub_add_cancel] at hshift
  simpa only [add_comm (clock t : ℝ), zero_add, sub_add_cancel] using
    congrArg (fun Z ↦ Z - I • ((H (t / T) - H ((clock t : ℝ) / T)) *
      allSampleCorrectorFamily T T H Hd hH (clock t) (t - clock t))) hshift

/-- Theorem 4.2's third-line integrand: triangle inequality and the product norm
bound applied to the explicit physical-time residual integral. -/
theorem unitPhysicalResidual_integral_product_bound {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hc : ContinuousOn Hd (Icc (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖unitPhysicalResidual T H Hd hH t‖ ≤
      ‖∫ σ in (clock t : ℝ)..t, (1 / T : ℝ) • Hd (σ / T) -
        (1 / T : ℝ) • Hd ((clock t : ℝ) / T)‖ +
      ‖H (t / T) - H ((clock t : ℝ) / T)‖ *
        ‖allSampleCorrectorFamily T T H Hd hH (clock t) (t - clock t)‖ := by
  rw [unitPhysicalResidual_integral_formula hT H Hd hH hd hc ht]
  exact norm_sub_le_of_le le_rfl (by
    simpa only [norm_smul, Complex.norm_I, one_mul] using norm_mul_le _ _)

/-- The physical residual profile in the proof of Theorem 4.2, including rounded switches. -/
theorem unitPhysicalResidual_profile_bound [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, ‖Hd u - Hd s‖ ≤ M * |u - s|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T T H hH w) :
    let τ := t - clock t
    let c₀ := frameBound w-frameBound (w/2)/2
    ‖unitPhysicalResidual T H Hd hH t‖ ≤
      (1 / (T : ℝ)^2) * (M*τ^2/2+|τ| * (c₀+τ^2/2)*L^2) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hs : t / T ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hTr.le, (div_le_one hTr).mpr ht.2⟩
  have hq := sample_mem (N := T) hs
  simp only [sample, mul_div_cancel₀ _ hTr.ne'] at hq
  have hlocal := local_taylor_chain hTr.le hTr hd hl hq
    (show ((clock t : ℝ) + (t - clock t)) / T ∈ Icc (0 : ℝ) 1 by
      convert hs using 1; congr 1; ring)
  have hshift := intervalIntegral.integral_comp_add_right
    (fun σ ↦ (1 / T : ℝ) • Hd (σ / T) - (1 / T : ℝ) • Hd ((clock t : ℝ) / T))
    (clock t : ℝ) (a := 0) (b := t - clock t)
  simp only [zero_add, sub_add_cancel] at hshift
  have hscale : (T : ℝ) / (T : ℝ)^2 = 1 / T := by field_simp
  have hi : ‖∫ σ in (clock t : ℝ)..t, (1 / T : ℝ) • Hd (σ / T) -
      (1 / T : ℝ) • Hd ((clock t : ℝ) / T)‖ ≤
      M / (T : ℝ)^2 * ((t - clock t)^2 / 2) := by
    rw [← hshift]
    have hb := hlocal.1.symm.trans_le (hlocal.2.1.trans_eq hlocal.2.2)
    simp only [hscale, add_comm (clock t : ℝ)] at hb
    exact hb.trans_eq (by field_simp)
  have hK : ‖H (t / T) - H ((clock t : ℝ) / T)‖ ≤ L / T * |t - clock t| := by
    have hb := (uniform_local_bounds (N := T) hTr.le H Hd hd hbd hl hq hs).1
    rw [← sub_div, abs_div, abs_of_pos hTr] at hb
    exact hb.trans_eq (by ring)
  have hclock := clock_bounds (N := T) hs
  simp only [mul_div_cancel₀ _ hTr.ne'] at hclock
  have hy := uniform_corrector_norm_LM hTr.le T H Hd hH hw hwidth
    hclock (hbd _ hq) (t := t - clock t)
  simp only [hscale] at hy
  have hL : 0 ≤ L := (norm_nonneg _).trans (hbd _ hs)
  have hsplit := unitPhysicalResidual_integral_product_bound hT H Hd hH hd
    (continuousOn_of_norm_sub_le hl) ht
  apply hsplit.trans
  have hprod := mul_le_mul hK hy (norm_nonneg _) (by positivity : 0 ≤ L / T * |t - clock t|)
  exact (add_le_add hi hprod).trans_eq (by field_simp)

/-- The physical residual is the normalized residual divided by duration;
its integral over any physical interval equals the corresponding normalized integral. -/
theorem uniform_physical_residual_integral {N : ℕ}
    (R : ℝ → 𝕄) (a b : ℝ) :
    (∫ t in a..b, ‖(1 / N : ℝ) • R (t / N)‖) =
      ∫ s in a / N..b / N, ‖R s‖ := by
  simp only [norm_smul_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹), one_div]
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul]
  exact intervalIntegral.inv_smul_integral_comp_div (fun s ↦ ‖R s‖) N

/-- Changing from normalized time to physical time preserves the residual integral. -/
theorem unitPhysicalResidual_integral {T : ℕ} (hT : 0 < T) (H Hd : ℝ → 𝕄)
    (hH : IsTimeDepHamiltonian H) :
    (∫ t in (0 : ℝ)..T, ‖unitPhysicalResidual T H Hd hH t‖) =
      ∫ s in (0 : ℝ)..1,
        ‖uniformPieceResidual T T H (uniformCorrectionPiece T T H Hd hH) s‖ := by
  have ht : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  simpa only [unitPhysicalResidual, zero_div, div_self ht] using
    uniform_physical_residual_integral (N := T)
      (uniformPieceResidual T T H (uniformCorrectionPiece T T H Hd hH)) 0 T


/-- Theorem 4.2: integrate the physical residual bound through the explicit
cell split and then evaluate the three moments. The norm integral remains in physical time; the
accompanying normalized
integrability statements feed the already established comparison identity. -/
theorem unit_residual_integral [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {L M : ℝ} (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ L)
    (hl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, ‖Hd u - Hd s‖ ≤ M * |u - s|)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T T H hH w) :
    let R := uniformPieceResidual T T H (uniformCorrectionPiece T T H Hd hH)
    let c₀ := frameBound w-frameBound (w/2)/2
    IntervalIntegrable R volume 0 1 ∧
    IntervalIntegrable (fun s ↦ ‖R s‖) volume 0 1 ∧
    (∫ t in (0 : ℝ)..T, ‖unitPhysicalResidual T H Hd hH t‖) ≤
      (T : ℝ)/(T : ℝ)^2 * (M/24+(c₀/4+1/64)*((T : ℝ)/T)*L^2) := by
  intro R c₀
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  rw [unitPhysicalResidual_integral hT H Hd hH]
  apply uniform_residual_integral_of_profile hT R
    (uniform_aestronglyMeasurable_pieceResidual T T H Hd hH
      (HasDerivWithinAt.continuousOn hd)) L M c₀
  intro s hs _hregular
  have ht : (T : ℝ)*s ∈ Icc (0 : ℝ) T :=
    ⟨mul_nonneg hTr.le hs.1, (mul_le_mul_of_nonneg_left hs.2 hTr.le).trans_eq (mul_one _)⟩
  have hp := unitPhysicalResidual_profile_bound hT H Hd hH hd hbd hl ht hw hwidth
  dsimp only at hp
  have hb := mul_le_mul_of_nonneg_left hp hTr.le
  simp only [unitPhysicalResidual, mul_div_cancel_left₀ _ hTr.ne',
    norm_smul_of_nonneg (by positivity : 0 ≤ (1 / T : ℝ)),
    ← mul_assoc, mul_one_div_cancel hTr.ne', one_mul] at hb
  exact hb.trans_eq (by dsimp only [c₀]; field_simp)

/-- **Theorem 4.2 residual computation** (`thm:clocks`): the residual of the correction in
Section 4, integrated in physical time. The derivative norm is its supremum
on `[0,1]`; the only derivative hypothesis is the Lipschitz bound `h`.
The proof uses the explicit residual integrand, the rounded half-interval split,
and the three moments from Lemma A.1(ii). -/
theorem cor_residual [NeZero d] {T : ℕ} (hT : 0 < T)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    {h w : ℝ}
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|)
    (hw : w < 2 * π) (hwidth : AllSampleWidth T T H hH w) :
    let c₀ := frameBound w - frameBound (w / 2) / 2
    let c₁ := c₀ / 4 + 1 / 64
    (∫ t in (0 : ℝ)..T, ‖unitPhysicalResidual T H Hd hH t‖) ≤
      (1 / T : ℝ) * (h / 24 + c₁ * unitSupNorm Hd ^ 2) := by
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ unitSupNorm Hd :=
    fun _ hs ↦ norm_le_unitSupNorm (continuousOn_of_norm_sub_le hlip) hs
  have hres := (unit_residual_integral hT H Hd hH hd hbd hlip hw hwidth).2.2
  have ht : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  dsimp only at hres ⊢
  exact hres.trans_eq (by field_simp)

/-- At every switch the jump is the difference of the spectral endpoint values,
with the common scale extracted exactly. -/
theorem uniformCorrectionPiece_jump_frame (T : ℝ) (N : ℕ)
    (H Hd : ℝ → 𝕄) (hH : IsTimeDepHamiltonian H)
    {w : ℝ} (hw : w < 2 * π) (hwidth : AllSampleWidth T N H hH w)
    {j : ℤ} (hj : 1 ≤ j) (hjN : j ≤ (N : ℤ)) :
    let Yr := allSampleCorrectorFamily T N H Hd hH
    let Yb := fun s ↦ frameOp ((T / N) • H s) (Hd s)
    Yr j (-(1/2)) - Yr (j - 1) (1/2) = (T/(N:ℝ)^2) •
      (Yb (((j:ℤ):ℝ)/N) - Yb (((j - 1):ℝ)/N)) := by
  intro Yr Yb
  dsimp only [Yr]
  rw [(allSampleCorrectorFamily_end_values T N H Hd hH hw hwidth (by omega :
    0 ≤ j ∧ j ≤ (N : ℤ))).1,
    (allSampleCorrectorFamily_end_values T N H Hd hH hw hwidth (by omega :
    0 ≤ (j - 1) ∧ (j - 1) ≤ (N : ℤ))).2]
  change (exponentialOperators _ _ _).2.2.1 - (exponentialOperators _ _ _).2.2.1 = _
  rw [← frameOp_eq_paper_value _ hw (hwidth _ (by omega)),
    ← frameOp_eq_paper_value _ hw (hwidth _ (by omega))]
  simp only [Yb, frameOp, ContinuousLinearMap.map_smul_of_tower, ← smul_sub,
    Int.cast_sub, Int.cast_one]

end UnitaryProducts.PaperProof
