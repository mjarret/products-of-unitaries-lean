/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.UniformTruncation
public import UnitaryProducts.PaperProof.ThmUnitStepsMax
public import UnitaryProducts.PaperProof.WalkCutFormula
public import UnitaryProducts.PaperProof.RotatingFrame
public import UnitaryProducts.Prose.FineSteps

/-! # Centering and the exact sample error in the unit-step theorem -/

@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts UnitaryProducts.Corrector UnitaryProducts.Paper
open UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The two products are endpoints of their piecewise-constant evolutions
by equation `eq:piecewise-product`. Duhamel's bound on `[0,T]`, split into
its `T` unit intervals, counts precisely the sampled generators in the product. -/
theorem unitProduct_sample_error_chain {H A : ℝ → 𝕄} (T : ℕ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, (A s).IsHermitian) :
    ‖(unitProduct A T).1 - (unitProduct H T).1‖ ≤
        (∫ t in (0 : ℝ)..T, ‖H ((⌊t⌋ : ℝ) / T) - A ((⌊t⌋ : ℝ) / T)‖) ∧
      (∫ t in (0 : ℝ)..T, ‖H ((⌊t⌋ : ℝ) / T) - A ((⌊t⌋ : ℝ) / T)‖) =
        ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [unitProduct, pieceProduct]
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  let K := fun (B : ℝ → 𝕄) (t : ℝ) ↦ B ((⌊t⌋ : ℝ) / T)
  have hpieces (B : ℝ → 𝕄) (j : ℕ) (_hj : j < T)
      (t : ℝ) (hmem : t ∈ Ioo (j : ℝ) (j + 1 : ℕ)) :
      K B t = B ((j : ℝ) / T) := by
    have hf : ⌊t⌋ = (j : ℤ) := by
      apply Int.floor_eq_iff.mpr
      simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] using
        (show (j : ℝ) ≤ t ∧ t < ((j + 1 : ℕ) : ℝ) from ⟨hmem.1.le, hmem.2⟩)
    simp only [K, hf, Int.cast_natCast]
  have hr (B : ℝ → 𝕄) : IsRegulated (K B) 0 T := by
    simpa only [Nat.cast_zero] using
      piecewise_regulated (K B) (fun j : ℕ ↦ (j : ℝ)) (fun j ↦ B ((j : ℝ) / T)) T
        (hpieces B)
  have hprod (B : ℝ → 𝕄) :
      pieceProduct (scheduleDuration (fun j : ℕ ↦ (j : ℝ)) T)
        (fun j ↦ B ((j : ℝ) / T)) T = (unitProduct B T).1 := by
    have hacc : ∀ n ≤ T,
        pieceProduct (scheduleDuration (fun j : ℕ ↦ (j : ℝ)) T)
          (fun j ↦ B ((j : ℝ) / T)) n =
        pieceProduct (fun _ ↦ 1) (fun j ↦ B ((j : ℝ) / T)) n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        simp only [pieceProduct, scheduleDuration, if_pos (show n < T by omega),
          Nat.cast_add, Nat.cast_one, add_sub_cancel_left, ih (by omega)]
    exact hacc T le_rfl
  have hexists (B : ℝ → 𝕄) (hB : ∀ s ∈ Icc (0 : ℝ) 1, (B s).IsHermitian) :
      ∃ U, IsEvolution (K B) U 0 T ∧ (unitProduct B T).1 = U T := by
    have hKB : ∀ t ∈ Icc (0 : ℝ) T, (K B t).IsHermitian := by
      intro t htmem
      apply hB
      refine ⟨div_nonneg ?_ ht.le, (div_le_one ht).mpr ((Int.floor_le t).trans htmem.2)⟩
      exact_mod_cast Int.floor_nonneg.mpr htmem.1
    obtain ⟨U, hU, he⟩ := Prose.pieceProduct_eq_evolution_of_pieces ht hKB T
      (fun j : ℕ ↦ (j : ℝ)) ⟨fun _ _ h ↦ Nat.cast_le.mpr h, by simp, rfl⟩
      (fun j ↦ B ((j : ℝ) / T))
      (fun j hj ↦ hB _ (walkCubic_sample hj.le)) (hpieces B)
    exact ⟨U, hU, (hprod B).symm.trans he⟩
  obtain ⟨U, hU, heU⟩ := hexists H hH
  obtain ⟨V, hV, heV⟩ := hexists A hA
  have hb := duhamel_bound ht.le (hr H) (hr A) hU hV
  have hi := ((hr H).intervalIntegrable_on ht.le).sub ((hr A).intervalIntegrable_on ht.le)
  have hicell (j : ℕ) (hj : j < T) :
      IntervalIntegrable (fun t ↦ ‖K H t - K A t‖) volume (j : ℝ) (j + 1 : ℕ) := by
    apply hi.norm.mono_set
    rw [uIcc_of_le (by exact_mod_cast Nat.le_succ j), uIcc_of_le ht.le]
    exact Icc_subset_Icc (Nat.cast_nonneg j) (Nat.cast_le.mpr hj)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hicell
  simp only [Nat.cast_zero] at hsplit
  refine ⟨?_, hsplit.symm.trans ?_⟩
  · simpa only [heV, heU] using hb
  apply Finset.sum_congr rfl
  intro j hj
  have hjT := Finset.mem_range.mp hj
  calc
    (∫ t in (j : ℝ)..(j + 1 : ℕ), ‖K H t - K A t‖) =
        ∫ _t in (j : ℝ)..(j + 1 : ℕ), ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne ((j + 1 : ℕ) : ℝ)] with t hne
      intro hmem
      rw [uIoc_of_le (by exact_mod_cast Nat.le_succ j)] at hmem
      have hcell : t ∈ Ioo (j : ℝ) (j + 1 : ℕ) :=
        ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩
      rw [hpieces H j hjT t hcell, hpieces A j hjT t hcell]
    _ = ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by simp

/-- The sample sum bound is the last line of the Duhamel chain in the proof
of Theorem 4.2. Both the integral inequality and its cell sum appear above. -/
theorem unitProduct_sample_error {H A : ℝ → 𝕄} (T : ℕ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, (A s).IsHermitian) :
    ‖(unitProduct A T).1 - (unitProduct H T).1‖ ≤
      ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
  obtain ⟨hduhamel, hsum⟩ := unitProduct_sample_error_chain T hH hA
  exact hduhamel.trans_eq hsum

/-- The single triangle-inequality display in the unit-step comparison, after unitary invariance. -/
theorem unitProduct_truncation_split {H A : ℝ → 𝕄} (T : ℕ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) (X : 𝕄) :
    ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - X‖ ≤
      ‖(unitProduct A T).1 - (unitProduct H T).1‖ +
        ‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - X‖ := by
  rw [← uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num)),
    ← uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- Insert the exact unit-step product while leaving its two endpoint phases
fixed; the additional error is the sum over `j < T`. -/
theorem unitProduct_truncation_comparison {H A : ℝ → 𝕄} (T : ℕ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hA : ∀ s ∈ Icc (0 : ℝ) 1, (A s).IsHermitian) (X : 𝕄) {B : ℝ}
    (hB : ‖(unitProduct H T).1 - evol (H 1) (-(1 / 2)) * X * evol (H 0) (1 / 2)‖ ≤ B) :
    ‖evol (H 1) (1 / 2) * (unitProduct A T).1 * evol (H 0) (-(1 / 2)) - X‖ ≤
      B + ∑ j ∈ Finset.range T, ‖H ((j : ℝ) / T) - A ((j : ℝ) / T)‖ := by
  have hsplit := unitProduct_truncation_split (A := A) T hH X
  have hexact := hB
  rw [uniform_phase_error_norm _ _ _ _ (hH 0 (by norm_num)) (hH 1 (by norm_num))] at hexact
  exact hsplit.trans ((add_le_add (unitProduct_sample_error T hH hA) hexact).trans_eq (add_comm _
    _))

/-- The paper's centered derivative bound, as the infimum of the attained
maximum norms over constant real scalar shifts. The next theorem proves attainment. -/
def unitCenteredNorm (D : ℝ → 𝕄) : ℝ :=
  sInf (Set.range fun b : ℝ ↦ unitSupNorm (fun s ↦ D s - b • (1 : 𝕄)))


/-- The maximum over the compact time interval is Lipschitz in the scalar shift. -/
theorem unitSupNorm_shift_lipschitz [NeZero d] {D : ℝ → 𝕄}
    (hD : ContinuousOn D (Icc (0 : ℝ) 1)) :
    LipschitzWith 1 (fun b : ℝ ↦ unitSupNorm (fun s ↦ D s - b • (1 : 𝕄))) := by
  have hmax (b : ℝ) := exists_norm_eq_unitSupNorm
    (hD.sub (continuousOn_const (c := b • (1 : 𝕄))))
  have hle (a b : ℝ) :
      unitSupNorm (fun s ↦ D s - a • (1 : 𝕄)) ≤
        unitSupNorm (fun s ↦ D s - b • (1 : 𝕄)) + |a - b| := by
    obtain ⟨s, hs, he⟩ := hmax a
    rw [← he]
    calc
      _ ≤ ‖D s - b • (1 : 𝕄)‖ + ‖(b - a) • (1 : 𝕄)‖ := by
        convert norm_add_le (D s - b • (1 : 𝕄)) ((b - a) • (1 : 𝕄)) using 1
        simp [sub_smul, sub_add_sub_cancel]
      _ ≤ _ := by
        simpa [norm_smul, abs_sub_comm] using add_le_add_right
          (norm_le_unitSupNorm (hD.sub continuousOn_const) hs) |a - b|
  apply LipschitzWith.of_le_add
  simpa only [Real.dist_eq] using hle

/-- The coercive lower bound for the scalar-centering objective in Theorem 4.2.
Together with its Lipschitz continuity, this confines a minimizer to a compact interval. -/
theorem unitSupNorm_shift_lower [NeZero d] {D : ℝ → 𝕄}
    (hD : ContinuousOn D (Icc (0 : ℝ) 1)) (b : ℝ) :
    |b| - unitSupNorm D ≤ unitSupNorm (fun s ↦ D s - b • (1 : 𝕄)) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hbase := norm_le_unitSupNorm hD h0
  have hshift := norm_le_unitSupNorm (hD.sub (continuousOn_const (c := b • (1 : 𝕄)))) h0
  have htriangle : |b| ≤ ‖D 0‖ + ‖D 0 - b • (1 : 𝕄)‖ := by
    simpa [norm_smul] using norm_sub_le (D 0) (D 0 - b • (1 : 𝕄))
  linarith

/-- A continuous matrix path attains the scalar minimum defining `L`, and
its centered norm is at most the uncentered maximum. -/
theorem unitCenteredNorm_attained {D : ℝ → 𝕄}
    (hD : ContinuousOn D (Icc (0 : ℝ) 1)) :
    (∃ b : ℝ, unitSupNorm (fun s ↦ D s - b • (1 : 𝕄)) = unitCenteredNorm D) ∧
      0 ≤ unitCenteredNorm D ∧ unitCenteredNorm D ≤ unitSupNorm D := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp [unitCenteredNorm, unitSupNorm, hz]
  letI : NeZero d := ⟨hd.ne'⟩
  let f : ℝ → ℝ := fun b ↦ unitSupNorm (fun s ↦ D s - b • (1 : 𝕄))
  have hf : Continuous f := (unitSupNorm_shift_lipschitz hD).continuous
  have hmax (b : ℝ) := exists_norm_eq_unitSupNorm
    (hD.sub (continuousOn_const (c := b • (1 : 𝕄))))
  have hnonneg (b : ℝ) : 0 ≤ f b := by
    obtain ⟨s, hs, he⟩ := hmax b
    exact (norm_nonneg _).trans_eq he
  have hf0 : f 0 = unitSupNorm D := by simp [f]
  let R := 2 * f 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [hnonneg 0]
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩) hf.continuousOn
  have hglobal (c : ℝ) : f b ≤ f c := by
    by_cases hc : c ∈ Icc (-R) R
    · exact hmin hc
    have hRabs : R ≤ |c| := le_of_not_ge (fun h ↦ hc (abs_le.mp h))
    have hlower := unitSupNorm_shift_lower hD c
    rw [← hf0] at hlower
    have hb0 : f b ≤ f 0 := hmin (by constructor <;> linarith)
    dsimp [R] at hRabs
    linarith
  have he : f b = unitCenteredNorm D := by
    have hleast : IsLeast (Set.range f) (f b) :=
      ⟨⟨b, rfl⟩, by rintro _ ⟨c, rfl⟩; exact hglobal c⟩
    exact hleast.csInf_eq.symm
  exact ⟨⟨b, he⟩, he ▸ hnonneg b, he ▸ (hglobal 0).trans_eq hf0⟩

/-- Subtracting a real scalar translates the full Hermitian spectrum.
In particular all eigenvalue differences are preserved. -/
theorem scalar_shift_eigenvalues {H : 𝕄} (hH : H.IsHermitian) (b : ℝ)
    (hB : (H - b • (1 : 𝕄)).IsHermitian) :
    Set.range hB.eigenvalues = (fun x : ℝ ↦ x - b) '' Set.range hH.eigenvalues := by
  rw [← hB.spectrum_real_eq_range_eigenvalues, ← hH.spectrum_real_eq_range_eigenvalues,
    ← Set.sub_singleton, spectrum.sub_singleton_eq, Algebra.algebraMap_eq_smul_one]

/-- A real scalar shift is Hermitian and preserves the bound on every
eigenvalue difference, using the translated spectrum. -/
theorem scalar_shift_sample_width {H : 𝕄} (hH : H.IsHermitian)
    {w : ℝ} (hwidth : ∀ p q, |hH.eigenvalues p - hH.eigenvalues q| ≤ w) (b : ℝ) :
    ∃ hB : (H - b • (1 : 𝕄)).IsHermitian,
      ∀ p q, |hB.eigenvalues p - hB.eigenvalues q| ≤ w := by
  have hB := hH.sub (Separation.isHermitian_real_smul
    (show (1 : 𝕄).IsHermitian from Matrix.isHermitian_one) b)
  have hr := scalar_shift_eigenvalues hH b hB
  refine ⟨hB, fun p q ↦ ?_⟩
  have hp : hB.eigenvalues p ∈ (fun x : ℝ ↦ x - b) '' Set.range hH.eigenvalues :=
    hr ▸ Set.mem_range_self p
  have hq : hB.eigenvalues q ∈ (fun x : ℝ ↦ x - b) '' Set.range hH.eigenvalues :=
    hr ▸ Set.mem_range_self q
  obtain ⟨x, ⟨i, rfl⟩, hi⟩ := hp
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := hq
  rw [← hi, ← hj, sub_sub_sub_cancel_right]
  exact hwidth i j

/-- The canonical end-value operator sends the identity to `1/12` times the
identity: only equal-eigenvalue entries survive in its eigenbasis formula. -/
theorem frameOp_one {H : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw : w < 2 * π) (hwidth : ∀ p q, |hH.eigenvalues p - hH.eigenvalues q| ≤ w) :
    frameOp H (1 : 𝕄) = (1 / 12 : ℂ) • (1 : 𝕄) := by
  rw [frameOp_eq_eigenbasis hH hw (eigen_interval hH hwidth)]
  have hu : star (hH.eigenvectorUnitary : 𝕄) * (hH.eigenvectorUnitary : 𝕄) = 1 :=
    Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have he : Matrix.of (fun a b ↦
      (frameMult (hH.eigenvalues a - hH.eigenvalues b) : ℂ) *
        (star (hH.eigenvectorUnitary : 𝕄) * (1 : 𝕄) * hH.eigenvectorUnitary) a b) =
      (1 / 12 : ℂ) • (1 : 𝕄) := by
    rw [mul_one, hu]
    ext p q
    by_cases hpq : p = q
    · subst q; simp [frameMult]
    · simp [hpq]
  rw [he, mul_smul_comm, smul_mul_assoc, mul_one,
    ← Unitary.coe_star, Unitary.coe_mul_star_self hH.eigenvectorUnitary]

/-- Centering the derivative subtracts the constant `b/12` from every
canonical end value. Thus adjacent-sample increments are unchanged. -/
theorem frameOp_centered {H D : 𝕄} (hH : H.IsHermitian) {w : ℝ}
    (hw : w < 2 * π) (hwidth : ∀ p q, |hH.eigenvalues p - hH.eigenvalues q| ≤ w)
    (a b : ℝ) :
    frameOp (H - a • (1 : 𝕄)) (D - b • (1 : 𝕄)) =
      frameOp H D - (b / 12 : ℝ) • (1 : 𝕄) := by
  have had : frameOp (H - a • (1 : 𝕄)) (D - b • (1 : 𝕄)) =
      frameOp H (D - b • (1 : 𝕄)) := by
    simpa only [Complex.coe_smul] using frameOp_sub_smul_one H (a : ℂ) (D - b • (1 : 𝕄))
  rw [had]
  change frameSeries (I • adL H) (D - b • (1 : 𝕄)) = _
  rw [map_sub, ContinuousLinearMap.map_smul_of_tower]
  change frameOp H D - b • frameOp H (1 : 𝕄) = _
  rw [frameOp_one hH hw hwidth]
  congr 1
  simp only [← Complex.coe_smul, smul_smul, Complex.ofReal_div, Complex.ofReal_ofNat,
    mul_one_div]

/-- The variation `Σ_T` is invariant under the linear scalar centering used
in the proof of Theorem 4.2. -/
theorem centered_sigma (H D : ℝ → 𝕄) (T : ℕ) (b : ℝ) {w : ℝ}
    (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hwidth : ∀ j : ℕ, ∀ hj : j ≤ T, ∀ p q,
      |(hH _ (walkCubic_sample hj)).eigenvalues p -
        (hH _ (walkCubic_sample hj)).eigenvalues q| ≤ w) :
    (∑ j ∈ Finset.range T,
      ‖frameOp (H ((j + 1 : ℕ) / T) - (b * ((j + 1 : ℕ) / T)) • (1 : 𝕄))
          (D ((j + 1 : ℕ) / T) - b • (1 : 𝕄)) -
        frameOp (H ((j : ℝ) / T) - (b * ((j : ℝ) / T)) • (1 : 𝕄))
          (D ((j : ℝ) / T) - b • (1 : 𝕄))‖) =
      ∑ j ∈ Finset.range T,
        ‖frameOp (H ((j + 1 : ℕ) / T)) (D ((j + 1 : ℕ) / T)) -
          frameOp (H ((j : ℝ) / T)) (D ((j : ℝ) / T))‖ := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjT : j < T := Finset.mem_range.mp hj
  rw [frameOp_centered (hH _ (walkCubic_sample (show j + 1 ≤ T by omega))) hw
    (hwidth _ (by omega)),
    frameOp_centered (hH _ (walkCubic_sample (show j ≤ T by omega))) hw
    (hwidth _ (by omega)), sub_sub_sub_cancel_right]

/-- The signed rounding error has period one. -/
theorem signed_clock_error_periodic :
    Function.Periodic (fun x : ℝ ↦ (UnitStepsProse.clock x : ℝ) - x) 1 := by
  intro x
  simp only [UnitStepsProse.clock, ← round_eq, round_add_one, Int.cast_add,
    Int.cast_one, add_sub_add_right_eq_sub]

/-- The signed rounding error is integrable on every bounded interval. -/
theorem signed_clock_error_integrable (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ (UnitStepsProse.clock x : ℝ) - x) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ ↦ (1 / 2 : ℝ)) volume a b).mono_fun'
  · have hm : Measurable (fun x : ℝ ↦ (UnitStepsProse.clock x : ℝ) - x) := by
      unfold UnitStepsProse.clock; fun_prop
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using UnitStepsProse.abs_clock_sub_le x

/-- The signed error integrates to zero over one rounded-clock period. -/
theorem signed_clock_error_mean_zero :
    (∫ x in (0 : ℝ)..1, (UnitStepsProse.clock x : ℝ) - x) = 0 := by
  have hp := signed_clock_error_periodic.intervalIntegral_add_eq 0 (-1 / 2)
  norm_num at hp
  rw [hp]
  have he : (∫ x in (-1 / 2 : ℝ)..(1 / 2), (UnitStepsProse.clock x : ℝ) - x) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), -x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hx
    intro hmem
    rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hmem
    have hq : UnitStepsProse.clock x = 0 := by
      rw [UnitStepsProse.clock, Int.floor_eq_iff]
      norm_num
      constructor <;> linarith [hmem.1, hmem.2, lt_of_le_of_ne hmem.2 hx]
    simp [hq]
  rw [show (-(1 / 2) : ℝ) = -1 / 2 by ring, he, intervalIntegral.integral_neg, integral_id]
  norm_num

/-- Equation (4.2): the rounded and ordinary clocks have the same integral
at an integer endpoint, which is precisely the phase cancellation under centering. -/
theorem integral_rounded_clock (T : ℕ) :
    (∫ x in (0 : ℝ)..(T : ℝ), (UnitStepsProse.clock x : ℝ)) = (T : ℝ) ^ 2 / 2 := by
  have hp := signed_clock_error_periodic.intervalIntegral_add_zsmul_eq (T : ℤ) 0
    signed_clock_error_integrable
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one,
    signed_clock_error_mean_zero, mul_zero] at hp
  have hid : IntervalIntegrable (fun x : ℝ ↦ x) volume 0 T :=
    continuous_id.intervalIntegrable 0 T
  have hclock := (signed_clock_error_integrable 0 T).add hid
  have he : (fun x : ℝ ↦ ((UnitStepsProse.clock x : ℝ) - x) + x) =
      fun x ↦ (UnitStepsProse.clock x : ℝ) := by funext x; ring
  rw [he] at hclock
  rw [intervalIntegral.integral_sub hclock hid, integral_id] at hp
  norm_num at hp
  linarith


/-- The rounded clock is monotone, so its discontinuity set is countable. -/
theorem rounded_clock_monotone : Monotone (fun t : ℝ ↦ (UnitStepsProse.clock t : ℝ)) := by
  intro x y hxy
  change ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ ((⌊y + 1 / 2⌋ : ℤ) : ℝ)
  exact Int.cast_le.mpr (Int.floor_mono (show x + 1 / 2 ≤ y + 1 / 2 by linarith))

/-- The integral of the rounded clock is continuous and has derivative `q`
away from a countable set. This is the scalar phase used in centering. -/
theorem rounded_clock_primitive_regular (T : ℕ) :
    ContinuousOn (fun t : ℝ ↦ ∫ u in (0 : ℝ)..t, (UnitStepsProse.clock u : ℝ))
      (Icc 0 T) ∧
    ∃ E : Set ℝ, E.Countable ∧ ∀ t ∈ Ioo (0 : ℝ) T, t ∉ E →
      HasDerivAt (fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, (UnitStepsProse.clock u : ℝ))
        (UnitStepsProse.clock t : ℝ) t := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ (UnitStepsProse.clock t : ℝ)) volume 0 T := by
    have hh := (signed_clock_error_integrable 0 T).add
      (continuous_id.intervalIntegrable (μ := volume) (0 : ℝ) (T : ℝ))
    simpa only [id_eq, sub_add_cancel] using hh
  let E := {t : ℝ | ¬ ContinuousAt (fun x : ℝ ↦ (UnitStepsProse.clock x : ℝ)) t}
  have hE : E.Countable := rounded_clock_monotone.countable_not_continuousAt
  refine ⟨(intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc).mono
    Icc_subset_uIcc, E, hE, fun t ht hn ↦ ?_⟩
  have hc : ContinuousAt (fun x : ℝ ↦ (UnitStepsProse.clock x : ℝ)) t := not_not.mp hn
  exact intervalIntegral.integral_hasDerivAt_right
    (hi.mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioo_subset_Icc_self ht))))
    ⟨Ioc 0 T, Ioc_mem_nhds ht.1 ht.2, hi.1.aestronglyMeasurable⟩ hc

/-- Subtracting `b*s` from the path leaves the terminal distance of the
continuous and rounded evolutions unchanged. -/
theorem centered_evolution_pair {H U V : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) (b : ℝ) :
    ∃ Ub Vb : ℝ → 𝕄,
      IsEvolution (fun t ↦ H (t / T) - (b * (t / T)) • (1 : 𝕄)) Ub 0 T ∧
      IsEvolution (fun t ↦ H (sample T (t / T)) -
        (b * sample T (t / T)) • (1 : 𝕄)) Vb 0 T ∧
      ‖Vb T - Ub T‖ = ‖V T - U T‖ ∧
      ∀ t, Vb t = Complex.exp (((b / T *
        ∫ u in (0 : ℝ)..t, (UnitStepsProse.clock u : ℝ) : ℝ) : ℂ) * I) • V t := by
  have ht : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  let φ : ℝ → ℝ := fun t ↦ (b / T) * (t ^ 2 / 2)
  let ψ : ℝ → ℝ := fun t ↦ (b / T) * ∫ u in (0 : ℝ)..t, (UnitStepsProse.clock u : ℝ)
  let Ub := fun t ↦ Complex.exp ((φ t : ℂ) * I) • U t
  let Vb := fun t ↦ Complex.exp ((ψ t : ℂ) * I) • V t
  have hφd (t : ℝ) : HasDerivAt φ (b * (t / T)) t := by
    convert (((hasDerivAt_id t).pow 2).div_const 2).const_mul (b / T) using 1
    dsimp [φ]
    ring
  have hφc : ContinuousOn φ (Icc (0 : ℝ) T) := by dsimp [φ]; fun_prop
  have hUb := scalar_phase_evolution hU hφc (by simp [φ]) ∅ countable_empty
    (fun t _ _ ↦ hφd t)
  obtain ⟨hqc, E, hE, hqd⟩ := rounded_clock_primitive_regular T
  have hψc : ContinuousOn ψ (Icc (0 : ℝ) T) := continuousOn_const.mul hqc
  have hs (t : ℝ) : sample T (t / T) = (UnitStepsProse.clock t : ℝ) / T := by
    simp only [sample, show (T : ℝ) * (t / T) = t by field_simp]
  have hψd (t : ℝ) (htm : t ∈ Ioo (0 : ℝ) T) (hn : t ∉ E) :
      HasDerivAt ψ (b * sample T (t / T)) t := by
    convert (hqd t htm hn).const_mul (b / T) using 1
    rw [hs]
    ring
  have hVb := scalar_phase_evolution hV hψc (by simp [ψ]) E hE hψd
  refine ⟨Ub, Vb, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · simpa only [Complex.coe_smul] using hUb
  · simpa only [Complex.coe_smul] using hVb
  · have he : ψ T = φ T := by dsimp [ψ, φ]; rw [integral_rounded_clock]
    dsimp [Ub, Vb]
    rw [he]
    exact phase_distance (φ T) (V T) (U T)

end UnitaryProducts.PaperProof
