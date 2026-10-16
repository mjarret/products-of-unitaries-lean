/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.ExactCorrection
public import UnitaryProducts.PaperProof.CorProducts
public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.Walks.BandMultiplicity

/-!
# Explicit conclusions supporting the paper's prose

Finite held samples, Hermitian sample replacement, nonresonance, inclusive
neighboring corrections, jumps of regulated functions, and the moving free arc.
-/

@[expose] public section
open scoped Matrix.Norms.L2Operator Topology
open Complex Real Set Filter MeasureTheory Matrix
open UnitaryProducts UnitaryProducts.Paper UnitaryProducts.Corrector UnitaryProducts.Dressed
noncomputable section
namespace UnitaryProducts.Prose
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Section 1: holding the stored truncated midpoint sample on each open
partition interval is a piecewise-constant family. Values at nodes are unrestricted. -/
theorem midpoint_bit_truncation_piecewise (H : ℝ → 𝕄) (k n : ℕ)
    (s : ℕ → ℝ) (index : ℝ → Fin n) (hn : 0 < n)
    (hs : StrictMonoOn s (Iic n))
    (hindex : ∀ j (hj : j < n), ∀ t ∈ Ioo (s j) (s (j + 1)), index t = ⟨j, hj⟩) :
    (piecewiseData (fun t ↦ truncHerm k
      (H ((s (index t) + s ((index t : ℕ) + 1)) / 2))) (s 0) (s n)).1 := by
  refine ⟨n, s, (fun j ↦ truncHerm k (H ((s j + s (j + 1)) / 2))),
    hn, rfl, rfl, hs, ?_⟩
  intro j hj t ht
  dsimp only
  rw [hindex j hj t ht]

/-- Section 1: the midpoint comparison requires only Hermiticity of the
replacement samples, with their maximum sample error added to the oscillation. -/
theorem midpoint_error_of_hermitian_samples {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 T) (hU : IsEvolution H U 0 T)
    (n : ℕ) (t : ℕ → ℝ) (ht : (variationCheckpoints H T n).2.1 t)
    (G : ℕ → 𝕄) (hG : ∀ j < n, (G j).IsHermitian) :
    ‖pieceProduct (scheduleDuration t n) G n - U T‖ ≤
      (∑ j ∈ Finset.range n, ∫ x in t j..t (j + 1),
        ‖H x - H ((t j + t (j + 1)) / 2)‖) +
      T * ⨆ j : Fin n, ‖H ((t j + t (j + 1)) / 2) - G j‖ := by
  have hb := piecewise_product_error_le_integral hT hreg hU n t ht G hG
  let β := ⨆ i : Fin n, ‖H ((t i + t (i + 1)) / 2) - G i‖
  have hβ : ∀ j < n, ‖H ((t j + t (j + 1)) / 2) - G j‖ ≤ β := fun j hj ↦
    le_ciSup (f := fun i : Fin n ↦ ‖H ((t i + t (i + 1)) / 2) - G i‖)
      (Set.finite_range _).bddAbove ⟨j, hj⟩
  have hi : ∀ j < n, ∀ c : 𝕄,
      IntervalIntegrable (fun x ↦ ‖H x - c‖) volume (t j) (t (j + 1)) := fun j hj c ↦
    (((hreg.intervalIntegrable_on hT.le).mono_set (by
      rw [uIcc_of_le (ht.1 (Nat.le_succ j)), uIcc_of_le hT.le]
      exact Icc_subset_Icc (ht.2.1 ▸ ht.1 (Nat.zero_le j))
        (ht.2.2 ▸ ht.1 hj))).sub intervalIntegrable_const).norm
  have hsum : ∑ j ∈ Finset.range n, ∫ _x in t j..t (j + 1), β = T * β := by
    simp only [intervalIntegral.integral_const, smul_eq_mul, ← Finset.sum_mul,
      Finset.sum_range_sub, ht.2.1, ht.2.2, sub_zero]
  refine hb.trans ?_
  change _ ≤ _ + T * β
  rw [← hsum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  rw [← intervalIntegral.integral_add (hi j hj' _) intervalIntegrable_const]
  exact intervalIntegral.integral_mono_on (ht.1 (Nat.le_succ j)) (hi j hj' _)
    ((hi j hj' _).add intervalIntegrable_const) fun x _ ↦
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add le_rfl (hβ j hj'))

/-- Section 1: the arbitrary Hermitian sample replacement bound in the
paper's normalized path variable and physical evolution time `T`. -/
theorem path_midpoint_error_of_hermitian_samples {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T)
    (hreg : IsRegulated H 0 1)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (n : ℕ) (s : ℕ → ℝ) (hs : (variationCheckpoints H 1 n).2.1 s)
    (G : ℕ → 𝕄) (hG : ∀ j < n, (G j).IsHermitian) :
    ‖pieceProduct (scheduleDuration (fun j ↦ T * s j) n) G n - U T‖ ≤
      T * ((∑ j ∈ Finset.range n, ∫ x in s j..s (j + 1),
        ‖H x - H ((s j + s (j + 1)) / 2)‖) +
      ⨆ j : Fin n, ‖H ((s j + s (j + 1)) / 2) - G j‖) := by
  have hb := midpoint_error_of_hermitian_samples hT (regulated_rescale hT hreg)
    hU n (fun j ↦ T * s j) (checkpoints_rescale hT hs _) G hG
  have hm : ∀ j, (T * s j + T * s (j + 1)) / 2 / T =
      (s j + s (j + 1)) / 2 := fun j ↦ by field_simp
  rw [osc_rescale H hT n s] at hb
  simp only [hm] at hb
  rwa [mul_add]

/-- Section 1: a width bound leaves a uniform positive distance from every
nonzero multiple of `2π`, including both signs of the multiple. -/
theorem width_resonance_distance {x w : ℝ} (hw : w < 2 * π) (hx : |x| ≤ w)
    {m : ℤ} (hm : m ≠ 0) :
    0 < 2 * π - w ∧ 2 * π - w ≤ |x - 2 * π * m| := by
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  have hperiod : 2 * π ≤ |2 * π * (m : ℝ)| := by
    rw [abs_mul, abs_of_pos (mul_pos (by norm_num) pi_pos)]
    exact le_mul_of_one_le_right (by positivity) hm1
  have htriangle := abs_sub_le (2 * π * (m : ℝ)) x 0
  rw [sub_zero, sub_zero, abs_sub_comm] at htriangle
  exact ⟨sub_pos.mpr hw, by linarith⟩

/-- Section 1: the `O(T⁻²)` neighboring endpoint-value bound holds for
all neighboring samples, including the pairs `(0,1)` and `(T-1,T)`. -/
theorem adjacent_corrector_jump_le_inclusive [NeZero d] {H Hd : ℝ → 𝕄} {N : ℕ}
    (hN : 2 ≤ N) {w h : ℝ} (hw : w < 2 * π) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s)
    (hbd : ∀ s ∈ Icc (0 : ℝ) 1, ‖Hd s‖ ≤ h) (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Hd t - Hd s‖ ≤ h * |t - s|) (hdiff : ∀ j : ℕ, ∀ hj : j ≤ N, ∀ p q,
      |(hH _ (unit_sample_mem_le hj)).eigenvalues p -
        (hH _ (unit_sample_mem_le hj)).eigenvalues q| ≤ w) (j : ℕ) (hjN : j < N) :
    ‖frameOp (H ((j + 1 : ℕ) / N)) ((1 / N : ℝ) • Hd ((j + 1 : ℕ) / N)) -
      frameOp (H ((j : ℝ) / N)) ((1 / N : ℝ) • Hd ((j : ℝ) / N))‖ ≤
      (frameBound w * h + 2 * frameLip w * h ^ 2) / (N : ℝ) ^ 2 := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff j (by omega) (0 : Fin d) (0 : Fin d)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hs := unit_sample_mem_le (show j ≤ N by omega)
  have ht := unit_sample_mem_le (show j + 1 ≤ N by omega)
  have hh : 0 ≤ h := (norm_nonneg _).trans (hbd _ hs)
  have hwidth (k : ℕ) (hkN : k ≤ N) :
      ∃ z : ℝ, ‖H ((k : ℝ) / N) - (z : ℂ) • 1‖ ≤ w / 2 :=
    ⟨_, norm_sub_smul_one_le_of_eigenvalues (hH _ (unit_sample_mem_le hkN)) hw0
      (eigen_interval _ (hdiff k hkN))⟩
  obtain ⟨z, hz⟩ := hwidth j (by omega)
  obtain ⟨z', hz'⟩ := hwidth (j + 1) (by omega)
  have hstep : |((j + 1 : ℕ) : ℝ) / N - (j : ℝ) / N| = 1 / N := by
    rw [← sub_div, abs_div, abs_of_pos hNR]; push_cast; simp
  have hδ := norm_sub_le_of_derivWithin_le hd hbd _ hs _ ht
  have hD := hlip _ hs _ ht
  rw [hstep] at hδ hD
  have hb := norm_frameOp_sub_le
    (D := (1 / N : ℝ) • Hd ((j + 1 : ℕ) / N))
    (D' := (1 / N : ℝ) • Hd ((j : ℝ) / N)) hw hz' hz
  rw [← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hNR)] at hb
  have hB := frameBound_nonneg hw0
  have hL := frameLip_nonneg hw0
  calc _ ≤ frameBound w * ((1 / N) * ‖Hd ((j + 1 : ℕ) / N) - Hd ((j : ℝ) / N)‖) +
        2 * frameLip w * ((1 / N) * ‖Hd ((j : ℝ) / N)‖) *
          ‖H ((j + 1 : ℕ) / N) - H ((j : ℝ) / N)‖ := hb
    _ ≤ frameBound w * ((1 / N) * (h * (1 / N))) +
        2 * frameLip w * ((1 / N) * h) * (h * (1 / N)) := by
      gcongr
      exact hbd _ hs
    _ = _ := by ring


/-- Section 4.2: on the cell centered at the inclusive sample `j`, the
unit-step correction solves the stated equation with `Ω = H(j/T)` and
`D = H'(j/T)/T`, in the local variable `τ`. -/
theorem unit_sample_corrector_ode {T : ℕ} (hT : 0 < T) (H Hd : ℝ → 𝕄)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian) {j : ℤ}
    (hj : 0 ≤ j ∧ j ≤ (T : ℤ)) (τ : ℝ) :
    let Y := PaperProof.allSampleCorrectorFamily T T H Hd hH j
    HasDerivAt Y
      (τ • ((1 / T : ℝ) • Hd ((j : ℝ) / T)) -
        I • (H ((j : ℝ) / T) * Y τ - Y τ * H ((j : ℝ) / T))) τ := by
  have hTR : (T : ℝ) ≠ 0 := (Nat.cast_pos.mpr hT).ne'
  have hscale : (T : ℝ) / (T : ℝ) ^ 2 = 1 / T := by field_simp
  simpa only [div_self hTR, one_smul, hscale] using
    PaperProof.allSampleCorrectorFamily_ode T T H Hd hH hj τ

/-- Section 4.1: at nonzero resonance, equal endpoint values force the
forcing entry itself to vanish. -/
theorem scalar_corrector_resonant_forcing_zero {m : ℤ} (hm : m ≠ 0)
    (a : ℂ) (y : ℝ → ℂ)
    (hc : ContinuousOn y (Icc (-1 / 2 : ℝ) (1 / 2)))
    (hy : ∀ t ∈ Ioo (-1 / 2 : ℝ) (1 / 2), HasDerivAt y
      ((t : ℂ) * a - I * (2 * π * m : ℝ) * y t) t)
    (hp : y (1 / 2) = y (-1 / 2)) : a = 0 := by
  have hz := (scalar_corrector_resonant_obstruction hm a y hc hy hp).2
  have hden : ((2 * π * m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (Int.cast_ne_zero.mpr hm)
  have hfactor : -I * (-1 : ℂ)^m ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hden)).resolve_left hfactor

/-- Section 5: a continuous Hermitian logarithm with uniformly bounded
width below `2π` supplies a free arc of fixed positive length with a continuous
location, determined by the least eigenvalue of the logarithm. -/
theorem continuous_logarithm_gives_free_arc [NeZero d] (H W : ℝ → 𝕄)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContinuousOn H (Icc (0 : ℝ) 1)) {w : ℝ} (hw : w < 2 * π)
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w)
    (hlog : ∀ s ∈ Icc (0 : ℝ) 1, evol (H s) 1 = W s) :
    spectrumAvoidsOpenArc W (2 * π - w) (fun s ↦ spectralBottom (H s)) := by
  have hw0 : 0 ≤ w := by simpa using hwidth 0 (by norm_num) 0 0
  obtain ⟨ha, _, harc⟩ := PaperProof.hamiltonian_window_arc H hH hc hwidth
  have hunit : (walk W 1).1 := by
    intro s hs
    rw [← hlog s hs]
    exact star_evol_mul_self (hH s hs) 1
  apply (spectrumAvoidsOpenArc_iff_closedArc W (2 * π - w) _ hunit
    (sub_le_self _ hw0)).mpr
  refine ⟨sub_pos.mpr hw, ha, ?_⟩
  intro s hs z hz
  rw [← hlog s hs] at hz
  simpa only [sub_sub_cancel] using harc s hs z hz


/-- Section 2: a regulated Hermitian family can have an actual jump.
The two one-sided limits at `1/2` are the distinct matrices `0` and `1`. -/
theorem regulated_family_with_jump [NeZero d] :
    ∃ H : ℝ → 𝕄, IsRegulated H 0 1 ∧
      (∀ t, (H t).IsHermitian) ∧
      Tendsto H (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) ∧
      Tendsto H (𝓝[>] (1 / 2 : ℝ)) (𝓝 1) ∧ (0 : 𝕄) ≠ 1 := by
  let H : ℝ → 𝕄 := fun t ↦ if t < 1 / 2 then 0 else 1
  have hpieces : ∀ (j : ℕ), j < 2 → ∀ x ∈ Ioo ((j : ℝ) / 2) (((j + 1 : ℕ) : ℝ) / 2),
      H x = (if j = 0 then 0 else 1) := by
    intro j hj x hx
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with rfl | rfl
    · have hx' : x < 1 / 2 := by simpa using hx.2
      simp only [H, if_pos hx']
      rfl
    · have hx' : ¬ x < 1 / 2 := by have := hx.1; norm_num at this; linarith
      simp only [H, if_neg hx', if_neg Nat.one_ne_zero]
  have hr : IsRegulated H 0 1 := by
    simpa only [Nat.cast_zero, zero_div, Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)]
      using piecewise_regulated H (fun j ↦ (j : ℝ) / 2)
        (fun j ↦ if j = 0 then 0 else 1) 2 hpieces
  refine ⟨H, hr, ?_, ?_, ?_, zero_ne_one⟩
  · intro t
    dsimp [H]
    split <;> simp
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [H, mem_Iio] at ht ⊢
    rw [if_pos ht]
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [H, mem_Ioi] at ht ⊢
    rw [if_neg (not_lt.mpr ht.le)]

/-- Section 1: any continuous leakage bound `C/T`, including the cited JRS
bound, transfers to the unit-step product with a constant independent of `T`.
The conclusion is the stated asymptotic first-order rate. -/
theorem unit_step_leakage_isBigO [NeZero d]
    (H : ℝ → 𝕄) (U : ℕ → ℝ → 𝕄)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hd : DifferentiableOn ℝ H (Icc (0 : ℝ) 1)) (h w C : ℝ)
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ h * |t - s|)
    (hw : w < 2 * π)
    (hwidth : ∀ s (hs : s ∈ Icc (0 : ℝ) 1) p q,
      |(hH s hs).eigenvalues p - (hH s hs).eigenvalues q| ≤ w)
    (hU : ∀ T : ℕ, 0 < T → IsEvolution (fun t ↦ H (t / T)) (U T) 0 T)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1))
    (hC : ∀ T : ℕ, 0 < T → ‖(1 - Q) * U T T * P‖ ≤ C / T) :
    Asymptotics.IsBigO atTop (fun T : ℕ ↦ ‖(1 - Q) * (unitProduct H T).1 * P‖)
      (fun T : ℕ ↦ (1 : ℝ) / T) := by
  let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2 / (4 * π ^ 2 * (n : ℝ) ^ 2 - x ^ 2)
  let c₀ := Nf w - Nf (w / 2) / 2
  let c₁ := c₀ / 4 + 1 / 64
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  let K := c₀ * (‖Hd 0‖ + ‖Hd 1‖) + (1 / 24 + Nf w) * h +
    (c₁ + 2 * frameLip w) * unitSupNorm Hd ^ 2
  apply Asymptotics.IsBigO.of_bound (C + K)
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTpos : 0 < T := by omega
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hb := PaperProof.cor_unit_transfer_bounds H (U T) T hTpos hH hd h w hlip hw
    (fun j hj ↦ hwidth _ (walkCubic_sample hj)) (hU T hTpos) id
    (fun _ ↦ rfl) P Q hP hQ hPc hQc
  simp only [show ∀ A : 𝕄, scalarEntryMap id A = A from fun _ ↦ rfl,
    sub_self, norm_zero, Finset.sum_const_zero, zero_add] at hb
  change |‖(1 - Q) * (unitProduct H T).1 * P‖ - ‖(1 - Q) * U T T * P‖| ≤ (1 / T) * K at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hTR)]
  have hbound := (le_abs_self _).trans hb
  calc
    ‖(1 - Q) * (unitProduct H T).1 * P‖ ≤ C / T + (1 / T) * K := by
      linarith [hC T hTpos]
    _ = (C + K) * (1 / T) := by ring

end UnitaryProducts.Prose
