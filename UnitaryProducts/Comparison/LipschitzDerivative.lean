/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.TransferBounds

/-!
# The unit-step comparison theorem

## Declarations

- `lipOn`
- `lipOn_spec`
- `mesh_lipschitz_nonneg`
- `unit_jumps_global_lip`
- `unit_jumps_le_lip`
- `unit_step_comparison`
- `unit_step_comparison_of_lipschitz_derivative`
- `unit_step_leakage_le_of_jrs_bound`
- `unit_step_leakage_transfer`
- `unit_steps_global_lip`
- `unit_steps_local_lip`
- `unit_steps_one_lip`
- `frameOp_smul_real`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Proof of the interior-sample comparison(i), before summation: each corrector jump
$\|F(\frac{j+2}N)-F(\frac{j+1}N)\|$, $F(s)=\mathcal N(\mathrm{ad}_{(T/N)H(s)})((T/N)H'(s))$, is at
most $\frac T{N^2}(\mathcal N(w)M_{j+1}+2\mathcal N'(w)\frac TN\ell_{j+1}^2)$, with $M_{j+1}$ a
Lipschitz constant and $\ell_{j+1}$ the maximum of $\|H'\|$ on the step $[\frac{j+1}N,\frac{j+2}N]$.

The proof follows the comparison's: Lemma A.1(ii) for the power series
(`norm_frameOp_sub_le`),
with $\|H(\frac{j+2}N)-H(\frac{j+1}N)\|\le\ell_{j+1}/N$ by the mean value inequality and
$\|H'(\frac{j+2}N)-H'(\frac{j+1}N)\|\le M_{j+1}/N$. -/
theorem unit_jumps_le_lip [NeZero d] (H : ℝ → 𝕄) (T : ℝ) (N : ℕ) (w : ℝ)
    (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (Mj : ℕ → ℝ)
    (hlip : ∀ i < N, ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ Mj i * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let F : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) ((T/N) • Hd s)
    1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ≤
      T/N^3*∑ j ∈ Finset.range (N-2),
        (frameBound w*Mj (j+1)+2*frameLip w*(T/N)*(meshSupNorm Hd N (j+1))^2) := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  intro Hd F
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hc' : 0 < T/N := div_pos hT hNR
  have hcd : ContDiffOn ℝ 0 Hd (Icc (0 : ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ (hc.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  -- Step 1 (paper, before the proof of Lemma A.1): an interior sample `(T/N) H(j/N)` of width at
  -- most `w` lies
  -- within `w/2` of a scalar, so `‖ad‖ ≤ w` there.
  have hwid (j : ℕ) (hj : 0 < j) (hjN : j < N) :
      ∃ z : ℝ, ‖(T/N) • H ((j:ℝ)/N) - (z:ℂ) • 1‖ ≤ w/2 :=
    ⟨_, UnitaryProducts.norm_sub_smul_one_le_of_eigenvalues _ hw0 (eigen_interval _
      (scaled_eigenvalue_bound (hH _ (walkCubic_sample hjN.le)) hc'.le (hdiff j hj hjN)))⟩
  have hfB := frameBound_nonneg hw0
  have hfL := frameLip_nonneg hw0
  -- Step 2: the bound for one jump, between the samples `(j+1)/N` and `(j+2)/N` of step `j+1`.
  have hterm (j : ℕ) (hj : j ∈ Finset.range (N-2)) :
      1/N*‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ≤
        T/N^3*(frameBound w*Mj (j+1)+
          2*frameLip w*(T/N)*(meshSupNorm Hd N (j+1))^2) := by
    have hjN := Finset.mem_range.mp hj
    obtain ⟨z₂, hz₂⟩ := hwid (j+2) (by omega) (by omega)
    obtain ⟨z₁, hz₁⟩ := hwid (j+1) (by omega) (by omega)
    have hsub := mesh_subset (N := N) (i := j+1)
    have hjR : ((j:ℕ):ℝ)+2 ≤ N := by exact_mod_cast (show j+2 ≤ N by omega)
    have hm (k : ℕ) (h1 : j+1 ≤ k) (h2 : k ≤ j+2) : ((k:ℕ):ℝ)/N ∈ meshInterval N (j+1) := by
      have h1' : ((j:ℕ):ℝ)+1 ≤ k := by exact_mod_cast h1
      have h2' : (k:ℝ) ≤ j+2 := by exact_mod_cast h2
      constructor <;> apply (div_le_div_iff_of_pos_right hNR).mpr
      · exact max_le (Nat.cast_nonneg _) (by push_cast; linarith)
      · exact le_min (by linarith) (by push_cast; linarith)
    have hm₁ := hm (j+1) le_rfl (by omega)
    have hm₂ := hm (j+2) (by omega) le_rfl
    have hLb : ∀ s ∈ meshInterval N (j+1), ‖Hd s‖ ≤ meshSupNorm Hd N (j+1) :=
      fun s hs ↦ meshSup_bound hcd.continuousOn hs
    have hstep : |((j+2:ℕ):ℝ)/N-((j+1:ℕ):ℝ)/N| = 1/N := by
      rw [show ((j+2:ℕ):ℝ)/N-((j+1:ℕ):ℝ)/N = 1/N by push_cast; ring, abs_of_pos (by positivity)]
    -- The change of `H` (mean value inequality) and of `H'` (Lipschitz) over one step.
    have hH12 : ‖H ((j+2:ℕ)/N) - H ((j+1:ℕ)/N)‖ ≤ meshSupNorm Hd N (j+1)*(1/N) := by
      simpa only [hstep] using UnitaryProducts.norm_sub_le_of_derivWithin_le
        (fun u hu ↦ (hd u (hsub hu)).mono hsub) hLb _ hm₁ _ hm₂
    have hD12 : ‖Hd ((j+2:ℕ)/N) - Hd ((j+1:ℕ)/N)‖ ≤ Mj (j+1)*(1/N) := by
      simpa only [hstep] using hlip (j+1) (by omega) _ hm₁ _ hm₂
    have hD1 : ‖Hd ((j+1:ℕ)/N)‖ ≤ meshSupNorm Hd N (j+1) := hLb _ hm₁
    have hL0 : 0 ≤ meshSupNorm Hd N (j+1) := (norm_nonneg _).trans hD1
    -- Lemma A.1(ii) for the series `frameOp`, then insert the two one-step bounds.
    have hb := norm_frameOp_sub_le (D := (T/N) • Hd ((j+2:ℕ)/N)) (D' := (T/N) • Hd ((j+1:ℕ)/N))
      hw hz₂ hz₁
    simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc'] at hb
    have hFb : ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ≤
        frameBound w*((T/N)*(Mj (j+1)*(1/N)))+
          2*frameLip w*((T/N)*meshSupNorm Hd N (j+1))*((T/N)*(meshSupNorm Hd N (j+1)*(1/N))) := by
      refine hb.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD12 hc'.le) hfB
      · exact mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD1 hc'.le)
          (by linarith)) (mul_le_mul_of_nonneg_left hH12 hc'.le)
          (mul_nonneg hc'.le (norm_nonneg _))
          (mul_nonneg (by linarith) (mul_nonneg hc'.le hL0))
    refine (mul_le_mul_of_nonneg_left hFb (by positivity)).trans_eq ?_
    field_simp
  -- Step 3: sum over the `N - 2` interior jumps.
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum hterm

/-- the interior-sample comparison(i) for the jump terms: with $M_j\le M$ and
$L=\max_{[0,1]}\|H'\|$, the
bound of `unit_jumps_le_lip` summed over the $N-2$ interior jumps is at most
$\frac T{N^2}(aM+bTL^2/N)$ (used with $a=\mathcal N(w)$, $b=2\mathcal N'(w)$). -/
theorem unit_jumps_global_lip (H : ℝ → 𝕄) (T a b : ℝ) (N : ℕ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (Mj : ℕ → ℝ) (M : ℝ) (hMj : ∀ i, 0 ≤ Mj i) (hMM : ∀ i < N, Mj i ≤ M) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
    T/N^3*∑ j ∈ Finset.range (N-2),
        (a*Mj (j+1)+b*(T/N)*(meshSupNorm Hd N (j+1))^2) ≤
      T/N^2*(a*M+b*T*L^2/N) := by
  intro Hd L
  have hN : 0<N := by omega
  have hNR : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hd : ContDiffOn ℝ 0 Hd (Icc (0 : ℝ) 1) :=
    hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hTN3 : 0 ≤ T/N^3 := div_nonneg hT.le (pow_nonneg hNR.le 3)
  have hTN : 0 ≤ T/N := div_nonneg hT.le hNR.le
  have hM0 : 0 ≤ M := (hMj 0).trans (hMM 0 hN)
  have hj (j : ℕ) (hj : j ∈ Finset.range (N-2)) :
      a*Mj (j+1)+b*(T/N)*(meshSupNorm Hd N (j+1))^2 ≤ a*M+b*(T/N)*L^2 := by
    have hjN : j+1 < N := by have := Finset.mem_range.mp hj; omega
    exact add_le_add (mul_le_mul_of_nonneg_left (hMM (j+1) hjN) ha)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ meshSup_nonneg
        (meshSupNorm_le_sSup hd.continuousOn) 2) (mul_nonneg hb hTN))
  have hsum := Finset.sum_le_sum hj
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hcard : ((N-2:ℕ):ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 2
  have hX : 0 ≤ a*M+b*(T/N)*L^2 :=
    add_nonneg (mul_nonneg ha hM0) (mul_nonneg (mul_nonneg hb hTN) (sq_nonneg L))
  calc _ ≤ T/N^3*(((N-2:ℕ):ℝ)*(a*M+b*(T/N)*L^2)) := mul_le_mul_of_nonneg_left hsum hTN3
    _ ≤ T/N^3*((N:ℝ)*(a*M+b*(T/N)*L^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hX) hTN3
    _ = _ := by field_simp

/-- A Lipschitz bound on a nondegenerate mesh cell forces a nonnegative constant. -/
theorem mesh_lipschitz_nonneg {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    {N i : ℕ} {M : ℝ} (hi : i < N)
    (hlip : ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
      ‖F t - F s‖ ≤ M * |t - s|) : 0 ≤ M := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hab : (i : ℝ) / N < ((i : ℝ) + 1) / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (lt_add_one _)
  have he : meshInterval N i = Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
    simp only [meshInterval, max_eq_right (Nat.cast_nonneg i),
      min_eq_right (by exact_mod_cast hi : (i : ℝ) + 1 ≤ N)]
  exact (mul_nonneg_iff_of_pos_right (abs_pos.mpr (sub_ne_zero.mpr hab.ne'))).mp
    ((norm_nonneg _).trans (hlip _ (he ▸ ⟨le_rfl, hab.le⟩) _ (he ▸ ⟨hab.le, le_rfl⟩)))

/-- the interior-sample comparison with per-step Lipschitz constants $M_j$ of $H'$, before
rewriting into mesh norms:
the constants $c_0=\mathcal N(w)-\mathcal N(w/2)/2$, $c_1=1/8$, $c_2=c_0+1/24$ (with the value of
$c_0$ at width $\pi$), and the three parts, assembled from `unit_steps_jumps_lip` (ii),
`unit_jumps_le_lip` (jump bound in the proof of (i)), and `unit_rhs_max_lip` with
`unit_jumps_global_lip` (i). The comparison's
series `Nf` and its derivative are identified with `frameBound`, `frameLip` by
`paper_series_eq`. -/
theorem unit_steps_one_lip [NeZero d] (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/8 ∧ c₂ = c₀+1/24 ∧ (w = π → c₀ = (π-2)/(2*π^2))) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (Mj : ℕ → ℝ) (M : ℝ) (_ : ∀ i < N, Mj i ≤ M)
      (_ : ∀ i < N, ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ Mj i * |t - s|)
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let F : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) ((T/N) • Hd s)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
          T/N^3*∑ j ∈ Finset.range N, (c₁*Mj j+c₂*(T/N)*(meshSupNorm Hd N j)^2)+
          1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ∧
      1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ≤
        T/N^3*∑ j ∈ Finset.range (N-2),
          (Nf w*Mj (j+1)+2*deriv Nf w*(T/N)*(meshSupNorm Hd N (j+1))^2) ∧
      c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
          T/N^3*∑ j ∈ Finset.range N, (c₁*Mj j+c₂*(T/N)*(meshSupNorm Hd N j)^2)+
          1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ ≤
        T/N^2*(2*c₀*L+(c₁+Nf w)*M+(c₂+2*deriv Nf w)*T*L^2/N) := by
  intro Nf
  refine ⟨Nf w-Nf (w/2)/2, 1/8, Nf w-Nf (w/2)/2+1/24, ⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · rintro rfl; dsimp only [Nf]
    rw [(paper_series_eq pi_pos.le (by linarith [pi_pos])).1,
      (paper_series_eq (by positivity : 0 ≤ π/2) (by linarith [pi_pos])).1,
      frameBound_center_pi]; have := pi_pos.ne'; field_simp
  · intro H U T N hT hN2 hH hc Mj M hMM hlip hdiff hU
    -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
    have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
    obtain ⟨hNf, hDf⟩ : Nf w = frameBound w ∧ deriv Nf w = frameLip w := paper_series_eq hw0 hw
    have hNfh : Nf (w/2) = frameBound (w/2) := (paper_series_eq (by linarith) (by linarith)).1
    have hq : 0 ≤ frameBound w-frameBound (w/2)/2 := (norm_nonneg _).trans
      (norm_frameSeries_sub_half_le (a := (0:ℂ)) (by simpa only [norm_zero] using hw0) hw)
    rw [hNf, hNfh, hDf]
    have hmain := unit_steps_jumps_lip H U T N w hT hN2 hw hH hc Mj hlip hdiff hU
    have hjump := unit_jumps_le_lip H T N w hT hN2 hw hH hc Mj hlip hdiff
    have hres := unit_rhs_max_lip H T (frameBound w-frameBound (w/2)/2) (1/8)
      (frameBound w-frameBound (w/2)/2+1/24) N hT hN2 hq (by norm_num) (by linarith) hc Mj M hMM
    have hMj i (hi : i < N) := mesh_lipschitz_nonneg hi (hlip i hi)
    have hM0 := (hMj 0 (by omega)).trans (hMM 0 (by omega))
    have hglob := unit_jumps_global_lip H T (frameBound w) (2*frameLip w) N hT hN2
      (frameBound_nonneg hw0) (by linarith [frameLip_nonneg hw0]) hc (fun i ↦ max (Mj i) 0) M
      (fun _ ↦ le_max_right _ _) (fun i hi ↦ max_le (hMM i hi) hM0)
    have hglob := (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left (Mj (j+1)) 0)
        (frameBound_nonneg hw0)) le_rfl)
      (div_nonneg hT.le (pow_nonneg (Nat.cast_nonneg N) 3))).trans hglob
    dsimp only at hmain hjump hres hglob ⊢
    refine ⟨hmain.trans_eq ?_, hjump, ?_⟩
    · congr 2; congr 1; exact Finset.sum_congr rfl fun j _ ↦ by ring
    · convert add_le_add hres (hjump.trans hglob) using 1; ring

/-- $\mathcal N(\mathrm{ad}_h)$ is real-linear: `frameOp h (r • D) = r • frameOp h D`. -/
private theorem frameOp_smul_real [NeZero d] (h D : 𝕄) (r : ℝ) :
    frameOp h (r • D) = r • frameOp h D := by
  unfold frameOp
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r D, map_smul,
    ← RCLike.real_smul_eq_coe_smul (K := ℂ) r]

/-- the interior-sample comparison with per-step Lipschitz constants $M_j$ of $H'$, in the
comparison's form: the jumps
are written with $\mathcal N(\mathrm{ad}_{TH/N})(H')$ (the derivative is not rescaled, as
$\mathcal N(\mathrm{ad}_h)$ is linear), and the residuals with the mesh norm $\|H'\|_{2,N}^2$
(`meshMoment Hd N 2`). For the jump bound in the proof of (i), the sum over the $N-2$ interior
steps is bounded by the sum
over all $N$ steps. -/
theorem unit_steps_local_lip [NeZero d] (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/8 ∧ c₂ = c₀+1/24 ∧ (w = π → c₀ = (π-2)/(2*π^2))) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (Mj : ℕ → ℝ) (M : ℝ) (_ : ∀ i < N, Mj i ≤ M)
      (_ : ∀ i < N, ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ Mj i * |t - s|)
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) (Hd s)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, Mj j)/N+
          c₂*(T/N)*meshMoment Hd N 2+
          ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖) ∧
      ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖ ≤
        Nf w*(∑ j ∈ Finset.range N, Mj j)/N+2*deriv Nf w*(T/N)*meshMoment Hd N 2 ∧
      T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, Mj j)/N+
          c₂*(T/N)*meshMoment Hd N 2+
          ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖) ≤
        T/N^2*(2*c₀*L+(c₁+Nf w)*M+(c₂+2*deriv Nf w)*T*L^2/N) := by
  intro Nf
  obtain ⟨c₀, c₁, c₂, hcs, hall⟩ := unit_steps_one_lip (d := d) w hw
  refine ⟨c₀, c₁, c₂, hcs, ?_⟩
  intro H U T N hT hN2 hH hc Mj M hMM hlip hdiff hU
  obtain ⟨h1, h2, h3⟩ := hall H U T N hT hN2 hH hc Mj M hMM hlip hdiff hU
  intro Hd Yb L
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hTN : 0 < T/N := div_pos hT hNR
  have hTN2 : 0 < T/N^2 := div_pos hT (pow_pos hNR 2)
  -- the jump terms: `F = (T/N) • Yb`
  have hterm : ∀ a b : ℝ,
      ‖frameOp ((T/N) • H a) ((T/N) • Hd a) - frameOp ((T/N) • H b) ((T/N) • Hd b)‖ =
        (T/N)*‖Yb a - Yb b‖ := fun a b ↦ by
    rw [frameOp_smul_real, frameOp_smul_real, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hTN]
  have eJ : 1/N*∑ j ∈ Finset.range (N-2),
        ‖frameOp ((T/N) • H ((j+2:ℕ)/N)) ((T/N) • Hd ((j+2:ℕ)/N)) -
          frameOp ((T/N) • H ((j+1:ℕ)/N)) ((T/N) • Hd ((j+1:ℕ)/N))‖ =
      T/N^2*∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖ := by
    simp only [hterm, ← Finset.mul_sum]; ring
  -- the residual terms in mesh norms
  have eR : ∀ a b : ℝ, T/N^3*∑ j ∈ Finset.range N,
        (a*Mj j+b*(T/N)*(meshSupNorm Hd N j)^2) =
      T/N^2*(a*(∑ j ∈ Finset.range N, Mj j)/N+b*(T/N)*meshMoment Hd N 2) := fun a b ↦ by
    unfold meshMoment; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
  rw [eR, eJ] at h1 h3
  refine ⟨?_, ?_, ?_⟩
  · convert h1 using 1; ring
  swap
  · convert h3 using 1; ring
  -- the jump clause
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  obtain ⟨hNf, hDf⟩ := paper_series_eq hw0 hw
  have hNf0 : 0 ≤ Nf w := by simpa only [← hNf] using frameBound_nonneg hw0
  have hDf0 : 0 ≤ deriv Nf w := by simpa only [← hDf] using frameLip_nonneg hw0
  set g : ℕ → ℝ := fun j ↦ Nf w*Mj j+2*deriv Nf w*(T/N)*(meshSupNorm Hd N j)^2
  have hg : ∀ j < N, 0 ≤ g j := fun j hj ↦
    add_nonneg (mul_nonneg hNf0 (mesh_lipschitz_nonneg hj (hlip j hj)))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDf0) hTN.le) (sq_nonneg _))
  have hsub : ∑ j ∈ Finset.range (N-2), g (j+1) ≤ ∑ j ∈ Finset.range N, g j := by
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ N), Finset.sum_range_succ' g]
    exact le_add_of_le_of_nonneg (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) fun j hj _ ↦ hg (j+1) (by
        have := Finset.mem_range.mp hj; omega)) (hg 0 (by omega))
  apply (mul_le_mul_iff_right₀ hTN2).mp
  rw [← eJ, ← eR (Nf w) (2*deriv Nf w)]
  exact h2.trans (mul_le_mul_of_nonneg_left hsub
    (div_nonneg hT.le (pow_nonneg hNR.le 3)))

/-- the interior-sample comparison(i) for one global Lipschitz constant $M$ of $H'$, with the
explicit
coefficients: the error is at most $\frac T{N^2}(2c_0L+(\frac18+\mathcal N(w))M
+(c_0+\frac1{24}+2\mathcal N'(w))TL^2/N)$, $c_0=\mathcal N(w)-\mathcal N(w/2)/2$, written with
`frameBound`, `frameLip`. This is the input of the width-π scaling bound
(`unit_step_comparison_scaling`). -/
theorem unit_steps_global_lip [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (w M : ℝ)
    (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
    let c₀ := frameBound w-frameBound (w/2)/2
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(2*c₀*L+(1/8+frameBound w)*M+(c₀+1/24+2*frameLip w)*T*L^2/N) := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  obtain ⟨c₀, c₁, c₂, ⟨rfl, rfl, rfl, _⟩, hall⟩ := unit_steps_local_lip (d := d) w hw
  have hb := hall H U T N hT hN2 hH hc (fun _ ↦ M) M (fun _ _ ↦ le_rfl)
    (fun i _ s hs t ht ↦ hlip s (mesh_subset hs) t (mesh_subset ht)) hdiff hU
  have hcomparison := hb.1.trans hb.2.2
  have hseries := paper_series_eq hw0 hw
  have hhalf := (paper_series_eq (x := w / 2) (by linarith) (by linarith)).1
  -- Combine the local comparison and jump estimates, then identify the paper coefficients.
  simpa only [hseries.1, hseries.2, hhalf] using hcomparison

/-- The least Lipschitz constant of `F` on `S`: the supremum of the difference quotients
$\|F(t)-F(s)\|/|t-s|$ over $s,t\in S$. With `F` $=H'$ and `S` the $j$-th step, it is the paper's
$M_j$, and the mean $\frac1N\sum_j$ `lipOn` is $\|H'\|_{\mathrm{Lip},N}$ (§4.2).

Junk values: it is an `sSup` of reals, so it is `0` when the quotients are unbounded (`F` not
Lipschitz on `S`) and when `S` is empty; the diagonal pairs $s=t$ give the quotient $0/0=0$. Every
use first bounds the quotients by an explicit constant (`lipOn_spec`), where it is the least
Lipschitz constant. -/
def lipOn {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (S : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ s ∈ S, ∃ t ∈ S, r = ‖F t - F s‖/|t-s|}

/-- If `F` is $M$-Lipschitz on `S` with $M\ge0$, then `lipOn F S` $\le M$ and `F` is
`lipOn F S`-Lipschitz on `S`. This is the least nonnegative constant, including for empty `S`. -/
theorem lipOn_spec {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (S : Set ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hlip : ∀ s ∈ S, ∀ t ∈ S, ‖F t - F s‖ ≤ M * |t - s|) :
    lipOn F S ≤ M ∧ ∀ s ∈ S, ∀ t ∈ S, ‖F t - F s‖ ≤ lipOn F S*|t-s| := by
  have hbound : ∀ r ∈ {r : ℝ | ∃ s ∈ S, ∃ t ∈ S, r = ‖F t - F s‖/|t-s|}, r ≤ M := by
    rintro _ ⟨s, hs, t, ht, rfl⟩
    by_cases he : t=s
    · simpa only [he, sub_self, norm_zero, abs_zero, div_zero] using hM
    · exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr he))).mpr (hlip s hs t ht)
  refine ⟨Real.sSup_le hbound hM, fun s hs t ht ↦ ?_⟩
  by_cases he : t=s
  · simp only [he, sub_self, norm_zero, abs_zero, mul_zero, le_refl]
  · apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr he))).mp
    exact le_csSup ⟨M, hbound⟩ ⟨s, hs, t, ht, rfl⟩

/-- the interior-sample comparison with two sizes, in the order of its proof (the two-size
statement is
`unit_step_comparison`, and the comparison's statement is `unit_step_comparison_one_size`). For
$0\le w<2\pi$, with $c_0=\mathcal N(w)-\mathcal N(w/2)/2$, $c_1=1/8$, and $c_2=c_0+1/24$, for
every Hamiltonian $H$ on $[0,1]$ with $M$-Lipschitz derivative, every $T>0$ and every $N\ge2$
whose interior samples $(T/N)H(j/N)$ have eigenvalue differences at most $w$:
$\|W_N-e^{iTH(1)/(2N)}U(T)e^{-iTH(0)/(2N)}\|$ is at most $\frac T{N^2}$ times the end, residual
and jump terms (part (ii)); the jump sum $\Sigma_N$ is at most
$\mathcal N(w)\|H'\|_{\mathrm{Lip},N}+2\mathcal N'(w)\frac TN\|H'\|_{2,N}^2$ (jump bound in the
proof of (i)); and the
bound of (ii) is at most $\frac T{N^2}(2c_0L+(c_1+\mathcal N(w))M+(c_2+2\mathcal N'(w))TL^2/N)$,
the right side of part (i).

Reading the statement against the comparison:
* `Nf` is $\mathcal N(x)=\sum_{n\ge1}2/(4\pi^2n^2-x^2)$ and `deriv Nf w` is $\mathcal N'(w)$.
* The constants are chosen before $H$ (`∃ c₀ c₁ c₂, … ∧ ∀ H U T N, …`), so they depend only on
  $w$; the first conjunct gives their values, which the paper puts at the head of the statement
  (it writes $c_1$ as $1/8$), and adds $c_0=(\pi-2)/(2\pi^2)$ at $w=\pi$, an additional identity.
* `derivWithin H (Icc 0 1)` is $H'$, one-sided at $0$ and $1$. `ContDiffOn ℝ 1 H` and `0 ≤ M`
  make explicit what the comparison's $\|H'(s_1)-H'(s_2)\|\le M|s_1-s_2|$ presupposes.
* `L := sSup …` is $\max_{[0,1]}\|H'\|$: $H'$ is continuous on the compact $[0,1]$, so the
  supremum is attained.
* `Yb s` is $\mathcal N(\mathrm{ad}_{TH(s)/N})(H'(s))$: `frameOp` is the power series in
  $\mathrm{ad}_h$, equal to the comparison's eigenbasis formula at width $<2\pi$
  (`frameOp_eq_paper_value`). It is evaluated only at the interior samples $(j+1)/N$, $(j+2)/N$,
  $j<N-2$, where the width hypothesis holds.
* `(∑ j ∈ range N, lipOn Hd (meshInterval N j))/N` is $\|H'\|_{\mathrm{Lip},N}$, the mean of the
  least Lipschitz constants of $H'$ on the steps (finite here, being at most $M$), and
  `meshMoment Hd N 2` is $\|H'\|_{2,N}^2$.
* The jump sum is $\Sigma_N$, reindexed: Lean's index $j<N-2$ is the comparison's $j+1$,
  $1\le j+1\le N-2$.
* The width hypothesis is stated for the eigenvalues of $H(j/N)$ times $T/N$, for all pairs
  `p q` and $0<j<N$.
* `evol G u` is $e^{-iuG}$, so the subtracted term is $e^{iTH(1)/(2N)}U(T)e^{-iTH(0)/(2N)}$, and
  `(unitProduct (fun s ↦ (T/N) • H s) N).1` is $W_N$.
* `[NeZero d]` is the comparison's $d\ge1$, which the proof uses.

The proof follows the comparison's estimates, with a different bookkeeping of the corrector jumps:
(1) the least Lipschitz constants $M_j$ of $H'$ on the steps are at most $M$ (`lipOn_spec`), and
`unit_steps_local_lip` / `unit_steps_one_lip` fix the constants and write the bound in mesh norms;
(2) `unit_steps_jumps_lip` rescales to $K(t)=(T/N)H(t/N)$ on $[0,N]$; (3) on $[0,N]$
(`endpoint_local_of_frame_bounds`) each cell contributes its residual through the proof of Lemma
A.1, each
end its corrector's center value, at most $c_0\|K'\|$, and each jump $\Delta_j$ its norm; Lean
telescopes the dressed product $U^\dagger(1-iY)V$ cell by cell and pays each $\|\Delta_j\|$ there,
instead of subtracting the transported jump $X_j$ (the two agree, as $\|X_j(N)\|=\|\Delta_j\|$);
the residual constants are computed exactly and then majorized by $c_1$, $c_2$; (4) the proof of (i)
bounds each jump by Lemma A.1(ii) (`unit_jumps_le_lip`), and part (i) uses $M_j\le M$ and
$L_j\le L$ (`unit_rhs_max_lip`, `unit_jumps_global_lip`). -/
theorem unit_step_comparison_of_lipschitz_derivative [NeZero d] (w : ℝ) (hw : w <
    2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/8 ∧ c₂ = c₀+1/24 ∧ (w = π → c₀ = (π-2)/(2*π^2))) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (M : ℝ)
      (_ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) (Hd s)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N
          j))/N+
          c₂*(T/N)*meshMoment Hd N 2+
          ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖) ∧
      ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖ ≤
        Nf w*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N j))/N+2*deriv Nf w*(T/N)*meshMoment
          Hd N 2 ∧
      T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N j))/N+
          c₂*(T/N)*meshMoment Hd N 2+
          ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖) ≤
        T/N^2*(2*c₀*L+(c₁+Nf w)*M+(c₂+2*deriv Nf w)*T*L^2/N) := by
  intro Nf
  obtain ⟨c₀, c₁, c₂, hcs, hall⟩ := unit_steps_local_lip (d := d) w hw
  refine ⟨c₀, c₁, c₂, hcs, ?_⟩
  intro H U T N hT hN2 hH hc M hlip hdiff hU
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  have hloc (i : ℕ) := lipOn_spec Hd (meshInterval N i)
    M (unit_lipschitz_constant_nonneg hlip)
    (fun s hs t ht ↦ hlip s (mesh_subset hs) t (mesh_subset ht))
  exact hall H U T N hT hN2 hH hc (fun i ↦ lipOn Hd (meshInterval N i)) M
    (fun i _ ↦ (hloc i).1) (fun i _ ↦ (hloc i).2) hdiff hU

/-- **the interior-sample comparison with two sizes** (the unit-step comparison theorem, (i) in
$L$ and $M$). This is
the two-size form of the interior-sample comparison ((i) in $L=\max\|H'\|$ and the Lipschitz
constant $M$ of $H'$);
the comparison's (i) is `unit_step_comparison_one_size` with one size $h$, derived from this one at
$M=h$, $L\le h$; (ii) and the jump bound in the proof of (i) are unchanged. For $0\le w<2\pi$, with
$c_0=\mathcal N(w)-\mathcal N(w/2)/2$, $c_1=1/8$, and $c_2=c_0+1/24$, for every Hamiltonian
$H$ on $[0,1]$ with $M$-Lipschitz derivative, every $T>0$ and every $N\ge2$ whose interior samples
$(T/N)H(j/N)$ have eigenvalue differences at most $w$, with
$\Sigma_N=\sum_{j=1}^{N-2}\|[\mathcal N(\mathrm{ad}_{TH/N})(H')]_{j/N}^{(j+1)/N}\|$:
(i) $\|W_N-e^{iTH(1)/(2N)}U(T)e^{-iTH(0)/(2N)}\|\le\frac T{N^2}(2c_0L+(c_1+\mathcal N(w))M+
(c_2+2\mathcal N'(w))TL^2/N)$; (ii) the same distance is at most $\frac T{N^2}$ times the end,
residual and jump terms, $c_0(\|H'(\frac1N)\|+\|H'(1-\frac1N)\|)+c_1\|H'\|_{\mathrm{Lip},N}+
c_2\frac TN\|H'\|_{2,N}^2+\Sigma_N$; the proof of (i) also gives $\Sigma_N\le\mathcal
N(w)\|H'\|_{\mathrm{Lip},N}+
2\mathcal N'(w)\frac TN\|H'\|_{2,N}^2$.

Reading the statement against the comparison:
* The hypotheses, constants, `Hd`, `Yb`, `L`, and the mesh norms read as in
  `unit_step_comparison_of_lipschitz_derivative`.
* `J` is $\Sigma_N$, reindexed: Lean's index $j<N-2$ is the comparison's $j+1$, $1\le j+1\le N-2$.
* The three conjuncts are parts (i), (ii), and the jump bound in the proof of (i), in this order.

The proof follows the comparison's: `unit_step_comparison_of_lipschitz_derivative` gives (ii), the
jump bound,
and the bound of the right side of (ii) by that of (i); chaining the first and last gives (i). -/
theorem unit_step_comparison [NeZero d] (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/8 ∧ c₂ = c₀+1/24 ∧ (w = π → c₀ = (π-2)/(2*π^2))) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (M : ℝ)
      (_ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) (Hd s)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      let J := ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        T/N^2*(2*c₀*L+(c₁+Nf w)*M+(c₂+2*deriv Nf w)*T*L^2/N) ∧
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N
          j))/N+c₂*(T/N)*meshMoment Hd N 2+J) ∧
      J ≤ Nf w*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N j))/N+2*deriv Nf w*(T/N)*
        meshMoment Hd N 2 := by
  intro Nf
  obtain ⟨c₀, c₁, c₂, hcs, hall⟩ := unit_step_comparison_of_lipschitz_derivative (d := d) w hw
  refine ⟨c₀, c₁, c₂, hcs, ?_⟩
  intro H U T N hT hN2 hH hc M hlip hdiff hU Hd Yb L J
  obtain ⟨h1, h2, h3⟩ := hall H U T N hT hN2 hH hc M hlip hdiff hU
  exact ⟨h1.trans h3, h1, h2⟩

/-- **the interior-sample leakage estimate with two sizes** (two-sided leakage transfer). This is
the two-size form of
the interior-sample leakage estimate; the comparison's is `unit_step_leakage_transfer_one_size`,
derived from this one at
$M=h$, $L\le h$. Let $H$, $U$, $W_N$, $T$, $N$, and $w$ be as in the interior-sample comparison
with two sizes
(`unit_step_comparison`), and let $P$ and $Q$ be orthogonal projectors commuting with $H(0)$ and
$H(1)$, respectively. Then $\bigl|\|(1-Q)W_NP\|-\|(1-Q)U(T)P\|\bigr|$ is at most the right side of
the interior-sample comparison(ii), and hence of (i).

Reading the statement against the comparison:
* The hypotheses, constants, `Hd`, `Yb`, `L`, `J`, and the mesh norms read as in
  `unit_step_comparison`; `W` is the $N$-step product $W_N$.
* `P`, `Q` are any star projections (orthogonal projectors) commuting with $H(0)$, $H(1)$; no
  band, gap, or adiabatic theorem enters.
* The two conjuncts are the bounds by the right sides of the interior-sample comparison(ii) and of
the two-size (i),
  in this order. Both directions of the transfer are the one absolute value.

The proof follows the comparison's: the half-step phases commute with $1-Q$ and $P$ and are
unitary, so
the two leakages differ by at most the distance that the interior-sample comparison bounds
(`unit_steps_dat`), and
the interior-sample comparison(ii) and (i) bound it (`unit_step_comparison`). -/
theorem unit_step_leakage_transfer [NeZero d] (w : ℝ) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/8 ∧ c₂ = c₀+1/24 ∧ (w = π → c₀ = (π-2)/(2*π^2))) ∧
    ∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
      (M : ℝ)
      (_ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ M * |t - s|)
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T)
      (P Q : 𝕄) (_ : IsStarProjection P) (_ : IsStarProjection Q)
      (_ : Commute P (H 0)) (_ : Commute Q (H 1)),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Yb : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) (Hd s)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      let J := ∑ j ∈ Finset.range (N-2), ‖Yb ((j+2:ℕ)/N)-Yb ((j+1:ℕ)/N)‖
      let W := (unitProduct (fun s ↦ (T/N) • H s) N).1
      |‖(1-Q)*W*P‖ - ‖(1-Q)*U T*P‖| ≤
        T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+c₁*(∑ j ∈ Finset.range N, lipOn Hd (meshInterval N
          j))/N+c₂*(T/N)*meshMoment Hd N 2+J) ∧
      |‖(1-Q)*W*P‖ - ‖(1-Q)*U T*P‖| ≤
        T/N^2*(2*c₀*L+(c₁+Nf w)*M+(c₂+2*deriv Nf w)*T*L^2/N) := by
  intro Nf
  obtain ⟨c₀, c₁, c₂, hcs, hall⟩ := unit_step_comparison (d := d) w hw
  refine ⟨c₀, c₁, c₂, hcs, ?_⟩
  intro H U T N hT hN2 hH hc M hlip hdiff hU P Q hP hQ hPc hQc Hd Yb L J W
  -- The half-step phases commute with `1-Q` and `P`: the leakages differ by at most the distance
  -- of the interior-sample comparison.
  have hb := unit_steps_dat H (U T) T N (hH 0 ⟨le_rfl, zero_le_one⟩)
    (hH 1 ⟨zero_le_one, le_rfl⟩) P Q hP hQ hPc hQc
  dsimp only at hb
  -- The comparison bounds bound that distance.
  obtain ⟨h1, h2, -⟩ := hall H U T N hT hN2 hH hc M hlip hdiff hU
  exact ⟨hb.trans h2, hb.trans h1⟩

/-- The Jansen–Ruskai–Seiler instance of the interior-sample leakage estimate (after Example 4.6,
the sentence beginning
"Under that bound"). For an integer $T\ge2$, a $C^2$ Hamiltonian $H$ with a band of $m$ eigenvalues
and endpoint projectors $P$ and $Q$ at $s=0$ and $s=1$, respectively, and interior samples
$H(j/T)$ of width at most $w<2\pi$: if $\|(1-Q)U(T)P\|\le J_m(H)/T$, then $T\|(1-Q)W_TP\|$ is at
most $J_m(H)$ plus $T$ times the right side of the interior-sample comparison(ii) with $N=T$.

Reading the statement against the comparison:
* This is stronger than the comparison's sentence: the band data `jrsCoefficientTracked H hH m g B`
  accepts any positive continuous lower bound `g` on the band's gap, where the paper uses the gap
  $\Gamma$ itself; with $g=\Gamma$, `J` is $J_m(H)$.
* `hband` carries the comparison's hypotheses on $H$: $C^2$, the band of $m$ eigenvalues tracked
  continuously in the intervals `B s`, and the gap bound `g`; `P` and `Q` are the spectral
  projectors of $H(0)$ on `B 0` and of $H(1)$ on `B 1`, respectively.
* The Jansen–Ruskai–Seiler bound is the hypothesis `‖(1-Q)*U T*P‖ ≤ J/T`; it is assumed, not
  proved.
* At $N=T$ the step is $T/T=1$, so the width hypothesis is stated for the eigenvalues of $H(j/T)$
  themselves; the factors `T/T^2`, `T/T` and `(T:ℝ)/T` are the interior-sample comparison(ii) at
$N=T$, unsimplified.
* `c₀ := frameBound w - frameBound (w/2)/2` is $c_0=\mathcal N(w)-\mathcal N(w/2)/2$ (`frameBound`
  is $\mathcal N$ on $[0,2\pi)$), and $1/8$, $c_0+1/24$ are $c_1$, $c_2$ of the interior-sample
comparison.
* `Yb` and the mesh terms read as in `unit_step_comparison`; `lipOn` is finite here because $H$ is
  $C^2$.

The proof is the instance: (1) the interior-sample leakage estimate (`unit_step_leakage_transfer`)
at $N=T$, with
Lipschitz constant $M=\max_{[0,1]}\|H''\|$ and the band's spectral projectors as $P$ and $Q$,
bounds the difference of the two leakages by the right side of the interior-sample comparison(ii);
(2) add the assumed
bound and multiply by $T$. -/
theorem unit_step_leakage_le_of_jrs_bound [NeZero d]
    (H U : ℝ → 𝕄) (T m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ) (w : ℝ) (hw : w < 2 * π)
    (hT2 : 2 ≤ T) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hband : (jrsCoefficientTracked H hH m g B).1)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0 < j, ∀ hjT : j < T, ∀ p q,
      |(hH _ (walkCubic_sample hjT.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjT.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let P := (jrsCoefficientTracked H hH m g B).2.1.1
    let Q := (jrsCoefficientTracked H hH m g B).2.1.2
    let J := (jrsCoefficientTracked H hH m g B).2.2
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let c₀ := frameBound w-frameBound (w/2)/2
    let Yb : ℝ → 𝕄 := fun s ↦ frameOp (((T:ℝ)/T) • H s) (Hd s)
    ‖(1-Q)*U T*P‖ ≤ J/T →
      T*‖(1-Q)*(unitProduct H T).1*P‖ ≤
        J+T*(T/T^2*(c₀*(‖Hd (1/T)‖+‖Hd (1-1/T)‖)+
          1/8*(∑ j ∈ Finset.range T, lipOn Hd (meshInterval T j))/T+
          (c₀+1/24)*(T/T)*meshMoment Hd T 2+
          ∑ j ∈ Finset.range (T-2), ‖Yb ((j+2:ℕ)/T)-Yb ((j+1:ℕ)/T)‖)) := by
  intro P Q J Hd c₀ Yb hJ
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) 0 0
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hc2 : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1) := hband.1.1
  -- Step 1 (paper, after Example 4.6): the transfer paragraph in Section 4.2 at `N = T`, with
  -- Lipschitz
  -- constant `M` the maximum of `‖H''‖` on `[0, 1]` (the single step `meshInterval 1 0`) and the
  -- band's spectral projectors, which commute with `H 0`, `H 1`; the constants written out.
  obtain ⟨c₀', c₁, c₂, hcs, hall⟩ := unit_step_leakage_transfer (d := d) w hw
  have hI : meshInterval 1 0 = Icc (0 : ℝ) 1 := by simp [meshInterval]
  have htr := (hall H U T T hTR hT2 hH (hc2.of_le (by norm_num))
    (meshSupNorm (derivWithin Hd (Icc (0 : ℝ) 1)) 1 0)
    (fun s hs t ht ↦ derivative_lipschitzOn_of_contDiffOn_two H 1 hc2 0
      s (hI ▸ hs) t (hI ▸ ht))
    (fun j hj hjT p q ↦ by simpa only [div_self hTR.ne', one_mul] using hdiff j hj hjT p q) hU P Q
    (UnitaryProducts.isStarProjection_specProj _ _) (UnitaryProducts.isStarProjection_specProj _ _)
    (UnitaryProducts.commute_specProj _ _) (UnitaryProducts.commute_specProj _ _)).1
  dsimp only at htr
  have hq := hcs.1
  dsimp only at hq
  rw [(paper_series_eq hw0 hw).1,
    (paper_series_eq (x := w/2) (by linarith) (by linarith)).1] at hq
  rw [hcs.2.1, hcs.2.2.1, hq] at htr
  rw [show (unitProduct (fun s ↦ ((T:ℝ)/T) • H s) T).1=(unitProduct H T).1 by
    simp only [div_self hTR.ne', one_smul]] at htr
  -- Step 2: `‖(1-Q) W_T P‖ ≤ ‖(1-Q) U(T) P‖ + error ≤ J/T + error`; multiply by `T`.
  have key := (sub_le_iff_le_add.mp ((le_abs_self _).trans htr)).trans
    (add_le_add le_rfl hJ)
  exact (mul_le_mul_of_nonneg_left key hTR.le).trans_eq
    (by rw [mul_add, mul_div_cancel₀ _ hTR.ne']; ring)

end UnitaryProducts.Paper
