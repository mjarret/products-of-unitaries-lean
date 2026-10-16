/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.IntegratedComparison

/-!
# The operator series $\mathcal N(\mathrm{ad}_h)$ and its bounds

## Declarations

- `corrBoundC_eq_half_add_mul`
- `corrSeries_eq_half_add_mul`
- `frameBound`
- `frameBound_eq_closedForm`
- `frameBound_mono`
- `frameBound_nonneg`
- `frameLip`
- `frameLip_nonneg`
- `frameSeries`
- `hasDerivAt_frameBound`
- `norm_frame_coefficient`
- `norm_frameSeries_le_of_le`
- `norm_frameSeries_sub_le`
- `one_div_twelve_le_frameBound`
- `phiSeries_mul_frameSeries`
- `summable_frameBound_majorant`
- `summable_frameLip_majorant`
- `summable_norm_frameSeries_terms`
- `evol_conj_frameOp_sub`
- `evol_conj_sub_self`
- `frameOp`
- `norm_frameOp_le`
- `norm_frameOp_sub_le`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real

noncomputable section

namespace UnitaryProducts.Corrector

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- `frameSeries a = ∑ B_{n+2} aⁿ/(n+2)!`, i.e. `(corrSeries a - 1/2)/a`. It converges absolutely
for $\|a\| < 2\pi$ (`summable_norm_frameSeries_terms`) and is the `tsum` junk value $0$ when the
series is not summable. -/
def frameSeries (a : A) : A :=
  ∑' n : ℕ, (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • a ^ n

/-- The majorant `∑ |B_{n+2}| wⁿ/(n+2)!` of the frame series: the Taylor series
$\sum_{k \ge 1} |B_{2k}| w^{2k-2}/(2k)!$ of the paper's $\mathcal N$ (§4.1; odd Bernoulli numbers
beyond $B_1$ vanish), equal to $\mathcal N(w)$ for $0 \le w < 2\pi$ (`paper_series_eq`). For
$|w| \ge 2\pi$ the series diverges and the value is the `tsum` junk value $0$. -/
def frameBound (w : ℝ) : ℝ :=
  ∑' n : ℕ, |((bernoulli (n + 2) : ℚ) : ℝ)| * w ^ n / (Nat.factorial (n + 2))

/-- The Lipschitz constant of the frame series on the ball of radius `w`,
`∑ |B_{n+2}| n wⁿ⁻¹/(n+2)!`: the termwise derivative of `frameBound` on $|w| < 2\pi$
(`hasDerivAt_frameBound`), hence the paper's $\mathcal N'(w)$ for $0 \le w < 2\pi$
(`paper_series_eq`). The $n = 0$ term is $0$. It is the `tsum` junk value $0$ where the series
diverges. -/
def frameLip (w : ℝ) : ℝ :=
  ∑' n : ℕ, |((bernoulli (n + 2) : ℚ) : ℝ)| * n * w ^ (n - 1) / (Nat.factorial (n + 2))

/-- The series `frameBound x` converges for $0 \le x < 2\pi$, by $|B_n|/n! \le 4/(2\pi)^n$. -/
theorem summable_frameBound_majorant {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    Summable (fun n : ℕ ↦ |((bernoulli (n + 2) : ℚ) : ℝ)| * x ^ n / (Nat.factorial (n + 2))) := by
  have hg : Summable (fun n : ℕ ↦ 4 / (2 * π) ^ 2 * (x / (2 * π)) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one (by positivity)).mpr hx)).mul_left _
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hg
  have h := abs_bernoulli_div_factorial_le (n + 2)
  calc _ = (|((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2))) * x ^ n := by ring
    _ ≤ (4 / (2 * π) ^ (n + 2)) * x ^ n := by gcongr
    _ = 4 / (2 * π) ^ 2 * (x / (2 * π)) ^ n := by rw [div_pow, pow_add]; field_simp

/-- The series `frameLip r` converges for $0 \le r < 2\pi$. -/
theorem summable_frameLip_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 2 * π) :
    Summable (fun n : ℕ ↦
      |((bernoulli (n + 2) : ℚ) : ℝ)| * n * r ^ (n - 1) / (Nat.factorial (n + 2))) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set x : ℝ := r / (2 * π) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hpi]; exact hr
  have hxnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have hgeo : Summable (fun n : ℕ ↦ (4 / (2 * π) ^ 3) * (((n : ℝ) + 1) * x ^ n)) :=
    (((summable_pow_mul_geometric_of_norm_lt_one 1 hxnorm).add
      (summable_pow_mul_geometric_of_norm_lt_one 0 hxnorm)).congr fun n ↦ by
        simp only [pow_one, pow_zero, one_mul]; ring).mul_left _
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hgeo
  have hb : |((bernoulli (n + 1 + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 1 + 2))
      ≤ 4 / (2 * π) ^ (n + 3) := abs_bernoulli_div_factorial_le (n + 3)
  have hrn : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  calc |((bernoulli (n + 1 + 2) : ℚ) : ℝ)| * ((n + 1 : ℕ) : ℝ) * r ^ (n + 1 - 1)
        / (Nat.factorial (n + 1 + 2))
      = (|((bernoulli (n + 1 + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 1 + 2)))
          * (((n : ℝ) + 1) * r ^ n) := by push_cast; ring
    _ ≤ (4 / (2 * π) ^ (n + 3)) * (((n : ℝ) + 1) * r ^ n) := by gcongr
    _ = (4 / (2 * π) ^ 3) * (((n : ℝ) + 1) * x ^ n) := by
        rw [hx, div_pow, pow_add]
        field_simp

theorem frameBound_nonneg {w : ℝ} (hw0 : 0 ≤ w) : 0 ≤ frameBound w :=
  tsum_nonneg fun n ↦ by positivity

theorem frameLip_nonneg {w : ℝ} (hw0 : 0 ≤ w) : 0 ≤ frameLip w :=
  tsum_nonneg fun n ↦ by have := pow_nonneg hw0 (n - 1); positivity

/-- The first term of the majorant: `1/12 ≤ frameBound w`. -/
theorem one_div_twelve_le_frameBound {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    1 / 12 ≤ frameBound w := by
  have h := (summable_frameBound_majorant hw0 hw).le_tsum 0 fun j _ ↦ by positivity
  have h0 : |((bernoulli (0 + 2) : ℚ) : ℝ)| * w ^ 0 / (Nat.factorial (0 + 2)) = 1 / 12 := by
    norm_num [bernoulli_eq_bernoulli'_of_ne_one, bernoulli'_two, Nat.factorial]
  rwa [h0] at h

/-- `frameBound` is increasing on $[0, 2\pi)$, as its coefficients are nonnegative. -/
theorem frameBound_mono {w v : ℝ} (hw0 : 0 ≤ w) (hwv : w ≤ v) (hv : v < 2 * π) :
    frameBound w ≤ frameBound v :=
  (summable_frameBound_majorant hw0 (hwv.trans_lt hv)).tsum_le_tsum (fun n ↦ by gcongr)
    (summable_frameBound_majorant (hw0.trans hwv) hv)

/-- The majorant of the correction series is `1/2 + w · frameBound w`. -/
theorem corrBoundC_eq_half_add_mul {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    corrBoundC w = 1 / 2 + w * frameBound w := by
  have hs : Summable (fun n : ℕ ↦
      |((bernoulli (n + 1) : ℚ) : ℝ)| * w ^ n / (Nat.factorial (n + 1))) :=
    (summable_bernoulli'_succ_majorant hw0 hw).congr fun n ↦ by
      rw [abs_bernoulli'_eq_abs_bernoulli]
  rw [corrBoundC_eq_tsum_abs_bernoulli, hs.tsum_eq_zero_add, frameBound, ← tsum_mul_left]
  congr 1
  · norm_num [bernoulli_one]
  · exact tsum_congr fun n ↦ by rw [pow_succ]; ring

/-- Closed form of the frame majorant: `𝔫(x) = (1 - (x/2) cot(x/2))/x²` for `0 < x < 2π`. -/
theorem frameBound_eq_closedForm {x : ℝ} (hx0 : 0 < x) (hx : x < 2 * π) :
    frameBound x = (1 - (x / 2) * Real.cot (x / 2)) / x ^ 2 := by
  have h2 : corrBoundC x = 1 / 2 + (1 - (x / 2) * Real.cot (x / 2)) / x :=
    tsum_abs_bernoulli'_succ_eq hx0 hx
  have h3 : x * frameBound x = (1 - (x / 2) * Real.cot (x / 2)) / x := by
    linarith [corrBoundC_eq_half_add_mul hx0.le hx]
  rw [eq_div_iff (pow_ne_zero 2 hx0.ne'), sq, ← mul_assoc, mul_comm (frameBound x) x, h3,
    div_mul_cancel₀ _ hx0.ne']

/-- **`𝔫'` is the derivative of `𝔫`**: term-by-term differentiation of the majorant on
`|x| < 2π`. -/
theorem hasDerivAt_frameBound {x : ℝ} (hx : |x| < 2 * π) :
    HasDerivAt frameBound (frameLip x) x := by
  set r : ℝ := (|x| + 2 * π) / 2 with hrdef
  have hxr : |x| < r := by rw [hrdef]; linarith
  have hr2 : r < 2 * π := by rw [hrdef]; linarith
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hmem : ∀ y ∈ Set.Ioo (-r) r, |y| < r := fun y hy ↦ abs_lt.mpr ⟨hy.1, hy.2⟩
  have hframe :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ ↦
        |((bernoulli (n + 2) : ℚ) : ℝ)| * n * r ^ (n - 1) / (Nat.factorial (n + 2)))
      (g := fun (n : ℕ) (y : ℝ) ↦
        |((bernoulli (n + 2) : ℚ) : ℝ)| * y ^ n / (Nat.factorial (n + 2)))
      (g' := fun (n : ℕ) (y : ℝ) ↦
        |((bernoulli (n + 2) : ℚ) : ℝ)| * n * y ^ (n - 1) / (Nat.factorial (n + 2)))
      (summable_frameLip_majorant hr0.le hr2) isOpen_Ioo
      (convex_Ioo (-r) r).isPreconnected
      (fun n y _ ↦ ?_) (fun n y hy ↦ ?_) (y₀ := 0) ⟨by linarith, hr0⟩ ?_ (abs_lt.mp hxr)
  · exact hframe
  · convert ((hasDerivAt_pow n y).const_mul |((bernoulli (n + 2) : ℚ) : ℝ)|).div_const
      ((Nat.factorial (n + 2) : ℝ)) using 1
    ring
  · simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_abs, abs_pow, Nat.abs_cast]
    gcongr
    exact (hmem y hy).le
  · exact summable_frameBound_majorant le_rfl (by positivity)

/-- The norm of the coefficient $B_{n+2}/(n+2)!$. -/
theorem norm_frame_coefficient (n : ℕ) :
    ‖(((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ))‖ =
      |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) := by
  rw [norm_div]
  simp

omit [CompleteSpace A] in
/-- Norms of the terms of `frameSeries` are summable. -/
theorem summable_norm_frameSeries_terms (a : A) (ha : ‖a‖ < 2 * π) :
    Summable (fun n : ℕ ↦
      ‖(((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • a ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_frameBound_majorant (norm_nonneg a) ha)
  rw [norm_smul, norm_frame_coefficient, div_mul_eq_mul_div]
  gcongr
  exact norm_pow_le a n

/-- The correction series is its constant term `1/2` plus `a` times the frame series. -/
theorem corrSeries_eq_half_add_mul (a : A) (ha : ‖a‖ < 2 * π) :
    corrSeries a = (2⁻¹ : ℂ) • (1 : A) + a * frameSeries a := by
  rw [corrSeries_eq_half_add a ha, frameSeries,
    ← (summable_norm_frameSeries_terms a ha).of_norm.tsum_mul_left]
  congr 1
  exact tsum_congr fun n ↦ by rw [mul_smul_comm, pow_succ']

omit [CompleteSpace A] in
/-- The dimension-free bound on the frame series. -/
theorem norm_frameSeries_le_of_le {a : A} {w : ℝ} (haw : ‖a‖ ≤ w) (hw : w < 2 * π) :
    ‖frameSeries a‖ ≤ frameBound w := by
  have hsum := summable_norm_frameSeries_terms a (haw.trans_lt hw)
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  refine hsum.tsum_le_tsum (fun n ↦ ?_)
    (summable_frameBound_majorant ((norm_nonneg a).trans haw) hw)
  rw [norm_smul, norm_frame_coefficient, div_mul_eq_mul_div]
  gcongr
  exact (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) haw n)

/-- **The frame series is Lipschitz** on `‖a‖, ‖b‖ ≤ r < 2π`, with constant `frameLip r`. -/
theorem norm_frameSeries_sub_le {a b : A} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r)
    (hr : r < 2 * π) : ‖frameSeries a - frameSeries b‖ ≤ frameLip r * ‖a - b‖ := by
  have hr0 : 0 ≤ r := (norm_nonneg a).trans ha
  have hsa := (summable_norm_frameSeries_terms a (lt_of_le_of_lt ha hr)).of_norm
  have hsb := (summable_norm_frameSeries_terms b (lt_of_le_of_lt hb hr)).of_norm
  have hdiff : frameSeries a - frameSeries b
      = ∑' n : ℕ, (((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ))
          • (a ^ n - b ^ n) := by
    rw [frameSeries, frameSeries, ← Summable.tsum_sub hsa hsb]
    exact tsum_congr fun n ↦ (smul_sub _ _ _).symm
  have hmaj : ∀ n : ℕ,
      ‖(((bernoulli (n + 2) : ℚ) : ℂ) / (Nat.factorial (n + 2) : ℂ)) • (a ^ n - b ^ n)‖
        ≤ |((bernoulli (n + 2) : ℚ) : ℝ)| * n * r ^ (n - 1) / (Nat.factorial (n + 2))
            * ‖a - b‖ := by
    intro n
    rw [norm_smul, norm_frame_coefficient]
    calc |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ) * ‖a ^ n - b ^ n‖
        ≤ |((bernoulli (n + 2) : ℚ) : ℝ)| / (Nat.factorial (n + 2) : ℝ)
            * ((n : ℝ) * r ^ (n - 1) * ‖a - b‖) :=
          mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le ha hb n) (by positivity)
      _ = _ := by ring
  rw [hdiff, frameLip, ← tsum_mul_right]
  exact tsum_of_norm_bounded
    ((summable_frameLip_majorant hr0 hr).mul_right ‖a - b‖).hasSum hmaj

/-- The first moment minus half the average is the averaged commutator of the frame series. -/
theorem phiSeries_mul_frameSeries (a : A) (ha : ‖a‖ < 2 * π) :
    phiSeries a * (a * frameSeries a) = psiSeries a - (2⁻¹ : ℂ) • phiSeries a := by
  have h : phiSeries a * corrSeries a = psiSeries a := by
    rw [← bernSeries_mul_psiSeries a ha, ← mul_assoc, phiSeries_mul_bernSeries a ha,
      one_mul]
  rw [corrSeries_eq_half_add_mul a ha, mul_add, mul_smul_comm, mul_one] at h
  exact eq_sub_of_add_eq' h

end UnitaryProducts.Corrector

namespace UnitaryProducts

open UnitaryProducts.Corrector Complex Set MeasureTheory

variable {d : ℕ}

local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The frame operator `N_h(D) = ∑ B_{n+2} (i·ad_h)ⁿ D/(n+2)!`: the paper's
$\mathcal N(\mathrm{ad}_h)(D)$ (§4.1), as a power series in $i\,\mathrm{ad}_h$ with radius of
convergence $2\pi$. Odd Bernoulli numbers beyond $B_1$ vanish and
$(-1)^k B_{2k+2} = |B_{2k+2}|$, so this is the paper's series with coefficients $|B_{2k}|/(2k)!$
in $\mathrm{ad}_h^2$. When the series is not summable, `frameOp` is the `tsum` junk value $0$.
The lemmas here and in `Corrector/FrameMultiplier.lean` assume $\|i\,\mathrm{ad}_h\| < 2\pi$, or
$\|h - c\| \le w/2$ for a scalar $c$, or eigenvalues in an interval of length $w$, with
$w < 2\pi$; each gives $\|i\,\mathrm{ad}_h\| < 2\pi$, where the series converges absolutely. -/
noncomputable def frameOp (h D : 𝕄) : 𝕄 := frameSeries (I • adL h) D

/-- The Section 4.1 multiplier preserves input differences, as used in Lemma A.3. -/
theorem frameOp_sub (h D E : 𝕄) :
    frameOp h (D - E) = frameOp h D - frameOp h E :=
  map_sub (frameSeries (I • adL h)) D E

/-- **The size of the frame operator**: `‖N_h(D)‖ ≤ 𝔫(w) ‖D‖`. -/
theorem norm_frameOp_le [NeZero d] {h D : 𝕄} {c w : ℝ} (hw : w < 2 * π)
    (hwidth : ‖h - (c : ℂ) • 1‖ ≤ w / 2) : ‖frameOp h D‖ ≤ frameBound w * ‖D‖ := by
  have hA : ‖I • adL h‖ ≤ w := (norm_I_smul_adL_le h (c : ℂ)).trans (by linarith)
  exact ((frameSeries (I • adL h)).le_opNorm D).trans
    (mul_le_mul_of_nonneg_right (norm_frameSeries_le_of_le hA hw) (norm_nonneg D))

/-- **The frame operator is Lipschitz**:
`‖N_h(D) - N_{h'}(D')‖ ≤ 𝔫(w) ‖D - D'‖ + 2 𝔫'(w) ‖D'‖ ‖h - h'‖`, the bound of Lemma A.1(ii). -/
theorem norm_frameOp_sub_le [NeZero d] {h h' D D' : 𝕄} {c c' w : ℝ}
    (hw : w < 2 * π) (hwidth : ‖h - (c : ℂ) • 1‖ ≤ w / 2)
    (hwidth' : ‖h' - (c' : ℂ) • 1‖ ≤ w / 2) :
    ‖frameOp h D - frameOp h' D'‖ ≤
      frameBound w * ‖D - D'‖ + 2 * frameLip w * ‖D'‖ * ‖h - h'‖ := by
  have haw : ‖(I • adL h : 𝕄 →L[ℂ] 𝕄)‖ ≤ w := (norm_I_smul_adL_le h (c : ℂ)).trans (by linarith)
  have ha'w : ‖(I • adL h' : 𝕄 →L[ℂ] 𝕄)‖ ≤ w :=
    (norm_I_smul_adL_le h' (c' : ℂ)).trans (by linarith)
  have key : frameOp h D - frameOp h' D'
      = frameSeries (I • adL h) (D - D')
          + (frameSeries (I • adL h) - frameSeries (I • adL h')) D' := by
    simp only [frameOp, map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((frameSeries (I • adL h)).le_opNorm (D - D')).trans
      (mul_le_mul_of_nonneg_right (norm_frameSeries_le_of_le haw hw) (norm_nonneg _))
  · have hL : ‖frameSeries (I • adL h) - frameSeries (I • adL h')‖
        ≤ frameLip w * (2 * ‖h - h'‖) :=
      (norm_frameSeries_sub_le haw ha'w hw).trans (mul_le_mul_of_nonneg_left
        (norm_I_smul_adL_sub_le h h')
        (frameLip_nonneg (by linarith [(norm_nonneg _).trans hwidth])))
    rw [show 2 * frameLip w * ‖D'‖ * ‖h - h'‖ = frameLip w * (2 * ‖h - h'‖) * ‖D'‖ by ring]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Conjugating by a unit step of `h` and subtracting: the fundamental theorem of calculus for
`τ ↦ e^{iτh} X e^{-iτh}`. -/
theorem evol_conj_sub_self (h X : 𝕄) :
    evol h (-1) * X * evol h 1 - X
      = ∫ τ in (0 : ℝ)..1, evol h (-τ) * (I • adL h) X * evol h τ := by
  have hderiv (τ : ℝ) : HasDerivAt (fun τ : ℝ ↦ evol h (-τ) * X * evol h τ)
      (evol h (-τ) * (I • adL h) X * evol h τ) τ := by
    have h1 : HasDerivAt (fun τ : ℝ ↦ evol h (-τ)) (-((-I • h) * evol h (-τ))) τ := by
      simpa [Function.comp_def] using (hasDerivAt_evol h (-τ)).scomp τ (hasDerivAt_neg τ)
    have h3 := (h1.mul_const X).mul (hasDerivAt_evol h τ)
    convert h3 using 1
    rw [(commute_evol h (-τ)).eq, ContinuousLinearMap.smul_apply, adL_apply]
    simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, neg_smul, neg_mul,
      mul_neg, neg_neg, mul_assoc]
    abel
  have hcont : Continuous (fun τ : ℝ ↦ evol h (-τ) * (I • adL h) X * evol h τ) :=
    (((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hderiv τ)
    (hcont.intervalIntegrable 0 1)]
  simp [evol_zero]

/-- **The frame identity.**  Below the aliasing limit,
`e^{ih} N_h(D) e^{-ih} - N_h(D) = ∫₀¹ (τ - 1/2) e^{iτh} D e^{-iτh} dτ`: Stein's equation
(equal end values of the periodic corrector) for `frameOp`. -/
theorem evol_conj_frameOp_sub [NeZero d] (h D : 𝕄) (hw : ‖I • adL h‖ < 2 * π) :
    evol h (-1) * frameOp h D * evol h 1 - frameOp h D
      = ∫ τ in (0 : ℝ)..1, (τ - 1 / 2) • (evol h (-τ) * D * evol h τ) := by
  have hcont : Continuous (fun τ : ℝ ↦ evol h (-τ) * D * evol h τ) :=
    (((continuous_evol h).comp continuous_neg).mul continuous_const).mul (continuous_evol h)
  have h1 := congrArg (fun T : 𝕄 →L[ℂ] 𝕄 ↦ T D)
    (phiSeries_mul_frameSeries (I • adL h) hw)
  change phiSeries (I • adL h) ((I • adL h) (frameOp h D)) =
    psiSeries (I • adL h) D - (2⁻¹ : ℂ) • phiSeries (I • adL h) D at h1
  rw [phiSeries_adL_apply, ← evol_conj_sub_self, psiSeries_adL_apply,
    phiSeries_adL_apply] at h1
  have hpt (τ : ℝ) : (τ - 1 / 2) • (evol h (-τ) * D * evol h τ)
      = (τ : ℂ) • (evol h (-τ) * D * evol h τ)
        - (2⁻¹ : ℂ) • (evol h (-τ) * D * evol h τ) := by
    rw [← Complex.coe_smul, ← sub_smul]
    congr 1; push_cast; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub ((Complex.continuous_ofReal.smul hcont).intervalIntegrable 0 1)
    ((hcont.const_smul (2⁻¹ : ℂ)).intervalIntegrable 0 1), intervalIntegral.integral_smul, ← h1]

end UnitaryProducts
