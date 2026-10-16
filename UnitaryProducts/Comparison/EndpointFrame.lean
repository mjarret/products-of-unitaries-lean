/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Corrector.PeriodicFrameDecomposition
public import UnitaryProducts.Corrector.SeparatedScalarStein
public import UnitaryProducts.Corrector.SeparatedStein
public import UnitaryProducts.Corrector.SineBounds
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# The center value of the periodic corrector

## Declarations

- `frameMult_sub_half`
- `norm_frameSeries_sub_half_le`
- `two_frameMult_sub_half_pi`
- `norm_cellPrimitive_sub_center_le`
- `norm_frameExtension_le_center`
- `frame_center_eq`
- `norm_frame_center_le`
- `eigenvalue_sub_le_norm_I_adL`
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.L2Operator
open Real Complex Set MeasureTheory
noncomputable section

namespace UnitaryProducts.Corrector
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

/-- Expand the center multiplier coefficient by coefficient in a generic Banach algebra.
This identity supplies both the construction and its nonnegative majorant. -/
theorem frameSeries_sub_half_eq_tsum {a : A} (ha : ‖a‖ < 2 * π) :
    frameSeries a - (1/2 : ℂ) • frameSeries ((1/2 : ℂ) • a) =
      ∑' n : ℕ, ((1 - (1/2 : ℂ)^(n+1)) *
        ((bernoulli (n+2) : ℂ) / (Nat.factorial (n+2) : ℂ))) • a^n := by
  have hhalf : ‖(1/2 : ℂ) • a‖ < 2*π := by
    rw [norm_smul]; norm_num; linarith [norm_nonneg a, pi_pos]
  have hs := (summable_norm_frameSeries_terms a ha).of_norm
  have hs' := (summable_norm_frameSeries_terms ((1/2 : ℂ) • a) hhalf).of_norm
  rw [frameSeries, frameSeries, ← hs'.tsum_const_smul (1/2 : ℂ),
    ← hs.tsum_sub (hs'.const_smul (1/2 : ℂ))]
  refine tsum_congr fun n ↦ ?_
  rw [smul_pow, smul_smul, smul_smul, ← sub_smul]
  congr 1
  rw [pow_succ]
  ring

/-- The center multiplier $f(x)=\mathcal N(x)-\mathcal N(x/2)/2$ applied to $a$ with
$\|a\|\le w<2\pi$ has norm at most $f(w)$: its coefficient of $x^{2k}$ is that of $\mathcal N$ times
$1-4^{-k}/2>0$ (proof of Lemma A.1). -/
theorem norm_frameSeries_sub_half_le {a : A} {w : ℝ}
    (haw : ‖a‖ ≤ w) (hw : w < 2 * π) :
    ‖frameSeries a - (1/2 : ℂ) • frameSeries ((1/2 : ℂ) • a)‖ ≤
      frameBound w - frameBound (w/2) / 2 := by
  have hw0 := (norm_nonneg a).trans haw
  have ha := haw.trans_lt hw
  have hhalf : ‖(1/2 : ℂ) • a‖ < 2*π := by
    rw [norm_smul]; norm_num; linarith [norm_nonneg a, pi_pos]
  let c : ℕ → ℂ := fun n ↦ (bernoulli (n+2) : ℂ) / (Nat.factorial (n+2) : ℂ)
  let k : ℕ → ℝ := fun n ↦ 1 - (1/2 : ℝ)^(n+1)
  have hk0 (n : ℕ) : 0 ≤ k n :=
    sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  have hk1 (n : ℕ) : k n ≤ 1 := sub_le_self _ (pow_nonneg (by norm_num) _)
  have he : frameSeries a - (1/2 : ℂ) • frameSeries ((1/2 : ℂ) • a) =
      ∑' n : ℕ, ((k n : ℂ) * c n) • a^n := by
    simpa only [k, c, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_ofNat] using frameSeries_sub_half_eq_tsum ha
  let m : ℕ → ℝ := fun n ↦ k n * |(bernoulli (n+2) : ℝ)| * w^n / (Nat.factorial (n+2) : ℝ)
  have hm : Summable m := by
    apply Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
      (summable_frameBound_majorant hw0 hw)
    · dsimp [m]; exact div_nonneg (mul_nonneg (mul_nonneg (hk0 n) (abs_nonneg _))
        (pow_nonneg hw0 _)) (Nat.cast_nonneg _)
    · dsimp [m]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) (hk1 n)
  have hterm (n : ℕ) : ‖((k n : ℂ) * c n) • a^n‖ ≤ m n := by
    have hc := norm_frame_coefficient n
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk0 n), hc]
    exact (mul_le_mul_of_nonneg_left
      ((norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg a) haw n))
      (mul_nonneg (hk0 n) (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))).trans_eq
      (by dsimp [m]; ring)
  have hsum : (∑' n, m n) = frameBound w - frameBound (w/2)/2 := by
    have hw2 : w/2 < 2*π := by linarith [pi_pos]
    rw [frameBound, frameBound, div_eq_mul_inv, ← tsum_mul_right,
      ← (summable_frameBound_majorant hw0 hw).tsum_sub
        ((summable_frameBound_majorant (div_nonneg hw0 (by norm_num)) hw2).mul_right (2:ℝ)⁻¹)]
    exact tsum_congr fun n ↦ by dsimp [m, k]; rw [pow_succ, div_pow, div_pow]; ring
  rw [he]
  exact ((hm.of_norm_bounded hterm).hasSum.norm_le_of_bounded hm.hasSum hterm).trans_eq hsum

/-- The half-angle identity used to evaluate Theorem B's constant at width $\pi$:
$\mathcal N(x)-\mathcal N(x/2)/2=1/(2x\sin(x/2))-1/x^2$ for $0<x<2\pi$, from
$\cot\frac x4-\cot\frac x2=1/\sin\frac x2$. -/
theorem frameMult_sub_half {x : ℝ} (hx : 0 < x) (hx' : x < 2 * π) :
    frameMult x - frameMult (x/2)/2 = 1/(2*x*Real.sin (x/2)) - 1/x^2 := by
  have hx2 : x/2 ≠ 0 := div_ne_zero hx.ne' (by norm_num)
  have hs : Real.sin (x/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have ht := cot_half_sub_cot (y := x/2) (by linarith) (by linarith)
  rw [frameMult, if_neg hx.ne', frameMult, if_neg hx2]
  calc _ = (Real.cot ((x/2)/2)-Real.cot (x/2))/(2*x)-1/x^2 := by
          field_simp; ring
    _ = _ := by rw [ht]; field_simp

/-- At $x=\pi$: $2(\mathcal N(\pi)-\mathcal N(\pi/2)/2)=1/\pi-2/\pi^2$, that is, $2c_0$ at width
$\pi$. -/
theorem two_frameMult_sub_half_pi :
    2*(frameMult π-frameMult (π/2)/2) = 1/π-2/π^2 := by
  rw [frameMult_sub_half pi_pos (by linarith [pi_pos]), Real.sin_pi_div_two]
  ring

end UnitaryProducts.Corrector

namespace UnitaryProducts
open UnitaryProducts.Corrector Matrix
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- The center value of the periodic corrector (proof of Lemma A.1): at $\tau=0$ (Lean's
$s=\frac12$), $Y(0)=-f(\mathrm{ad}_h)(D)$ with $f(x)=\mathcal N(x)-\mathcal N(x/2)/2$ written as the
difference of two frame series; follows from the unique mean-zero corrector and matrix-level
halving. -/
theorem frame_center_eq {h : 𝕄} (hh : h.IsHermitian)
    (hdiff : ∀ p q, |hh.eigenvalues p - hh.eigenvalues q| < 2 * π) (D : 𝕄) :
    Dressed.frameExtension h D (frameOp h D) (1/2) =
      -((frameSeries (I • adL h) -
        (1/2:ℂ) • frameSeries ((1/2:ℂ) • (I • adL h))) D) := by
  ext a b : 2
  letI : NeZero d := ⟨a.pos.ne'⟩
  apply congrArg (fun X : 𝕄 ↦ X a b)
  let f : Fin d × Fin d → ℝ := fun pq ↦ |hh.eigenvalues pq.1 - hh.eigenvalues pq.2|
  let w := Finset.univ.sup' Finset.univ_nonempty f
  have hw : w < 2 * π :=
    (Finset.sup'_lt_iff Finset.univ_nonempty).2 (fun pq _ ↦ hdiff pq.1 pq.2)
  have hwid (p q : Fin d) : |hh.eigenvalues p - hh.eigenvalues q| ≤ w :=
    Finset.le_sup' f (Finset.mem_univ (p, q))
  have hc := PaperProof.periodic_corrector_center hw hh hwid D
  change Dressed.frameExtension h D (Paper.exponentialOperators h hh D).2.2.1
    (0 + 1 / 2) = _ at hc
  rw [← Paper.frameOp_eq_paper_value hh hw hwid D] at hc
  simpa only [zero_add] using hc

omit [NeZero d] in
/-- Every eigenvalue difference is bounded by the norm of the commutator operator. -/
theorem eigenvalue_sub_le_norm_I_adL {h : 𝕄} (hh : h.IsHermitian) (p q : Fin d) :
    |hh.eigenvalues p - hh.eigenvalues q| ≤ ‖I • adL h‖ := by
  let e := (Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary).symm.toAlgEquiv
  let E := e.symm (Matrix.single p q (1 : ℂ))
  have hE : E ≠ 0 := by
    intro hz
    have he := congrArg (fun X : 𝕄 ↦ e X p q) hz
    simp [E] at he
  have had : adL h E = ((hh.eigenvalues p - hh.eigenvalues q : ℝ) : ℂ) • E := by
    obtain ⟨hp, hq⟩ := Separation.eigenbasis_matrix_unit hh p q 1
    change h * E - E * h = _
    simpa only [← sub_smul, ← Complex.ofReal_sub] using congrArg₂ (· - ·) hp hq
  have hb := (I • adL h).le_opNorm E
  rw [ContinuousLinearMap.smul_apply, had, norm_smul, norm_smul, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs] at hb
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hE)).mp hb

omit [NeZero d] in
/-- The center bound of the proof of Lemma A.1: if $\|i\,\mathrm{ad}_h\|\le w<2\pi$, then
$\|Y(0)\|\le(\mathcal N(w)-\mathcal N(w/2)/2)\|D\|$ (`frameBound` is $\mathcal N$ on $[0,2\pi)$). -/
theorem norm_frame_center_le {h D : 𝕄} (hh : h.IsHermitian) {w : ℝ}
    (hw : w < 2 * π) (hA : ‖I • adL h‖ ≤ w) :
    ‖Dressed.frameExtension h D (frameOp h D) (1/2)‖ ≤
      (frameBound w-frameBound (w/2)/2)*‖D‖ := by
  -- In dimension zero every matrix vanishes; handle this before choosing an eigenvalue.
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz (X : Matrix (Fin 0) (Fin 0) ℂ) : X = 0 := Subsingleton.elim _ _
    simp only [hz, norm_zero, mul_zero, le_refl]
  letI : NeZero d := ⟨hd.ne'⟩
  rw [frame_center_eq hh (fun p q ↦
    (eigenvalue_sub_le_norm_I_adL hh p q).trans_lt (hA.trans_lt hw)), norm_neg]
  exact ((frameSeries (I • adL h)-(1/2:ℂ) • frameSeries ((1/2:ℂ) • (I • adL h))).le_opNorm D).trans
    (mul_le_mul_of_nonneg_right (norm_frameSeries_sub_half_le hA hw) (norm_nonneg D))

end UnitaryProducts

namespace UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The integral term of the corrector moves by at most $(s-\frac12)^2\|D\|/2$ away from the
center, since its derivative has norm $|s-\frac12|\|D\|$ (proof of Lemma A.1). -/
theorem norm_cellPrimitive_sub_center_le (h D : 𝕄) (hh : h.IsHermitian) (s : ℝ) :
    ‖cellPrimitive h D s-cellPrimitive h D (1/2)‖ ≤ (s-1/2)^2/2*‖D‖ := by
  have hb := norm_cellPrimitive_sub_le h D hh (1/2) s
    (by simpa only [le_min_iff, max_le_iff, le_refl, true_and] using le_total (1/2 : ℝ) s)
  simpa only [sub_self, abs_zero, zero_add, ← sq, sq_abs] using hb

/-- The profile of the proof of Lemma A.1 in terms of the actual center value:
$\|Y(\tau)\|\le\|Y(0)\|+\frac{\tau^2}2\|D\|$, $\tau=s-\frac12$, for any starting value `Ybar`. -/
theorem norm_frameExtension_le_center (h D Ybar : 𝕄) (hh : h.IsHermitian) (s : ℝ) :
    ‖frameExtension h D Ybar s‖ ≤
      ‖frameExtension h D Ybar (1/2)‖+(s-1/2)^2/2*‖D‖ := by
  have hrot : evol h (s-1/2)*frameExtension h D Ybar (1/2)*evol h (-(s-1/2)) =
      evol h s*(Ybar+cellPrimitive h D (1/2))*evol h (-s) := by
    simp only [frameExtension, ← mul_assoc, ← evol_add, sub_add_cancel]
    rw [mul_assoc, ← evol_add, show -(1/2:ℝ)+ -(s-1/2) = -s by ring]
  have he : frameExtension h D Ybar s =
      evol h (s-1/2)*frameExtension h D Ybar (1/2)*evol h (-(s-1/2)) +
      evol h s*(cellPrimitive h D s-cellPrimitive h D (1/2))*evol h (-s) := by
    rw [hrot, frameExtension]
    simp only [mul_add, add_mul, mul_sub, sub_mul]
    abel
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [neg_neg] using norm_evol_conj_le hh (frameExtension h D Ybar (1/2)) (-(s-1/2))
  · simpa only [neg_neg] using
      (norm_evol_conj_le hh (cellPrimitive h D s-cellPrimitive h D (1/2)) (-s)).trans
        (norm_cellPrimitive_sub_center_le h D hh s)

end UnitaryProducts.Dressed
