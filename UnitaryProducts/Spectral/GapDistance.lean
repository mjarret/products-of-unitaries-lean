/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Approximation.TruncationLevels
public import UnitaryProducts.Corrector.BernoulliBounds

/-!
# Partial fractions of $\mathcal N$ and non-resonance margins

## Declarations

- `frameMult_eq_tsum`
- `exists_hasSeparatedSpectrum_of_nonresonant`
- `real_cot_series`
- `exists_allowed_finset`
- `exists_margin`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Set Real
noncomputable section

namespace UnitaryProducts.Corrector

/-- The real cotangent expansion, transferred from Mathlib's complex expansion. -/
private theorem real_cot_series {z : ℝ} (hz : ∀ n : ℤ, z ≠ n) :
    π * Real.cot (π*z) = 1/z + ∑' n : ℕ+, (1/(z-n)+1/(z+n)) := by
  have hc : (z : ℂ) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    exact hz n (by exact_mod_cast hn.symm)
  apply Complex.ofReal_injective
  convert cot_series_rep hc using 1 <;>
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_tsum,
      Real.cot_eq_cos_div_sin, Complex.cot, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_natCast]

/-- Partial fractions of the frame multiplier away from all integral resonances: for
$x \notin 2\pi\mathbb Z$, $(1 - (x/2)\cot(x/2))/x^2 = \sum_{n \ge 1} 2/(4\pi^2 n^2 - x^2)$,
the partial-fraction series of $\mathcal N$. It is Mathlib's `cot_series_rep` rescaled. -/
theorem frameMult_eq_tsum {x : ℝ} (hx : ∀ n : ℤ, x ≠ 2*π*n) :
    frameMult x = ∑' n : ℕ+, 2/(4*π^2*(n : ℝ)^2-x^2) := by
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hp : 2*π ≠ 0 := mul_ne_zero (by norm_num) pi_ne_zero
  let z := x/(2*π)
  have hz : ∀ n : ℤ, z ≠ n := fun n hn ↦
    hx n (by simpa only [mul_comm] using (div_eq_iff hp).mp hn)
  have hz0 : z ≠ 0 := div_ne_zero hx0 hp
  have hc := real_cot_series hz
  have ht (n : ℕ+) : -(1/(z-n)+1/(z+n))/(2*π*x) =
      2/(4*π^2*(n : ℝ)^2-x^2) := by
    have hm : z-(n : ℝ) ≠ 0 := sub_ne_zero.mpr (hz (n : ℕ))
    have ha : z+(n : ℝ) ≠ 0 := fun he ↦
      hz (-(n : ℤ)) (by push_cast; exact eq_neg_of_add_eq_zero_left he)
    have he : 4*π^2*(n : ℝ)^2-x^2 = -(2*π)^2*(z-n)*(z+n) := by
      dsimp [z]
      field_simp
      ; ring
    have hxe : x = 2*π*z := by dsimp [z]; field_simp
    rw [he, hxe]
    field_simp [hm, ha, hz0, pi_ne_zero]
    ; ring
  rw [frameMult, if_neg hx0, ← tsum_congr ht, tsum_div_const, tsum_neg,
    (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hc.symm)), show π*z=x/2 by dsimp [z]; field_simp]
  dsimp [z]; field_simp
  ; ring

end UnitaryProducts.Corrector

namespace UnitaryProducts.Separation

/-- A single nonresonant frequency has a positive margin. -/
private theorem exists_margin {x : ℝ}
    (hx : ∀ n : ℤ, n ≠ 0 → x ≠ 2*π*n) :
    ∃ γ > 0, x = 0 ∨ ∀ n : ℤ, n ≠ 0 → γ ≤ |x-2*π*n| := by
  by_cases hx0 : x=0
  · exact ⟨1, zero_lt_one, Or.inl hx0⟩
  have hp : 0 < 2*π := mul_pos (by norm_num) pi_pos
  let y := x/(2*π)
  have hy : ∀ n : ℤ, y ≠ n := fun n hn ↦ by
    have he : x=2*π*n := by simpa only [mul_comm] using (div_eq_iff hp.ne').mp hn
    by_cases hn0 : n=0
    · subst n; exact hx0 (by simpa using he)
    · exact hx n hn0 he
  have hl : (⌊y⌋ : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) (hy _).symm
  have hu : y < (⌊y⌋ : ℝ)+1 := Int.lt_floor_add_one y
  let δ := min (y-(⌊y⌋ : ℝ)) ((⌊y⌋ : ℝ)+1-y)
  have hd : 0 < δ := lt_min (sub_pos.mpr hl) (sub_pos.mpr hu)
  refine ⟨(2*π)*δ, mul_pos hp hd, Or.inr ?_⟩
  intro n _
  have hb : δ ≤ |y-(n : ℝ)| := by
    rcases le_or_gt n ⌊y⌋ with hn | hn
    · have hnr : (n : ℝ) ≤ ⌊y⌋ := by exact_mod_cast hn
      exact (min_le_left _ _).trans ((sub_le_sub_left hnr y).trans (le_abs_self _))
    · have hnr : (⌊y⌋ : ℝ)+1 ≤ n := by exact_mod_cast (Int.add_one_le_iff.mpr hn)
      exact (min_le_right _ _).trans ((sub_le_sub_right hnr y).trans
        ((le_abs_self _).trans_eq (abs_sub_comm _ _)))
  have he : x-2*π*n = (2*π)*(y-n) := by dsimp [y]; field_simp
  rw [he, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left hb hp.le

private theorem exists_allowed_finset {α : Type*} (s : Finset α) (v : α → ℝ)
    (hv : ∀ i ∈ s, ∀ n : ℤ, n ≠ 0 → v i ≠ 2*π*n) :
    ∃ γ > 0, ∃ W, ∀ i ∈ s, v i ∈ allowedDifferences γ W := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, 0, fun i hi ↦ False.elim (by simp at hi)⟩
  | @insert i s hi ih =>
    obtain ⟨γ, hγ, W, hW⟩ := ih (fun j hj ↦ hv j (Finset.mem_insert_of_mem hj))
    obtain ⟨δ, hδ, hd⟩ := exists_margin (hv i (Finset.mem_insert_self i s))
    refine ⟨min δ γ, lt_min hδ hγ, max |v i| W, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨abs_le.mp (le_max_left _ _),
        hd.imp_right fun hn n hn0 ↦ (min_le_left _ _).trans (hn n hn0)⟩
    · obtain ⟨hw, hd⟩ := hW j hj
      exact ⟨abs_le.mp ((abs_le.mpr hw).trans (le_max_right _ _)),
        hd.imp_right fun hn n hn0 ↦ (min_le_right _ _).trans (hn n hn0)⟩

variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- Finite spectra have common separation and width witnesses: if no eigenvalue difference of
$h$ lies in $2\pi\mathbb Z \setminus \{0\}$, there are $\gamma > 0$ and $W$ with every difference
in $[-W, W]$ and either $0$ or at least $\gamma$ from every nonzero multiple of $2\pi$. The proof
of the proof of Lemma A.1 uses it to reach the separated-spectrum form of the corrector. -/
theorem exists_hasSeparatedSpectrum_of_nonresonant {h : 𝕄} (hh : h.IsHermitian)
    (hn : ∀ p q (n : ℤ), n ≠ 0 → hh.eigenvalues p - hh.eigenvalues q ≠ 2 * π * n) :
    ∃ γ > 0, ∃ W, HasSeparatedSpectrum hh γ W := by
  obtain ⟨γ, hγ, W, hW⟩ := exists_allowed_finset (Finset.univ : Finset (Fin d × Fin d))
    (fun pq ↦ hh.eigenvalues pq.1-hh.eigenvalues pq.2) (fun pq _ ↦ hn pq.1 pq.2)
  exact ⟨γ, hγ, W, fun p q ↦ hW (p,q) (Finset.mem_univ _)⟩

end UnitaryProducts.Separation

