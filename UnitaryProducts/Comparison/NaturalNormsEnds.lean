/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.NaturalNorms

/-!
# The unit-step comparison on `[0, N]` with separate end coefficients

## Declarations

- `endpoint_local_width_ends`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real

noncomputable section
namespace UnitaryProducts.Dressed
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ
open UnitaryProducts.Corrector

/-- The comparison at unit steps on $[0,N]$, $N=n+2$, at width $w<2\pi$, with separate
coefficients on the two end steps and the interior steps: `b₀` (ends) and `b₁` (interior) on the
Lipschitz constants $M_i$ of $K'$, `r₀` and `r₁` on the squared bounds $L_i^2$ on $\|K'\|$. The
jumps are bounded by Lemma A.1(ii) and folded into the interior coefficients, using
`endpoint_local_of_frame_bounds`. -/
theorem endpoint_local_width_ends (K Kd U : ℝ → 𝕄) (n : ℕ) (w b₀ b₁ r₀ r₁ : ℝ)
    (L M : ℕ → ℝ) (z : ℕ → ℝ)
    (hw : w < 2 * π) (hK : ∀ t, (K t).IsHermitian)
    (hd : ∀ t ∈ Icc (0 : ℝ) (n + 2), HasDerivWithinAt K (Kd t) (Icc 0 (n + 2)) t)
    (hL : ∀ i ≤ n + 1, ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t‖ ≤ L i)
    (hlip : ∀ i ≤ n + 1, ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t - Kd s‖ ≤ M i * |t - s|)
    (hU : SolvesSchrodinger K U 0 (n + 2)) (hU0 : U 0 = 1)
    (hwidth : ∀ j : ℕ, 0 < j → j ≤ n+1 → ‖K j-(z j:ℂ) • 1‖ ≤ w/2)
    (hb0 : (1/8:ℝ) ≤ b₀) (hb1 : 1/24+frameBound w ≤ b₁)
    (hr0 : frameBound w-frameBound (w/2)/2+1/24 ≤ r₀)
    (hr1 : (frameBound w-frameBound (w/2)/2)/4+1/64+2*frameLip w ≤ r₁) :
    ‖pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      evol (K (n+2)) (-(1/2))*U (n+2)*evol (K 0) (1/2)‖ ≤
      (frameBound w-frameBound (w/2)/2)*(‖Kd 1‖+‖Kd (n+1)‖)+
      (b₀*(M 0+M (n+1))+b₁*(∑ j ∈ Finset.range n, M (j+1)))+r₀*((L 0)^2+(L (n+1))^2)+
      r₁*(∑ j ∈ Finset.range n, (L (j+1))^2) := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := by linarith [(norm_nonneg _).trans (hwidth 1 (by omega) (by omega))]
  have hM i (hi : i ≤ n + 1) := local_lipschitz_nonneg hi (hlip i hi)
  let q := frameBound w-frameBound (w/2)/2
  have hq : 0 ≤ q := (norm_nonneg _).trans (norm_frameSeries_sub_half_le
    (a := (0 : ℂ)) (by simpa only [norm_zero] using hw0) hw)
  have hA (j : ℕ) (hj : 0 < j) (hjn : j ≤ n+1) : ‖I • adL (K j)‖ ≤ w :=
    (norm_I_smul_adL_le (K j) (z j:ℂ)).trans (by linarith [hwidth j hj hjn])
  let F i := M i/24+(q/4+1/64)*(L i)^2
  let G i := 5*M i/48+(7*q/8+13/384)*(L i)^2
  let J i := frameBound w*M i+2*frameLip w*(L i)^2
  have hjump (j : ℕ) (hj : j<n) :
      ‖frameOp (K (j+2)) (Kd (j+2))-frameOp (K (j+1)) (Kd (j+1))‖ ≤ J (j+1) := by
    have hjR : (j:ℝ)<n := Nat.cast_lt.mpr hj
    have hmem : ∀ c : ℝ, 1 ≤ c → c ≤ 2 →
        ((j:ℝ)+c) ∈ Icc (localLeft (j+1)) (localRight n (j+1)) := fun c hc1 hc2 ↦ by
      simp only [localLeft, localRight, mem_Icc, max_le_iff, le_min_iff, Nat.cast_add, Nat.cast_one]
      constructor <;> constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hmem₁ := hmem 1 le_rfl one_le_two
    have hmem₂ := hmem 2 one_le_two le_rfl
    have hsub := local_subset n (j+1)
    have hk := norm_sub_le_of_derivWithin_le
      (fun t ht ↦ (hd t (hsub ht)).mono hsub) (hL (j+1) (by omega))
      _ hmem₁ _ hmem₂
    have hdd := hlip (j+1) (by omega) _ hmem₁ _ hmem₂
    have hone : (j:ℝ)+2-((j:ℝ)+1)=1 := by ring
    rw [hone,abs_one,mul_one] at hk hdd
    have hb := norm_frameOp_sub_le (D := Kd ((j+2:ℕ):ℝ)) (D' := Kd ((j+1:ℕ):ℝ))
      hw (hwidth (j+2) (by omega) (by omega)) (hwidth (j+1) (by omega) (by omega))
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hb
    refine hb.trans ?_
    calc _ ≤ frameBound w*M (j+1)+(2*frameLip w*L (j+1))*L (j+1) :=
          add_le_add (mul_le_mul_of_nonneg_left hdd (frameBound_nonneg hw0))
            (mul_le_mul
              (mul_le_mul_of_nonneg_left (hL (j+1) (by omega) _ hmem₁)
                (mul_nonneg (by norm_num) (frameLip_nonneg hw0)))
              hk (norm_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) (frameLip_nonneg hw0))
                ((norm_nonneg _).trans (hL (j+1) (by omega) _ hmem₁))))
      _ = J (j+1) := by dsimp [J]; ring
  have he := endpoint_local_of_frame_bounds K Kd U n q L M (fun j ↦ J (j+1)) hK hq hd hL hlip
    hU hU0
    (fun j hj hjn ↦ evol_conj_frameOp_sub _ _ ((hA j hj hjn).trans_lt hw))
    (fun j hj hjn ↦ norm_frame_center_le (hK j) hw (hA j hj hjn)) hjump
  change _ ≤ q*‖Kd 1‖+q*‖Kd (n+1)‖+
    (∑ j ∈ Finset.range (n+1), (F j+F (j+1))/2)+G 0+G (n+1)+
      (∑ j ∈ Finset.range n, J (j+1)) at he
  rw [sum_adjacent] at he
  have hbd i (hi : i≤n+1) : F i/2+G i ≤ b₀*M i+r₀*(L i)^2 := by
    calc _ = (1/8)*M i+(q+1/24)*(L i)^2 := by dsimp [F,G]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hb0 (hM i hi))
        (mul_le_mul_of_nonneg_right hr0 (sq_nonneg _))
  have hint i (hi : i≤n+1) : F i+J i ≤ b₁*M i+r₁*(L i)^2 := by
    calc _ = (1/24+frameBound w)*M i+(q/4+1/64+2*frameLip w)*(L i)^2 := by dsimp [F,J]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hb1 (hM i hi))
        (mul_le_mul_of_nonneg_right hr1 (sq_nonneg _))
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun j hj ↦ hint (j+1) (by have := Finset.mem_range.mp hj; omega))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change _ ≤ q*(‖Kd 1‖+‖Kd (n+1)‖)+_+_+_
  exact he.trans (by linarith only [hsum, hbd 0 (by omega), hbd (n+1) le_rfl])

end UnitaryProducts.Dressed
