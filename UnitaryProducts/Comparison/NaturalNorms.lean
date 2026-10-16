/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Comparison.EndpointHamiltonian

/-!
# The unit-step comparison on `[0, N]`, cell by cell

## Declarations

- `endpoint_local_of_frame_bounds`
- `first_local`
- `half_local_left`
- `half_local_right`
- `integral_half_center_majorant_left`
- `integral_half_center_majorant_right`
- `last_local`
- `localLeft`
- `localRight`
- `local_subset`
- `local_lipschitz_nonneg`
- `norm_last_half_center_local_le`
- `norm_part_cell_center_le`
- `norm_split_cell_center_le`
- `norm_three_part_traces_sum_le`
- `sum_adjacent`
- `sum_two_ends`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set MeasureTheory Real

noncomputable section
namespace UnitaryProducts.Dressed
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- The last half cell $[B-\frac12,B]$, which borrows the corrector of the last interior sample
$K(B-1)$: the change of the dressed product over it is at most $5M/48+(7q/8+13/384)L^2$, given
$\|K'\|\le L$, $K'$ $M$-Lipschitz on $[B-1,B]$, and the center bound $\|Y(0)\|\le qL$. -/
theorem norm_last_half_center_local_le {K Kd U : ℝ → 𝕄} {B q L M : ℝ} {P : 𝕄}
    (hB : 1 ≤ B) (hK : ∀ t, (K t).IsHermitian)
    (hd : ∀ t ∈ Icc (B - 1) B, HasDerivWithinAt K (Kd t) (Icc (B - 1) B) t)
    (hL : ∀ t ∈ Icc (B - 1) B, ‖Kd t‖ ≤ L)
    (hlip : ∀ s ∈ Icc (B - 1) B, ∀ t ∈ Icc (B - 1) B, ‖Kd t - Kd s‖ ≤ M * |t - s|)
    (hU : SolvesSchrodinger K U 0 B) (hUn : ∀ t ∈ Icc (0 : ℝ) B, ‖U t‖ ≤ 1)
    (hP : ‖P‖ ≤ 1)
    (hcenter : ‖frameExtension (K (B - 1)) (Kd (B - 1)) (frameOp (K (B - 1)) (Kd (B - 1)))
        (1 / 2)‖ ≤ q * L) :
    ‖star (U B)*(1-I • frameExtension (K (B-1)) (Kd (B-1))
        (frameOp (K (B-1)) (Kd (B-1))) (1/2))*(evol (K B) (1/2)*P)-
      star (U (B-1/2))*(1-I • frameOp (K (B-1)) (Kd (B-1)))*P‖ ≤
      5*M/48+(7*q/8+13/384)*L^2 := by
  have hc : Icc (B-1/2) B ⊆ Icc (0:ℝ) B := Icc_subset_Icc (by linarith) le_rfl
  have hbmem : B ∈ Icc (B-1) B := ⟨by linarith, le_rfl⟩
  have h1 : B-1 ∈ Icc (B-1) B := ⟨le_rfl, by linarith⟩
  have hKlip := norm_sub_le_of_derivWithin_le hd hL
  let V : ℝ → 𝕄 := fun t ↦ evol (K B) (t-(B-1/2))*P
  have hV t : HasDerivAt V (-I • (K B*V t)) t := by
    simpa only [V, Function.comp_def, one_smul, smul_mul_assoc, mul_assoc] using
      (((hasDerivAt_evol (K B) (t-(B-1/2))).scomp t
        ((hasDerivAt_id t).sub_const (B-1/2))).mul_const P)
  have hb := norm_borrowed_frame_cell (a := B-1/2) (b := B) (c := B)
    (h := K (B-1)) (g := K B) (D := Kd (B-1)) (Ybar := frameOp (K (B-1)) (Kd (B-1)))
    (by linarith) (fun t ht ↦ ((hU t (hc ht)).mono hc).continuousWithinAt)
    (fun t _ ↦ (hV t).continuousAt.continuousWithinAt) (fun t _ ↦ hK t)
    (fun t ht ↦ ((hU t (hc (Ioo_subset_Icc_self ht))).mono hc).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) (fun t _ ↦ hV t)
    (fun t ht ↦ hUn t (hc (Ioo_subset_Icc_self ht)))
    (fun t _ ↦ by simpa using norm_mul_le_of_le (norm_evol_le (hK B) _) hP)
    (fun t ↦ M*((B-t)-(B-t)^2/2)+(2-(B-t))*(q+(B-t)^2/2)*L^2)
    ((by fun_prop : Continuous fun t:ℝ ↦
      M*((B-t)-(B-t)^2/2)+(2-(B-t))*(q+(B-t)^2/2)*L^2).intervalIntegrable _ _)
    (fun t ht ↦ by
      have htm : t ∈ Icc (B-1) B := ⟨by linarith [ht.1], ht.2.le⟩
      have hr := norm_borrowed_taylor_left hd hlip htm hbmem h1 ht.2.le
        (by linarith [ht.1] : B-1 ≤ t)
      have hr' : ‖K t-K B-(t-B) • Kd (B-1)‖ ≤ M*((B-t)-(B-t)^2/2) := by
        rw [show K t-K B-(t-B) • Kd (B-1) = -(K B-K t-(B-t) • Kd (B-1)) by module, norm_neg]
        exact hr.trans_eq (by ring)
      have hu := hKlip (B-1) h1 t htm
      have hv := hKlip (B-1) h1 B hbmem
      rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t-(B-1))] at hu
      rw [abs_of_nonneg (by linarith : 0 ≤ B-(B-1))] at hv
      exact (norm_borrowed_residual_profile (hK (B-1)) (hL (B-1) h1) hcenter hr' hu hv).trans_eq
        (by ring))
  have he := intervalIntegral.integral_comp_sub_left
    (fun t:ℝ ↦ M*(t-t^2/2)+(2-t)*(q+t^2/2)*L^2) B (a := B-1/2) (b := B)
  have hs : B-(B-1/2)=(1/2:ℝ) := by ring
  have hl : B-1/2-B+1/2=0 := by ring
  have hv₀ : V (B-1/2)=P := by simp only [V, sub_self, evol_zero, one_mul]
  have hv₁ : V B=evol (K B) (1/2)*P := by dsimp [V]; rw [hs]
  rwa [he, sub_self, hs, integral_borrowed_half_majorant, hl, zero_add, frameExtension_zero, hv₀,
    hv₁] at hb

omit [NeZero d] in
/-- The telescoping of the dressed product $u^\dagger(1-iy)v$: if consecutive values differ by at
most $F_j$ across each full cell and $J_j$ across each jump, by $G_0$, $G_1$ across the two end
half cells, and the end correctors satisfy $\|y_0\|\le C_0$, $\|y_1\|\le C_1$, then
$\|u_1-v_1\|\le C_0+C_1+\sum F_j+G_0+G_1+\sum J_j$. Here $u$ is the evolution and $v$ the
rounded-clock product, both starting at $1$. -/
theorem norm_three_part_traces_sum_le (n : ℕ) (u v y : ℕ → 𝕄) (u₀ v₀ y₀ u₁ v₁ y₁ : 𝕄)
    (F J : ℕ → ℝ) (G₀ G₁ C₀ C₁ : ℝ)
    (hunit : star u₁ * u₁ = 1) (hv : ‖v₁‖ ≤ 1) (hzero : u₀ = 1) (hvzero : v₀ = 1)
    (hc₀ : ‖y₀‖ ≤ C₀) (hc₁ : ‖y₁‖ ≤ C₁)
    (hfirst : ‖star (u 0) * (1 - I • y 0) * v 0 - star u₀ * (1 - I • y₀) * v₀‖ ≤ G₀)
    (hlast : ‖star u₁ * (1 - I • y₁) * v₁ - star (u (n + 1)) * (1 - I • y n) * v (n + 1)‖ ≤ G₁)
    (hfull : ∀ j ≤ n, ‖star (u (j + 1)) * (1 - I • y j) * v (j + 1) -
      star (u j) * (1 - I • y j) * v j‖ ≤ F j)
    (hjump : ∀ j < n, ‖star (u (j + 1)) * (1 - I • y (j + 1)) * v (j + 1) -
      star (u (j + 1)) * (1 - I • y j) * v (j + 1)‖ ≤ J j) :
    ‖u₁-v₁‖ ≤ C₀+C₁+(∑ j ∈ Finset.range (n+1), F j)+G₀+G₁+(∑ j ∈ Finset.range n, J j) := by
  let left : ℕ → 𝕄 := fun j ↦ star (u j)*(1-I • y j)*v j
  let right : ℕ → 𝕄 := fun j ↦ star (u (j+1))*(1-I • y j)*v (j+1)
  have hm : ‖right n-left 0‖ ≤ (∑ j ∈ Finset.range (n+1), F j)+(∑ j ∈ Finset.range n, J j) := by
    exact (norm_piecewise_sub_le left right n).trans
      (add_le_add (Finset.sum_le_sum fun j hj ↦ hfull j (by simpa using Finset.mem_range.mp hj))
        (Finset.sum_le_sum fun j hj ↦ hjump j (Finset.mem_range.mp hj)))
  have hstart : ‖star u₀*(1-I • y₀)*v₀-1‖ ≤ C₀ := by
    rwa [hzero, hvzero, star_one, one_mul, mul_one, sub_sub_cancel_left, norm_neg, norm_smul,
      Complex.norm_I, one_mul]
  have hchain : ‖star u₁*(1-I • y₁)*v₁-1‖ ≤ G₁+((∑ j ∈ Finset.range (n+1), F j)+(∑ j ∈
    Finset.range n, J j))+(G₀+C₀) := by
    calc _ ≤ ‖star u₁*(1-I • y₁)*v₁-right n‖+‖right n-1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ G₁+(‖right n-left 0‖+‖left 0-1‖) :=
        add_le_add hlast (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ ≤ G₁+((∑ j ∈ Finset.range (n+1), F j)+(∑ j ∈ Finset.range n, J j))+(G₀+C₀) := by
        have hs := (norm_sub_le_norm_sub_add_norm_sub (left 0)
          (star u₀*(1-I • y₀)*v₀) 1).trans (add_le_add hfirst hstart)
        exact (add_le_add le_rfl (add_le_add hm hs)).trans_eq (by ring)
  exact ((norm_sub_le_dressed_add (Y := y₁) hunit hv).trans
    (add_le_add hchain hc₁)).trans_eq (by ring)

/-- The residual majorant integrated over the right half $[c,c+\frac12]$ of a cell:
$M/48+(q/8+1/128)L^2$. -/
theorem integral_half_center_majorant_right (c q L M : ℝ) :
    (∫ t in c..(c+1/2), M/2*(t-c)^2+L^2*|t-c| *(q+(t-c)^2/2)) =
      M/48+(q/8+1/128)*L^2 := by
  have he := intervalIntegral.integral_comp_sub_right (fun t:ℝ ↦ M/2*t^2+L^2*|t| *(q+t^2/2)) c
    (a := c) (b := c+1/2)
  rw [he, sub_self, show c+1/2-c=(1/2:ℝ) by ring]
  have hcongr : EqOn (fun t:ℝ ↦ M/2*t^2+L^2*|t| *(q+t^2/2))
      (fun t ↦ M/2*t^2+L^2*(q*t+t^3/2)) (uIcc 0 (1/2)) := fun t ht ↦ by
    rw [uIcc_of_le (by norm_num)] at ht; dsimp only; rw [abs_of_nonneg ht.1]; ring
  rw [intervalIntegral.integral_congr hcongr]
  let P : ℝ → ℝ := fun t ↦ M/6*t^3+L^2*(q*t^2/2+t^4/8)
  have hd (t : ℝ) : HasDerivAt P (M/2*t^2+L^2*(q*t+t^3/2)) t := by
    convert ((hasDerivAt_pow 3 t).const_mul (M/6)).add
      (((((hasDerivAt_pow 2 t).const_mul q).div_const 2).add
        ((hasDerivAt_pow 4 t).div_const 8)).const_mul (L^2)) using 1 ; dsimp [P] ; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    ((by fun_prop : Continuous fun t:ℝ ↦ M/2*t^2+L^2*(q*t+t^3/2)).intervalIntegrable _ _)]
  dsimp [P]; ring

/-- The residual majorant integrated over the left half $[c-\frac12,c]$ of a cell:
$M/48+(q/8+1/128)L^2$. -/
theorem integral_half_center_majorant_left (c q L M : ℝ) :
    (∫ t in (c-1/2)..c, M/2*(t-c)^2+L^2*|t-c| *(q+(t-c)^2/2)) =
      M/48+(q/8+1/128)*L^2 := by
  have he := intervalIntegral.integral_comp_sub_right (fun t:ℝ ↦ M/2*t^2+L^2*|t| *(q+t^2/2)) c
    (a := c-1/2) (b := c)
  rw [he, show c-1/2-c=(-1/2:ℝ) by ring, sub_self]
  have heven : (fun t : ℝ ↦ M/2*(-t)^2+L^2*|-t| *(q+(-t)^2/2)) =
      (fun t ↦ M/2*t^2+L^2*|t| *(q+t^2/2)) := by funext t; rw [neg_sq, abs_neg]
  rw [← heven, intervalIntegral.integral_comp_neg
    (fun t : ℝ ↦ M/2*t^2+L^2*|t| *(q+t^2/2))]
  simpa [neg_div] using integral_half_center_majorant_right 0 q L M

omit [NeZero d] in
/-- The residual bound (4.2) (`eq:corrected-residual`) of the proof of Theorem 4.2 on part $[a,b]$
of the cell around the
sample $c$: the change of the dressed product is at most
$\int_a^b\bigl(\frac M2(t-c)^2+L^2|t-c|(q+\frac{(t-c)^2}2)\bigr)dt$, from the Taylor remainder of
$K$ and the size profile of the proof of Lemma A.1. -/
theorem norm_part_cell_center_le {K Kd U : ℝ → 𝕄} {A B a b c q L M : ℝ} {P : 𝕄}
    (hab : a ≤ b) (hsub : Icc a b ⊆ Icc A B) (hcm : c ∈ Icc A B)
    (hK : ∀ t, (K t).IsHermitian)
    (hd : ∀ t ∈ Icc A B, HasDerivWithinAt K (Kd t) (Icc A B) t)
    (hL : ∀ t ∈ Icc A B, ‖Kd t‖ ≤ L)
    (hlip : ∀ s ∈ Icc A B, ∀ t ∈ Icc A B, ‖Kd t - Kd s‖ ≤ M * |t - s|)
    (hU : SolvesSchrodinger K U A B) (hUn : ∀ t ∈ Icc A B, ‖U t‖ ≤ 1)
    (hP : ‖P‖ ≤ 1)
    (hcenter : ‖frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (1 / 2)‖ ≤ q * L) :
    ‖star (U b)*(1-I • frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (b-c+1/2))*
        (evol (K c) (b-(c-1/2))*P)-
      star (U a)*(1-I • frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (a-c+1/2))*
        (evol (K c) (a-(c-1/2))*P)‖ ≤
      ∫ t in a..b, M/2*(t-c)^2+L^2*|t-c| *(q+(t-c)^2/2) := by
  let V : ℝ → 𝕄 := fun t ↦ evol (K c) (t-(c-1/2))*P
  have hV t : HasDerivAt V (-I • (K c*V t)) t := by
    simpa only [V, Function.comp_def, one_smul, smul_mul_assoc, mul_assoc] using
      (((hasDerivAt_evol (K c) (t-(c-1/2))).scomp t
        ((hasDerivAt_id t).sub_const (c-1/2))).mul_const P)
  have hKlip := norm_sub_le_of_derivWithin_le hd hL
  exact norm_borrowed_frame_cell (a := a) (b := b) (c := c)
    (h := K c) (g := K c) (D := Kd c) (Ybar := frameOp (K c) (Kd c))
    hab (fun t ht ↦ ((hU t (hsub ht)).mono hsub).continuousWithinAt)
    (fun t _ ↦ (hV t).continuousAt.continuousWithinAt) (fun t _ ↦ hK t)
    (fun t ht ↦ ((hU t (hsub (Ioo_subset_Icc_self ht))).mono hsub).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)) (fun t _ ↦ hV t)
    (fun t ht ↦ hUn t (hsub (Ioo_subset_Icc_self ht)))
    (fun t _ ↦ by simpa using norm_mul_le_of_le (norm_evol_le (hK c) _) hP)
    (fun t ↦ M/2*(t-c)^2+L^2*|t-c| *(q+(t-c)^2/2))
    ((by fun_prop : Continuous fun t:ℝ ↦ M/2*(t-c)^2+L^2*|t-c| *(q+(t-c)^2/2)).intervalIntegrable
      _ _)
    (fun t ht ↦ by
      have hr := norm_taylor_sub_le_of_lipschitz_deriv_half_Icc K Kd hd hlip c hcm t
        (hsub (Ioo_subset_Icc_self ht))
      have hp := norm_borrowed_residual_profile (hK c) (hL c hcm) hcenter hr
        (hKlip c hcm t (hsub (Ioo_subset_Icc_self ht)))
        (show ‖K c-K c‖ ≤ (0:ℝ) by rw [sub_self, norm_zero])
      exact hp.trans_eq (by ring))

omit [NeZero d] in
/-- One full cell $[c-\frac12,c+\frac12]$ around an interior sample $c$, split at $c$ so that each
half uses the bounds of its own unit step: the change of the dressed product is at most
$(M_1/24+(q/4+1/64)L_1^2+M_2/24+(q/4+1/64)L_2^2)/2$. Stein's equation (`hstein`) gives the
corrector equal end values, so the cell starts and ends at `Ybar`. -/
theorem norm_split_cell_center_le {K Kd U : ℝ → 𝕄} {A₁ B₁ A₂ B₂ c q L₁ M₁ L₂ M₂ : ℝ} {P : 𝕄}
    (h₁ : Icc (c - 1 / 2) c ⊆ Icc A₁ B₁) (h₂ : Icc c (c + 1 / 2) ⊆ Icc A₂ B₂)
    (hK : ∀ t, (K t).IsHermitian)
    (hd₁ : ∀ t ∈ Icc A₁ B₁, HasDerivWithinAt K (Kd t) (Icc A₁ B₁) t)
    (hd₂ : ∀ t ∈ Icc A₂ B₂, HasDerivWithinAt K (Kd t) (Icc A₂ B₂) t)
    (hL₁ : ∀ t ∈ Icc A₁ B₁, ‖Kd t‖ ≤ L₁) (hL₂ : ∀ t ∈ Icc A₂ B₂, ‖Kd t‖ ≤ L₂)
    (hlip₁ : ∀ s ∈ Icc A₁ B₁, ∀ t ∈ Icc A₁ B₁, ‖Kd t - Kd s‖ ≤ M₁ * |t - s|)
    (hlip₂ : ∀ s ∈ Icc A₂ B₂, ∀ t ∈ Icc A₂ B₂, ‖Kd t - Kd s‖ ≤ M₂ * |t - s|)
    (hU₁ : SolvesSchrodinger K U A₁ B₁) (hU₂ : SolvesSchrodinger K U A₂ B₂)
    (hUn₁ : ∀ t ∈ Icc A₁ B₁, ‖U t‖ ≤ 1) (hUn₂ : ∀ t ∈ Icc A₂ B₂, ‖U t‖ ≤ 1)
    (hP : ‖P‖ ≤ 1)
    (hstein : evol (K c) (-1) * frameOp (K c) (Kd c) * evol (K c) 1 - frameOp (K c) (Kd c) =
      cellPrimitive (K c) (Kd c) 1)
    (hcenter₁ : ‖frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (1 / 2)‖ ≤ q * L₁)
    (hcenter₂ : ‖frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (1 / 2)‖ ≤ q * L₂) :
    ‖star (U (c+1/2))*(1-I • frameOp (K c) (Kd c))*(evol (K c) 1*P)-
      star (U (c-1/2))*(1-I • frameOp (K c) (Kd c))*P‖ ≤
      (M₁/24+(q/4+1/64)*L₁^2+(M₂/24+(q/4+1/64)*L₂^2))/2 := by
  have hcm₁ : c ∈ Icc A₁ B₁ := h₁ ⟨by linarith, le_rfl⟩
  have hcm₂ : c ∈ Icc A₂ B₂ := h₂ ⟨le_rfl, by linarith⟩
  have hl := norm_part_cell_center_le (a := c-1/2) (b := c) (P := P) (by linarith) h₁ hcm₁ hK
    hd₁ hL₁ hlip₁ hU₁ hUn₁ hP hcenter₁
  have hr := norm_part_cell_center_le (a := c) (b := c+1/2) (P := P) (by linarith) h₂ hcm₂ hK
    hd₂ hL₂ hlip₂ hU₂ hUn₂ hP hcenter₂
  have e3 : c-c+1/2=(1/2:ℝ) := by ring
  have e6 : c-(c-1/2)=(1/2:ℝ) := by ring
  rw [integral_half_center_majorant_left, show c-1/2-c+1/2=(0:ℝ) by ring, e3,
    show c-1/2-(c-1/2)=(0:ℝ) by ring, e6, frameExtension_zero, evol_zero, one_mul] at hl
  rw [integral_half_center_majorant_right, show c+1/2-c+1/2=(1:ℝ) by ring, e3,
    show c+1/2-(c-1/2)=(1:ℝ) by ring, e6, (frameExtension_periodic_iff _ _ _).mpr hstein] at hr
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (star (U c)*(1-I • frameExtension (K c) (Kd c) (frameOp (K c) (Kd c)) (1/2))*
      (evol (K c) (1/2)*P)) _).trans ((add_le_add hr hl).trans_eq (by ring))

/-- The left endpoint $\max(0,i)=i$ of the unit cell $[i,i+1]$ of $[0,N]$ (the rescaled $i$-th
step of $[0,1]$). -/
def localLeft (i : ℕ) : ℝ := max 0 (i:ℝ)
/-- The right endpoint $\min(n+2,i+1)$ of the unit cell $[i,i+1]$ of $[0,N]$, $N=n+2$: it is
$i+1$ for $i\le n+1$, the only cells used. -/
def localRight (n i : ℕ) : ℝ := min ((n:ℝ)+2) ((i:ℝ)+1)

/-- Each unit cell lies in $[0,n+2]$. -/
theorem local_subset (n i : ℕ) :
    Icc (localLeft i) (localRight n i) ⊆ Icc (0:ℝ) (n+2) :=
  Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)

/-- The left half $[j+\frac12,j+1]$ of the full cell around the sample $j+1$ lies in cell $j$. -/
theorem half_local_left (n j : ℕ) (hj : j ≤ n) :
    Icc ((j:ℝ)+1-1/2) ((j:ℝ)+1) ⊆ Icc (localLeft j) (localRight n j) :=
  Icc_subset_Icc (max_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) (by linarith))
    (le_min (by linarith [(Nat.cast_le (α := ℝ)).mpr hj]) (by linarith))

/-- The right half $[j+1,j+\frac32]$ of the full cell around the sample $j+1$ lies in cell
$j+1$. -/
theorem half_local_right (n j : ℕ) (hj : j ≤ n) :
    Icc ((j:ℝ)+1) ((j:ℝ)+1+1/2) ⊆ Icc (localLeft (j+1)) (localRight n (j+1)) :=
  Icc_subset_Icc (max_le (by positivity) (by push_cast; linarith))
    (le_min (by linarith [(Nat.cast_le (α := ℝ)).mpr hj]) (by push_cast; linarith))

/-- $[0,1]$ is the first unit cell. -/
theorem first_local (n : ℕ) : Icc (0:ℝ) 1 ⊆ Icc (localLeft 0) (localRight n 0) :=
  Icc_subset_Icc (by norm_num [localLeft])
    (le_min (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num))

/-- $[N-1,N]$ is the last unit cell. -/
theorem last_local (n : ℕ) : Icc ((n:ℝ)+2-1) (n+2) ⊆
    Icc (localLeft (n+1)) (localRight n (n+1)) :=
  Icc_subset_Icc (max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by push_cast; linarith))
    (le_min le_rfl (by push_cast; linarith))

/-- Reindexing: a sum of averages of neighbours weighs the two end terms by $\frac12$ and each
interior term by $1$. Used to collect the cell residuals by unit step. -/
theorem sum_adjacent (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+1), (f j+f (j+1))/2) =
      f 0/2+f (n+1)/2+(∑ j ∈ Finset.range n, f (j+1)) := by
  induction n with
  | zero => simp only [Finset.sum_range_one, Finset.sum_range_zero, zero_add, add_zero]; ring
  | succ n ih => rw [Finset.sum_range_succ _ (n+1), ih, Finset.sum_range_succ _ n]; ring

/-- Reindexing: a sum over $n+2$ steps is the two end steps plus the $n$ interior steps. -/
theorem sum_two_ends (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (n+2), f j) = f 0+f (n+1)+(∑ j ∈ Finset.range n, f (j+1)) := by
  induction n with
  | zero => simp [Finset.sum_range_succ]
  | succ n ih => rw [Finset.sum_range_succ _ (n+2), ih, Finset.sum_range_succ _ n]; ring

omit [NeZero d] in
/-- Theorem 4.2 at unit steps on $[0,N]$, $N=n+2$, given at every interior sample $K(j)$
Stein's equation (`hstein`) and the center bound $\|Y_j(0)\|\le q\|K'(j)\|$ (`hcenter`), local
bounds $\|K'\|\le L_i$ and $M_i$-Lipschitz $K'$ on each unit cell, and bounds $J_j$ on the
jumps:
$\|W-e^{iK(N)/2}U(N)e^{-iK(0)/2}\|$ is at most the two end values $q\|K'(1)\|+q\|K'(N-1)\|$,
the
full-cell residuals, the two end half-cell residuals, and the jumps.

The proof follows the paper's proof of Theorem 4.2: telescope the dressed product
$U^\dagger(1-iY)V$, with $V$ the rounded-clock product, over (1) the first half cell, which
borrows the corrector of $K(1)$; (2) the last half cell, which borrows that of $K(N-1)$; (3) the
full cells $[j+\frac12,j+\frac32]$, with residuals from the Taylor remainder and the proof of
Lemma A.1;
(4) the jumps $\Delta_j$, each paid by its norm; (5) the end values $Y_1(0)$, $Y_{N-1}(0)$.
Finally the outer half-step phases are removed. -/
theorem endpoint_local_of_frame_bounds (K Kd U : ℝ → 𝕄) (n : ℕ) (q : ℝ) (L M J : ℕ → ℝ)
    (hK : ∀ t, (K t).IsHermitian) (hq : 0 ≤ q)
    (hd : ∀ t ∈ Icc (0 : ℝ) (n + 2), HasDerivWithinAt K (Kd t) (Icc 0 (n + 2)) t)
    (hL : ∀ i ≤ n + 1, ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t‖ ≤ L i)
    (hlip : ∀ i ≤ n + 1, ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t - Kd s‖ ≤ M i * |t - s|)
    (hU : SolvesSchrodinger K U 0 (n + 2)) (hU0 : U 0 = 1)
    (hstein : ∀ j : ℕ, 0 < j → j ≤ n+1 →
      evol (K j) (-1)*frameOp (K j) (Kd j)*evol (K j) 1-frameOp (K j) (Kd j) =
        cellPrimitive (K j) (Kd j) 1)
    (hcenter : ∀ j : ℕ, 0 < j → j ≤ n+1 →
      ‖frameExtension (K j) (Kd j) (frameOp (K j) (Kd j)) (1/2)‖ ≤ q*‖Kd j‖)
    (hjump : ∀ j < n, ‖frameOp (K (j+2)) (Kd (j+2))-frameOp (K (j+1)) (Kd (j+1))‖ ≤ J j) :
    ‖pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      evol (K (n+2)) (-(1/2))*U (n+2)*evol (K 0) (1/2)‖ ≤
      q*‖Kd 1‖+q*‖Kd (n+1)‖+
      (∑ j ∈ Finset.range (n+1),
        (M j/24+(q/4+1/64)*(L j)^2 + (M (j+1)/24+(q/4+1/64)*(L (j+1))^2))/2)+
      (5*M 0/48+(7*q/8+13/384)*(L 0)^2)+
      (5*M (n+1)/48+(7*q/8+13/384)*(L (n+1))^2)+
      (∑ j ∈ Finset.range n, J j) := by
  -- Setup: `P` is the rounded-clock product (half a step of `K 0` first, then unit steps), the
  -- paper's `Ŵ`; `y j` is the corrector end value `𝒩(ad_{K(j+1)})(K'(j+1))` of the cell around the
  -- sample `j + 1`.
  let P := pieceProduct (fun j ↦ if j=0 then (1/2:ℝ) else 1) (fun j ↦ K j)
  let y : ℕ → 𝕄 := fun j ↦ frameOp (K (j+1)) (Kd (j+1))
  have hUn : ∀ t ∈ Icc (0:ℝ) (n+2), ‖U t‖ ≤ 1 :=
    fun t ht ↦ hU.norm_le_one_of_initial_one (fun t _ ↦ hK t) hU0 ht
  have hPn j : ‖P j‖ ≤ 1 := norm_le_one_of_star_mul_self
    (star_pieceProduct_mul_self (fun k _ ↦ hK k))
  have hP0 : P 1=evol (K 0) (1/2) := by simp only [P, pieceProduct, ite_true, mul_one,
    Nat.cast_zero]
  have hPstep j : P (j+2)=evol (K (j+1)) 1*P (j+1) := by
    change evol (K ((j+1:ℕ):ℝ)) (if j+1=0 then 1/2 else 1)*P (j+1)=_
    rw [if_neg (by omega)]; push_cast; rfl
  have hfinalunit : star (U (n+2))*U (n+2)=1 := by
    rw [hU.star_mul_self_eq (fun t _ ↦ hK t) _ ⟨by positivity, le_rfl⟩,
      hU0, star_one, one_mul]
  have hfinalnorm : ‖evol (K (n+2)) (1/2)*P (n+2)‖ ≤ 1 := by
    simpa using norm_mul_le_of_le (norm_evol_le (hK _) _) (hPn (n+2))
  -- Step 1 (first half cell `[0, 1/2]`): it borrows the corrector of the sample `K(1)`.
  have hfirstSub := (first_local n).trans (local_subset n 0)
  have hfirst := norm_first_half_center_le (K := K) (Kd := Kd) (U := U)
    (B := 1) (q := q) (L := L 0) (M := M 0) le_rfl hK
    (fun t ht ↦ (hd t (hfirstSub ht)).mono hfirstSub)
    (fun t ht ↦ hL 0 (by omega) t (first_local n ht))
    (fun u hu t ht ↦ hlip 0 (by omega) u (first_local n hu) t (first_local n ht))
    (fun t ht ↦ (hU t (hfirstSub ht)).mono hfirstSub)
    (fun t ht ↦ hUn t (hfirstSub ht)) hU0
    (by simpa using hstein 1 (by omega) (by omega))
    (by
      have hb := hcenter 1 (by omega) (by omega)
      norm_num only [Nat.cast_one] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left (hL 0 (by omega) 1 (first_local n
        ⟨zero_le_one,le_rfl⟩)) hq))
  -- Step 2 (last half cell `[N - 1/2, N]`): it borrows the corrector of the sample `K(N-1)`.
  have hlastSub := (last_local n).trans (local_subset n (n+1))
  have hlast := norm_last_half_center_local_le (K := K) (Kd := Kd) (U := U) (P := P (n+2))
    (B := (n:ℝ)+2) (q := q) (L := L (n+1)) (M := M (n+1))
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) hK
    (fun t ht ↦ (hd t (hlastSub ht)).mono hlastSub)
    (fun t ht ↦ hL (n+1) le_rfl t (last_local n ht))
    (fun u hu t ht ↦ hlip (n+1) le_rfl u (last_local n hu) t (last_local n ht))
    hU hUn (hPn (n+2))
    (by
      rw [show (n:ℝ)+2-1=(n:ℝ)+1 by ring]
      have hc := hcenter (n+1) (by omega) le_rfl
      simp only [Nat.cast_add, Nat.cast_one] at hc
      exact hc.trans (mul_le_mul_of_nonneg_left
        (hL (n+1) le_rfl ((n:ℝ)+1) (last_local n ⟨by linarith,by linarith⟩)) hq))
  -- Telescoping (paper: the corrected integral of Theorem 2.2, cell by cell). The arguments
  -- below are, in order: the end values `‖Y_1(0)‖, ‖Y_{N-1}(0)‖ ≤ q ‖K'‖` (the proof of Lemma
  -- A.1); the
  -- two half cells of Steps 1 and 2; Step 3, the residual on each full cell; Step 4, each jump.
  have hm := norm_three_part_traces_sum_le n (fun j ↦ U (j+1/2)) (fun j ↦ P (j+1)) y
    (U 0) 1 (frameExtension (K 1) (Kd 1) (frameOp (K 1) (Kd 1)) (1/2))
    (U (n+2)) (evol (K (n+2)) (1/2)*P (n+2))
    (frameExtension (K (n+1)) (Kd (n+1)) (frameOp (K (n+1)) (Kd (n+1))) (1/2))
    (fun j ↦ (M j/24+(q/4+1/64)*(L j)^2 +
      (M (j+1)/24+(q/4+1/64)*(L (j+1))^2))/2) J
    (5*M 0/48+(7*q/8+13/384)*(L 0)^2)
    (5*M (n+1)/48+(7*q/8+13/384)*(L (n+1))^2)
    (q*‖Kd 1‖) (q*‖Kd (n+1)‖)
    hfinalunit hfinalnorm hU0 rfl
    (by simpa using hcenter 1 (by omega) (by omega))
    (by simpa only [Nat.cast_add, Nat.cast_one] using hcenter (n+1) (by omega) le_rfl)
    (by simpa only [Nat.cast_zero, zero_add, y, hP0, hU0, star_one, one_mul, mul_one] using hfirst)
    (by simpa only [show (n:ℝ)+2-1=(n:ℝ)+1 by ring, show (n:ℝ)+2-1/2=(n:ℝ)+1+1/2 by ring, y,
      Nat.cast_add, Nat.cast_one] using hlast)
    -- Step 3 (residual on the full cell `[j + 1/2, j + 3/2]` around the sample `j + 1`), split
    -- at the sample; Stein's equation gives the corrector equal end values.
    (by
      intro j hj
      have hs₁ := local_subset n j
      have hs₂ := local_subset n (j+1)
      have hc₁ : ((j:ℝ)+1) ∈ Icc (localLeft j) (localRight n j) :=
        half_local_left n j hj ⟨by linarith, le_rfl⟩
      have hc₂ : ((j:ℝ)+1) ∈ Icc (localLeft (j+1)) (localRight n (j+1)) :=
        half_local_right n j hj ⟨le_rfl, by linarith⟩
      have hcen := hcenter (j+1) (by omega) (by omega)
      simp only [Nat.cast_add,Nat.cast_one] at hcen
      have hb := norm_split_cell_center_le (c := (j:ℝ)+1) (P := P (j+1)) (q := q)
        (half_local_left n j hj) (half_local_right n j hj) hK
        (fun t ht ↦ (hd t (hs₁ ht)).mono hs₁) (fun t ht ↦ (hd t (hs₂ ht)).mono hs₂)
        (hL j (by omega)) (hL (j+1) (by omega)) (hlip j (by omega)) (hlip (j+1) (by omega))
        (hU.mono hs₁) (hU.mono hs₂)
        (fun t ht ↦ hUn t (hs₁ ht)) (fun t ht ↦ hUn t (hs₂ ht)) (hPn _)
        (by simpa only [Nat.cast_add,Nat.cast_one] using hstein (j+1) (by omega) (by omega))
        (hcen.trans (mul_le_mul_of_nonneg_left (hL j (by omega) _ hc₁) hq))
        (hcen.trans (mul_le_mul_of_nonneg_left (hL (j+1) (by omega) _ hc₂) hq))
      simpa only [y, Nat.cast_add, Nat.cast_one, show (j:ℝ)+1-1/2=(j:ℝ)+1/2 by ring, hPstep]
        using hb)
    -- Step 4 (jump `Δ_j` at time `j + 3/2`): the dressed product changes by at most `‖Δ_j‖`.
    (by
      intro j hj
      have hmem : (j:ℝ)+1+1/2 ∈ Icc (0:ℝ) (n+2) :=
        ⟨by positivity, by linarith [(Nat.cast_lt (α := ℝ)).mpr hj]⟩
      have hn := norm_dressed_jump_le (hUn _ hmem) (hPn (j+2)) (Y := y (j+1)) (Z := y j)
      simpa only [Nat.cast_add, Nat.cast_one] using hn.trans (by
        simpa only [y, Nat.cast_add, Nat.cast_one, show (j:ℝ)+1+1=(j:ℝ)+2 by ring]
          using hjump j hj))
  -- Step 5: the rounded-clock product is `e^{-iK(N)/2} W e^{iK(0)/2}` (paper: the rounded clock
  -- gives exact half-step phases); remove the unitary outer phases.
  have hp : pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)=P (n+2)*evol (K 0) (1/2) := by
    simpa only [P, Nat.cast_zero] using pieceProduct_one_eq_half_mul (fun j ↦ K j) (n+1)
  have he : pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      evol (K (n+2)) (-(1/2))*U (n+2)*evol (K 0) (1/2) =
      evol (K (n+2)) (-(1/2))*(evol (K (n+2)) (1/2)*P (n+2)-U (n+2))*evol (K 0) (1/2) := by
    rw [hp, mul_sub, sub_mul, ← mul_assoc, evol_neg_mul_self, one_mul]
  rw [he]
  rw [norm_sub_rev] at hm
  exact (norm_mul_le_of_le (norm_mul_le_of_le (norm_evol_le (hK _) _) hm)
    (norm_evol_le (hK _) _)).trans_eq (by ring)

open UnitaryProducts.Corrector

/-- A Lipschitz bound on a full local cell forces its constant to be nonnegative. -/
theorem local_lipschitz_nonneg {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    {n i : ℕ} {M : ℝ} (hi : i ≤ n + 1)
    (hlip : ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖F t - F s‖ ≤ M * |t - s|) : 0 ≤ M := by
  have hi' : (i : ℝ) + 1 ≤ n + 2 := by exact_mod_cast Nat.add_le_add_right hi 1
  have he : Icc (localLeft i) (localRight n i) = Icc (i : ℝ) (i + 1) := by
    simp only [localLeft, localRight, max_eq_right (Nat.cast_nonneg i), min_eq_right hi']
  have hb := hlip i (by rw [he]; constructor <;> linarith)
    (i + 1) (by rw [he]; constructor <;> linarith)
  simpa only [add_sub_cancel_left, abs_one, mul_one] using (norm_nonneg _).trans hb

end UnitaryProducts.Dressed
