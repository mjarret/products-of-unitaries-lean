/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Comparison.Coefficients
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# The unit-step comparison at width below `2π`: jump form and `C²` forms

## Declarations

- `derivative_lipschitzOn_of_contDiffOn_two`
- `unit_steps_jumps_lip`
- `endpoint_local_jumps`
- `paper_series_eq`
- `unit_rhs_max_general`
- `unit_steps_jumps_width`
- `unit_steps_named_width`
- `unit_steps_width`
- `meshSupNorm_le_sSup`
- `unit_rhs_max_lip`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
open UnitaryProducts UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- the interior-sample comparison(ii) at unit steps on $[0,N]$, $N=n+2$, with the exact corrector
jumps: at width
$w<2\pi$ the error is at most $c_0(\|K'(1)\|+\|K'(N-1)\|)$, the residuals
$\sum_i(M_i/8+(c_0+\frac1{24})L_i^2)$ over the unit cells, and the jumps, the sum over $j$ of
$\|\mathcal N(\mathrm{ad}_{K(j+2)})(K'(j+2))-\mathcal N(\mathrm{ad}_{K(j+1)})(K'(j+1))\|$,
with $c_0=\mathcal N(w)-\mathcal N(w/2)/2$.

The proof supplies the inputs of `endpoint_local_of_frame_bounds` at each interior sample:
Stein's equation for the power series `frameOp` (`evol_conj_frameOp_sub`) and the center bound
(`norm_frame_center_le`, the proof of Lemma A.1); it then majorizes the exact residual
coefficients of the
interior halves and the end halves by $1/8$ and $c_2=c_0+1/24$ of the interior-sample comparison
(`sum_adjacent`,
`sum_two_ends`). -/
theorem endpoint_local_jumps [NeZero d] (K Kd U : ℝ → 𝕄) (n : ℕ) (w : ℝ)
    (L M : ℕ → ℝ) (z : ℕ → ℝ)
    (hw : w < 2 * π) (hK : ∀ t, (K t).IsHermitian)
    (hd : ∀ t ∈ Icc (0 : ℝ) (n + 2), HasDerivWithinAt K (Kd t) (Icc 0 (n + 2)) t)
    (hL : ∀ i ≤ n + 1, ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t‖ ≤ L i)
    (hlip : ∀ i ≤ n + 1, ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t - Kd s‖ ≤ M i * |t - s|)
    (hU : SolvesSchrodinger K U 0 (n + 2)) (hU0 : U 0 = 1)
    (hwidth : ∀ j : ℕ, 0 < j → j ≤ n+1 → ‖K j-(z j:ℂ) • 1‖ ≤ w/2) :
    ‖pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      evol (K (n + 2)) (-(1/2))*U (n+2)*evol (K 0) (1/2)‖ ≤
      (frameBound w-frameBound (w/2)/2)*(‖Kd 1‖+‖Kd (n+1)‖)+
      (∑ i ∈ Finset.range (n + 2), (M i/8+(frameBound w-frameBound (w/2)/2+1/24)*(L i)^2))+
      ∑ j ∈ Finset.range n, ‖frameOp (K (j+2)) (Kd (j+2))-frameOp (K (j+1)) (Kd (j+1))‖ := by
  -- The norm bound implies w ≥ 0; no separate nonnegativity hypothesis is needed.
  have hw0 : 0 ≤ w := by linarith [(norm_nonneg _).trans (hwidth 1 (by omega) (by omega))]
  have hM i (hi : i ≤ n + 1) := local_lipschitz_nonneg hi (hlip i hi)
  let q := frameBound w-frameBound (w/2)/2
  have hq : 0 ≤ q := (norm_nonneg _).trans (norm_frameSeries_sub_half_le
    (a := (0 : ℂ)) (by simpa only [norm_zero] using hw0) hw)
  have hA (j : ℕ) (hj : 0 < j) (hjn : j ≤ n+1) : ‖I • adL (K j)‖ ≤ w :=
    (norm_I_smul_adL_le (K j) (z j:ℂ)).trans (by linarith [hwidth j hj hjn])
  let J : ℕ → ℝ := fun j ↦ ‖frameOp (K (j+2)) (Kd (j+2))-frameOp (K (j+1)) (Kd (j+1))‖
  have he := endpoint_local_of_frame_bounds K Kd U n q L M J hK hq hd hL hlip hU hU0
    (fun j hj hjn ↦ evol_conj_frameOp_sub _ _ ((hA j hj hjn).trans_lt hw))
    (fun j hj hjn ↦ norm_frame_center_le (hK j) hw (hA j hj hjn))
    (fun j _ ↦ le_rfl)
  rw [sum_adjacent] at he
  let f : ℕ → ℝ := fun i ↦ M i/8+(q+1/24)*(L i)^2
  have hint (j : ℕ) (hj : j ∈ Finset.range n) :
      M (j+1)/24+(q/4+1/64)*(L (j+1))^2 ≤ f (j+1) := by
    have hMj := hM (j+1) (by have := Finset.mem_range.mp hj; omega)
    exact add_le_add (by linarith) (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  refine he.trans ?_
  rw [sum_two_ends n f]
  have hs := Finset.sum_le_sum hint
  change _ ≤ q*(‖Kd 1‖+‖Kd (n+1)‖)+(f 0+f (n+1)+∑ j ∈ Finset.range n, f (j+1))+
    ∑ j ∈ Finset.range n, J j
  calc _ = q*(‖Kd 1‖+‖Kd (n+1)‖)+(f 0+f (n+1)+
          ∑ j ∈ Finset.range n, (M (j+1)/24+(q/4+1/64)*(L (j+1))^2))+
          ∑ j ∈ Finset.range n, J j := by
        dsimp only [f]; ring
    _ ≤ _ := by gcongr

/-- the interior-sample comparison(ii) in jump form, with a Lipschitz constant $M_j$ of $H'$ on
each step: the error
is at most the end term $q\frac T{N^2}(\|H'(\frac1N)\|+\|H'(1-\frac1N)\|)$, the residuals
$\frac T{N^3}\sum_j(M_j/8+(q+\frac1{24})\frac TN L_j^2)$ with $L_j$ the step maximum of
$\|H'\|$ and $q=\mathcal N(w)-\mathcal N(w/2)/2$, and the exact corrector jumps
$\frac1N\sum_j\|F(\frac{j+2}N)-F(\frac{j+1}N)\|$ of
$F(s)=\mathcal N(\mathrm{ad}_{(T/N)H(s)})((T/N)H'(s))$.

The proof is the comparison's change of variables: (a) rescale to unit steps,
$K(t)=(T/N)H(t/N)$ and $V(t)=U(Tt/N)$ on $[0,N]$, and transfer the derivative bounds, the
evolution and the sample widths; (b) apply the unit-step comparison `endpoint_local_jumps`;
(c) translate the bound, including the jumps, back to $[0,1]$. -/
theorem unit_steps_jumps_lip [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (w : ℝ)
    (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (Mj : ℕ → ℝ)
    (hlip : ∀ i < N, ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
      ‖derivWithin H (Icc (0 : ℝ) 1) t - derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ Mj i * |t - s|)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let q := frameBound w-frameBound (w/2)/2
    let F : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) ((T/N) • Hd s)
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      q*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
      T/N^3*∑ j ∈ Finset.range N, (Mj j/8+(q+1/24)*(T/N)*(meshSupNorm Hd N j)^2)+
      1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  intro Hd q F
  -- Step (a): rescale to unit steps. Write `N = n + 2` and `c = T/N`.
  obtain ⟨n,rfl⟩ : ∃ n, N=n+2 := ⟨N-2,by omega⟩
  let R : ℝ := (n:ℝ)+2
  have hR : 0<R := by dsimp [R]; positivity
  have hcast : ((n+2:ℕ):ℝ)=R := by dsimp [R]; push_cast; rfl
  let c := T/R
  have hcpos : 0<c := div_pos hT hR
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ (hc.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hcd : ContDiffOn ℝ 0 Hd (Icc 0 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hL : ∀ i<n+2, ∀ s ∈ meshInterval (n+2) i, ‖Hd s‖ ≤ meshSupNorm Hd (n+2) i :=
    fun i _ s hs ↦ meshSup_bound hcd.continuousOn hs
  -- `G` is `H` frozen at `H 0` outside `[0, 1]`; it is only evaluated on `[0, 1]`.
  -- `K(t) = c G(t/N)` is the paper's unit-step Hamiltonian on `[0, N]`, with derivative `Kd`.
  let G : ℝ → 𝕄 := fun s ↦ if s ∈ Icc (0 : ℝ) 1 then H s else H 0
  have he : EqOn G H (Icc (0 : ℝ) 1) := fun s hs ↦ if_pos hs
  have hG : ∀ s, (G s).IsHermitian := fun s ↦ by
    dsimp only [G]; split_ifs with hs; exacts [hH s hs, hH 0 ⟨le_rfl, zero_le_one⟩]
  have hdG : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G (Hd s) (Icc 0 1) s :=
    fun s hs ↦ (hd s hs).congr (fun t ht ↦ he ht) (he hs)
  let K : ℝ → 𝕄 := fun t ↦ c • G (t/R)
  let Kd : ℝ → 𝕄 := fun t ↦ (c/R) • Hd (t/R)
  have hmem : ∀ t ∈ Icc (0 : ℝ) R, t/R ∈ Icc (0 : ℝ) 1 :=
    fun t ht ↦ ⟨div_nonneg ht.1 hR.le,(div_le_one hR).mpr ht.2⟩
  have hK : ∀ t, (K t).IsHermitian :=
    fun t ↦ UnitaryProducts.Separation.isHermitian_real_smul (hG _) c
  have hdK : ∀ t ∈ Icc (0 : ℝ) R, HasDerivWithinAt K (Kd t) (Icc 0 R) t := by
    intro t ht
    have hb := ((hdG (t/R) (hmem t ht)).scomp t
      (((hasDerivAt_id t).div_const R).hasDerivWithinAt) hmem).const_smul c
    simpa only
      [K,Kd,Function.comp_def,one_div,smul_smul,div_eq_mul_inv,id_eq,one_mul,Pi.smul_apply] using hb
  -- The unit cell `[i, i+1]` of `[0, N]` is the step `[i/N, (i+1)/N]` of `[0, 1]`; on it
  -- `‖K'‖ ≤ (T/N²) ℓ_i` and `K'` is `(T/N³) M_i`-Lipschitz.
  have hlocal i : ∀ t ∈ Icc (localLeft i) (localRight n i), t/R ∈ meshInterval (n+2) i := by
    intro t ht
    change max 0 (i:ℝ)/((n+2:ℕ):ℝ) ≤ t/R ∧ t/R ≤ min ((n+2:ℕ):ℝ) ((i:ℝ)+1)/((n+2:ℕ):ℝ)
    rw [hcast]
    exact ⟨(div_le_div_iff_of_pos_right hR).mpr ht.1,(div_le_div_iff_of_pos_right hR).mpr ht.2⟩
  have hkd (t : ℝ) : ‖Kd t‖=(c/R)*‖Hd (t/R)‖ := by
    dsimp only [Kd]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hcpos hR)]
  have hLK i (hi : i≤n+1) : ∀ t ∈ Icc (localLeft i) (localRight n i),
      ‖Kd t‖ ≤ (c/R)*meshSupNorm Hd (n+2) i := fun t ht ↦ (hkd t).le.trans
    (mul_le_mul_of_nonneg_left (hL i (by omega) _ (hlocal i t ht)) (div_nonneg hcpos.le hR.le))
  have hMK i (hi : i≤n+1) : ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t-Kd s‖ ≤ (c/R^2*Mj i)*|t-s| := by
    intro s hs t ht
    have hb := hlip i (by omega) _ (hlocal i s hs) _ (hlocal i t ht)
    dsimp [Kd]
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hcpos hR)]
    have hb' := mul_le_mul_of_nonneg_left hb (div_nonneg hcpos.le hR.le)
    rw [← sub_div,abs_div,abs_of_pos hR] at hb'
    exact hb'.trans_eq (by ring_nf)
  have hKc : ContinuousOn K (Icc (0 : ℝ) R) := fun t ht ↦ (hdK t ht).continuousWithinAt
  -- The evolution: `V(t) = U(Tt/N)` is the evolution of `K` on `[0, N]` (paper: `Û`).
  have hUG : IsEvolution (fun t ↦ G (t / T)) U 0 T := by
    obtain ⟨hu,h0,hunit,S,hS,hud⟩ := hU
    refine ⟨hu,h0,hunit,S,hS,fun t ht hn ↦ ?_⟩
    change HasDerivWithinAt U (-I • (G (t/T)*U t)) (Icc 0 T) t
    rw [he ⟨div_nonneg ht.1 hT.le,(div_le_one hT).mpr ht.2⟩]
    exact hud t ht hn
  have hTc : T/c=R := by dsimp [c]; field_simp
  let V : ℝ → 𝕄 := fun t ↦ U (c*t)
  have hUV : IsEvolution K V 0 R := by
    simpa only [hTc] using rescaled_evolution hUG hcpos
  have hV : UnitaryProducts.SolvesSchrodinger K V 0 R := continuous_evolution_solves hKc hUV
  have hV0 : V 0=1 := hUV.2.1
  -- The width hypothesis: the interior samples `K(j) = (T/N) H(j/N)` have eigenvalue differences
  -- at most `w`, so each lies within `w/2` of a scalar.
  have hs (k : ℕ) (hk : k ≤ n+2) : (k:ℝ)/R ∈ Icc (0 : ℝ) 1 := by
    rw [← hcast]; exact walkCubic_sample hk
  have hKdiff (j : ℕ) (hj : 0<j) (hjN : j≤n+1) : ∀ p q,
      |(hK j).eigenvalues p-(hK j).eigenvalues q| ≤ w := by
    simpa only [K,he (hs j (by omega))] using scaled_eigenvalue_bound (hH _ (hs j (by omega)))
      hcpos.le (fun p q ↦ by simpa only [hcast, c] using hdiff j hj (by omega) p q)
  let z (j : ℕ) := sInf (Set.range (hK j).eigenvalues)+w/2
  have hwidth (j : ℕ) hj hjn : ‖K j-(z j:ℂ) • 1‖ ≤ w/2 :=
    UnitaryProducts.norm_sub_smul_one_le_of_eigenvalues (hK j) hw0
      (eigen_interval (hK j) (hKdiff j hj hjn))
  -- Step (b): the comparison at unit steps on `[0, N]`.
  have hb := endpoint_local_jumps K Kd V n w (fun i ↦ (c/R)*meshSupNorm Hd (n+2) i)
    (fun i ↦ (c/R^2)*Mj i) z hw hK hdK hLK hMK hV hV0 hwidth
  -- Step (c): translate back to `[0, 1]`: `V(N) = U(T)`, `K(N) = c H(1)`, `K(0) = c H(0)`, and
  -- the product of the `K(j)` is `W_N`.
  have hVN : V R=U T := by
    change U (c*R)=U T
    rw [show c*R=T by dsimp [c]; field_simp]
  have hKN : K R=c • H 1 := by dsimp [K]; rw [div_self hR.ne',he ⟨zero_le_one,le_rfl⟩]
  have hK0 : K 0=c • H 0 := by dsimp [K]; rw [zero_div,he ⟨le_rfl,zero_le_one⟩]
  have hevol (A : 𝕄) (t : ℝ) : UnitaryProducts.evol (c • A) t=UnitaryProducts.evol A (c*t) := by
    rw [← UnitaryProducts.evol_energy_rescale A (c*t) hcpos.ne', mul_div_cancel_left₀ t hcpos.ne']
  have hp : UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)=
      (unitProduct (fun s ↦ c • H s) (n+2)).1 := by
    simpa only [unitProduct,K,hcast] using
      product_congr (n+2) (show EqOn (fun s ↦ c • G s) (fun s ↦ c • H s) (Icc (0 : ℝ) 1)
        from fun s hs ↦ by dsimp only; rw [he hs])
  change ‖UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      UnitaryProducts.evol (K R) (-(1/2))*V R*UnitaryProducts.evol (K 0) (1/2)‖ ≤ _ at hb
  rw [hp,hVN,hKN,hK0,hevol,hevol,hkd,hkd] at hb
  -- the jumps, in the path's coordinates
  have hjump (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖frameOp (K ((j:ℝ)+2)) (Kd ((j:ℝ)+2))-frameOp (K ((j:ℝ)+1)) (Kd ((j:ℝ)+1))‖ =
        1/R*‖F ((j+2:ℕ)/((n+2:ℕ):ℝ))-F ((j+1:ℕ)/((n+2:ℕ):ℝ))‖ := by
    have hjn := Finset.mem_range.mp hj
    have hs2 : ((j:ℝ)+2)/R ∈ Icc (0 : ℝ) 1 := by exact_mod_cast hs (j+2) (by omega)
    have hs1 : ((j:ℝ)+1)/R ∈ Icc (0 : ℝ) 1 := by exact_mod_cast hs (j+1) (by omega)
    have hF (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        frameOp (c • G s) ((c/R) • Hd s) = (1/R : ℝ) • F s := by
      dsimp only [F]
      rw [he hs, hcast, show (c/R) • Hd s = (1/R : ℝ) • (c • Hd s) by
        rw [smul_smul, one_div_mul_eq_div]]
      exact (frameSeries (I • adL (c • H s))).map_smul_of_tower _ _
    dsimp only [K, Kd]
    rw [hF _ hs2,hF _ hs1,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hR),hcast]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hjump] at hb
  have heqL i : ((c/R)*meshSupNorm Hd (n+2) i)^2=(c/R)^2*(meshSupNorm Hd (n+2) i)^2 := by ring
  simp_rw [heqL] at hb
  have e1 : ((n:ℝ)+1)/R = 1-1/((n+2:ℕ):ℝ) := by rw [hcast]; dsimp only [R]; field_simp; ring
  rw [e1, ← hcast] at hb
  have hc' : c = T/((n+2:ℕ):ℝ) := by rw [hcast]
  rw [hc', show T/((n+2:ℕ):ℝ)*-(1/2) = -(T/(2*((n+2:ℕ):ℝ))) by ring,
    show T/((n+2:ℕ):ℝ)*(1/2) = T/(2*((n+2:ℕ):ℝ)) by ring,
    show frameBound w - frameBound (w/2)/2 = q from rfl] at hb
  simp only [show n+2-2=n by omega]
  refine hb.trans_eq ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  field_simp

/-- Twice continuously differentiable paths have locally Lipschitz derivatives: on each step,
$H'$ is Lipschitz with constant $\max_{\text{step}}\|H''\|$ (mean value inequality). -/
theorem derivative_lipschitzOn_of_contDiffOn_two (H : ℝ → 𝕄) (N : ℕ)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1)) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    ∀ i, ∀ s ∈ meshInterval N i, ∀ t ∈ meshInterval N i,
      ‖Hd t-Hd s‖ ≤ meshSupNorm Hdd N i * |t-s| := by
  intro Hd Hdd i s hs t ht
  have hcd : ContDiffOn ℝ 1 Hd (Icc 0 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcdd : ContDiffOn ℝ 0 Hdd (Icc (0 : ℝ) 1) :=
    hcd.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  exact UnitaryProducts.norm_sub_le_of_derivWithin_le (fun u hu ↦
      ((hcd.differentiableOn (by norm_num) u (mesh_subset hu)).hasDerivWithinAt).mono mesh_subset)
    (fun u hu ↦ meshSup_bound hcdd.continuousOn hu) s hs t ht

/-- The jump form of the unit-step comparison at width `w` for a $C^2$ path, in the path's own
coordinates: the right side keeps the exact corrector jumps
$F(\frac{j+2}N)-F(\frac{j+1}N)$, $F(s)=\mathcal N(\mathrm{ad}_{(T/N)H(s)})((T/N)H'(s))$, and uses
the step maximum of $\|H''\|$ as the Lipschitz constant of $H'$.

This specializes `unit_steps_jumps_lip` using `derivative_lipschitzOn_of_contDiffOn_two`.
The shared proof rescales to $K(t)=(T/N)H(t/N)$ on $[0,N]$, applies `endpoint_local_jumps`,
and translates back, including the exact corrector jumps. -/
theorem unit_steps_jumps_width [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (w : ℝ)
    (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let q := frameBound w-frameBound (w/2)/2
    let F : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) ((T/N) • Hd s)
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      q*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
      T/N^3*∑ j ∈ Finset.range N, (meshSupNorm Hdd N j/8+(q+1/24)*(T/N)*(meshSupNorm Hd N j)^2)+
      1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖ := by
  exact unit_steps_jumps_lip H U T N w hT hN2 hw hH (hc.of_le (by norm_num))
    (meshSupNorm (derivWithin (derivWithin H (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1)) N)
    (fun i _ ↦ derivative_lipschitzOn_of_contDiffOn_two H N hc i) hdiff hU

/-- The paper's series $\mathcal N(x)=\sum_{n\ge1}2/(4\pi^2n^2-x^2)$ and its derivative are the
Bernoulli majorants `frameBound`, `frameLip` on $[0,2\pi)$. -/
theorem paper_series_eq {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2 * π) :
    (∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)) = frameBound x ∧
      deriv (fun y : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-y^2)) x = frameLip x := by
  have ha : |x| < 2*π := by rwa [abs_of_nonneg hx0]
  exact ⟨(frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt ha)).symm.trans
      (by simpa only [abs_of_nonneg hx0] using (frameBound_abs_eq_frameMult ha).symm),
    (deriv_frameMult_eq_partialFractions ha).symm.trans (hasDerivAt_frameMult ha).deriv⟩

/-- A mesh-cell norm maximum is at most the maximum on the whole parameter interval. -/
theorem meshSupNorm_le_sSup {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hc : ContinuousOn F (Icc (0 : ℝ) 1)) {N i : ℕ} :
    meshSupNorm F N i ≤ sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1) := by
  exact Real.sSup_le
    (fun _ ⟨s, hs, he⟩ ↦ he ▸ hc.norm.le_sSup_image_Icc (mesh_subset hs))
    (Real.sSup_nonneg fun _ ⟨s, _, he⟩ ↦ he ▸ norm_nonneg (F s))

/-- the interior-sample comparison(i) for the end and residual terms: with $M_j\le M$ on every
step and
$L=\max_{[0,1]}\|H'\|$, the end term and the residuals of part (ii) are at most
$\frac T{N^2}(2c_0L+c_1M+c_2TL^2/N)$, for any nonnegative $c_0,c_1,c_2$. -/
theorem unit_rhs_max_lip (H : ℝ → 𝕄) (T c₀ c₁ c₂ : ℝ) (N : ℕ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (h0 : 0 ≤ c₀) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (hc : ContDiffOn ℝ 1 H (Icc (0 : ℝ) 1))
    (Mj : ℕ → ℝ) (M : ℝ) (hMM : ∀ i < N, Mj i ≤ M) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
    c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
      T/N^3*∑ j ∈ Finset.range N, (c₁*Mj j+c₂*(T/N)*(meshSupNorm Hd N j)^2) ≤
    T/N^2*(2*c₀*L+c₁*M+c₂*T*L^2/N) := by
  intro Hd L
  have hNR : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1 ≤ N by omega)
  have hd : ContDiffOn ℝ 0 Hd (Icc 0 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hp0 : ‖Hd (1/N)‖ ≤ L := hd.continuousOn.norm.le_sSup_image_Icc (c := (1:ℝ)/N)
    ⟨div_nonneg zero_le_one hNR.le, (div_le_one hNR).mpr hN1⟩
  have hp1 : ‖Hd (1-1/N)‖ ≤ L := hd.continuousOn.norm.le_sSup_image_Icc (c := 1-(1:ℝ)/N)
    ⟨sub_nonneg.mpr ((div_le_one hNR).mpr hN1), sub_le_self _ (div_nonneg zero_le_one hNR.le)⟩
  have hTN2 : 0 ≤ T/N^2 := div_nonneg hT.le (sq_nonneg _)
  have hTN3 : 0 ≤ T/N^3 := div_nonneg hT.le (pow_nonneg (Nat.cast_nonneg N) 3)
  have hTN : 0 ≤ T/N := div_nonneg hT.le (Nat.cast_nonneg N)
  have hj (j : ℕ) (hj : j ∈ Finset.range N) :
      c₁*Mj j+c₂*(T/N)*(meshSupNorm Hd N j)^2 ≤ c₁*M+c₂*(T/N)*L^2 := by
    have hjN := Finset.mem_range.mp hj
    exact add_le_add (mul_le_mul_of_nonneg_left (hMM j hjN) h1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        meshSup_nonneg
        (meshSupNorm_le_sSup hd.continuousOn) 2) (mul_nonneg h2 hTN))
  calc _ ≤ c₀*(T/N^2)*(L+L)+T/N^3*∑ _j ∈ Finset.range N, (c₁*M+c₂*(T/N)*L^2) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hp0 hp1) (mul_nonneg h0 hTN2))
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hj) hTN3)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
        ring

/-- The global form, as in the interior-sample comparison(i), of the $C^2$ bound for any
nonnegative constants:
the end term and the step residuals are at most $\frac T{N^2}(2c_0L+c_1M+c_2TL^2/N)$ with
$L=\max\|H'\|$, $M=\max\|H''\|$ (both `sSup`s of continuous norms on $[0,1]$, so genuine maxima). -/
theorem unit_rhs_max_general (H : ℝ → 𝕄) (T c₀ c₁ c₂ : ℝ) (N : ℕ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (h0 : 0 ≤ c₀) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1)) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
    let M := sSup ((fun s ↦ ‖Hdd s‖) '' Icc (0 : ℝ) 1)
    c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
      T/N^3*∑ j ∈ Finset.range N, (c₁*meshSupNorm Hdd N j+c₂*(T/N)*(meshSupNorm Hd N j)^2) ≤
    T/N^2*(2*c₀*L+c₁*M+c₂*T*L^2/N) := by
  intro Hd Hdd L M
  have hd : ContDiffOn ℝ 1 Hd (Icc 0 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hdd : ContDiffOn ℝ 0 Hdd (Icc 0 1) := hd.derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  exact unit_rhs_max_lip H T c₀ c₁ c₂ N hT hN2 h0 h1 h2 (hc.of_le (by norm_num))
    (meshSupNorm Hdd N) M (fun _ _ ↦ meshSupNorm_le_sSup hdd.continuousOn)

/-- The $C^2$ unit-step comparison at width $w<2\pi$ with one coefficient pair on every step,
$c_1=1/24+\mathcal N(w)$ on the step maxima of $\|H''\|$ and
$c_2=\max(c_0+1/24,\,c_0/4+1/64+2\mathcal N'(w))$ on $\frac TN$ times the step maxima of
$\|H'\|^2$; the jumps are already bounded by Lemma A.1(ii) and folded in. -/
theorem unit_steps_named_width [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (w : ℝ)
    (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let c₀ := frameBound w-frameBound (w/2)/2
    let c₁ := 1/24+frameBound w
    let c₂ := max (c₀+1/24) (c₀/4+1/64+2*frameLip w)
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
    c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
      T/N^3*∑ j ∈ Finset.range N, (c₁*meshSupNorm Hdd N j+c₂*(T/N)*(meshSupNorm Hd N j)^2) := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  intro Hd Hdd c₀ c₁ c₂
  have h12 := one_div_twelve_le_frameBound hw0 hw
  have hb := unit_steps_local_norms_ends H U T N w c₁ c₁ c₂ c₂ hT hN2 hw hH hc hdiff hU
    (by dsimp only [c₁]; linarith) le_rfl (le_max_left _ _) (le_max_right _ _)
  refine hb.trans_eq ?_
  obtain ⟨n, rfl⟩ : ∃ n, N = n+2 := ⟨N-2, by omega⟩
  have hR : (0 : ℝ) < ((n+2:ℕ):ℝ) := by positivity
  dsimp only [boundaryMean]
  rw [show (((n+2:ℕ):ℝ)-1)/((n+2:ℕ):ℝ) = 1-1/((n+2:ℕ):ℝ) by field_simp, sum_two_ends n,
    show n+2-1 = n+1 from rfl, show n+2-2 = n from rfl]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  field_simp
  ring

/-- The $C^2$ unit-step comparison at width $w<2\pi$, bundled for the walk comparison: constants
$c_0=\mathcal N(w)-\mathcal N(w/2)/2$, $c_1=1/24+\mathcal N(w)$,
$c_2=\max(c_0+1/24,\,c_0/4+1/64+2\mathcal N'(w))$ (with their values and bounds at $w=\pi$), the
bound with one coefficient pair (`unit_steps_named_width`), the jump form
(`unit_steps_jumps_width`), and the global form (`unit_rhs_max_general`). -/
theorem unit_steps_width [NeZero d] (w : ℝ) (hw0 : 0 ≤ w) (hw : w < 2 * π) :
    let Nf : ℝ → ℝ := fun x ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)
    ∃ c₀ c₁ c₂ : ℝ,
    (c₀ = Nf w-Nf (w/2)/2 ∧ c₁ = 1/24+Nf w ∧ c₂ = max (c₀+1/24) (c₀/4+1/64+2*deriv Nf w) ∧
      (w = π → c₀ = 1/(2 * π)-1/π^2 ∧ c₀ < 1/16 ∧ c₁ = 1/24+1/π^2 ∧ c₁ < 1/6 ∧
        c₂ = max (c₀+1/24) (c₀/4+1/64+(1-8/π^2)/(2 * π)))) ∧
    (∀ (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
      (_ : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
      (_ : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
        (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
          (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
      (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
      let F : ℝ → 𝕄 := fun s ↦ frameOp ((T/N) • H s) ((T/N) • Hd s)
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
          T/N^3*∑ j ∈ Finset.range N, (c₁*meshSupNorm Hdd N j+c₂*(T/N)*(meshSupNorm Hd N j)^2) ∧
      ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
        UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
        c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
          T/N^3*∑ j ∈ Finset.range N, (meshSupNorm Hdd N j/8+(c₀+1/24)*(T/N)*(meshSupNorm Hd N
            j)^2)+
          1/N*∑ j ∈ Finset.range (N-2), ‖F ((j+2:ℕ)/N)-F ((j+1:ℕ)/N)‖) ∧
    (∀ (H : ℝ → 𝕄) (T : ℝ) (N : ℕ) (_ : 0 < T) (_ : 2 ≤ N)
      (_ : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1)),
      let Hd := derivWithin H (Icc (0 : ℝ) 1)
      let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
      let L := sSup ((fun s ↦ ‖Hd s‖) '' Icc (0 : ℝ) 1)
      let M := sSup ((fun s ↦ ‖Hdd s‖) '' Icc (0 : ℝ) 1)
      c₀*(T/N^2)*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+
        T/N^3*∑ j ∈ Finset.range N, (c₁*meshSupNorm Hdd N j+c₂*(T/N)*(meshSupNorm Hd N j)^2) ≤
      T/N^2*(2*c₀*L+c₁*M+c₂*T*L^2/N)) := by
  intro Nf
  obtain ⟨hN, hD⟩ := paper_series_eq hw0 hw
  obtain ⟨hNh, -⟩ := paper_series_eq (x := w/2) (by linarith) (by linarith)
  have h12 := one_div_twelve_le_frameBound hw0 hw
  have hq : 0 ≤ frameBound w-frameBound (w/2)/2 := (norm_nonneg _).trans
    (norm_frameSeries_sub_half_le (a := (0:ℂ)) (w := w) (by simpa only [norm_zero] using hw0) hw)
  refine ⟨frameBound w-frameBound (w/2)/2, 1/24+frameBound w,
    max (frameBound w-frameBound (w/2)/2+1/24) ((frameBound w-frameBound
      (w/2)/2)/4+1/64+2*frameLip w),
    ⟨by dsimp only [Nf]; rw [hN, hNh], by dsimp only [Nf]; rw [hN],
      by dsimp only [Nf]; rw [hD], ?_⟩, ?_, ?_⟩
  · rintro rfl
    have hc0 := frameBound_center_pi
    have hpi := frameBound_frameLip_pi.1
    obtain ⟨-, hlt, hc1, -⟩ := unit_constants_bounds
    refine ⟨hc0, hc0 ▸ hlt, by rw [hpi], by rw [hpi]; exact lt_of_le_of_lt unitC1_ge.2 hc1, ?_⟩
    have e : (1:ℝ)/(2 * π)-4/π^3 = (1-8/π^2)/(2 * π) := by
      have := pi_pos.ne'
      field_simp
      ring
    rw [frameBound_frameLip_pi.2, e]
  · intro H U T N hT hN2 hH hc hdiff hU Hd Hdd F
    exact ⟨unit_steps_named_width H U T N w hT hN2 hw hH hc hdiff hU,
      unit_steps_jumps_width H U T N w hT hN2 hw hH hc hdiff hU⟩
  · intro H T N hT hN2 hc
    exact unit_rhs_max_general H T _ _ _ N hT hN2 hq (by linarith)
      (le_trans (by linarith) (le_max_left _ _)) hc

end UnitaryProducts.Paper
