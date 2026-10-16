/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Comparison.EndpointHamiltonian
public import UnitaryProducts.Comparison.NaturalNormsEnds
public import UnitaryProducts.Evolution.UnitaryGenerators
public import UnitaryProducts.Paper.FineStepBounds
public import UnitaryProducts.Spectral.GapDistance
public import UnitaryProducts.Corrector.PeriodicCharacterization

/-!
# Unit-step products, the periodic corrector, and mesh norms

## Declarations

- `boundaryMean`
- `continuous_evolution_solves`
- `deriv_frameMult_eq_partialFractions`
- `eigen_interval_of_norm`
- `endSupMean`
- `intervalSupNorm`
- `meshInterval`
- `meshMoment`
- `meshSupNorm`
- `meshSup_bound`
- `meshSup_nonneg`
- `mesh_subset`
- `norm_le_unitSupNorm`
- `periodic_corrector_stein_identity`
- `product_congr`
- `rescaled_evolution`
- `rescaled_evolution_steps`
- `separatedFrame_eq_correctorSeries`
- `step_products_unit`
- `unitProduct`
- `unitSupNorm`
- `unit_steps_dat`
- `unit_steps_jrs_windows`
- `unit_steps_local_data_ends`
- `unit_steps_local_data_split`
- `unit_steps_local_norms_split`
- `unit_steps_one_lipschitz`
- `unit_steps_one_norms`
- `unit_steps_transfer_windows`
- `unit_steps_windows_coeff`
- `walk`
- `walkCubic_sample`
- `walk_log_moving`
- `walk_step_products`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real MeasureTheory Matrix Filter
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- **Definition 2.3** (`def:unit-product`): the unit-step product of `H` with `T` factors,
together with the rounded clock. The first component is
$e^{-iH((T-1)/T)}\cdots e^{-iH(0)}$; the second is $q(t)=\lfloor t+1/2\rfloor$.
The empty product at `T = 0` is an internal convention; the paper assumes `T ≥ 1`. -/
def unitProduct (H : ℝ → 𝕄) (T : ℕ) : 𝕄 × (ℝ → ℝ) :=
  (UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ H (j / T)) T,
   fun t ↦ (⌊t + 1 / 2⌋ : ℤ))

/-- Internal specialization of the general-duration encoding to the unit-step product
of Definition 2.3. It also handles the empty product convention. -/
theorem step_products_unit (H : ℝ → 𝕄) {N : ℕ} :
    (stepProducts H N N).2.1 = (unitProduct H N).1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rfl
  have hNZ : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [stepProducts, unitProduct, div_self hNZ, one_smul]

/-- On $|w|<2\pi$ the derivative of the closed form `frameMult` is $\mathcal N'(w)$, the
derivative of the paper's series. -/
theorem deriv_frameMult_eq_partialFractions {w : ℝ} (hw : |w| < 2 * π) :
    deriv UnitaryProducts.Corrector.frameMult w =
      deriv (fun x : ℝ ↦ ∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-x^2)) w := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hw] with x hx
  exact frameMult_eq_partialFractions (ne_two_pi_mul_of_abs_lt hx)

/-- For a spectrum separated from $2\pi\mathbb Z\setminus\{0\}$, the kernel operator
`separatedFrame` is the paper's $\mathcal N(\mathrm{ad}_h)(D)$, by induction over the eigenoperators
of $h$. Used for Stein's equation (`periodic_corrector_stein_identity`). -/
theorem separatedFrame_eq_correctorSeries (γ w : ℝ) (hγ : 0 < γ)
    {h : 𝕄} (hh : h.IsHermitian)
    (hsep : UnitaryProducts.Separation.HasSeparatedSpectrum hh γ w) (D : 𝕄) :
    UnitaryProducts.Separation.separatedFrame γ w hγ h D =
      (exponentialOperators h hh D).2.2.1 := by
  have hn (p q : Fin d) (n : ℤ) (hn : n ≠ 0) :
      hh.eigenvalues p - hh.eigenvalues q ≠ 2 * π*n := by
    intro he
    rcases (hsep p q).2 with hz | hs
    · exact mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (Int.cast_ne_zero.mpr hn)
        (he.symm.trans (Set.mem_singleton_iff.mp hz))
    · exact (not_le_of_gt hγ) (by simpa only [he, sub_self, abs_zero] using hs n hn)
  let V : 𝕄 := hh.eigenvectorUnitary
  let f : 𝕄 → 𝕄 := fun M ↦ Matrix.of (fun p q ↦
    ((∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-(hh.eigenvalues p - hh.eigenvalues q)^2) : ℝ) : ℂ) * M p q)
  have hfin : V * (star V * D * V) * star V = D :=
    (Unitary.conjStarAlgAut ℂ 𝕄 hh.eigenvectorUnitary).apply_symm_apply D
  have hfadd (X Y : 𝕄) : f (X + Y) = f X + f Y := by
    ext p q
    exact mul_add _ _ _
  have hfzero : f 0 = 0 := by ext p q; exact mul_zero _
  have hfsingle (p q : Fin d) (z : ℂ) :
      f (single p q z) =
        ((∑' n : ℕ+, 2/(4*π^2*(n:ℝ)^2-(hh.eigenvalues p - hh.eigenvalues q)^2) : ℝ) : ℂ) • single
          p q z := by
    ext i j
    simp only [f, of_apply, smul_apply, smul_eq_mul]
    by_cases h : p = i ∧ q = j
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rw [single_apply_of_ne p q z i j h, mul_zero, mul_zero]
  let P : 𝕄 → Prop := fun M ↦
    UnitaryProducts.Separation.separatedFrame γ w hγ h (V * M * star V) = V * f M * star V
  have hP : ∀ M, P M := by
    intro M
    refine Matrix.induction_on' (P := P) M ?_ ?_ ?_
    · change UnitaryProducts.Separation.separatedFrame γ w hγ h (V * 0 * star V) = V * f 0 * star V
      simp [hfzero, UnitaryProducts.Separation.separatedFrame,
        UnitaryProducts.Separation.kernelFrame]
    · intro X Y hX hY
      change P X at hX
      change P Y at hY
      dsimp only [P] at hX hY ⊢
      rw [mul_add, add_mul, UnitaryProducts.Separation.separatedFrame_add γ w hγ hh,
        hX, hY, hfadd, mul_add, add_mul]
    · intro p q z
      obtain ⟨hp, hq⟩ := UnitaryProducts.Separation.eigenbasis_matrix_unit hh p q z
      dsimp only [P]
      rw [UnitaryProducts.Separation.separatedFrame_of_eigen γ w hγ hp hq (hsep p q),
        hfsingle, ← frameMult_eq_partialFractions (hn p q), mul_smul_comm, smul_mul_assoc]
  simpa only [P, hfin] using hP (star V * D * V)

/-- Supports the Section 4.1 end-value identity, $Y(\frac12)=\mathcal N(\mathrm{ad}_\Omega)(D)$,
under non-resonance
alone, together with Stein's equation
$e^{i\Omega}\mathcal N(\mathrm{ad}_\Omega)(D)e^{-i\Omega}-\mathcal N(\mathrm{ad}_\Omega)(D)
=\int_0^1(\tau-\frac12)e^{i\tau\Omega}De^{-i\tau\Omega}\,d\tau$, the form of equal end
values that this proof uses (the paper checks equal end values entrywise, before the
canonical-cell construction in Lemma A.1).

Reading the statement against the paper:
* The hypothesis `hn` is the canonical-cell construction in Lemma A.1's non-resonance: no
eigenvalue difference of $\Omega$ lies
  in $2\pi\mathbb Z\setminus\{0\}$. It is weaker than the width $<2\pi$ of the proof of Lemma A.1.
* `F.2.2.1` is $\mathcal N(\mathrm{ad}_\Omega)(D)$ and `F.2.2.2` is the periodic corrector $Y$
  (`exponentialOperators`).
* `evol Ω (-1)` is $e^{i\Omega}$ and `evol Ω τ` is $e^{-i\tau\Omega}$.
* Stronger than the paper's setting: no $d\ge1$.

The proof takes a different route from the paper's entrywise check in an eigenbasis: (1)
non-resonance gives a uniform separation of the eigenvalue differences from
$2\pi\mathbb Z\setminus\{0\}$ (`exists_hasSeparatedSpectrum_of_nonresonant`); (2) a kernel operator
`separatedFrame`, built from a Schwartz extension of the scalar multiplier chosen with
`Classical.choose`, equals $\mathcal N(\mathrm{ad}_\Omega)(D)$ (`separatedFrame_eq_correctorSeries`,
an induction over eigenoperators); every choice gives the same matrix; (3) Stein's equation for that
operator is a second eigenoperator induction (`separatedFrame_stein`); (4) equal end values follow
from Stein's equation (`frameExtension_periodic_iff`). -/
theorem periodic_corrector_stein_identity {Ω : 𝕄} (hΩ : Ω.IsHermitian)
    (hn : ∀ p q (n : ℤ), n ≠ 0 → hΩ.eigenvalues p - hΩ.eigenvalues q ≠ 2 * π * n)
    (D : 𝕄) :
    let F := exponentialOperators Ω hΩ D
    F.2.2.2 (1 / 2) = F.2.2.1 ∧
      UnitaryProducts.evol Ω (-1) * F.2.2.1 * UnitaryProducts.evol Ω 1 - F.2.2.1 =
        ∫ τ in (0 : ℝ)..1, (τ - 1 / 2) •
          (UnitaryProducts.evol Ω (-τ) * D * UnitaryProducts.evol Ω τ) := by
  obtain ⟨γ, hγ, w, hs⟩ := UnitaryProducts.Separation.exists_hasSeparatedSpectrum_of_nonresonant
    hΩ hn
  have he := separatedFrame_eq_correctorSeries γ w hγ hΩ hs D
  have hi := UnitaryProducts.Separation.separatedFrame_stein γ w hγ hΩ hs D
  rw [he] at hi
  refine ⟨?_, hi⟩
  change UnitaryProducts.Dressed.frameExtension Ω D
    (exponentialOperators Ω hΩ D).2.2.1 (1 / 2 + 1 / 2) = _
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num]
  exact (UnitaryProducts.Dressed.frameExtension_periodic_iff _ _ _).mpr hi

/-- For a continuous Hamiltonian, a $U$ it generates in the sense of §2 (eq. (2.1)) solves the
Schrödinger equation one-sidedly at every point of $[a,b]$ (not only off a countable set). Used
after rescaling to unit steps. -/
theorem continuous_evolution_solves {K U : ℝ → 𝕄} {a b : ℝ}
    (hK : ContinuousOn K (Icc a b)) (hU : IsEvolution K U a b) :
    UnitaryProducts.SolvesSchrodinger K U a b := by
  obtain ⟨hUc, hU0, _, S, hS, hUd⟩ := hU
  let F : ℝ → 𝕄 := fun x ↦ -I • (K x * U x)
  have hFc : ContinuousOn F (Icc a b) := (hK.mul hUc).const_smul (-I)
  have hint : ∀ t ∈ Icc a b, (∫ x in a..t, F x) = U t - 1 := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have he := integral_eq_of_hasDerivAt_off_countable_of_le U F ht.1 hS
      (hUc.mono hsub) (fun x hx ↦
        (hUd x (hsub (Ioo_subset_Icc_self hx.1)) hx.2).hasDerivAt
          (Icc_mem_nhds hx.1.1 (hx.1.2.trans_le ht.2)))
      ((hFc.mono hsub).intervalIntegrable_of_Icc ht.1)
    simpa only [hU0] using he
  intro t ht
  letI : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hmeas : StronglyMeasurableAtFilter F (nhdsWithin t (Icc a b)) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hFc.aestronglyMeasurable measurableSet_Icc⟩
  have hFi : IntervalIntegrable F volume a t :=
    (hFc.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hd := (intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc a b) hFi hmeas (hFc t ht)).add_const 1
  exact hd.congr (fun x hx ↦ sub_eq_iff_eq_add.mp (hint x hx).symm)
    (sub_eq_iff_eq_add.mp (hint t ht).symm)

/-- The samples $j/N$, $j \le N$, lie in $[0, 1]$: the form of Mathlib's `unitInterval.div_mem`
that the statements of §4 use, including the zero denominator convention. -/
theorem walkCubic_sample {N j : ℕ} (hj : j ≤ N) :
    (j : ℝ) / N ∈ Icc (0 : ℝ) 1 :=
  unitInterval.div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)

/-- The unit-step product depends only on the values of $H$ on $[0,1]$. -/
theorem product_congr {H G : ℝ → 𝕄} (T : ℕ)
    (he : EqOn H G (Icc (0 : ℝ) 1)) :
    (unitProduct H T).1 = (unitProduct G T).1 := by
  have hp : ∀ n ≤ T, UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ H (j/T)) n =
      UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ G (j/T)) n := by
    intro n
    induction n with
    | zero => exact fun _ ↦ rfl
    | succ n ih =>
      intro hn
      rw [UnitaryProducts.pieceProduct, UnitaryProducts.pieceProduct,
        he (walkCubic_sample (Nat.le_of_succ_le hn)), ih (Nat.le_of_succ_le hn)]
  exact hp T le_rfl

/-- Simultaneous energy and time scaling preserves the evolution endpoint. -/
theorem rescaled_evolution {H U : ℝ → 𝕄} {T : ℝ}
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) {c : ℝ} (hc : 0 < c) :
    IsEvolution (fun t ↦ c • H (t/(T/c))) (fun t ↦ U (c*t)) 0 (T/c) := by
  obtain ⟨hUc,hU0,hUU,S,hS,hUd⟩ := hU
  refine ⟨UnitaryProducts.continuousOn_energy_rescale hc hUc, ?_, ?_,
    (fun t : ℝ ↦ c*t) ⁻¹' S, hS.preimage (mul_right_injective₀ hc.ne'), ?_⟩
  · simpa only [mul_zero] using hU0
  · intro t ht
    apply hUU
    exact ⟨mul_nonneg hc.le ht.1, (mul_le_mul_of_nonneg_left ht.2 hc.le).trans_eq (by field_simp)⟩
  · intro t ht hn
    have h := UnitaryProducts.schrodinger_energy_rescale_off_set hc S hUd t ht hn
    convert h using 1 ; congr 2 ; field_simp

/-- Supports "Rescaling energy and time together meets it" and "it is also the final value of the
evolution of $(T/N)H$ over time $N$" (§4.2, before Theorem 4.2): if $U$ is the evolution of $H$
over time $T$, then $(T/N)H(t/N)$ generates $t\mapsto U((T/N)t)$ on $[0,N]$, so the evolution of
$(T/N)H$ over time $N$ is $t\mapsto U((T/N)t)$, whose value at $N$ is $U(T)$.

Reading the statement against the paper:
* The unit-step samples of $(T/N)H$ over time $N$ are $(T/N)H(j/N)$, so its unit-step product is
  the $N$-step product `unitProduct (fun s ↦ (T/N) • H s) N` of $H$ over time $T$, by definition.
* `IsEvolution G V 0 N` says that $G$ generates $V$ on $[0,N]$ (§2).

The proof is the time change $t\mapsto(T/N)t$ (`rescaled_evolution` with $c=T/N$), and
$T/(T/N)=N$. -/
theorem rescaled_evolution_steps {H U : ℝ → 𝕄} {T : ℝ} (hT : 0 < T) (N : ℕ) (hN : 0 < N)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    IsEvolution (fun t ↦ (T/N) • H (t/N)) (fun t ↦ U ((T/N)*t)) 0 N ∧ U ((T/N)*N) = U T := by
  have hN' : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := rescaled_evolution hU (div_pos hT (Nat.cast_pos.mpr hN))
  rw [show T/(T/N) = (N:ℝ) by field_simp] at h
  exact ⟨h, by rw [div_mul_cancel₀ T hN']⟩

/-- Leakage transfer to unit steps (proof of the transfer paragraph in Section 4.2): for star
projections $P$ and $Q$
commuting with $H(0)$ and $H(1)$, respectively, the leakages $\|(1-Q)W_NP\|$ and $\|(1-Q)AP\|$
differ by at most $\|W_N-e^{iTH(1)/(2N)}Ae^{-iTH(0)/(2N)}\|$, for any matrix $A$ (in use,
$A=U(T)$). The half-step phases commute with $1-Q$ and $P$, respectively, and are isometries
(`half_step_leakage_comparison`). This is the content of `unit_steps_dat_leakage`. -/
theorem unit_steps_dat (H : ℝ → 𝕄) (A : 𝕄) (T : ℝ) (N : ℕ)
    (hH0 : (H 0).IsHermitian) (hH1 : (H 1).IsHermitian)
    (P Q : 𝕄) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPc : Commute P (H 0)) (hQc : Commute Q (H 1)) :
    let W := (unitProduct (fun s ↦ (T/N) • H s) N).1
    |‖(1-Q)*W*P‖ - ‖(1-Q)*A*P‖| ≤
      ‖W - UnitaryProducts.evol (H 1) (-(T/(2*N)))*A*UnitaryProducts.evol (H 0) (T/(2*N))‖ := by
  intro W
  have hb := UnitaryProducts.half_step_leakage_comparison
    (UnitaryProducts.Separation.isHermitian_real_smul hH0 (T/N))
    (UnitaryProducts.Separation.isHermitian_real_smul hH1 (T/N))
    hP hQ (hPc.smul_right (T/N)) (hQc.smul_right (T/N)) W A
  have hevol (B : 𝕄) (t : ℝ) :
      UnitaryProducts.evol ((T/N) • B) t = UnitaryProducts.evol B ((T/N)*t) := by
    simp only [UnitaryProducts.evol, smul_comm (-I) (T / (N : ℝ)),
      smul_smul, mul_comm t]
  simpa only [hevol, show (T / (N : ℝ)) * (1 / 2) = T / (2 * N) by ring,
    show (T / (N : ℝ)) * (-(1 / 2)) = -(T / (2 * N)) by ring] using hb


/-- A walk and its sampled product (§4.3). The first component says that $W(s)$ is unitary for
$s\in[0,1]$; the second is the sampled product $W_T=W((T-1)/T)\cdots W(0)$. For `T = 0` the
product is the empty product `1`; every use has $T\ge1$. -/
def walk (W : ℝ → 𝕄) (T : ℕ) : Prop × 𝕄 :=
  (∀ s ∈ Icc (0 : ℝ) 1, star (W s) * W s = 1,
   UnitaryProducts.stepProduct W T T)

/-- Supports "the walk's sampled product is the logarithm's unit-step product" (§4.3):
 if $e^{-iH(j/N)}=W(j/N)$ at the samples, then $W_N$ is the $N$-step product of $H$
over time $N$.

Reading the statement against the paper:
* `hlog` asks $e^{-iH(j/N)}=W(j/N)$ only at the samples $j<N$, which is all the identity uses;
  `evol G 1` is $e^{-iG}$.
* `(walk W N).2` is $W_N=W((N-1)/N)\cdots W(0)$ and `(stepProducts H N N).2.1` is the $N$-step
  product of $H$ over time $N$ (Definition 2.3).

The proof follows the paper's: rewrite the right side as the unit-step product
(`step_products_unit`), then replace each factor $e^{-iH(j/N)}$ by $W(j/N)$
(`stepProduct_eq_pieceProduct`). -/
theorem walk_step_products (W H : ℝ → 𝕄) {N : ℕ}
    (hlog : ∀ j : ℕ, j < N → UnitaryProducts.evol (H (j/N)) 1 = W (j/N)) :
    (walk W N).2 = (stepProducts H N N).2.1 := by
  rw [step_products_unit H]
  exact UnitaryProducts.stepProduct_eq_pieceProduct hlog N le_rfl

theorem eigen_interval_of_norm {A : 𝕄} (hA : A.IsHermitian)
    {l w : ℝ} (hAwidth : ‖A - ((l + w / 2 : ℝ) : ℂ) • 1‖ ≤ w / 2) :
    ∀ i, hA.eigenvalues i ∈ Icc l (l+w) := by
  intro i
  letI : NeZero d := ⟨i.pos.ne'⟩
  have hm : hA.eigenvalues i-(l+w / 2) ∈
      spectrum ℝ (A-algebraMap ℝ 𝕄 (l+w / 2)) := by
    rw [← spectrum.sub_singleton_eq]
    exact ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i,
      l+w / 2, Set.mem_singleton _, rfl⟩
  have hb := spectrum.norm_le_norm_of_mem hm
  have hb' : |hA.eigenvalues i-(l+w / 2)| ≤ ‖A - ((l + w / 2 : ℝ) : ℂ) • 1‖ := by
    simpa only [Real.norm_eq_abs, Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using hb
  obtain ⟨hlo, hhi⟩ := abs_le.mp (hb'.trans hAwidth)
  constructor <;> linarith

/-- The maximum $\max_{[0,1]}\|F\|$ of the norm of `F` on the parameter interval $[0,1]$.

It is an `sSup`: a genuine maximum when `F` is continuous on $[0,1]$ (a compact image), and the
junk value `0` when the norms are unbounded; every use assumes continuity. -/
def unitSupNorm {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) : ℝ :=
  sSup ((fun s ↦ ‖F s‖) '' Icc (0 : ℝ) 1)

/-- Every value of a continuous `F` on $[0,1]$ is at most `unitSupNorm F`. -/
theorem norm_le_unitSupNorm {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → E} (hc : ContinuousOn F (Icc (0 : ℝ) 1))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ‖F s‖ ≤ unitSupNorm F :=
  hc.norm.le_sSup_image_Icc hs

/-- A continuous moving closed arc selects a continuous logarithm: if the spectrum of each $W(s)$
lies in $\{e^{-i\theta}:a(s)\le\theta\le a(s)+w\}$ with $w<2\pi$, there is a continuous Hermitian
$\Lambda$ with eigenvalues in $[a(s),a(s)+w]$ and $e^{-i\Lambda(s)}=W(s)$ (existence in
Lemma A.2 (existence and uniqueness)). -/
theorem walk_log_moving [NeZero d] (a : ℝ → ℝ) (w : ℝ)
    (hw : w < 2 * π) (W : ℝ → 𝕄)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hW : ContinuousOn W (Icc (0 : ℝ) 1))
    (hunit : (walk W 1).1)
    (harc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (a s) (a s + w), z = Complex.exp (-I * (θ : ℂ))) :
    ∃ Λ : ℝ → 𝕄, ∃ hΛ : ∀ s ∈ Icc (0 : ℝ) 1, (Λ s).IsHermitian,
      ContinuousOn Λ (Icc (0 : ℝ) 1) ∧
      ∀ s (hs : s ∈ Icc (0 : ℝ) 1),
        (∀ i, (hΛ s hs).eigenvalues i ∈ Icc (a s) (a s+w)) ∧
        UnitaryProducts.evol (Λ s) 1 = W s := by
  let φ := fun s ↦ -(a s+w / 2+π)
  let γ := 2 * π-w
  have hspec : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ spectrum ℂ (W s),
      ∃ θ ∈ Icc (φ s+γ/2) (φ s+2 * π-γ/2), z=Complex.exp ((θ:ℂ)*I) := by
    intro s hs z hz
    obtain ⟨θ,hθ,he⟩ := harc s hs z hz
    refine ⟨-θ, ⟨?_, ?_⟩, ?_⟩
    · dsimp [φ,γ]; linarith [hθ.2]
    · dsimp [φ,γ]; linarith [hθ.1]
    · rw [he]; congr 1; push_cast; ring
  obtain ⟨Λ,hΛ,hc,he⟩ := UnitaryProducts.exists_log_moving_cut W φ (fun _ ↦ γ)
    (Icc (0 : ℝ) 1) hW ((ha.add continuousOn_const).add continuousOn_const).neg
    continuousOn_const (fun _ _ ↦ sub_pos.mpr hw) hunit hspec
  refine ⟨Λ, fun s _ ↦ hΛ s, hc, fun s hs ↦ ⟨?_, (he s hs).1⟩⟩
  apply eigen_interval_of_norm (hΛ s)
  simpa only [show -(φ s+π)=a s+w / 2 by dsimp [φ]; ring, show 2 * π-γ=w by dsimp [γ]; ring]
    using (he s hs).2

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts.Dressed UnitaryProducts.Corrector
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The $i$-th step $[i/N,(i+1)/N]$ of the mesh of §4.2, as a closed interval.

The endpoints are written $\max(0,i)/N$ and $\min(N,i+1)/N$, so for $i<N$ the set is exactly
$[i/N,(i+1)/N]\subseteq[0,1]$. For $i\ge N$ it is $\{1\}$ or empty, and for $N=0$ it is $\{0\}$
(division by zero is `0`); every use has $0<N$ and $i<N$. -/
def meshInterval (N i : ℕ) : Set ℝ :=
  Icc (max 0 (i:ℝ)/N) (min (N:ℝ) ((i:ℝ)+1)/N)

/-- The maximum $\max_{a\le s\le b}\|F(s)\|$ of the norm of `F` on $[a,b]$.

It is an `sSup`: for `F` continuous on a nonempty $[a,b]$ it is a genuine maximum (a compact
image); it is the junk value `0` when the norms are unbounded or $a>b$. -/
def intervalSupNorm {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (a b : ℝ) : ℝ :=
  sSup ((fun s ↦ ‖F s‖) '' Icc a b)

/-- The maximum $\max_{i/N\le s\le(i+1)/N}\|F(s)\|$ of the norm of `F` on the $i$-th step
(`meshInterval`), the term used by the mesh-norm comparisons.

It is an `sSup` of the norm of `F` over a closed cell: when `F` is continuous on $[0,1]$, $0<N$ and
$i<N$, the cell is compact and nonempty and this is a genuine maximum. Otherwise it may be the
junk value `0` (unbounded norms or an empty cell); every use is in the good case. -/
def meshSupNorm {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (N i : ℕ) : ℝ :=
  sSup ((fun s ↦ ‖F s‖) '' meshInterval N i)

/-- The mesh norms: `meshMoment F N p` is
$\frac1N\sum_{j=0}^{N-1}\max_{j/N\le s\le(j+1)/N}\|F(s)\|^p$, written $\|F\|_{1,N}$ here at $p=1$
(the first mesh moment) and $\|F\|_{2,N}^2$ at $p=2$.
So `meshMoment F N 2` is $\|H'\|_{2,N}^2$ for $F=H'$, and `meshMoment F N 1` is $\|H''\|_{1,N}$ for
$F=H''$. For `N = 0` it is `0`. The maxima are those of `meshSupNorm`. -/
def meshMoment {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (N p : ℕ) : ℝ :=
  (∑ i ∈ Finset.range N, (meshSupNorm F N i)^p)/N

/-- The mean $(\|F(1/N)\|+\|F(1-1/N)\|)/2$ of the norms of `F` at the first and last interior
samples. With $F=H'$, the end term $c_0(\|H'(\frac1N)\|+\|H'(1-\frac1N)\|)$ of the interior-sample
comparison is
$2c_0$ times `boundaryMean F N`. These are point values, not maxima over the end steps. The second
sample is written $(N-1)/N$. For `N = 0` both points are $0$ (division by zero is `0`); every use
has $N\ge2$. -/
def boundaryMean {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (N : ℕ) : ℝ :=
  (‖F (1/N)‖+‖F (((N:ℝ)-1)/N)‖)/2

/-- Each step lies in $[0,1]$. -/
theorem mesh_subset {N i : ℕ} : meshInterval N i ⊆ Icc (0 : ℝ) 1 := fun _ hs ↦
  ⟨(div_nonneg (le_max_left _ _) (Nat.cast_nonneg N)).trans hs.1,
    hs.2.trans (div_le_one_of_le₀ (min_le_left _ _) (Nat.cast_nonneg N))⟩

/-- For continuous `F`, every value on a step is at most the maximum `meshSupNorm F N i`. -/
theorem meshSup_bound {E : Type*} [NormedAddCommGroup E] {F : ℝ → E}
    (hc : ContinuousOn F (Icc (0 : ℝ) 1)) {N i : ℕ} {s : ℝ}
    (hs : s ∈ meshInterval N i) : ‖F s‖ ≤ meshSupNorm F N i := by
  exact le_csSup ((isCompact_Icc).bddAbove_image (hc.mono mesh_subset).norm) ⟨s,hs,rfl⟩

/-- The supremum of the step's norms is nonnegative, including empty or unbounded images. -/
theorem meshSup_nonneg {E : Type*} [NormedAddCommGroup E] {F : ℝ → E} {N i : ℕ} :
    0 ≤ meshSupNorm F N i :=
  Real.sSup_nonneg fun _ ⟨s, _, hs⟩ ↦ hs ▸ norm_nonneg (F s)

set_option maxHeartbeats 400000 in
-- Rescaling to `[0, N]` and normalizing the rational bound exceed the default heartbeat limit.
/-- The $C^2$ unit-step comparison at width $w<2\pi$ with per-step data: if $\|H'\|\le L_i$ and
$\|H''\|\le M_i$ on the $i$-th step, the error is bounded with coefficient `b₀` on the $M_i$ of the
two end steps and `b₁` on the interior ones, and `r₀`, `r₁` likewise on the $L_i^2$, for any
coefficients at least the thresholds in the hypotheses (`frameBound`, `frameLip` are
$\mathcal N$, $\mathcal N'$ on $[0,2\pi)$). The proof rescales to $K(t)=(T/N)H(t/N)$ on $[0,N]$
as in `unit_steps_jumps_lip`, applies `endpoint_local_width_ends`, and translates back. -/
theorem unit_steps_local_data_ends [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ)
    (w b₀ b₁ r₀ r₁ : ℝ) (L M : ℕ → ℝ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hL : ∀ i < N, ∀ s ∈ meshInterval N i, ‖derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ L i)
    (hM : ∀ i < N, ∀ s ∈ meshInterval N i,
      ‖derivWithin (derivWithin H (Icc (0 : ℝ) 1)) (Icc 0 1) s‖ ≤ M i)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hb0 : (1/8:ℝ)≤b₀) (hb1 : 1/24+frameBound w≤b₁)
    (hr0 : frameBound w-frameBound (w/2)/2+1/24≤r₀)
    (hr1 : (frameBound w-frameBound (w/2)/2)/4+1/64+2*frameLip w≤r₁) :
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(2*(frameBound w-frameBound (w/2)/2)*boundaryMean (derivWithin H (Icc (0 : ℝ) 1)) N+
        b₀*((M 0+M (N-1))/N)+b₁*((∑ j ∈ Finset.range (N-2), M (j+1))/N)+(T/N)*(r₀*(((L 0)^2+(L
          (N-1))^2)/N)+
          r₁*((∑ j ∈ Finset.range (N-2), (L (j+1))^2)/N))) := by
  -- Taking equal eigenvalue indices in the width hypothesis gives 0 ≤ w.
  have hw0 : 0 ≤ w := by simpa using hdiff 1 (by omega) (by omega) (0 : Fin d) 0
  obtain ⟨n,rfl⟩ : ∃ n, N=n+2 := ⟨N-2,by omega⟩
  let R : ℝ := (n:ℝ)+2
  have hR : 0<R := by dsimp [R]; positivity
  have hcast : ((n+2:ℕ):ℝ)=R := by dsimp [R]; push_cast; rfl
  let c := T/R
  have hcpos : 0<c := div_pos hT hR
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt H (Hd s) (Icc 0 1) s :=
    fun s hs ↦ (hc.differentiableOn (by norm_num) s hs).hasDerivWithinAt
  have hcd : ContDiffOn ℝ 1 Hd (Icc (0 : ℝ) 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by
    norm_num)
  have hdd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt Hd (derivWithin Hd (Icc (0 : ℝ) 1) s) (Icc 0 1) s :=
    fun s hs ↦ (hcd.differentiableOn (by norm_num) s hs).hasDerivWithinAt
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
  have hlocal i : ∀ t ∈ Icc (localLeft i) (localRight n i), t/R ∈ meshInterval (n+2) i := by
    intro t ht
    change max 0 (i:ℝ)/((n+2:ℕ):ℝ) ≤ t/R ∧ t/R ≤ min ((n+2:ℕ):ℝ) ((i:ℝ)+1)/((n+2:ℕ):ℝ)
    rw [hcast]
    exact ⟨(div_le_div_iff_of_pos_right hR).mpr ht.1,(div_le_div_iff_of_pos_right hR).mpr ht.2⟩
  have hLK i (hi : i≤n+1) : ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t‖ ≤ (c/R)*L i := by
    intro t ht
    dsimp only [Kd]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hcpos hR)]
    exact mul_le_mul_of_nonneg_left (hL i (by omega) _ (hlocal i t ht)) (div_nonneg hcpos.le hR.le)
  have hMK i (hi : i≤n+1) : ∀ s ∈ Icc (localLeft i) (localRight n i),
      ∀ t ∈ Icc (localLeft i) (localRight n i), ‖Kd t-Kd s‖ ≤ (c/R^2*M i)*|t-s| := by
    intro s hs t ht
    have hsub := mesh_subset (N := n+2) (i := i)
    have hb := UnitaryProducts.norm_sub_le_of_derivWithin_le
      (fun u hu ↦ (hdd u (hsub hu)).mono hsub) (hM i (by omega))
      _ (hlocal i s hs) _ (hlocal i t ht)
    dsimp [Kd]
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hcpos hR)]
    have hb' := mul_le_mul_of_nonneg_left hb (div_nonneg hcpos.le hR.le)
    rw [← sub_div,abs_div,abs_of_pos hR] at hb'
    exact hb'.trans_eq (by ring_nf)
  have hKc : ContinuousOn K (Icc (0 : ℝ) R) := fun t ht ↦ (hdK t ht).continuousWithinAt
  have hUG : IsEvolution (fun t ↦ G (t / T)) U 0 T := by
    obtain ⟨hu,h0,hunit,S,hS,hud⟩ := hU
    refine ⟨hu,h0,hunit,S,hS,?_⟩
    intro t ht hn
    have hs : t/T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hT.le,(div_le_one hT).mpr ht.2⟩
    change HasDerivWithinAt U (-I • (G (t/T)*U t)) (Icc 0 T) t
    rw [he hs]; exact hud t ht hn
  have hTc : T/c=R := by dsimp [c]; field_simp
  let V : ℝ → 𝕄 := fun t ↦ U (c*t)
  have hUV : IsEvolution K V 0 R := by
    simpa only [hTc] using rescaled_evolution hUG hcpos
  have hV : UnitaryProducts.SolvesSchrodinger K V 0 R := continuous_evolution_solves hKc hUV
  have hV0 : V 0=1 := hUV.2.1
  have hKdiff (j : ℕ) (hj : 0<j) (hjN : j≤n+1) : ∀ p q,
      |(hK j).eigenvalues p-(hK j).eigenvalues q| ≤ w := by
    have hs : (j:ℝ)/R ∈ Icc (0 : ℝ) 1 := by
      rw [← hcast]; exact walkCubic_sample (by omega)
    have hb := scaled_eigenvalue_bound (hH _ hs) hcpos.le
      (fun p q ↦ by simpa only [hcast, c] using hdiff j hj (by omega) p q)
    simpa only [K,he hs] using hb
  let z (j : ℕ) := sInf (Set.range (hK j).eigenvalues)+w/2
  have hwidth (j : ℕ) hj hjn : ‖K j-(z j:ℂ) • 1‖ ≤ w/2 :=
    UnitaryProducts.norm_sub_smul_one_le_of_eigenvalues (hK j) hw0 (eigen_interval (hK j)
      (hKdiff j hj hjn))
  have hb := endpoint_local_width_ends K Kd V n w b₀ b₁ r₀ r₁ (fun i ↦ (c/R)*L i)
    (fun i ↦ (c/R^2)*M i) z hw hK hdK hLK hMK hV hV0 hwidth
    hb0 hb1 hr0 hr1
  have hVN : V R=U T := by
    change U (c*R)=U T
    rw [show c*R=T by dsimp [c]; field_simp]
  have hKN : K R=c • H 1 := by dsimp [K]; rw [div_self hR.ne',he ⟨zero_le_one,le_rfl⟩]
  have hK0 : K 0=c • H 0 := by dsimp [K]; rw [zero_div,he ⟨le_rfl,zero_le_one⟩]
  have hevol (A : 𝕄) (t : ℝ) : UnitaryProducts.evol (c • A) t=UnitaryProducts.evol A (c*t) := by
    convert UnitaryProducts.evol_energy_rescale A (c*t) hcpos.ne' using 1
    field_simp
  have hp : UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)=
      (unitProduct (fun s ↦ c • H s) (n+2)).1 := by
    simpa only [unitProduct,K,hcast] using
      product_congr (n+2) (show EqOn (fun s ↦ c • G s) (fun s ↦ c • H s) (Icc (0 : ℝ) 1)
        from fun s hs ↦ by dsimp only; rw [he hs])
  change ‖UnitaryProducts.pieceProduct (fun _ ↦ 1) (fun j ↦ K j) (n+2)-
      UnitaryProducts.evol (K R) (-(1/2))*V R*UnitaryProducts.evol (K 0) (1/2)‖ ≤ _ at hb
  rw [hp,hVN,hKN,hK0,hevol,hevol] at hb
  have hkd (t : ℝ) : ‖Kd t‖=(c/R)*‖Hd (t/R)‖ := by
    dsimp only [Kd]; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hcpos hR)]
  rw [hkd,hkd] at hb
  have heqL i : ((c/R)*L i)^2=(c/R)^2*(L i)^2 := by ring
  simp_rw [heqL] at hb
  simp only [←Finset.mul_sum] at hb
  simp only [show n+2-1=n+1 by omega, show n+2-2=n by omega]
  convert hb using 1 <;> dsimp [boundaryMean,Hd,c,R] <;> push_cast <;> field_simp ; ring_nf

/-- The $C^2$ unit-step comparison at width $w<2\pi$ with per-step data: if $\|H'\|\le L_i$ and
$\|H''\|\le M_i$ on the $i$-th step, the comparison error is bounded with one coefficient `b` on
the $M_i$, a coefficient `r₀` on $L_i^2$ for the two end steps and `r₁` for the interior steps,
for any `b`, `r₀`, `r₁` at least the values the residual and jump estimates produce. The
`frameBound`, `frameLip` in those thresholds are $\mathcal N$, $\mathcal N'$ on $[0,2\pi)$. The
proof specializes `unit_steps_local_data_ends` to equal coefficients and rejoins the end
and interior sums. -/
theorem unit_steps_local_data_split [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ)
    (w b r₀ r₁ : ℝ) (L M : ℕ → ℝ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hL : ∀ i < N, ∀ s ∈ meshInterval N i, ‖derivWithin H (Icc (0 : ℝ) 1) s‖ ≤ L i)
    (hM : ∀ i < N, ∀ s ∈ meshInterval N i,
      ‖derivWithin (derivWithin H (Icc (0 : ℝ) 1)) (Icc 0 1) s‖ ≤ M i)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hb0 : (1/8:ℝ)≤b) (hb1 : 1/24+frameBound w≤b)
    (hr0 : frameBound w-frameBound (w / 2)/2+1/24≤r₀)
    (hr1 : (frameBound w-frameBound (w / 2)/2)/4+1/64+2*frameLip w≤r₁) :
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(2*(frameBound w-frameBound (w / 2)/2)*boundaryMean (derivWithin H (Icc (0 : ℝ) 1)) N+
        b*((∑ i ∈ Finset.range N, M i)/N)+(T/N)*(r₀*(((L 0)^2+(L (N-1))^2)/N)+
          r₁*((∑ j ∈ Finset.range (N-2), (L (j+1))^2)/N))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  apply (unit_steps_local_data_ends H U T (n + 2) w b b r₀ r₁ L M hT hN2
    hw hH hc hL hM hdiff hU hb0 hb1 hr0 hr1).trans_eq
  simp only [show n + 2 - 1 = n + 1 by omega, Nat.add_sub_cancel]
  rw [sum_two_ends]; ring

/-- The mean of the maxima of $\|F\|$ over the first and last steps,
$(\max_{[0,1/N]}\|F\|+\max_{[1-1/N,1]}\|F\|)/2$: with $F=W'$ and $N=T$, the end term of
`walk_unit_comparison_sharp`. The maxima are `intervalSupNorm`s, genuine for `F` continuous on
$[0,1]$. For `N = 0` the intervals are $\{0\}$ and $\{1\}$ (division by zero is `0`); every use
has $N\ge1$. -/
def endSupMean {E : Type*} [NormedAddCommGroup E] (F : ℝ → E) (N : ℕ) : ℝ :=
  (intervalSupNorm F 0 (1/N)+intervalSupNorm F (1-1/N) 1)/2

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- One factor ($N=1$, unit time): if $H$ is $L$-Lipschitz on $[0,1]$, then
$\|e^{-iH(0)}-e^{iH(1)/2}U(1)e^{-iH(0)/2}\|\le L/4$, with no width condition. The two half steps
of the rounded clock each cost $L/8$ by Duhamel (`halfIntegral_le_lipschitz`). Used for $T=1$ in
`walk_unit_comparison_sharp`. -/
theorem unit_steps_one_lipschitz [NeZero d]
    (H U : ℝ → 𝕄) (L : ℝ)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContinuousOn H (Icc (0 : ℝ) 1))
    (hlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖H t - H s‖ ≤ L * |t - s|)
    (hU : IsEvolution H U 0 1) :
    ‖(unitProduct H 1).1 - UnitaryProducts.evol (H 1) (-(1/2)) *
      U 1 * UnitaryProducts.evol (H 0) (1/2)‖ ≤ L/4 := by
  classical
  let G : ℝ → 𝕄 := fun s ↦ H (projIcc 0 1 zero_le_one s)
  have he : EqOn G H (Icc (0 : ℝ) 1) := fun s hs ↦
    congrArg H (congrArg Subtype.val (projIcc_of_mem zero_le_one hs))
  have hG : ∀ s, (G s).IsHermitian := fun s ↦ hH _ (projIcc 0 1 zero_le_one s).property
  have hGc : ContinuousOn G (Icc (0 : ℝ) 1) := hc.congr he
  have hsol := continuous_evolution_solves hc hU
  have hGsol : UnitaryProducts.SolvesSchrodinger (fun t ↦ G (t/(1:ℕ))) U 0 (1:ℕ) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [Nat.cast_one] using ht
    simpa only [Nat.cast_one, div_one, he ht'] using hsol t ht'
  have hGlip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖G t-G s‖ ≤ L*|t-s| :=
    fun s hs t ht ↦ by rw [he hs, he ht]; exact hlip s hs t ht
  have hb := UnitaryProducts.Dressed.unit_steps_integral G (fun _ ↦ 0) 1
    (fun _ ↦ 0) (fun _ ↦ 0) U one_pos hG hGc hGsol hU.2.1
    (fun j h0 hj ↦ absurd hj (by omega))
    (fun j h0 hj ↦ absurd hj (by omega))
  have hhalf := UnitaryProducts.Dressed.halfIntegral_le_lipschitz G 1 L one_pos hGlip
  simp only [Nat.cast_one, mul_one] at hhalf
  simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, ↓reduceIte,
    norm_zero, add_zero, Nat.cast_one, div_one] at hb
  have hb' : ‖(unitProduct G 1).1 - UnitaryProducts.evol (G 1) (-(1/2)) *
      U 1 * UnitaryProducts.evol (G 0) (1/2)‖ ≤ L/4 := by
    simpa only [unitProduct, Nat.cast_one, div_one] using hb.trans hhalf
  rwa [product_congr 1 he, he ⟨zero_le_one, le_rfl⟩,
    he ⟨le_rfl, zero_le_one⟩] at hb'

/-- For one factor over time $T$, the comparison error is at most $T\max_{[0,1]}\|H'\|/4$: the
`unit_steps_one_lipschitz` bound for $TH$, whose Lipschitz constant is $T\max\|H'\|$. Used for
$T=1$ in `walk_unit_comparison_sharp`. -/
theorem unit_steps_one_norms [NeZero d]
    (H U : ℝ → 𝕄) (T : ℝ) (hT : 0 < T)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    ‖(unitProduct (fun s ↦ T • H s) 1).1 -
      UnitaryProducts.evol (H 1) (-(T/2)) * U T * UnitaryProducts.evol (H 0) (T/2)‖ ≤
      T * unitSupNorm (derivWithin H (Icc (0 : ℝ) 1)) / 4 := by
  let Hd := derivWithin H (Icc (0 : ℝ) 1)
  have hV : IsEvolution (fun s ↦ T • H s) (fun t ↦ U (T*t)) 0 1 := by
    simpa only [div_self hT.ne', div_one] using rescaled_evolution hU hT
  have hbound s (hs : s ∈ Icc (0 : ℝ) 1) : ‖T • Hd s‖ ≤ T * unitSupNorm Hd := by
    rw [norm_smul, Real.norm_of_nonneg hT.le]
    exact mul_le_mul_of_nonneg_left (norm_le_unitSupNorm
      (hc.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)) hs) hT.le
  have hb := unit_steps_one_lipschitz (fun s ↦ T • H s) (fun t ↦ U (T*t))
    (T * unitSupNorm Hd) (fun s hs ↦ UnitaryProducts.Separation.isHermitian_real_smul (hH s hs) T)
    (hc.continuousOn.const_smul T)
    (UnitaryProducts.norm_sub_le_of_derivWithin_le
      (fun s hs ↦ (hc.differentiableOn (by norm_num) s hs).hasDerivWithinAt.const_smul T)
      hbound) hV
  have hevol (A : 𝕄) (t : ℝ) : UnitaryProducts.evol (T • A) t = UnitaryProducts.evol A (T*t) := by
    convert UnitaryProducts.evol_energy_rescale A (T*t) hT.ne' using 1
    field_simp
  rw [hevol, hevol] at hb
  simpa only [mul_one, show T * (-(1/2):ℝ) = -(T/2) by ring,
    show T * (1/2:ℝ) = T/2 by ring] using hb

end UnitaryProducts.Paper

namespace UnitaryProducts.Paper
open UnitaryProducts.Corrector UnitaryProducts.Dressed
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- `unit_steps_local_data_split` with the per-step bounds taken to be the step maxima of $H'$
and $H''$, written with the mesh norms of §4.2. -/
theorem unit_steps_local_norms_split [NeZero d] (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ)
    (w b r₀ r₁ : ℝ) (hT : 0 < T) (hN2 : 2 ≤ N) (hw : w < 2 * π)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ w)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hb0 : (1/8:ℝ)≤b) (hb1 : 1/24+frameBound w≤b)
    (hr0 : frameBound w-frameBound (w / 2)/2+1/24≤r₀)
    (hr1 : (frameBound w-frameBound (w / 2)/2)/4+1/64+2*frameLip w≤r₁) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(2*(frameBound w-frameBound (w / 2)/2)*boundaryMean Hd N+
        b*meshMoment Hdd N 1+(T/N)*(r₀*(((meshSupNorm Hd N 0)^2+(meshSupNorm Hd N (N-1))^2)/N)+
          r₁*((∑ j ∈ Finset.range (N-2), (meshSupNorm Hd N (j+1))^2)/N))) := by
  intro Hd Hdd
  have hd : ContDiffOn ℝ 1 Hd (Icc (0 : ℝ) 1) := hc.derivWithin uniqueDiffOn_Icc_zero_one (by
    norm_num)
  have hdd : ContDiffOn ℝ 0 Hdd (Icc (0 : ℝ) 1) := hd.derivWithin uniqueDiffOn_Icc_zero_one (by
    norm_num)
  have hb := unit_steps_local_data_split H U T N w b r₀ r₁ (meshSupNorm Hd N) (meshSupNorm Hdd N)
    hT hN2 hw hH hc
    (fun i _ s hs ↦ meshSup_bound hd.continuousOn hs)
    (fun i _ s hs ↦ meshSup_bound hdd.continuousOn hs)
    hdiff hU hb0 hb1 hr0 hr1
  simpa only [meshMoment,pow_one] using hb

/-- The $C^2$ unit-step comparison at width $\pi$, with the explicit constants
$c_0=1/(2\pi)-1/\pi^2$ (`frameBound_center_pi`), $1/24+1/\pi^2$ on $\|H''\|_{1,N}$, and
$c_0/4+1/64+2\mathcal N'(\pi)$, $1/24+c_0$ on the interior and end terms of $\|H'\|_{2,N}^2$. -/
theorem unit_steps_windows_coeff [NeZero d]
    (H U : ℝ → 𝕄) (T : ℝ) (N : ℕ) (hT : 0 < T) (hN2 : 2 ≤ N)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hc : ContDiffOn ℝ 2 H (Icc (0 : ℝ) 1))
    (hdiff : ∀ j : ℕ, ∀ _hj : 0<j, ∀ hjN : j<N, ∀ p q,
      (T/N)*|(hH _ (walkCubic_sample hjN.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjN.le)).eigenvalues q| ≤ π)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let c₀ := 1/(2 * π)-1/π^2
    ‖(unitProduct (fun s ↦ (T/N) • H s) N).1-
      UnitaryProducts.evol (H 1) (-(T/(2*N)))*U T*UnitaryProducts.evol (H 0) (T/(2*N))‖ ≤
      T/N^2*(c₀*(‖Hd (1/N)‖+‖Hd (1-1/N)‖)+(1/24+1/π^2)*meshMoment Hdd N 1+
        (T/N)*((c₀/4+1/64+2*frameLip π)*((∑ j ∈ Finset.range (N-2), (meshSupNorm Hd N (j+1))^2)/N)+
          (1/24+c₀)*(((meshSupNorm Hd N 0)^2+(meshSupNorm Hd N (N-1))^2)/N))) := by
  have h12 := one_div_twelve_le_frameBound pi_pos.le (by linarith [pi_pos] : π < 2 * π)
  have hb := unit_steps_local_norms_split H U T N π (1/24+1/π^2) (1/24+(1/(2 * π)-1/π^2))
    ((1/(2 * π)-1/π^2)/4+1/64+2*frameLip π) hT hN2
    (by linarith [pi_pos]) hH hc hdiff hU
    (by rw [frameBound_frameLip_pi.1] at h12; linarith)
    (by rw [frameBound_frameLip_pi.1])
    (by rw [frameBound_center_pi]; exact (add_comm _ _).le)
    (by rw [frameBound_center_pi])
  have hN : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  dsimp only [boundaryMean] at hb ⊢
  rw [show ((N:ℝ)-1)/N=1-1/N by field_simp, frameBound_center_pi] at hb
  exact hb.trans_eq (by ring)

/-- The Jansen–Ruskai–Seiler instance of the leakage comparison at width $\pi$, with the $C^2$
comparison
`unit_steps_windows_coeff` in place of the interior-sample comparison: the assumed bound
$\|(1-Q)U(T)P\|\le J/T$ gives $T\|(1-Q)W_TP\|\le J+T\cdot(\text{comparison bound at }N=T)$. -/
theorem unit_steps_jrs_windows [NeZero d]
    (H U : ℝ → 𝕄) (T m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ)
    (hT2 : 2 ≤ T) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hband : (jrsCoefficientTracked H hH m g B).1)
    (hdiff : ∀ j : ℕ, ∀ _hj : 0 < j, ∀ hjT : j < T, ∀ p q,
      |(hH _ (walkCubic_sample hjT.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjT.le)).eigenvalues q| ≤ π)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T) :
    let P := (jrsCoefficientTracked H hH m g B).2.1.1
    let Q := (jrsCoefficientTracked H hH m g B).2.1.2
    let J := (jrsCoefficientTracked H hH m g B).2.2
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let c₀ := 1/(2 * π)-1/π^2
    ‖(1-Q)*U T*P‖ ≤ J/T →
      T*‖(1-Q)*(unitProduct H T).1*P‖ ≤
        J+T*(T/T^2*(c₀*(‖Hd (1/T)‖+‖Hd (1-1/T)‖)+(1/24+1/π^2)*meshMoment Hdd T 1+
          (T/T)*((c₀/4+1/64+2*frameLip π)*((∑ j ∈ Finset.range (T-2), (meshSupNorm Hd T
            (j+1))^2)/T)+
            (1/24+c₀)*(((meshSupNorm Hd T 0)^2+(meshSupNorm Hd T (T-1))^2)/T)))) := by
  dsimp only
  intro hJ
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr (by omega)
  have hp : (T:ℝ)/(2*T)=1/2 := by field_simp
  have hb := unit_steps_dat H (U T) T T
    (hH 0 ⟨le_rfl, zero_le_one⟩) (hH 1 ⟨zero_le_one, le_rfl⟩)
    (jrsCoefficientTracked H hH m g B).2.1.1 (jrsCoefficientTracked H hH m g B).2.1.2
    (UnitaryProducts.isStarProjection_specProj _ _) (UnitaryProducts.isStarProjection_specProj _ _)
    (UnitaryProducts.commute_specProj _ _) (UnitaryProducts.commute_specProj _ _)
  have hcomp := unit_steps_windows_coeff H U T T hTR hT2 hH hband.1.1
    (by intro j hj hjT p q
        simpa only [div_self hTR.ne', one_mul] using hdiff j hj hjT p q) hU
  dsimp only at hb hcomp
  have hW : (unitProduct (fun s ↦ ((T:ℝ)/T) • H s) T).1=(unitProduct H T).1 := by
    simp only [div_self hTR.ne', one_smul]
  rw [hW, hp] at hcomp hb
  have key := (sub_le_iff_le_add.mp ((le_abs_self _).trans (hb.trans hcomp))).trans
    (add_le_add le_rfl hJ)
  have e : ∀ X Y : ℝ, (T:ℝ)*(X+Y/T)=Y+T*X := by
    intro X Y
    have h : (T:ℝ)*(Y/T)=Y := by field_simp
    rw [mul_add, h]; ring
  exact (mul_le_mul_of_nonneg_left key hTR.le).trans_eq (e _ _)

/-- Bundle of the two unit-step transfers: the leakage transfer `unit_steps_dat` and the
width-$\pi$ Jansen–Ruskai–Seiler transfer `unit_steps_jrs_windows`. -/
theorem unit_steps_transfer_windows [NeZero d] :
    (∀ (H : ℝ → 𝕄) (A : 𝕄) (T : ℝ) (N : ℕ)
    (_hH0 : (H 0).IsHermitian) (_hH1 : (H 1).IsHermitian)
    (P Q : 𝕄) (_hP : IsStarProjection P) (_hQ : IsStarProjection Q)
    (_hPc : Commute P (H 0)) (_hQc : Commute Q (H 1)),
    let W := (unitProduct (fun s ↦ (T/N) • H s) N).1
    |‖(1-Q)*W*P‖ - ‖(1-Q)*A*P‖| ≤
      ‖W - UnitaryProducts.evol (H 1) (-(T/(2*N)))*A*UnitaryProducts.evol (H 0) (T/(2*N))‖) ∧
    (∀ (H U : ℝ → 𝕄) (T m : ℕ) (g : ℝ → ℝ) (B : ℝ → Set ℝ)
    (_ : 2 ≤ T) (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (_ : (jrsCoefficientTracked H hH m g B).1)
    (_ : ∀ j : ℕ, ∀ _hj : 0 < j, ∀ hjT : j < T, ∀ p q,
      |(hH _ (walkCubic_sample hjT.le)).eigenvalues p-
        (hH _ (walkCubic_sample hjT.le)).eigenvalues q| ≤ π)
    (_ : IsEvolution (fun t ↦ H (t / T)) U 0 T),
    let P := (jrsCoefficientTracked H hH m g B).2.1.1
    let Q := (jrsCoefficientTracked H hH m g B).2.1.2
    let J := (jrsCoefficientTracked H hH m g B).2.2
    let Hd := derivWithin H (Icc (0 : ℝ) 1)
    let Hdd := derivWithin Hd (Icc (0 : ℝ) 1)
    let c₀ := 1/(2 * π)-1/π^2
    ‖(1-Q)*U T*P‖ ≤ J/T →
      T*‖(1-Q)*(unitProduct H T).1*P‖ ≤
        J+T*(T/T^2*(c₀*(‖Hd (1/T)‖+‖Hd (1-1/T)‖)+(1/24+1/π^2)*meshMoment Hdd T 1+
          (T/T)*((c₀/4+1/64+2*frameLip π)*((∑ j ∈ Finset.range (T-2), (meshSupNorm Hd T
            (j+1))^2)/T)+
            (1/24+c₀)*(((meshSupNorm Hd T 0)^2+(meshSupNorm Hd T (T-1))^2)/T))))) :=
  ⟨unit_steps_dat, unit_steps_jrs_windows⟩

end UnitaryProducts.Paper

-- Generate the equation lemmas for the mesh definitions.
run_cmd Lean.Elab.Command.liftTermElabM do
  discard <| Lean.Meta.getEqnsFor? `UnitaryProducts.Paper.meshInterval
