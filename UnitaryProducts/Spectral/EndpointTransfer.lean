/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Paper.FineStepBounds
public import UnitaryProducts.Spectral.ExactGap

/-!
# Supporting transfer for interval windows

## Declarations

- `transfer_gap`
- `transfer_spectral_gap`
- `endpoint_gap_form`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Set Filter
namespace UnitaryProducts.Paper
variable {d : ℕ} [NeZero d]
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

omit [NeZero d] in
/-- the unnumbered endpoint-transfer estimate for interval windows, with the separation explicit.
Let $P$, $Q$ be the spectral
projectors of $H(0)$, $H(T)$ onto windows with collars of width $\gamma_0$, $\gamma_1$, and $P'$,
$Q'$ those of $D_0$, $D_1$ onto the windows widened by $\gamma_t/2$, and let
$\varepsilon_t = \|H(t) - D_t\| < \gamma_t/2$. Then (i) is the leakage comparison, and at each
endpoint the separation $\delta_t$ of the other eigenvalues of $D_t$ from the window satisfies
$\gamma_t - \varepsilon_t \le \delta_t$ (written $(1 - \varepsilon_t/\gamma_t)\gamma_t$) and
$\gamma_t/2 < \delta_t$, with $\|P - P'\| \le \varepsilon_0/\delta_0$ and
$\|Q - Q'\| \le \varepsilon_1/\delta_1$.

Part (i) is the paper's three-term identity (`norm_leak_sub_le_of_contraction`), with
$\|U(T)\| \le 1$ from unitarity; the endpoint bounds are `endpoint_projector_bound` (Weyl and
Davis–Kahan). -/
theorem transfer_spectral_gap {H U : ℝ → 𝕄} {T γ₀ γ₁ m₀ r₀ m₁ r₁ : ℝ}
    (hT : 0 < T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hU : IsEvolution H U 0 T) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hg₀ : UnitaryProducts.HasGap (hH 0 ⟨le_rfl, hT.le⟩) m₀ r₀ γ₀)
    (hg₁ : UnitaryProducts.HasGap (hH T ⟨hT.le, le_rfl⟩) m₁ r₁ γ₁)
    (D₀ D₁ : 𝕄) (hd₀ : D₀.IsHermitian) (hd₁ : D₁.IsHermitian)
    (he₀ : ‖H 0 - D₀‖ < γ₀ / 2) (he₁ : ‖H T - D₁‖ < γ₁ / 2)
    (hn₀ : (UnitaryProducts.endpointComplement hd₀ m₀ r₀ γ₀).Nonempty)
    (hn₁ : (UnitaryProducts.endpointComplement hd₁ m₁ r₁ γ₁).Nonempty) (W : 𝕄) :
    let P := UnitaryProducts.windowProj m₀ r₀ (H 0)
    let Q := UnitaryProducts.windowProj m₁ r₁ (H T)
    let P' := UnitaryProducts.windowProj m₀ (r₀+γ₀ / 2) D₀
    let Q' := UnitaryProducts.windowProj m₁ (r₁+γ₁ / 2) D₁
    let δ₀ := UnitaryProducts.endpointSeparation hd₀ m₀ r₀ γ₀ hn₀
    let δ₁ := UnitaryProducts.endpointSeparation hd₁ m₁ r₁ γ₁ hn₁
    ‖(1-Q')*W*P'-(1-Q)*U T*P‖ ≤ ‖W-U T‖+‖P-P'‖+‖Q-Q'‖ ∧
    ((1-‖H 0 - D₀‖/γ₀)*γ₀ ≤ δ₀ ∧ γ₀/2 < δ₀ ∧ ‖P-P'‖ ≤ ‖H 0 - D₀‖/δ₀) ∧
    ((1-‖H T - D₁‖/γ₁)*γ₁ ≤ δ₁ ∧ γ₁/2 < δ₁ ∧ ‖Q-Q'‖ ≤ ‖H T - D₁‖/δ₁) := by
  have hp := UnitaryProducts.endpoint_projector_bound (hH 0 ⟨le_rfl, hT.le⟩) hd₀ hr₀ hg₀ he₀ hn₀
  have hq := UnitaryProducts.endpoint_projector_bound (hH T ⟨hT.le, le_rfl⟩) hd₁ hr₁ hg₁ he₁ hn₁
  refine ⟨?_, hp, hq⟩
  exact (UnitaryProducts.norm_leak_sub_le_of_contraction
    (UnitaryProducts.isStarProjection_windowProj m₀ r₀ (H 0))
    (UnitaryProducts.isStarProjection_windowProj m₀ (r₀+γ₀ / 2) D₀)
    (UnitaryProducts.isStarProjection_windowProj m₁ (r₁+γ₁ / 2) D₁)
    (UnitaryProducts.norm_le_one_of_star_mul_self (hU.2.2.1 T ⟨hT.le, le_rfl⟩))
    (Pₜ := UnitaryProducts.windowProj m₁ r₁ (H T)) (U' := W)).trans_eq
    (by rw [norm_sub_rev (UnitaryProducts.windowProj m₀ (r₀+γ₀ / 2) D₀)]; ring)

/-- The separation `(1-ε/γ)γ` is `γ-ε`, and below half the gap `ε/(γ-ε) ≤ 2ε/γ`: the last two
lines of the paper's proof of the unnumbered endpoint projector estimate. -/
private theorem endpoint_gap_form {p e γ δ : ℝ} (he0 : 0 ≤ e) (he : e < γ / 2)
    (hδ : (1 - e / γ) * γ ≤ δ) (hp : p ≤ e / δ) : p ≤ e/(γ-e) ∧ e/(γ-e) ≤ 2*e/γ := by
  have hγ : 0 < γ := by linarith
  rw [sub_mul, one_mul, div_mul_cancel₀ e hγ.ne'] at hδ
  refine ⟨hp.trans (div_le_div_of_nonneg_left he0 (by linarith) hδ), ?_⟩
  calc e/(γ-e) ≤ e/(γ / 2) := div_le_div_of_nonneg_left he0 (half_pos hγ) (by linarith)
    _ = 2*e/γ := by rw [div_div_eq_mul_div, mul_comm e 2]

omit [NeZero d] in
/-- **the unnumbered endpoint-transfer estimate** for interval windows: as `transfer_spectral_gap`,
with the separation
$\delta_t$ replaced by $\gamma_t - \varepsilon_t$ (`endpoint_gap_form`), so that
$\|P - P'\| \le \varepsilon_0/(\gamma_0 - \varepsilon_0) \le 2\varepsilon_0/\gamma_0$, and the
same at $T$. `leakage_le_of_endpoint_approximation_sharp` applies it with $\gamma_t$ the exact
gap of the band and rewrites the windows as the bands' index-set projectors. -/
theorem transfer_gap {H U : ℝ → 𝕄} {T γ₀ γ₁ m₀ r₀ m₁ r₁ : ℝ}
    (hT : 0 < T) (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (hU : IsEvolution H U 0 T) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hg₀ : UnitaryProducts.HasGap (hH 0 ⟨le_rfl, hT.le⟩) m₀ r₀ γ₀)
    (hg₁ : UnitaryProducts.HasGap (hH T ⟨hT.le, le_rfl⟩) m₁ r₁ γ₁)
    (D₀ D₁ : 𝕄) (hd₀ : D₀.IsHermitian) (hd₁ : D₁.IsHermitian)
    (he₀ : ‖H 0 - D₀‖ < γ₀ / 2) (he₁ : ‖H T - D₁‖ < γ₁ / 2)
    (hn₀ : (UnitaryProducts.endpointComplement hd₀ m₀ r₀ γ₀).Nonempty)
    (hn₁ : (UnitaryProducts.endpointComplement hd₁ m₁ r₁ γ₁).Nonempty) (W : 𝕄) :
    let P := UnitaryProducts.windowProj m₀ r₀ (H 0)
    let Q := UnitaryProducts.windowProj m₁ r₁ (H T)
    let P' := UnitaryProducts.windowProj m₀ (r₀+γ₀ / 2) D₀
    let Q' := UnitaryProducts.windowProj m₁ (r₁+γ₁ / 2) D₁
    ‖(1-Q')*W*P'-(1-Q)*U T*P‖ ≤ ‖W-U T‖+‖P-P'‖+‖Q-Q'‖ ∧
    (‖P-P'‖ ≤ ‖H 0 - D₀‖/(γ₀-‖H 0 - D₀‖) ∧ ‖H 0 - D₀‖/(γ₀-‖H 0 - D₀‖) ≤ 2*‖H 0 - D₀‖/γ₀) ∧
    (‖Q-Q'‖ ≤ ‖H T - D₁‖/(γ₁-‖H T - D₁‖) ∧ ‖H T - D₁‖/(γ₁-‖H T - D₁‖) ≤ 2*‖H T - D₁‖/γ₁) := by
  have hb := transfer_spectral_gap hT hH hU hr₀ hr₁ hg₀ hg₁ D₀ D₁ hd₀ hd₁ he₀ he₁ hn₀ hn₁ W
  exact ⟨hb.1, endpoint_gap_form (norm_nonneg _) he₀ hb.2.1.1 hb.2.1.2.2,
    endpoint_gap_form (norm_nonneg _) he₁ hb.2.2.1 hb.2.2.2.2⟩

end UnitaryProducts.Paper
