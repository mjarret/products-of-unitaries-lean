/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.PaperProof.CenteredUnitSteps

/-! # The centered rotating-frame bound for unit-step products -/
@[expose] public section

open scoped Matrix.Norms.L2Operator Topology
open Complex Set Real MeasureTheory Matrix Filter
open UnitaryProducts.Paper UnitaryProducts.Paper.UnitStepsProse

noncomputable section
namespace UnitaryProducts.PaperProof
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The rotating-frame bound written with a primitive equal to the frame
integral on its interval. Derivatives agree at every interior point. -/
theorem frame_bound_of_primitive_eq {a b : ℝ} (hab : a ≤ b) {K G U V S : ℝ → 𝕄}
    (hKr : IsRegulated K a b) (hGr : IsRegulated G a b)
    (hU : IsEvolution K U a b) (hV : IsEvolution G V a b)
    (hS : EqOn S (frameIntegral K G V a) (Icc a b)) :
    |‖V b - U b‖ - ‖S b‖| ≤ ∫ t in a..b, ‖deriv S t * S t‖ := by
  have hpair := rotating_frame_bound hab hKr hGr hU hV
  have hnorm := hpair.1.trans hpair.2
  rw [← hS ⟨hab, le_rfl⟩] at hnorm
  refine hnorm.trans_eq ?_
  apply intervalIntegral.integral_congr_ae
  have hex : ({a, b} : Set ℝ).Countable := (Set.toFinite _).countable
  filter_upwards [hex.ae_notMem volume] with t ht hti
  rw [uIoc_of_le hab] at hti
  have htb : t ≠ b := fun h ↦ ht (by simp [h])
  have hti' : t ∈ Ioo a b := ⟨hti.1, lt_of_le_of_ne hti.2 htb⟩
  have he : S =ᶠ[𝓝 t] frameIntegral K G V a :=
    Filter.eventually_of_mem (Icc_mem_nhds hti'.1 hti'.2) (fun _ hy ↦ hS hy)
  rw [he.deriv_eq, hS (Ioo_subset_Icc_self hti')]

/-- The scalar-centered frame integral in Theorem 4.2. The scalar is an identity matrix, as
everywhere in the paper. -/
def centeredUnitFrameIntegral (H V : ℝ → 𝕄) (T : ℕ) (b t : ℝ) : 𝕄 :=
  ∫ u in 0..t, star (V u) * (H (u / T) - H ((clock u : ℝ) / T)) * V u -
    (b * (u - (clock u : ℝ)) / T) • (1 : 𝕄)

/-- the rotating-frame estimate specialized to the centered unit-step frame integral:
the literal centered frame integral bounds the
phase-corrected unit-step product, for every real centering scalar. No smoothness
or width hypothesis is needed. -/
theorem frame_unit {H U V : ℝ → 𝕄} {T : ℕ} (hT : 0 < T)
    (hHr : IsRegulated H 0 1)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, (H s).IsHermitian)
    (hU : IsEvolution (fun t ↦ H (t / T)) U 0 T)
    (hV : IsEvolution (fun t ↦ H (sample T (t / T))) V 0 T) (b : ℝ) :
    |‖evol (H 1) (1 / 2) * (unitProduct H T).1 * evol (H 0) (-(1 / 2)) - U T‖ -
        ‖centeredUnitFrameIntegral H V T b T‖| ≤
      ∫ t in (0 : ℝ)..T,
        ‖deriv (centeredUnitFrameIntegral H V T b) t * centeredUnitFrameIntegral H V T b t‖ := by
  have hTp : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hTn : (T : ℝ) ≠ 0 := hTp.ne'
  let Hb := fun s ↦ H s - (b * s) • (1 : 𝕄)
  have hHbr : IsRegulated Hb 0 1 := Prose.regulated_sub hHr
    (Prose.regulated_of_continuousOn (by fun_prop))
  have hs (t : ℝ) : sample T (t / T) = (clock t : ℝ) / T := by
    simp only [sample, show (T : ℝ) * (t / T) = t by field_simp]
  have hKbr : IsRegulated (fun t ↦ Hb (t / T)) 0 T := regulated_rescale hTp hHbr
  have hGbr : IsRegulated (fun t ↦ Hb (sample T (t / T))) 0 T := by
    simpa only [hs, clock] using rounded_hamiltonian_regulated Hb T
  obtain ⟨Ub, Vb, hUb, hVb, hdist, hphase⟩ := centered_evolution_pair hT hU hV b
  have hprimitive : EqOn (centeredUnitFrameIntegral H V T b)
      (frameIntegral (fun t ↦ Hb (t / T)) (fun t ↦ Hb (sample T (t / T))) Vb 0)
      (Icc (0 : ℝ) T) := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
    dsimp only [frameIntegrand, Hb]
    rw [hphase]
    have he := centered_frame_integrand (H (u / T)) (H (sample T (u / T))) (V u)
      (b * (u / T)) (b * sample T (u / T))
      ((b / T) * ∫ x in (0 : ℝ)..u, (clock x : ℝ)) (hV.2.2.1 u huT)
    simp only [Complex.coe_smul, hs] at he
    simp only [hs]
    rw [he]
    congr 2
    ring
  have hbound := frame_bound_of_primitive_eq hTp.le hKbr hGbr hUb hVb hprimitive
  rw [hdist] at hbound
  have hproduct := regulated_evolution_rounded.2 H hH (T : ℝ) T hTp hT V
    (by simpa only [sample, clock, mul_div_assoc] using hV)
  have hhalf : (T : ℝ) / (2 * T) = 1 / 2 := by field_simp
  simp only [div_self hTn, one_smul, hhalf] at hproduct
  rw [hproduct] at hbound
  exact hbound

end UnitaryProducts.PaperProof
