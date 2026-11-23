/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import RoundedClocks.Definitions

/-! # Pointwise logarithm calculus

Lemma A.2 identifies the principal logarithm of a unitary matrix from its spectral phases and
gives the pointwise functional-calculus identities along a unitary path.
-/

@[expose] public section

open Real Complex Set Matrix
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
namespace RoundedClocks.WalkLog

/-- The operator-norm matrix algebra used for the functional calculus. -/
def matrixCStarAlgebra (d : ℕ) : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

attribute [local instance] matrixCStarAlgebra
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The spectral projector at `z`, defined by the characteristic function of its
singleton on the finite spectrum. -/
def finiteSpectralProjector (U : 𝕄) (z : ℂ) : 𝕄 :=
  cfc (fun ζ : ℂ ↦ if ζ = z then 1 else 0) U

/-- The finite-dimensional spectral theorem written as the sum of its named
spectral projectors. Any scalar function is continuous on the finite spectrum. -/
theorem finite_spectral_expansion (U : 𝕄) (f : ℂ → ℂ) :
    cfc f U = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
      f z • finiteSpectralProjector U z := by
  classical
  let S := (Matrix.finite_spectrum U).toFinset
  have hsum : cfc f U = cfc (fun ζ ↦ ∑ z ∈ S,
      f z • (if ζ = z then (1 : ℂ) else 0)) U := by
    apply cfc_congr
    intro ζ hζ
    have hmem : ζ ∈ S := (Matrix.finite_spectrum U).mem_toFinset.mpr hζ
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ζ]
    · simp
    · intro z _ hz
      simp [Ne.symm hz]
    · exact fun hz ↦ (hz hmem).elim
  rw [hsum]
  have hmap := cfc_sum (fun z ζ : ℂ ↦ f z • (if ζ = z then (1 : ℂ) else 0))
    U S (fun _ _ ↦ (Matrix.finite_spectrum U).continuousOn _)
  simp only [Finset.sum_fn] at hmap
  rw [hmap]
  apply Finset.sum_congr rfl
  intro z _
  exact cfc_smul (f z) _ U ((Matrix.finite_spectrum U).continuousOn _)

/-- The characteristic functions give self-adjoint idempotent projectors. -/
theorem finiteSpectralProjector_properties (U : 𝕄) (z : ℂ) :
    (finiteSpectralProjector U z).IsHermitian ∧
    finiteSpectralProjector U z * finiteSpectralProjector U z =
      finiteSpectralProjector U z := by
  classical
  let e : ℂ → ℂ := fun ζ ↦ if ζ = z then 1 else 0
  have hc := (Matrix.finite_spectrum U).continuousOn e
  constructor
  · change star (cfc e U) = cfc e U
    rw [← cfc_star]
    apply cfc_congr
    intro ζ _
    simp [e]
  · change cfc e U * cfc e U = cfc e U
    rw [← cfc_mul e e U hc hc]
    apply cfc_congr
    intro ζ _
    by_cases h : ζ = z <;> simp [e, h]

/-- Lemma A.2: a unitary matrix is the sum of its eigenvalues times the
spectral projectors. Replacing each eigenvalue by its chosen phase constructs its logarithm. -/
theorem unitary_spectral_decomposition (U : 𝕄) (hu : star U * U = 1) :
    U = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
      z • finiteSpectralProjector U z := by
  letI : IsStarNormal U :=
    ⟨by change star U * U = U * star U; rw [hu, mul_eq_one_comm.mp hu]⟩
  simpa only [cfc_id, id_eq] using finite_spectral_expansion U id

/-- Pointwise spectral construction in Lemma A.2. Choose each phase in the
prescribed interval, then sum those phases times the spectral projectors. The
functional calculus proves Hermiticity, the spectral window, and exponentiation. -/
theorem walk_log_pointwise (a w : ℝ)
    (U : 𝕄) (hu : star U * U = 1)
    (harc : ∀ z ∈ spectrum ℂ U,
      ∃ θ ∈ Icc a (a + w), z = Complex.exp (-I * (θ : ℂ))) :
    ∃ H : 𝕄, ∃ _hH : H.IsHermitian,
      HasRealSpectrumIn H (Icc a (a + w)) ∧ NormedSpace.exp (-I • H) = U := by
  classical
  letI : IsStarNormal U :=
    ⟨by change star U * U = U * star U; rw [hu, mul_eq_one_comm.mp hu]⟩
  let θ : ℂ → ℝ := fun z ↦ if hz : z ∈ spectrum ℂ U then (harc z hz).choose else a
  have hθ (z : ℂ) (hz : z ∈ spectrum ℂ U) :
      θ z ∈ Icc a (a + w) ∧ z = Complex.exp (-I * (θ z : ℂ)) := by
    simpa only [θ, dif_pos hz] using (harc z hz).choose_spec
  let f : ℂ → ℂ := fun z ↦ (θ z : ℂ)
  let H := ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
    f z • finiteSpectralProjector U z
  have hHcfc : H = cfc f U := (finite_spectral_expansion U f).symm
  have hc := (Matrix.finite_spectrum U).continuousOn f
  have hH : H.IsHermitian := by
    change star H = H
    simp only [H, star_sum, star_smul]
    apply Finset.sum_congr rfl
    intro z _
    rw [show star (finiteSpectralProjector U z) = finiteSpectralProjector U z from
      (finiteSpectralProjector_properties U z).1]
    simp only [f, Complex.star_def, Complex.conj_ofReal]
  refine ⟨H, hH, ?_, ?_⟩
  · intro x hx
    have hspec : (x : ℂ) ∈ spectrum ℂ H :=
      (spectrum.algebraMap_mem_iff ℂ).mpr hx
    have hmap : spectrum ℂ H = f '' spectrum ℂ U := by
      rw [hHcfc, cfc_map_spectrum f U (inferInstance : IsStarNormal U) hc]
    rw [hmap] at hspec
    obtain ⟨z, hz, heq⟩ := hspec
    have he : θ z = x := Complex.ofReal_injective heq
    rw [← he]
    exact (hθ z hz).1
  · rw [hHcfc, ← cfc_smul (-I) f U hc,
      ← CFC.complex_exp_eq_normedSpace_exp, ← cfc_comp (R := ℂ) Complex.exp (fun z : ℂ ↦ -I • f z) U
        (inferInstance : IsStarNormal U) Complex.continuous_exp.continuousOn (hc.const_smul (-I))]
    calc
      _ = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
          Complex.exp (-I * f z) • finiteSpectralProjector U z :=
        finite_spectral_expansion U (fun z ↦ Complex.exp (-I * f z))
      _ = ∑ z ∈ (Matrix.finite_spectrum U).toFinset,
          z • finiteSpectralProjector U z := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← (hθ z ((Matrix.finite_spectrum U).mem_toFinset.mp hz)).2]
      _ = U := (unitary_spectral_decomposition U hu).symm

/-- The inverse phase branch centered at `-α`, used on the unit circle. -/
noncomputable def argBranch (α : ℝ) (z : ℂ) : ℂ :=
  -((α : ℂ) + ((z * Complex.exp (-(α : ℝ) * I)).arg : ℂ))

/-- `toIocMod` is the identity on `(-π, π)`. -/
theorem toIocMod_eq_of_abs_lt {ψ : ℝ} (h : |ψ| < π) :
    toIocMod Real.two_pi_pos (-π) ψ = ψ :=
  (toIocMod_eq_self _).2 ⟨(abs_lt.mp h).1, by linarith [(abs_lt.mp h).2]⟩

/-- $e^{i\theta}e^{-i\alpha} = e^{i(\theta - \alpha)}$. -/
theorem exp_mul_I_mul_exp {α θ : ℝ} :
    Complex.exp ((θ : ℂ) * I) * Complex.exp (-(α : ℝ) * I)
      = Complex.exp (((θ - α : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `argBranch α` $(e^{i\theta}) = -\theta$ when $|\theta - \alpha| < \pi$. -/
theorem argBranch_exp_mul_I {α θ : ℝ} (h : |θ - α| < π) :
    argBranch α (Complex.exp ((θ : ℂ) * I)) = -(θ : ℂ) := by
  rw [argBranch, exp_mul_I_mul_exp, Complex.arg_exp_mul_I, toIocMod_eq_of_abs_lt h]
  push_cast; ring

/-- $e^{-iH}$ is the functional calculus of $z \mapsto e^{-iz}$ at a Hermitian $H$. -/
theorem exp_eq_cfc (H : 𝕄) (hH : H.IsHermitian) :
    NormedSpace.exp (-I • H) = cfc (fun z : ℂ ↦ Complex.exp (-I * z)) H := by
  have := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  rw [cfc_comp_const_mul (-I) Complex.exp H Complex.continuous_exp.continuousOn,
    CFC.complex_exp_eq_normedSpace_exp]


/-- Applying the inverse phase branch recovers a Hermitian matrix in the given window. -/
theorem cfc_branch_exp {H : 𝕄} {a w : ℝ} (hw : w < 2 * π)
    (hH : IsHermitian H) (hwin : HasRealSpectrumIn H (Icc a (a + w))) :
    cfc (argBranch (-(a + w / 2))) (NormedSpace.exp (-I • H)) = H := by
  letI : IsStarNormal H := (Matrix.isHermitian_iff_isSelfAdjoint.mp hH).isStarNormal
  have hc := (Matrix.finite_spectrum H).continuousOn
    (fun z : ℂ ↦ Complex.exp (-I * z))
  have hf := ((Matrix.finite_spectrum H).image
    (fun z : ℂ ↦ Complex.exp (-I * z))).continuousOn (argBranch (-(a + w / 2)))
  rw [exp_eq_cfc H hH, ← cfc_comp (R := ℂ) _ _ H
    (inferInstance : IsStarNormal H) hf hc]
  have he : cfc (argBranch (-(a + w / 2)) ∘
      fun z : ℂ ↦ Complex.exp (-I * z)) H = cfc (id : ℂ → ℂ) H := by
    apply cfc_congr
    intro z hz
    have hsa := Matrix.isHermitian_iff_isSelfAdjoint.mp hH
    obtain ⟨θ, rfl⟩ : ∃ θ : ℝ, z = (θ : ℂ) :=
      ⟨z.re, IsSelfAdjoint.mem_spectrum_eq_re hsa hz⟩
    have hθ := hwin ((spectrum.algebraMap_mem_iff ℂ).mp hz)
    have habs : |(-θ) - (-(a + w / 2))| < π := by
      apply abs_lt.mpr
      constructor <;> linarith [hθ.1, hθ.2]
    change argBranch (-(a + w / 2)) (Complex.exp (-I * (θ : ℂ))) = (θ : ℂ)
    rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      argBranch_exp_mul_I habs]
    simp
  rw [he, cfc_id ℂ H]

/-- The phase branch is injective on every closed window of width less than `2π`. -/
theorem walk_log_unique {A B : 𝕄} {a w : ℝ} (hw : w < 2 * π)
    (hA : IsHermitian A) (hAw : HasRealSpectrumIn A (Icc a (a + w)))
    (hB : IsHermitian B) (hBw : HasRealSpectrumIn B (Icc a (a + w)))
    (he : NormedSpace.exp (-I • A) = NormedSpace.exp (-I • B)) : A = B := by
  rw [← cfc_branch_exp hw hA hAw, ← cfc_branch_exp hw hB hBw, he]

end RoundedClocks.WalkLog
