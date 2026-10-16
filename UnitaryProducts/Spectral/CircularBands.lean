/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module

public import UnitaryProducts.Spectral.BandTransfer
public import UnitaryProducts.Spectral.SampledWidth
public import UnitaryProducts.Walks.BandMultiplicity

/-!
# Circular spectral gaps and angular distance

## Declarations

- `angularDistance`
- `angularDistance_isLeast`
- `circularGap`
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Complex Set Real
noncomputable section
namespace UnitaryProducts.Paper
variable {d : ℕ}
local notation "𝕄" => Matrix (Fin d) (Fin d) ℂ

/-- The spectral gap $\Gamma(U)$ of the band of a unitary matrix $U$ on the arc
$\{e^{-i\theta} : \alpha < \theta < \beta\}$, measured along the circle (paragraph after
Definition 2.5): the least angular distance $\min_k |\theta - \phi + 2\pi k|$ from a band phase to
a phase of the rest of the spectrum. Phases are represented in the one turn starting at $\alpha$,
where $0 < y - x < 2\pi$ and `min (y-x) (2π-(y-x))` is exactly that distance (as in
`trackedCircularBand`).

It is an `sInf`, so it returns `0` when there is no band phase or no outside phase. Under
`circularBand` both exist, the set is finite and its elements are positive, so the infimum is a
minimum. -/
def circularGap (U : 𝕄) (α β : ℝ) : ℝ :=
  sInf {g : ℝ | ∃ x y : ℝ, x ∈ Ioo α β ∧ y ∈ Ioo β (α+2*π) ∧
    Complex.exp (-I*(x:ℂ)) ∈ spectrum ℂ U ∧ Complex.exp (-I*(y:ℂ)) ∈ spectrum ℂ U ∧
    g = min (y-x) (2*π-(y-x))}

/-- The circular distance is the absolute value of the representative in $[-\pi,\pi)$.
`angularDistance_isLeast` proves that this is precisely the integer minimum in Definition 2.5. -/
def angularDistance (θ φ : ℝ) : ℝ := |toIcoMod Real.two_pi_pos (-π) (θ-φ)|

/-- The minimum $\min_{k\in\mathbb Z}|\theta-\phi+2\pi k|$ exists and equals the circular
distance; the witness is the negative quotient in reduction modulo $2\pi$. -/
theorem angularDistance_isLeast (θ φ : ℝ) :
    IsLeast (Set.range (fun k : ℤ ↦ |θ-φ+2*π*k|)) (angularDistance θ φ) := by
  let q := toIcoDiv Real.two_pi_pos (-π) (θ-φ)
  let u := toIcoMod Real.two_pi_pos (-π) (θ-φ)
  have hq : θ-φ = (q : ℝ)*(2*π)+u :=
    (toIcoDiv_mul_sub_toIcoMod Real.two_pi_pos (-π) (θ-φ)).symm
  have hu₁ : -π ≤ u := left_le_toIcoMod Real.two_pi_pos (-π) (θ-φ)
  have hu₂ : u < π := by
    have := toIcoMod_lt_right Real.two_pi_pos (-π) (θ-φ)
    dsimp [u]
    linarith
  have hu : |u| ≤ π := abs_le.mpr ⟨hu₁, hu₂.le⟩
  change IsLeast (Set.range (fun k : ℤ ↦ |θ-φ+2*π*k|)) |u|
  refine ⟨⟨-q, ?_⟩, ?_⟩
  · change |θ-φ+2*π*((-q : ℤ):ℝ)| = |u|
    rw [Int.cast_neg, hq]
    congr 1
    ring
  · rintro g ⟨k, rfl⟩
    change |u| ≤ |θ-φ+2*π*(k:ℝ)|
    rcases lt_trichotomy (q+k) 0 with h | h | h
    · have hn : (q : ℝ)+(k : ℝ) ≤ -1 := by exact_mod_cast (show q+k ≤ -1 by omega)
      have hb : π ≤ -(θ-φ+2*π*k) := by
        have hm := mul_le_mul_of_nonneg_left hn Real.two_pi_pos.le
        linarith
      exact hu.trans (hb.trans (neg_le_abs _))
    · have hn : (q : ℝ)+(k : ℝ) = 0 := by exact_mod_cast h
      have he : θ-φ+2*π*k = u := by
        have hm := congrArg (fun x : ℝ ↦ 2 * π * x) hn
        linarith
      rw [he]
    · have hn : (1 : ℝ) ≤ (q : ℝ)+(k : ℝ) := by exact_mod_cast (show 1 ≤ q+k by omega)
      have hb : π ≤ θ-φ+2*π*k := by
        have hm := mul_le_mul_of_nonneg_left hn Real.two_pi_pos.le
        linarith
      exact hu.trans (hb.trans (le_abs_self _))

local notation "𝔼" => EuclideanSpace ℂ (Fin d)

/-- Number of eigenvalues, counted with multiplicity (as roots of the characteristic polynomial),
of a unitary matrix on the open arc $\{e^{-i\theta} : \alpha < \theta < \beta\}$: the paper's
"band of $m$ eigenvalues ... counted with multiplicity" (paragraph after Definition 2.5). -/
def arcEigenvalueCount (U : 𝕄) (α β : ℝ) : ℕ := by
  classical
  exact (U.charpoly.roots.filter (fun z ↦ ∃ θ ∈ Ioo α β, z = Complex.exp (-I*(θ:ℂ)))).card


/-- For phases in one turn, the integer minimum is the smaller of the two circular routes. -/
theorem angularDistance_eq_min {x y : ℝ} (hxy : x ≤ y) (hyx : y - x ≤ 2 * π) :
    angularDistance x y = min (y-x) (2*π-(y-x)) := by
  apply (angularDistance_isLeast x y).unique
  constructor
  · by_cases h : y-x ≤ π
    · refine ⟨0, ?_⟩
      dsimp only
      rw [Int.cast_zero, mul_zero, add_zero, abs_of_nonpos (by linarith),
        min_eq_left (by linarith)]
      ring
    · refine ⟨1, ?_⟩
      dsimp only
      rw [Int.cast_one, mul_one, abs_of_nonneg (by linarith), min_eq_right (by linarith)]
      ring
  · rintro g ⟨k, rfl⟩
    change min (y-x) (2*π-(y-x)) ≤ |x-y+2*π*(k:ℝ)|
    by_cases hk : k ≤ 0
    · have hk' : (k:ℝ) ≤ 0 := by exact_mod_cast hk
      have hb : y-x ≤ -(x-y+2*π*k) := by
        have hm := mul_le_mul_of_nonneg_left hk' Real.two_pi_pos.le
        linarith
      exact (min_le_left _ _).trans (hb.trans (neg_le_abs _))
    · have hk' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hb : 2*π-(y-x) ≤ x-y+2*π*k := by
        have hm := mul_le_mul_of_nonneg_left hk' Real.two_pi_pos.le
        linarith
      exact (min_le_right _ _).trans (hb.trans (le_abs_self _))

end UnitaryProducts.Paper
