/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Semantics
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixExtractionProofs
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-!
# CubeRatio

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From a pure-flux response ratio to a `sigma_*^{-1}` operator-norm ratio

Source: ABK26: the conditional `lambda_{s,q}` sensitivity estimate applies the
`D_h` bound *specialized to the bottom right entry of* `A(cube)`, i.e. to the
pure-flux matrix `sigma_*^{-1}`, on every triadic descendant of the unit cube.

The bottom-right specialization is purely algebraic.  `sigma_*^{-1}(U; a)` is
defined entrywise from the pure-flux response `J(U, a, 0, ·)`
(`Book.Ch02.sigmaStarInvEntry`), and its quadratic form is exactly

```
q · sigma_*^{-1}(U; a) q = 2 J(U, a, 0, q) .
```

Hence a ratio estimate `J(U, b1, 0, q) ≤ rho * J(U, b0, 0, q)` valid for *every*
loading `q` is precisely a Löwner comparison
`sigma_*^{-1}(U; b1) ≤ rho * sigma_*^{-1}(U; b0)`, and since both matrices are
positive semidefinite the Euclidean operator norm `Book.Ch02.matrixNorm` is
monotone along that order.  No polarization of the off-diagonal entries is
needed: the quadratic form determines the comparison.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Scaling of the Euclidean operator matrix norm -/

/-- The Euclidean operator matrix norm is absolutely homogeneous. -/
theorem matrixNorm_smul (c : ℝ) (A : Mat d) :
    Ch02.matrixNorm (c • A) = |c| * Ch02.matrixNorm A := by
  unfold Ch02.matrixNorm
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-! ## The pure-flux quadratic form -/

/-- The quadratic form of `sigma_*^{-1}(U; a)` is twice the pure-flux
response. -/
theorem vecDot_matVecMul_sigmaStarInvCoarse (U : Domain d) (a : CoeffOn U)
    (q : Vec d) :
    vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U a) q) = 2 * responseJ U a 0 q := by
  rw [responseJ_zero_q_eq_sigmaStarInvCoarse U a q]
  ring

/-! ## The Löwner comparison -/

/-- A pure-flux response ratio at every loading is a Löwner comparison of the
pure-flux matrices. -/
theorem matLoewnerLE_smul_of_responseJ_le (U : Domain d) (b₀ b₁ : CoeffOn U)
    {ρ : ℝ}
    (hJ : ∀ q : Vec d, responseJ U b₁ 0 q ≤ ρ * responseJ U b₀ 0 q) :
    MatLoewnerLE (Ch02.sigmaStarInvCoarse U b₁) (ρ • Ch02.sigmaStarInvCoarse U b₀) := by
  intro q
  have hsmul : vecDot q (matVecMul (ρ • Ch02.sigmaStarInvCoarse U b₀) q) =
      ρ * vecDot q (matVecMul (Ch02.sigmaStarInvCoarse U b₀) q) := by
    rw [smul_matVecMul, vecDot_smul_right]
  rw [hsmul, vecDot_matVecMul_sigmaStarInvCoarse,
    vecDot_matVecMul_sigmaStarInvCoarse]
  have := hJ q
  linarith

/-- A scalar multiple of a positive semidefinite matrix by a nonnegative scalar
is positive semidefinite, in the ambient `Mat d` spelling. -/
theorem posSemidef_smul_of_nonneg {A : Mat d} (hA : A.PosSemidef) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : (ρ • A).PosSemidef := by
  simpa using hA.smul (by exact_mod_cast hρ : (0 : ℝ) ≤ ρ)

/-! ## The one-cube ratio -/

/-- **The one-cube `sigma_*^{-1}` ratio from a pure-flux response ratio.**

If the pure-flux response of `b₁` is at most `rho` times that of `b₀` at every
loading, the same ratio holds for the Euclidean operator norms of the pure-flux
matrices.  This is the bottom-right specialization used at every triadic
descendant in the proof of the conditional `lambda_{s,q}` sensitivity
estimate. -/
theorem matrixNorm_sigmaStarInvCoarse_le_of_responseJ_le (U : Domain d)
    (b₀ b₁ : CoeffOn U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hJ : ∀ q : Vec d, responseJ U b₁ 0 q ≤ ρ * responseJ U b₀ 0 q) :
    Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U b₁) ≤
      ρ * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U b₀) := by
  have hpsd₁ : (Ch02.sigmaStarInvCoarse U b₁).PosSemidef :=
    (Ch02.sigmaStarInvCoarse_posDef U b₁).posSemidef
  have hpsd₀ : (ρ • Ch02.sigmaStarInvCoarse U b₀).PosSemidef :=
    posSemidef_smul_of_nonneg (Ch02.sigmaStarInvCoarse_posDef U b₀).posSemidef hρ
  have hmain := matrixNorm_le_of_matLoewnerLE_of_posSemidef hpsd₁ hpsd₀
    (matLoewnerLE_smul_of_responseJ_le U b₀ b₁ hJ)
  rwa [matrixNorm_smul, abs_of_nonneg hρ] at hmain

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
