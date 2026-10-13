/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.EllipticityOrdered
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# CubeEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse ellipticity chain at a general triadic cube

Source: ABK26, the loading half of `e.split.besov.stuff.begin`.

`Provider.DhBound.Discharge.EllipticityOrdered` already proves the chain

```
|p|² ≤ |σ_*^{-1}(U; a)| · 2 (J(U, p, q; a) + p·q)
```

at an *arbitrary* Chapter 2 domain, and CoarseGraining's
`Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv` bounds `|σ_*^{-1}(R; a)|` by
`λ_{s,q}^{-1}(R; a)` at an *arbitrary* triadic cube.  This module combines the
two at the **pure-potential** loading `q = 0`, where the cross term `p·q`
vanishes and the chain becomes the clean budget

```
|p| ≤ √2 · λ_{3/8,2}^{-1/2}(R; a) · J(R, p, 0; a)^{1/2} .
```

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

noncomputable section

variable {d : ℕ}

/-- The coarse gauge of a compatible family at any triadic cube is positive. -/
theorem lambdaSq_sensitivity_pos [NeZero d] (R : TriadicCube d)
    (G : Ch02.TriadicCoeffFamily d) :
    0 < Ch02.lambdaSq R (3 / 8) (.finite 2) G :=
  Ch02.lambdaSq_finite_pos R G (by norm_num) (by norm_num)

/-- `λ_{3/8,2}^{-1}(R; a) ≥ 0`. -/
theorem lambdaSq_inv_nonneg [NeZero d] (R : TriadicCube d)
    (G : Ch02.TriadicCoeffFamily d) :
    0 ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ :=
  (inv_pos.mpr (lambdaSq_sensitivity_pos R G)).le

/-- **The ellipticity chain at a general triadic cube, pure-potential
loading.** -/
theorem vecNormSq_le_lambdaSq_inv_mul_two_mul_responseJ [NeZero d]
    (R : TriadicCube d) (G : Ch02.TriadicCoeffFamily d) (b : CoeffOn (cubeDomain R))
    (hG : CoeffOn.AEEq (G.coeffOn R) b) (p : Vec d) :
    vecNormSq p ≤ (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ *
      (2 * responseJ (cubeDomain R) b p 0) := by
  have hchain :=
    vecNormSq_le_matrixNorm_sigmaStarInvCoarse_mul_two_mul_add (cubeDomain R) b p 0
  have hzero : vecDot p (0 : Vec d) = 0 := by simp [vecDot]
  rw [hzero, add_zero] at hchain
  have hmat : Ch02.coarseSigmaStarInvMatrixNorm R G =
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (cubeDomain R) b) := by
    unfold Ch02.coarseSigmaStarInvMatrixNorm
    rw [Ch02.sigmaStarInvCoarse_eq_ofAEEq hG]
  have hbound := Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv R G
    (s := (3 / 8 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num)
  rw [hmat] at hbound
  have hJnn : 0 ≤ 2 * responseJ (cubeDomain R) b p 0 := by
    have := Ch02.responseJ_nonneg (cubeDomain R) b p 0
    linarith
  exact hchain.trans (mul_le_mul_of_nonneg_right hbound hJnn)

/-- **The loading budget at a general triadic cube, pure-potential loading.** -/
theorem vecNorm_le_sqrt_two_mul_sqrt_lambdaSq_inv_mul_sqrt_responseJ [NeZero d]
    (R : TriadicCube d) (G : Ch02.TriadicCoeffFamily d) (b : CoeffOn (cubeDomain R))
    (hG : CoeffOn.AEEq (G.coeffOn R) b) (p : Vec d) :
    vecNorm p ≤ Real.sqrt 2 *
      (Real.sqrt ((Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹) *
        Real.sqrt (responseJ (cubeDomain R) b p 0)) := by
  set L : ℝ := (Ch02.lambdaSq R (3 / 8) (.finite 2) G)⁻¹ with hL
  set J : ℝ := responseJ (cubeDomain R) b p 0 with hJ
  have hLnn : 0 ≤ L := lambdaSq_inv_nonneg R G
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg (cubeDomain R) b p 0
  have hmain := vecNormSq_le_lambdaSq_inv_mul_two_mul_responseJ R G b hG p
  have hsq : vecNormSq p ≤ (Real.sqrt 2 * (Real.sqrt L * Real.sqrt J)) ^ 2 := by
    have hexp : (Real.sqrt 2 * (Real.sqrt L * Real.sqrt J)) ^ 2 = 2 * (L * J) := by
      have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      have hl : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLnn
      have hj : Real.sqrt J ^ 2 = J := Real.sq_sqrt hJnn
      calc (Real.sqrt 2 * (Real.sqrt L * Real.sqrt J)) ^ 2
          = Real.sqrt 2 ^ 2 * (Real.sqrt L ^ 2 * Real.sqrt J ^ 2) := by ring
        _ = 2 * (L * J) := by rw [h2, hl, hj]
    rw [hexp]
    calc vecNormSq p ≤ L * (2 * J) := hmain
      _ = 2 * (L * J) := by ring
  have hrhs : 0 ≤ Real.sqrt 2 * (Real.sqrt L * Real.sqrt J) := by positivity
  have hvn : (0 : ℝ) ≤ vecNorm p := Ch02.vecNorm_nonneg p
  nlinarith [Ch02.vecNorm_sq_eq_vecNormSq p]

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
