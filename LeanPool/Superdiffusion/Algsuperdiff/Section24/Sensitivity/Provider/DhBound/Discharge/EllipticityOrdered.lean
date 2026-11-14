/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.AdjointResponse
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.Lambda.UnitCubeLambdaCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# EllipticityOrdered

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The loading is controlled by the coarse gauge and the response

Source: ABK26, the last summand of the three-way split of the source
combination `∇w + ∇w^* + ℓ_p`: the affine piece contributes the constant
gradient `p`, and the proof of `l.Dh.bound` estimates `|p|` by the ellipticity
chain `e.cg.bounds.basic.definitions` together with `e.J.by.means.of.bfA`,

```
|p|² ≤ |σ_*^{-1}| (p · σ_* p) ≤ |σ_*^{-1}| (p · σ p) ≤ λ_{3/8,2}^{-1} · 2 (J + p·q) .
```

The three inequalities are, in order,

* `Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse`
  applied with the (unconditionally invertible) pair `σ_*`, `σ_*^{-1}`;
* the Löwner order `Book.Ch02.sigmaStarCoarse_le_sigmaCoarse`;
* the canonical coarse-matrix formula
  `Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical`, whose middle term
  is a nonnegative quadratic form in `q + κ p`.

The one-cube ellipticity bound
`Book.Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv` then replaces
`|σ_*^{-1}|` by the coarse gauge, which is transported to the frozen
`unitCubeLambda` by the characterization theorem, exactly as in
`Provider.DhBound.Assembly.GaugeBridge`.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.UnitCubeMultiscale

noncomputable section

variable {d : ℕ}

/-! ## The general-domain chain -/

/-- `σ_*^{-1}` is a left inverse of `σ_*` at every Chapter 2 domain. -/
theorem matVecMul_sigmaStarInvCoarse_sigmaStarCoarse (U : Domain d) (a : CoeffOn U)
    (ξ : Vec d) :
    matVecMul (Ch02.sigmaStarInvCoarse U a)
        (matVecMul (Ch02.sigmaStarCoarse U a) ξ) = ξ := by
  rw [matVecMul_mul,
    Ch02.sigmaStarInvCoarse_mul_sigmaStarCoarse
      (Ch02.isUnit_det_sigmaStarInvCoarse U a)]
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The first link of the ellipticity chain. -/
theorem vecNormSq_le_matrixNorm_mul_vecDot_sigmaStarCoarse (U : Domain d)
    (a : CoeffOn U) (p : Vec d) :
    vecNormSq p ≤ Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) *
      vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) :=
  Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    (A := Ch02.sigmaStarCoarse U a) (B := Ch02.sigmaStarInvCoarse U a)
    (Ch02.sigmaStarInvCoarse_posDef U a).posSemidef
    (matVecMul_sigmaStarInvCoarse_sigmaStarCoarse U a) p

/-- The second link: the Löwner order `σ_* ≤ σ`. -/
theorem vecDot_sigmaStarCoarse_le_vecDot_sigmaCoarse (U : Domain d) (a : CoeffOn U)
    (p : Vec d) :
    vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) ≤
      vecDot p (matVecMul (Ch02.sigmaCoarse U a) p) := by
  have h := Ch02.sigmaStarCoarse_le_sigmaCoarse U a p
  linarith

/-- The third link: the pure-gradient quadratic form is at most `2 (J + p·q)`. -/
theorem vecDot_sigmaCoarse_le_two_mul_add (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) :
    vecDot p (matVecMul (Ch02.sigmaCoarse U a) p) ≤
      2 * (responseJ U a p q + vecDot p q) := by
  have hcan := Ch02.responseJ_eq_coarseMatrices_formula_canonical U a p q
  have hquad : 0 ≤ vecDot (q + matVecMul (Ch02.kappaCoarse U a) p)
      (matVecMul (Ch02.sigmaStarInvCoarse U a)
        (q + matVecMul (Ch02.kappaCoarse U a) p)) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Ch02.sigmaStarInvCoarse_posDef U a).posSemidef.dotProduct_mulVec_nonneg
        (q + matVecMul (Ch02.kappaCoarse U a) p)
  linarith

/-- **The ellipticity chain at a general Chapter 2 domain.** -/
theorem vecNormSq_le_matrixNorm_sigmaStarInvCoarse_mul_two_mul_add (U : Domain d)
    (a : CoeffOn U) (p q : Vec d) :
    vecNormSq p ≤ Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) *
      (2 * (responseJ U a p q + vecDot p q)) := by
  have hnorm : 0 ≤ Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) := by
    rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
    exact Ch02.matrixOperatorNorm_nonneg _
  refine (vecNormSq_le_matrixNorm_mul_vecDot_sigmaStarCoarse U a p).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hnorm
  exact (vecDot_sigmaStarCoarse_le_vecDot_sigmaCoarse U a p).trans
    (vecDot_sigmaCoarse_le_two_mul_add U a p q)

/-- The right-hand quadratic budget of the ellipticity chain is nonnegative. -/
theorem zero_le_two_mul_responseJ_add_vecDot (U : Domain d) (a : CoeffOn U)
    (p q : Vec d) :
    0 ≤ 2 * (responseJ U a p q + vecDot p q) := by
  have hstar : 0 ≤ vecDot p (matVecMul (Ch02.sigmaStarCoarse U a) p) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      (Ch02.sigmaStarCoarse_posDef U a).posSemidef.dotProduct_mulVec_nonneg p
  have h1 := vecDot_sigmaStarCoarse_le_vecDot_sigmaCoarse U a p
  have h2 := vecDot_sigmaCoarse_le_two_mul_add U a p q
  linarith

/-! ## The frozen unit-cube gauge -/

/-- The frozen coarse gauge at the sensitivity exponents is positive. -/
theorem unitCubeLambda_sensitivity_pos [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    0 < unitCubeLambda (3 / 8) (.finite 2) a := by
  classical
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  have hgauge : unitCubeLambda (3 / 8) (.finite 2) a =
      Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) F :=
    unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) a F hF
  rw [hgauge]
  exact Ch02.lambdaSq_finite_pos (originCube d 0) F (by norm_num) (by norm_num)

/-- **The ellipticity chain at the frozen unit-cube carrier.** -/
theorem vecNormSq_le_unitCubeLambda_inv_mul_two_mul_add [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (p q : Vec d) :
    vecNormSq p ≤ (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ *
      (2 * (responseJ (cubeDomain (originCube d 0)) a p q + vecDot p q)) := by
  classical
  obtain ⟨F, hF⟩ := exists_compatibleTriadicCoeffFamily a
  have hgauge : unitCubeLambda (3 / 8) (.finite 2) a =
      Ch02.lambdaSq (originCube d 0) (3 / 8) (.finite 2) F :=
    unitCubeLambda_characterization (3 / 8 : ℝ) (.finite 2) a F hF
  have hmat : Ch02.coarseSigmaStarInvMatrixNorm (originCube d 0) F =
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (cubeDomain (originCube d 0)) a) := by
    unfold Ch02.coarseSigmaStarInvMatrixNorm
    rw [Ch02.sigmaStarInvCoarse_eq_ofAEEq hF]
  have hbound :=
    Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv (originCube d 0) F
      (s := (3 / 8 : ℝ)) (q := (2 : ℝ)) (by norm_num) (by norm_num)
  rw [hmat, ← hgauge] at hbound
  refine (vecNormSq_le_matrixNorm_sigmaStarInvCoarse_mul_two_mul_add
    (cubeDomain (originCube d 0)) a p q).trans ?_
  exact mul_le_mul_of_nonneg_right hbound
    (zero_le_two_mul_responseJ_add_vecDot (cubeDomain (originCube d 0)) a p q)

/-! ## The budget shape consumed by the Term BC assembly -/

/-- **The frozen budget shape for the loading.**

`|p| ≤ √2 · λ_{3/8,2}^{-1/2} · ( J^{1/2} + |p·q|^{1/2} )`. -/
theorem vecNorm_le_sqrt_two_mul_sqrt_unitCubeLambda_inv_mul_add [NeZero d]
    (a : CoeffOn (cubeDomain (originCube d 0))) (p q : Vec d) :
    vecNorm p ≤ Real.sqrt 2 *
      Real.sqrt ((unitCubeLambda (3 / 8) (.finite 2) a)⁻¹) *
      (Real.sqrt (responseJ (cubeDomain (originCube d 0)) a p q) +
        Real.sqrt |vecDot p q|) := by
  classical
  set L : ℝ := (unitCubeLambda (3 / 8) (.finite 2) a)⁻¹ with hL
  set J : ℝ := responseJ (cubeDomain (originCube d 0)) a p q with hJ
  have hJnn : 0 ≤ J := Ch02.responseJ_nonneg _ a p q
  have hmain := vecNormSq_le_unitCubeLambda_inv_mul_two_mul_add a p q
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact le_of_lt (inv_pos.mpr (unitCubeLambda_sensitivity_pos a))
  have hstep : vecNormSq p ≤ L * (2 * (J + |vecDot p q|)) := by
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hLnn)
    have := le_abs_self (vecDot p q)
    linarith
  have hsq : vecNorm p ^ 2 ≤ L * (2 * (J + |vecDot p q|)) := by
    rw [vecNorm_sq_eq_vecNormSq]; exact hstep
  have hrhs : Real.sqrt (L * (2 * (J + |vecDot p q|))) ≤
      Real.sqrt 2 * Real.sqrt L * (Real.sqrt J + Real.sqrt |vecDot p q|) := by
    have habs : (0 : ℝ) ≤ |vecDot p q| := abs_nonneg _
    have hsum : Real.sqrt (J + |vecDot p q|) ≤
        Real.sqrt J + Real.sqrt |vecDot p q| :=
      sqrt_add_le_add_sqrt_of_nonneg hJnn habs
    have hfactor : Real.sqrt (L * (2 * (J + |vecDot p q|))) =
        Real.sqrt L * (Real.sqrt 2 * Real.sqrt (J + |vecDot p q|)) := by
      rw [Real.sqrt_mul hLnn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hfactor]
    have hmul : Real.sqrt 2 * Real.sqrt (J + |vecDot p q|) ≤
        Real.sqrt 2 * (Real.sqrt J + Real.sqrt |vecDot p q|) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg 2)
    calc Real.sqrt L * (Real.sqrt 2 * Real.sqrt (J + |vecDot p q|))
        ≤ Real.sqrt L * (Real.sqrt 2 * (Real.sqrt J + Real.sqrt |vecDot p q|)) :=
          mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg L)
      _ = Real.sqrt 2 * Real.sqrt L * (Real.sqrt J + Real.sqrt |vecDot p q|) := by
          ring
  refine le_trans ?_ hrhs
  have hp : vecNorm p = Real.sqrt (vecNorm p ^ 2) :=
    (Real.sqrt_sq (vecNorm_nonneg p)).symm
  rw [hp]
  exact Real.sqrt_le_sqrt hsq

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
