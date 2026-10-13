/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Semantics
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixExtractionProofs
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MagicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# BMatrix

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The coarse matrix `b` as the pure-potential response

Source: ABK26 (`e.big.Lambda.sensitivity`).  The descendant estimate of that
display is stated for the one-cube matrix norm `|b(R; a)|`, while the
sensitivity input is the response functional `J`.  This module records the
exact bridge between them.

The canonical coarse-matrix formula for the response
(`Ch02.responseJ_eq_coarseMatrices_formula_canonical`) reads

```
J(U, p, q; a) = ½ p·σ p + ½ (q + κp)·σ_*^{-1}(q + κp) - p·q ,
```

so at the **pure-potential** loading `q = 0` it collapses to

```
J(U, p, 0; a) = ½ p·(σ + κᵗ σ_*^{-1} κ) p = ½ p·b(U; a) p .
```

Since `b` is positive definite and symmetric, the one-cube norm
`|b| = coarseBMatrixNorm` is exactly the supremum of that quadratic form over
the unit sphere, which is the two-sided comparison proved below.  The same
formula applied to the transposed coefficient field shows that the
pure-potential response is transpose-invariant; that is what removes the
`|p·q|` shift from the adjoint budget of the descendant `D_h` estimate.

Every declaration in this module is an internal helper for the Section 2.4
sensitivity providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.BigLambda

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The pure-potential response is the `b` quadratic form -/

/-- **`2 J(U, p, 0; a) = p · b(U; a) p`.** -/
theorem responseJ_potential_eq_half_bCoarse (U : Domain d) (a : CoeffOn U)
    (p : Vec d) :
    responseJ U a p 0 =
      (1 / 2 : ℝ) * vecDot p (matVecMul (Ch02.bCoarse U a) p) := by
  have hb : Ch02.bCoarse U a =
      Ch02.sigmaCoarse U a +
        matTranspose (Ch02.kappaCoarse U a) *
          (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) := by
    show Ch02.sigmaCoarse U a +
        matTranspose (Ch02.kappaCoarse U a) * Ch02.sigmaStarInvCoarse U a *
          Ch02.kappaCoarse U a = _
    rw [mul_assoc]
  have hRHS : vecDot p (matVecMul (Ch02.bCoarse U a) p) =
      vecDot p (matVecMul (Ch02.sigmaCoarse U a) p) +
        vecDot (matVecMul (Ch02.kappaCoarse U a) p)
          (matVecMul (Ch02.sigmaStarInvCoarse U a)
            (matVecMul (Ch02.kappaCoarse U a) p)) := by
    conv_lhs => rw [hb]
    rw [add_matVecMul, vecDot_add_right,
      ← matVecMul_mul (matTranspose (Ch02.kappaCoarse U a))
        (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) p,
      vecDot_matVecMul_transpose p
        (matVecMul (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) p)
        (Ch02.kappaCoarse U a),
      ← matVecMul_mul (Ch02.sigmaStarInvCoarse U a) (Ch02.kappaCoarse U a) p]
  rw [Ch02.responseJ_eq_coarseMatrices_formula_canonical U a p 0, hRHS]
  simp [vecDot]
  ring

/-- **The pure-potential response is transpose invariant.**

This is the exact reason why the adjoint half of the zero-trace witness carries
no `|p·q|` shift at the pure-potential loading. -/
theorem responseJ_potential_transpose (U : Domain d) (a : CoeffOn U) (p : Vec d) :
    responseJ U a.transpose p 0 = responseJ U a p 0 := by
  have hadj := (Ch02.responseMagicIdentitiesTheory U a).adjoint_quadratic p 0
  rw [hadj, responseJ_potential_eq_half_bCoarse U a p]
  have hb : Ch02.bCoarse U a =
      Ch02.sigmaCoarse U a +
        matTranspose (Ch02.kappaCoarse U a) *
          (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) := by
    show Ch02.sigmaCoarse U a +
        matTranspose (Ch02.kappaCoarse U a) * Ch02.sigmaStarInvCoarse U a *
          Ch02.kappaCoarse U a = _
    rw [mul_assoc]
  have hRHS : vecDot p (matVecMul (Ch02.bCoarse U a) p) =
      vecDot p (matVecMul (Ch02.sigmaCoarse U a) p) +
        vecDot (matVecMul (Ch02.kappaCoarse U a) p)
          (matVecMul (Ch02.sigmaStarInvCoarse U a)
            (matVecMul (Ch02.kappaCoarse U a) p)) := by
    conv_lhs => rw [hb]
    rw [add_matVecMul, vecDot_add_right,
      ← matVecMul_mul (matTranspose (Ch02.kappaCoarse U a))
        (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) p,
      vecDot_matVecMul_transpose p
        (matVecMul (Ch02.sigmaStarInvCoarse U a * Ch02.kappaCoarse U a) p)
        (Ch02.kappaCoarse U a),
      ← matVecMul_mul (Ch02.sigmaStarInvCoarse U a) (Ch02.kappaCoarse U a) p]
  rw [hRHS]
  have hneg : matVecMul (Ch02.sigmaStarInvCoarse U a)
      (0 - matVecMul (Ch02.kappaCoarse U a) p) =
      -matVecMul (Ch02.sigmaStarInvCoarse U a)
        (matVecMul (Ch02.kappaCoarse U a) p) := by
    rw [zero_sub, matVecMul_neg]
  rw [hneg, zero_sub, vecDot_neg_left, vecDot_neg_right]
  simp [vecDot]
  ring

/-! ## Two-sided comparison with the one-cube norm -/

/-- The quadratic form of `b` never exceeds `|b| |p|²`. -/
theorem two_mul_responseJ_potential_le_coarseBMatrixNorm (Q : TriadicCube d)
    (A : Ch02.TriadicCoeffFamily d) (p : Vec d) :
    2 * responseJ (cubeDomain Q) (A.coeffOn Q) p 0 ≤
      Ch02.coarseBMatrixNorm Q A * vecNormSq p := by
  have hquad := Ch02.vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef
    (Ch02.bCoarse_posDef (cubeDomain Q) (A.coeffOn Q)).posSemidef p
  rw [responseJ_potential_eq_half_bCoarse (cubeDomain Q) (A.coeffOn Q) p]
  unfold Ch02.coarseBMatrixNorm
  rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
  linarith

/-- A uniform quadratic-form bound gives the one-cube norm bound. -/
theorem coarseBMatrixNorm_le_of_forall_responseJ_potential [NeZero d]
    (Q : TriadicCube d) (A : Ch02.TriadicCoeffFamily d) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ p : Vec d,
      2 * responseJ (cubeDomain Q) (A.coeffOn Q) p 0 ≤ M * vecNormSq p) :
    Ch02.coarseBMatrixNorm Q A ≤ M := by
  have hone : ∀ x : Vec d,
      vecDot x (matVecMul ((M • (1 : Mat d))) x) = M * vecNormSq x := by
    intro x
    have : matVecMul ((M • (1 : Mat d))) x = M • x := by
      funext i
      simp [matVecMul, Matrix.smul_apply, Matrix.one_apply,
        Finset.sum_ite_eq, mul_comm]
    rw [this, vecDot_smul_right]
    rfl
  have hloew : MatLoewnerLE (Ch02.bCoarse (cubeDomain Q) (A.coeffOn Q))
      (M • (1 : Mat d)) := by
    intro x
    have h := hbound x
    rw [responseJ_potential_eq_half_bCoarse (cubeDomain Q) (A.coeffOn Q) x] at h
    rw [hone x]
    linarith
  have hps : ((M • (1 : Mat d)) : Mat d).PosSemidef := by
    exact Matrix.PosSemidef.one.smul hM
  have hnorm := Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
    (Ch02.bCoarse_posDef (cubeDomain Q) (A.coeffOn Q)).posSemidef hps hloew
  have hM1 : Ch02.matrixNorm ((M • (1 : Mat d)) : Mat d) = M := by
    rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
    exact Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hM
  rw [hM1] at hnorm
  exact hnorm

end

end Algsuperdiff.Section24.Sensitivity.Provider.BigLambda
