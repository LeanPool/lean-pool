/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BlockCoarseMatrix
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity

/-!
# DoubledAdjointEllipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Adjoint invariance of the coarse-grained ellipticity constants

ABK26 Remark `r.cg.poincare.doubled.variables` states the doubled-variables
Poincare inequality `e.CG.Poincare.doubled.vars` with the coarse-grained
ellipticity constants `lambda_{s,q}(cu_m; a)` and `Lambda_{s,q}(cu_m; a)` of
the *primal* coefficient field, although its proof applies
`p.coarse.grained.Poincare` to the adjoint solution `v^*` as well, and
therefore produces `lambda_{s,q}(cu_m; a^t)` and `Lambda_{s,q}(cu_m; a^t)` on
that half.  The two agree.  This module proves that -- item (beta) of the
infrastructure list recorded in `DoubledEnergyIdentity.lean`.

## The mechanism

Both constants are geometric sums of the one-cube norms
`|sigma_*^{-1}(R; a)|` and `|b(R; a)|` over descendants, and the two coarse
matrices are adjoint invariant:

* `sigma_*(U; a^t) = sigma_*(U; a)` (CoarseGraining
  `BlockCoarseMatrixTheory.adjoint_sigmaStar`), hence `sigma_*^{-1}(U; a^t) =
  sigma_*^{-1}(U; a)` since `sigma_*^{-1}` has invertible determinant;
* `b = sigma + kappa^t sigma_*^{-1} kappa` with `sigma(U; a^t) = sigma(U; a)`
  and `kappa(U; a^t) = -kappa(U; a)`, so the sign cancels in the quadratic
  correction.

## Main results

* `adjointFamily` -- the adjoint triadic coefficient family `a^t`.
* `sigmaStarInvCoarse_transpose`, `bCoarse_transpose` -- the two matrix
  identities.
* `lambdaSq_adjointFamily`, `LambdaSq_adjointFamily` -- the display's own
  invariance, for every exponent `q` (finite and endpoint).

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.

## References

* ABK26, `r.cg.poincare.doubled.variables`; `e.bfA.magic.swapping`;
  `e.findSfull`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## The adjoint family -/

/-- **The adjoint triadic coefficient family `a^t`.**  Cube by cube it is
CoarseGraining's `CoeffOn.transpose`; the restriction compatibility is
inherited from `a` by transposing the almost-everywhere identity. -/
def adjointFamily (a : Ch02.TriadicCoeffFamily d) : Ch02.TriadicCoeffFamily d where
  coeffOn Q := (a.coeffOn Q).transpose
  restrictsTo_of_subset := by
    intro Q R hsub
    have h := a.restrictsTo_of_subset hsub
    have h2 : ∀ᵐ x ∂ volumeMeasureOn ((Ch02.cubeDomain R : Set (Vec d))),
        matTranspose ((a.coeffOn R).toCoeffField x) =
          matTranspose ((a.coeffOn Q).toCoeffField x) := by
      filter_upwards [h] with x hx
      exact congrArg matTranspose hx
    exact h2

@[simp] theorem adjointFamily_coeffOn (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) :
    (adjointFamily a).coeffOn Q = (a.coeffOn Q).transpose :=
  rfl

/-! ## Adjoint invariance of the two coarse matrices -/

/-- `sigma_*^{-1}(U; a^t) = sigma_*^{-1}(U; a)`. -/
theorem sigmaStarInvCoarse_transpose (U : Ch02.Domain d) (a : Ch02.CoeffOn U) :
    Ch02.sigmaStarInvCoarse U a.transpose = Ch02.sigmaStarInvCoarse U a := by
  have h := (Ch02.blockCoarseMatrixTheory U a).adjoint_sigmaStar
  have h1 := congrArg Inv.inv h
  rw [Ch02.sigmaStarCoarse, Ch02.sigmaStarCoarse,
    Matrix.nonsing_inv_nonsing_inv _ (Ch02.isUnit_det_sigmaStarInvCoarse U a.transpose),
    Matrix.nonsing_inv_nonsing_inv _ (Ch02.isUnit_det_sigmaStarInvCoarse U a)] at h1
  exact h1

/-- `b(U; a^t) = b(U; a)`: `sigma` is invariant, `kappa` changes sign, and the
correction `kappa^t sigma_*^{-1} kappa` is even in `kappa`. -/
theorem bCoarse_transpose (U : Ch02.Domain d) (a : Ch02.CoeffOn U) :
    Ch02.bCoarse U a.transpose = Ch02.bCoarse U a := by
  have hs := (Ch02.blockCoarseMatrixTheory U a).adjoint_sigma
  have hk := (Ch02.blockCoarseMatrixTheory U a).adjoint_kappa
  have hsi := sigmaStarInvCoarse_transpose U a
  unfold Ch02.bCoarse Ch02.CoarseMatrices.b
  simp only [Ch02.coarseMatrices_sigma, Ch02.coarseMatrices_sigmaStarInv,
    Ch02.coarseMatrices_kappa, hs, hk, hsi]
  simp [matTranspose]

/-! ## Adjoint invariance of the one-cube and descendant norms -/

theorem coarseSigmaStarInvMatrixNorm_adjointFamily (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) :
    Ch02.coarseSigmaStarInvMatrixNorm Q (adjointFamily a) =
      Ch02.coarseSigmaStarInvMatrixNorm Q a := by
  unfold Ch02.coarseSigmaStarInvMatrixNorm
  rw [adjointFamily_coeffOn, sigmaStarInvCoarse_transpose]

theorem coarseBMatrixNorm_adjointFamily (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) :
    Ch02.coarseBMatrixNorm Q (adjointFamily a) = Ch02.coarseBMatrixNorm Q a := by
  unfold Ch02.coarseBMatrixNorm
  rw [adjointFamily_coeffOn, bCoarse_transpose]

theorem maxDescendantSigmaStarInvMatrixNormAtScale_adjointFamily (Q : TriadicCube d)
    (k : ℤ) (a : Ch02.TriadicCoeffFamily d) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k (adjointFamily a) =
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a := by
  unfold Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  refine congrArg _ ?_
  funext R
  exact coarseSigmaStarInvMatrixNorm_adjointFamily R a

theorem maxDescendantBMatrixNormAtScale_adjointFamily (Q : TriadicCube d)
    (k : ℤ) (a : Ch02.TriadicCoeffFamily d) :
    Ch02.maxDescendantBMatrixNormAtScale Q k (adjointFamily a) =
      Ch02.maxDescendantBMatrixNormAtScale Q k a := by
  unfold Ch02.maxDescendantBMatrixNormAtScale
  refine congrArg _ ?_
  funext R
  exact coarseBMatrixNorm_adjointFamily R a

/-! ## Adjoint invariance of the coarse-grained ellipticity constants -/

/-- **`lambda_{s,q}(Q; a^t) = lambda_{s,q}(Q; a)`**, for every exponent. -/
theorem lambdaSq_adjointFamily (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) :
    Ch02.lambdaSq Q s q (adjointFamily a) = Ch02.lambdaSq Q s q a := by
  cases q with
  | finite q =>
      simp only [Ch02.lambdaSq, Ch02.lambdaSqFinite,
        maxDescendantSigmaStarInvMatrixNormAtScale_adjointFamily]
  | infinity =>
      simp only [Ch02.lambdaSq, Ch02.lambdaSqInfinity,
        maxDescendantSigmaStarInvMatrixNormAtScale_adjointFamily]

/-- **`Lambda_{s,q}(Q; a^t) = Lambda_{s,q}(Q; a)`**, for every exponent. -/
theorem LambdaSq_adjointFamily (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) :
    Ch02.LambdaSq Q s q (adjointFamily a) = Ch02.LambdaSq Q s q a := by
  cases q with
  | finite q =>
      simp only [Ch02.LambdaSq, Ch02.LambdaSqFinite,
        maxDescendantBMatrixNormAtScale_adjointFamily]
  | infinity =>
      simp only [Ch02.LambdaSq, Ch02.LambdaSqInfinity,
        maxDescendantBMatrixNormAtScale_adjointFamily]

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
