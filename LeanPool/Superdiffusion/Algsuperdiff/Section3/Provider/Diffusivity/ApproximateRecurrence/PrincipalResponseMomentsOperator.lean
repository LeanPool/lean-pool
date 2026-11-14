/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponsePDef
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BlockCoarseMatrix

/-!
# PrincipalResponseMomentsOperator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iv) of the principal response, the operator-norm display

Source display in ABK26, inside Step 3 of the proof of
`l.approximate.recurrence.formula` (label):

```
E[ | bfAhom_{m-1}^{-1/2} bfA_m(cu_n) bfAhom_{m-1}^{-1/2} |^8 ]^{1/8}
  <= C E[ ( shom_{m-1}^{-1} Lambda_{gamma,1}(cu_m)
            + shom_{m-1} lambda_{gamma,1}(cu_m) )^8 ]^{1/8}
  <= C gamma^{-1} ,
```

introduced by "by Proposition `p.cg.ellipticity.bounds` (label) and
`e.ellipticities.monotone.ordered` (label)".

## What is proved here, and what is not

This module supplies the **first inequality** of that display, and supplies it
*pathwise* -- as a deterministic inequality between two functions of the
coefficient field -- which is strictly stronger than the printed inequality
between eighth moments.  The second inequality, the numerical bound
`C gamma^{-1}` for the eighth moment of the right-hand side, is **not** proved
here: it is the content of `p.cg.ellipticity.bounds` at `s = gamma`, `q = 1`,
and nothing below invokes that proposition or any consequence of it.

## The second summand

Every statement below carries the corrected `lambda^{-1}`; the printed `lambda`
occurs nowhere.

## The reading of `| . |`

For the symmetric positive block matrix
`M = bfAhom^{-1/2} bfA(U; a) bfAhom^{-1/2}` the manuscript's `|M|` is the
Euclidean operator norm, which for such a matrix is exactly the supremum of the
doubled quadratic form `X . M X` over the unit sphere.  The statements below
are that supremum bound, written as the homogeneous inequality
`X . M X <= c (X . X)` for every doubled load `X`; `conjugatedCoarseBlockMatrix`
is the matrix `M` itself, so no reading of the display is left implicit.

## Route

The mechanism is one line of block algebra rather than an estimate.  Writing `P
= bfAhom^{-1/2} X` and `Q = bfAhom^{1/2} X`, the pairing `P. Q` collapses to
`X. X` because the two legs of `bfAhom^{\pm 1/2}` are reciprocal scalars on
reciprocal blocks, so the splitting identity `e.bfcoarsegrainedmatrices`
(label; the double-variable `bfJ` it is about is `e.bfJfull.var`, label)

```
bfJ(U, P, Q) = 1/2 P . bfA(U) P + 1/2 Q . bfA_*^{-1}(U) Q - P . Q
```

together with the positivity of `bfA_*^{-1}(U)` gives

```
X . bfAhom^{-1/2} bfA(U) bfAhom^{-1/2} X <= 2 bfJ(U, P, Q) + 2 (X . X) ,
```

and the already-proved sharp one-cube estimate of `e.J.by.f` (label) for a
scalar comparator bounds `bfJ` at a unit probe by `shom^{-1}|b(U)| +
shom|sigma_*^{-1}(U)| - 2`.  The two one-cube norms are then replaced by
`Lambda_{s,q}` and `lambda^{-1}_{s,q}` by `e.ellipticities.monotone.ordered`,
and the localization cube `cu_n` is traded for `cu_m` by
`e.bound.one.cube.by.lambdas` (label).

## Main results

* `conjugatedCoarseBlockMatrix` -- the matrix `M` of the display.
* `blockVecDot_conjugatedCoarseBlockMatrix_le_weightedCoarseEllipticity`
  -- the display's `|M|` bound by the two one-cube norms.
* `blockVecDot_coarseBlockMatrix_le_weightedCoarseEllipticity`
  -- the same statement read as a domination of `P . bfA(U) P`.
* `coarseEllipticity_le_multiscaleEllipticity`,
  `blockVecDot_coarseBlockMatrix_le_weightedMultiscaleEllipticity`
  -- the same display once the two one-cube norms are replaced by
  `Lambda_{s,q}` and `lambda^{-1}_{s,q}` on the cube itself.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The conjugated matrix of the display -/

/-- **The matrix `bfAhom^{-1/2} bfA(U; a) bfAhom^{-1/2}`.**

`bfAhom` is the deterministic scalar block diagonal `annealedLimitBlock`, so
its inverse square root is `annealedLimitBlockInvSqrt`; the conjugation is the
one printed inside the norm. -/
def conjugatedCoarseBlockMatrix (sigma : PositiveScalar) (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) : BlockMat d :=
  Ch02.blockMatMul (annealedLimitBlockInvSqrt sigma)
    (Ch02.blockMatMul (Ch02.coarseBlockMatrix U a)
      (annealedLimitBlockInvSqrt sigma))

/-- The conjugated matrix acts by applying the inverse square root, then the
coarse block matrix, then the inverse square root again. -/
theorem blockMatVecMul_conjugatedCoarseBlockMatrix (sigma : PositiveScalar)
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (X : BlockVec d) :
    blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X =
      blockMatVecMul (annealedLimitBlockInvSqrt sigma)
        (blockMatVecMul (Ch02.coarseBlockMatrix U a)
          (blockMatVecMul (annealedLimitBlockInvSqrt sigma) X)) := by
  rw [conjugatedCoarseBlockMatrix, blockMatVecMul_blockMatMul,
    blockMatVecMul_blockMatMul]

/-! ## The pairing collapse -/

private theorem sqrt_positiveScalar_ne_zero (sigma : PositiveScalar) :
    Real.sqrt (sigma : ℝ) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 sigma.2)

/-- The two legs of `bfAhom^{\pm 1/2}` are reciprocal on reciprocal blocks, so
the pairing of `bfAhom^{-1/2} X` with `bfAhom^{1/2} X` is the plain squared
length of `X`.  This is why the `- P . Q` term of the splitting identity
contributes the exact constant `- 2` at a unit probe. -/
theorem blockVecDot_annealedLimitBlockInvSqrt_annealedLimitBlockSqrt
    (sigma : PositiveScalar) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (annealedLimitBlockInvSqrt sigma) X)
        (blockMatVecMul (annealedLimitBlockSqrt sigma) X) = blockVecDot X X := by
  have hne := sqrt_positiveScalar_ne_zero sigma
  rw [← Prod.mk.eta (p := X), blockMatVecMul_annealedLimitBlockInvSqrt,
    blockMatVecMul_annealedLimitBlockSqrt]
  rw [blockVecDot, blockVecDot, inverseSqrtLoad, sqrtLoad, inverseSqrtLoad,
    sqrtLoad, vecDot_smul_left, vecDot_smul_right, vecDot_smul_left,
    vecDot_smul_right]
  have h1 : (Real.sqrt (sigma : ℝ))⁻¹ *
      (Real.sqrt (sigma : ℝ) * vecDot X.1 X.1) = vecDot X.1 X.1 := by
    field_simp
  have h2 : Real.sqrt (sigma : ℝ) *
      ((Real.sqrt (sigma : ℝ))⁻¹ * vecDot X.2 X.2) = vecDot X.2 X.2 := by
    field_simp
  rw [h1, h2]

/-- The inverse square root is symmetric for the doubled pairing: it may be
moved from one side of `blockVecDot` to the other. -/
private theorem blockVecDot_annealedLimitBlockInvSqrt_comm (sigma : PositiveScalar)
    (X W : BlockVec d) :
    blockVecDot X (blockMatVecMul (annealedLimitBlockInvSqrt sigma) W) =
      blockVecDot (blockMatVecMul (annealedLimitBlockInvSqrt sigma) X) W := by
  rw [← Prod.mk.eta (p := W), ← Prod.mk.eta (p := X),
    blockMatVecMul_annealedLimitBlockInvSqrt,
    blockMatVecMul_annealedLimitBlockInvSqrt]
  rw [blockVecDot, blockVecDot, inverseSqrtLoad, sqrtLoad, inverseSqrtLoad,
    sqrtLoad, vecDot_smul_left, vecDot_smul_right, vecDot_smul_left,
    vecDot_smul_right]

/-! ## The unit probe -/

/-- The display at a unit probe: for `X . X = 1`,

```
X . bfAhom^{-1/2} bfA(U; a) bfAhom^{-1/2} X
  <= 2 shom^{-1}|b(U;a)| + 2 shom|sigma_*^{-1}(U;a)| - 2 .
```

The `- 2` is retained because it is exact, not because it is needed. -/
theorem blockVecDot_conjugatedCoarseBlockMatrix_unit_le (sigma : PositiveScalar)
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) {X : BlockVec d}
    (hX : blockVecDot X X = 1) :
    blockVecDot X (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X) ≤
      2 * ((sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
        (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a)) - 2 := by
  set P : BlockVec d := blockMatVecMul (annealedLimitBlockInvSqrt sigma) X
    with hPdef
  set Q : BlockVec d := blockMatVecMul (annealedLimitBlockSqrt sigma) X
    with hQdef
  have hsplit :=
    (Ch02.blockCoarseMatrixTheory U a).doubled_response_splitting P Q
  have hstar :
      0 ≤ blockVecDot Q
        (blockMatVecMul (Ch02.coarseStarredBlockMatrixInv U a) Q) := by
    rcases eq_or_ne Q 0 with hQ0 | hQ0
    · rw [hQ0]
      simp [blockVecDot, blockMatVecMul, matVecMul, vecDot]
    · exact le_of_lt
        ((Ch02.blockCoarseMatrixTheory U a).starred_inverse_posDef Q hQ0)
  have hPQ : blockVecDot P Q = 1 := by
    rw [hPdef, hQdef,
      blockVecDot_annealedLimitBlockInvSqrt_annealedLimitBlockSqrt, hX]
  have hJ : Ch02.doubledResponseJ U a P Q ≤
      (sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
        (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a) - 2 := by
    have hnorm : vecNormSq X.1 + vecNormSq X.2 = 1 := hX
    have hPeq : P =
        ((Real.sqrt (sigma : ℝ))⁻¹ • X.1, Real.sqrt (sigma : ℝ) • X.2) := by
      rw [hPdef, ← Prod.mk.eta (p := X),
        blockMatVecMul_annealedLimitBlockInvSqrt]
      rfl
    have hQeq : Q =
        (Real.sqrt (sigma : ℝ) • X.1, (Real.sqrt (sigma : ℝ))⁻¹ • X.2) := by
      rw [hQdef, ← Prod.mk.eta (p := X),
        blockMatVecMul_annealedLimitBlockSqrt]
      rfl
    rw [hPeq, hQeq]
    exact Provider.ErrorComparison.doubledResponseJ_scalarNormalized_le U a
      sigma.2 X.1 X.2 hnorm
  have hconj : blockVecDot X
      (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X) =
      blockVecDot P (blockMatVecMul (Ch02.coarseBlockMatrix U a) P) := by
    rw [blockMatVecMul_conjugatedCoarseBlockMatrix, ← hPdef,
      blockVecDot_annealedLimitBlockInvSqrt_comm]
  rw [hconj]
  linarith

/-! ## The homogeneous form -/

private theorem blockVecDot_self_eq_zero_iff {X : BlockVec d} :
    blockVecDot X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have h1 : vecNormSq X.1 + vecNormSq X.2 = 0 := h
    have hfst : X.1 = 0 :=
      vecNormSq_eq_zero (le_antisymm (by linarith [vecNormSq_nonneg X.2])
        (vecNormSq_nonneg X.1))
    have hsnd : X.2 = 0 :=
      vecNormSq_eq_zero (le_antisymm (by linarith [vecNormSq_nonneg X.1])
        (vecNormSq_nonneg X.2))
    exact Prod.ext hfst hsnd
  · intro h
    rw [h]
    simp [blockVecDot, vecDot]

/-- **The display, in operator-norm form.**  For every doubled load `X`,

```
X . bfAhom^{-1/2} bfA(U; a) bfAhom^{-1/2} X
  <= ( 2 shom^{-1}|b(U;a)| + 2 shom|sigma_*^{-1}(U;a)| - 2 ) (X . X) ,
```

which for the symmetric positive matrix on the left is exactly the manuscript's
`| bfAhom^{-1/2} bfA(U;a) bfAhom^{-1/2} | <= 2 shom^{-1}|b| + 2 shom|sigma_*^{-1}| - 2`. -/
theorem blockVecDot_conjugatedCoarseBlockMatrix_le_weightedCoarseEllipticity
    (sigma : PositiveScalar) (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X) ≤
      (2 * ((sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
        (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a)) - 2) *
        blockVecDot X X := by
  rcases eq_or_ne X 0 with hX0 | hX0
  · rw [hX0]
    simp [blockVecDot, blockMatVecMul, matVecMul, vecDot]
  · have hpos : 0 < blockVecDot X X :=
      lt_of_le_of_ne (blockVecDot_nonneg X)
        (fun h => hX0 (blockVecDot_self_eq_zero_iff.1 h.symm))
    set t : ℝ := Real.sqrt (blockVecDot X X) with htdef
    have htpos : 0 < t := Real.sqrt_pos.2 hpos
    have htsq : t * t = blockVecDot X X := Real.mul_self_sqrt hpos.le
    have hunit : blockVecDot (t⁻¹ • X) (t⁻¹ • X) = 1 := by
      rw [blockVecDot_smul_left, blockVecDot_smul_right, ← htsq]
      field_simp
    have hkey := blockVecDot_conjugatedCoarseBlockMatrix_unit_le sigma U a hunit
    rw [blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right]
      at hkey
    have hscale := mul_le_mul_of_nonneg_left hkey (mul_self_nonneg t)
    have hcollapse : t * t *
        (t⁻¹ * (t⁻¹ *
          blockVecDot X (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X))) =
        blockVecDot X
          (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X) := by
      field_simp
    rw [hcollapse, htsq] at hscale
    calc blockVecDot X
          (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X)
        ≤ blockVecDot X X *
            (2 * ((sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
              (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a)) - 2) :=
          hscale
      _ = (2 * ((sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
            (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a)) - 2) *
            blockVecDot X X := by ring

/-! ## The load reading: `bfAhom^{1/2}` undoes the conjugation -/

/-- Applying `bfAhom^{-1/2}` after `bfAhom^{1/2}` is the identity on doubled
loads. -/
theorem blockMatVecMul_annealedLimitBlockInvSqrt_annealedLimitBlockSqrt
    (sigma : PositiveScalar) (Y : BlockVec d) :
    blockMatVecMul (annealedLimitBlockInvSqrt sigma)
        (blockMatVecMul (annealedLimitBlockSqrt sigma) Y) = Y := by
  have hne := sqrt_positiveScalar_ne_zero sigma
  rw [← Prod.mk.eta (p := Y), blockMatVecMul_annealedLimitBlockSqrt,
    blockMatVecMul_annealedLimitBlockInvSqrt, inverseSqrtLoad, sqrtLoad,
    sqrtLoad, inverseSqrtLoad, smul_smul, smul_smul]
  have h1 : (Real.sqrt (sigma : ℝ))⁻¹ * Real.sqrt (sigma : ℝ) = 1 := by
    field_simp
  have h2 : Real.sqrt (sigma : ℝ) * (Real.sqrt (sigma : ℝ))⁻¹ = 1 := by
    field_simp
  rw [h1, h2, one_smul, one_smul]

/-- **The squared length `| bfAhom^{1/2} P |^2`.**  It is the `shom`-weighted pair
`shom |p|^2 + shom^{-1} |q|^2`, i.e. exactly the integrand of the sub-step (ii)
display. -/
theorem blockVecDot_annealedLimitBlockSqrt_self (sigma : PositiveScalar)
    (Y : BlockVec d) :
    blockVecDot (blockMatVecMul (annealedLimitBlockSqrt sigma) Y)
        (blockMatVecMul (annealedLimitBlockSqrt sigma) Y) =
      (sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2 := by
  have hne := sqrt_positiveScalar_ne_zero sigma
  rw [← Prod.mk.eta (p := Y), blockMatVecMul_annealedLimitBlockSqrt, blockVecDot,
    sqrtLoad, inverseSqrtLoad, vecDot_smul_left, vecDot_smul_right,
    vecDot_smul_left, vecDot_smul_right]
  have h1 : Real.sqrt (sigma : ℝ) * (Real.sqrt (sigma : ℝ) * vecDot Y.1 Y.1) =
      (sigma : ℝ) * vecNormSq Y.1 := by
    rw [← mul_assoc, Real.mul_self_sqrt sigma.2.le]
    rfl
  have h2 : (Real.sqrt (sigma : ℝ))⁻¹ *
      ((Real.sqrt (sigma : ℝ))⁻¹ * vecDot Y.2 Y.2) =
      (sigma : ℝ)⁻¹ * vecNormSq Y.2 := by
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt sigma.2.le]
    rfl
  rw [h1, h2]

/-- **The display, read on a load.**  The conjugation is undone by writing the load
as `bfAhom^{-1/2}` applied to a doubled vector: for every load `Y`,

```
Y . bfA(U; a) Y
  <= ( 2 shom^{-1}|b(U;a)| + 2 shom|sigma_*^{-1}(U;a)| - 2 )
       ( shom |Y_1|^2 + shom^{-1} |Y_2|^2 ) ,
```

whose right-hand factor is `| bfAhom^{1/2} Y |^2`.  This is the form in which
the display is consumed: it is the pointwise domination `X <= B . V^2` of the
Hoelder split, with `B` the operator norm and `V` the normalized load length. -/
theorem blockVecDot_coarseBlockMatrix_le_weightedCoarseEllipticity
    (sigma : PositiveScalar) (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (Ch02.coarseBlockMatrix U a) Y) ≤
      (2 * ((sigma : ℝ)⁻¹ * Ch02.matrixNorm (Ch02.bCoarse U a) +
        (sigma : ℝ) * Ch02.matrixNorm (Ch02.sigmaStarInvCoarse U a)) - 2) *
        ((sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2) := by
  set X : BlockVec d := blockMatVecMul (annealedLimitBlockSqrt sigma) Y with hXdef
  have hY : blockMatVecMul (annealedLimitBlockInvSqrt sigma) X = Y := by
    rw [hXdef, blockMatVecMul_annealedLimitBlockInvSqrt_annealedLimitBlockSqrt]
  have hconj : blockVecDot X
      (blockMatVecMul (conjugatedCoarseBlockMatrix sigma U a) X) =
      blockVecDot Y (blockMatVecMul (Ch02.coarseBlockMatrix U a) Y) := by
    rw [blockMatVecMul_conjugatedCoarseBlockMatrix, hY,
      blockVecDot_annealedLimitBlockInvSqrt_comm, hY]
  have hnorm : blockVecDot X X =
      (sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2 := by
    rw [hXdef, blockVecDot_annealedLimitBlockSqrt_self]
  have h := blockVecDot_conjugatedCoarseBlockMatrix_le_weightedCoarseEllipticity
    sigma U a X
  rwa [hconj, hnorm] at h

/-! ## The corrected display on one triadic cube -/

/-- `e.ellipticities.monotone.ordered` (label) at the two ends of its chain, in the
form the display needs: the two one-cube norms are dominated by `Lambda_{s,q}`
and by `lambda^{-1}_{s,q}`. -/
theorem coarseEllipticity_le_multiscaleEllipticity [NeZero d]
    (R : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s : ℝ}
    {q : Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    Ch02.matrixNorm (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) ≤
        Ch02.LambdaSq R s q a ∧
      Ch02.matrixNorm (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) ≤
        (Ch02.lambdaSq R s q a)⁻¹ := by
  obtain ⟨-, hlow, -, hup, -⟩ :=
    Provider.ErrorComparison.ellipticities_monotone_ordered R a
      (t := s / 2) (s := s) (by linarith) (by linarith) hq
  refine ⟨hup, ?_⟩
  have hpos : 0 < Ch02.lambdaSq R s q a := Ch02.lambdaSq_pos R a hs hq
  have := inv_anti₀ hpos hlow
  rwa [inv_inv] at this

/-- ```
Y . bfA(R; a) Y
  <= 2 ( shom^{-1} Lambda_{s,q}(R; a) + shom lambda^{-1}_{s,q}(R; a) )
       ( shom |Y_1|^2 + shom^{-1} |Y_2|^2 ) .
``` -/
theorem blockVecDot_coarseBlockMatrix_le_weightedMultiscaleEllipticity [NeZero d]
    (sigma : PositiveScalar) (R : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} {q : Ch02.MultiscaleExponent}
    (hs : 0 < s) (hq : q.IsAdmissible) (Y : BlockVec d) :
    blockVecDot Y
        (blockMatVecMul
          (Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (a.coeffOn R)) Y) ≤
      2 * ((sigma : ℝ)⁻¹ * Ch02.LambdaSq R s q a +
        (sigma : ℝ) * (Ch02.lambdaSq R s q a)⁻¹) *
        ((sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2) := by
  obtain ⟨hb, hstar⟩ := coarseEllipticity_le_multiscaleEllipticity R a hs hq
  have hfac : (0 : ℝ) ≤
      (sigma : ℝ) * vecNormSq Y.1 + (sigma : ℝ)⁻¹ * vecNormSq Y.2 := by
    have h1 := vecNormSq_nonneg Y.1
    have h2 := vecNormSq_nonneg Y.2
    have hs1 := sigma.2.le
    have hs2 := (inv_pos.2 sigma.2).le
    positivity
  refine le_trans
    (blockVecDot_coarseBlockMatrix_le_weightedCoarseEllipticity sigma _ _ Y) ?_
  refine mul_le_mul_of_nonneg_right ?_ hfac
  have hbm : (sigma : ℝ)⁻¹ *
      Ch02.matrixNorm (Ch02.bCoarse (Ch02.cubeDomain R) (a.coeffOn R)) ≤
      (sigma : ℝ)⁻¹ * Ch02.LambdaSq R s q a :=
    mul_le_mul_of_nonneg_left hb (inv_pos.2 sigma.2).le
  have hsm : (sigma : ℝ) *
      Ch02.matrixNorm
        (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R) (a.coeffOn R)) ≤
      (sigma : ℝ) * (Ch02.lambdaSq R s q a)⁻¹ :=
    mul_le_mul_of_nonneg_left hstar sigma.2.le
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
