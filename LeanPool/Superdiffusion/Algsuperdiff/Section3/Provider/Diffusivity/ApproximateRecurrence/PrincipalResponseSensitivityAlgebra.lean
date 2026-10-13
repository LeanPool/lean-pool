/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.CoarseGaugeCoarseMatrices
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.BlockCoarseMatrix

/-!
# PrincipalResponseSensitivityAlgebra

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: `e.J.by.means.of.bfA` on a gauge-sheared doubled load

Source displays in ABK26:

* `e.J.by.means.of.bfA` (label; display):

  ```
  J(U, p, q; a) = 1/2 (p; -q) . bfA(U; a) (p; -q) - p . q ,
  ```

* the opening two equalities of Step 3 of `l.approximate.recurrence.formula`:
  with `hbar = (h)_{z+cu_n}` the averaged fresh shell,

  ```
  P_z . bfA_m(z+cu_n) P_z 1_{Q_z}
    = bfG_{-hbar} P_z . bfA(z+cu_n; a_m - hbar) bfG_{-hbar} P_z 1_{Q_z}
    = ( 2 J(z+cu_n, -p_z, q_z - hbar p_z; a_m - hbar) - 2 p_z . q_z ) 1_{Q_z} .
  ```

The first equality is `blockVecDot_coarseBlockMatrix_sub_const_skew` of
`ApproximateRecurrence.CoarseGaugeCoarseMatrices`, already proved.  This module
supplies the second one, and the composite of the two.

## The second equality

With `Y = bfG_{-hbar} P_z = (p_z; q_z - hbar p_z)`, `e.J.by.means.of.bfA` at
the load `(p, q) = (-p_z, q_z - hbar p_z)` gives

```
J(U, -p_z, q_z - hbar p_z; c)
  = 1/2 Y . bfA(U; c) Y - (-p_z) . (q_z - hbar p_z)
  = 1/2 Y . bfA(U; c) Y + p_z . q_z ,
```

the last step because `hbar` is skew, so `p_z . hbar p_z = 0`.  Hence

```
Y . bfA(U; c) Y = 2 J(U, -p_z, q_z - hbar p_z; c) - 2 p_z . q_z ,
```

which is the second equality above.

## Carrier and hypotheses

Everything is stated for an arbitrary `Homogenization.Book.Ch02.Domain` and
arbitrary `CoeffOn` objects; the localization cube, the fresh shell and the
good event do not appear.  The only hypotheses are the two source premises:
`hbar` is a constant antisymmetric matrix (it is an average of antisymmetric
shell increments -- see `ApproximateRecurrence.PrincipalResponseShellAverage`),
and `b` represents the shifted field `a - hbar`.  No proof step is carried as a
hypothesis.

## Consistency check

Composing `blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub_const_skew` with
`responseJ_neg_sub_matVecMul_eq_of_sub_const_skew` returns
`blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub` at the unshifted field:
the gauge shear and the field shift cancel, exactly as they must.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-- **`e.J.by.means.of.bfA` on a doubled load.**  For every coefficient object and
every doubled load `X`,

```
X . bfA(U; c) X = 2 J(U, -X_1, X_2; c) - 2 X_1 . X_2 .
```

This is CoarseGraining's `responseJ_eq_block_quadratic` solved for the
quadratic form. -/
theorem blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub
    (U : Domain d) (c : CoeffOn U) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U c) X) =
      2 * responseJ U c (-X.1) X.2 - 2 * vecDot X.1 X.2 := by
  have h := HCPolySupport.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic U c
    (-X.1) X.2
  rw [neg_neg, vecDot_neg_left] at h
  have hX : ((X.1, X.2) : BlockVec d) = X := rfl
  rw [hX] at h
  linarith

/-- **ABK26** (see the module docstring).  The doubled quadratic
form at the gauge-sheared load `bfG_{-hbar} X` is twice the response at the
sheared arguments, minus twice the *unsheared* pairing `X_1 . X_2` -- the shear
does not change the pairing because `hbar` is skew. -/
theorem blockVecDot_coarseBlockMatrix_blockGauge_eq_two_responseJ_sub
    (U : Domain d) (c : CoeffOn U) {hbar : Mat d}
    (hskew : matTranspose hbar = -hbar) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
        (blockMatVecMul (Book.Ch02.coarseBlockMatrix U c)
          (blockMatVecMul (blockGauge (-hbar)) X)) =
      2 * responseJ U c (-X.1) (X.2 - matVecMul hbar X.1) - 2 * vecDot X.1 X.2 := by
  have hY : blockMatVecMul (blockGauge (-hbar)) X =
      ((X.1, X.2 - matVecMul hbar X.1) : BlockVec d) := by
    rw [blockMatVecMul_blockGauge]
    refine Prod.ext rfl ?_
    change matVecMul (-hbar) X.1 + X.2 = X.2 - matVecMul hbar X.1
    rw [neg_matVecMul]
    abel
  have hcross : vecDot X.1 (X.2 - matVecMul hbar X.1) = vecDot X.1 X.2 := by
    rw [vecDot_sub_right,
      vecDot_matVecMul_self_eq_zero_of_transpose_eq_neg hskew X.1, sub_zero]
  rw [hY, blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub U c
    ((X.1, X.2 - matVecMul hbar X.1) : BlockVec d), hcross]

/-- **ABK26 in one line.**  The two opening equalities of Step 3,
composed: the unsheared quadratic form of the *unshifted* field equals twice
the response of the *shifted* field at the sheared arguments, minus twice the
pairing. -/
theorem blockVecDot_coarseBlockMatrix_eq_two_responseJ_sub_const_skew
    {U : Domain d} {a b : CoeffOn U} {hbar : Mat d}
    (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) X) =
      2 * responseJ U b (-X.1) (X.2 - matVecMul hbar X.1) - 2 * vecDot X.1 X.2 := by
  rw [← blockVecDot_coarseBlockMatrix_sub_const_skew hskew hab X]
  exact blockVecDot_coarseBlockMatrix_blockGauge_eq_two_responseJ_sub U b hskew X

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
