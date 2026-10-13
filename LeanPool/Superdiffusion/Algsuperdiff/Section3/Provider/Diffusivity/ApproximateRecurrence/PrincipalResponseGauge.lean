/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Block

/-!
# PrincipalResponseGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the constant-skew gauge shear and its coarse block covariance

Source displays in ABK26:

* `e.Gh.def` defines, for a matrix `h`, the doubled shear `bfG_h = [[Id, 0],
  [h, Id]]`;
* `e.Gh.additive` records `bfG_{h1 + h2} = bfG_{h1} bfG_{h2}`, hence
  `bfG_h^{-1} = bfG_{-h}`;
* `e.bfA.LDLt` writes the doubled matrix as `bfA = bfG_{-kappa}^t diag(sigma,
  sigma^{-1}) bfG_{-kappa}`, so that a shift of the coupling matrix `kappa` is
  a conjugation by a shear.

The one place in Section 3.4 where these are used at full strength is the first
equality of Step 3 of `l.approximate.recurrence.formula`: with `hbar` the
average of the fresh shell `k_m - k_{m-h}` over the localization cube `z +
cu_n`,

```
P_z . bfA_m(z + cu_n) P_z
  = bfG_{-hbar} P_z . bfA(z + cu_n; a_m - hbar) bfG_{-hbar} P_z .
```

## What this module proves, and at which carrier

The manuscript's identity is read here at the *coarse matrix package* carrier
`Homogenization.Book.Ch02.CoarseMatrices`, i.e. at the triple
`(sigma, sigmaStarInv, kappa)` out of which
`Homogenization.Book.Ch02.blockMatrixOfCoarseMatrices` assembles `bfA`.  At that
carrier the statement is an unconditional algebraic identity
(`blockVecDot_blockMatrixOfCoarseMatrices_gaugeShift`): shifting `kappa` by
`-h` and shearing the load by `bfG_{-h}` leaves the doubled quadratic form
unchanged.  Skew-symmetry of `h` is not needed for it and is therefore not
assumed.

## What this module does NOT prove

It does **not** prove the manuscript's identity at the *coefficient field*
carrier, because that requires the coarse-graining to intertwine with a constant
skew shift of the field, namely

```
Homogenization.Book.Ch02.coarseMatrices U (a - hbar)
  = gaugeShiftCoarseMatrices hbar (Homogenization.Book.Ch02.coarseMatrices U a)
```

for constant skew `hbar` -- equivalently `sigmaCoarse` and `sigmaStarInvCoarse`
are unchanged and `kappaCoarse` drops by `hbar`.  That statement is about the
variational definition of the coarse matrices, not about block algebra.  Nothing
here asserts it, and no declaration in this file takes it as a hypothesis.

**Update: that obligation is now discharged.**  The sentence above originally
said the statement "is not available in this tree", which is no longer true.
`ApproximateRecurrence.CoarseGaugeCoarseMatrices` proves it unconditionally,
for every `Domain` and `CoeffOn` of CoarseGraining's Chapter 2 carrier and
every constant skew `hbar`, as `coarseMatrices_sub_const_skew` and its
hypothesis-free form `coarseMatrices_perturbConstCoeffOn`.  The
coefficient-field reading is `blockVecDot_coarseBlockMatrix_sub_const_skew`
there.  This file remains the block-algebra half only.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## The doubled shear `bfG_h` -/

/-- `e.Gh.def`: the doubled shear `bfG_h = [[Id, 0], [h, Id]]`. -/
def blockGauge (h : Mat d) : BlockMat d where
  upperLeft := 1
  upperRight := 0
  lowerLeft := h
  lowerRight := 1

private theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem matVecMul_zero_left (x : Vec d) :
    matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

/-- The shear acts on a doubled load by adding `h` applied to the first slot
into the second slot. -/
theorem blockMatVecMul_blockGauge (h : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockGauge h) X = (X.1, matVecMul h X.1 + X.2) := by
  have hfst : matVecMul (1 : Mat d) X.1 + matVecMul (0 : Mat d) X.2 = X.1 := by
    rw [matVecMul_one, matVecMul_zero_left, add_zero]
  have hsnd :
      matVecMul h X.1 + matVecMul (1 : Mat d) X.2 = matVecMul h X.1 + X.2 := by
    rw [matVecMul_one]
  exact Prod.ext hfst hsnd

/-! ## The coarse quadratic form and its shift covariance -/

private theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]

private theorem vecDot_sub_right' (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, sub_eq_add_neg]

private theorem matVecMul_sub_right' (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]

/-- The completed-square expansion of the doubled quadratic form of
`blockMatrixOfCoarseMatrices` against the unsigned load `(p, q)`.

This is the `e.bfA.LDLt` normal form read as a quadratic form.  The same
expansion appears, `private`, inside
`Algsuperdiff.Section3.Provider.Block.AdjointQuadratic`; it is reproved here
rather than exported from there so that this module depends only on
CoarseGraining. -/
private theorem blockVecDot_blockMatrixOfCoarseMatrices_load
    (M : CoarseMatrices d) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)) =
      vecDot p (matVecMul M.sigma p) +
        vecDot (q - matVecMul M.kappa p)
          (matVecMul M.sigmaStarInv (q - matVecMul M.kappa p)) := by
  have hkey1 :
      vecDot p (matVecMul (matTranspose M.kappa * M.sigmaStarInv * M.kappa) p) =
        vecDot (matVecMul M.kappa p)
          (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) := by
    rw [← matVecMul_mul, ← matVecMul_mul,
      vecDot_matVecMul_transpose p
        (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) M.kappa]
  have hkey2 :
      vecDot p (matVecMul (matTranspose M.kappa * M.sigmaStarInv) q) =
        vecDot (matVecMul M.kappa p) (matVecMul M.sigmaStarInv q) := by
    rw [← matVecMul_mul,
      vecDot_matVecMul_transpose p (matVecMul M.sigmaStarInv q) M.kappa]
  have hfst :
      vecDot p ((blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)).1) =
        vecDot p (matVecMul M.sigma p) +
          vecDot (matVecMul M.kappa p)
            (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) -
          vecDot (matVecMul M.kappa p) (matVecMul M.sigmaStarInv q) := by
    show vecDot p
        (matVecMul (M.sigma + matTranspose M.kappa * M.sigmaStarInv * M.kappa) p +
          matVecMul (-(matTranspose M.kappa * M.sigmaStarInv)) q) = _
    rw [add_matVecMul, neg_matVecMul, vecDot_add_right, vecDot_add_right,
      vecDot_neg_right, hkey1, hkey2]
    ring
  have hsnd :
      vecDot q ((blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)).2) =
        -vecDot q (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) +
          vecDot q (matVecMul M.sigmaStarInv q) := by
    show vecDot q
        (matVecMul (-(M.sigmaStarInv * M.kappa)) p + matVecMul M.sigmaStarInv q) = _
    rw [neg_matVecMul, ← matVecMul_mul, vecDot_add_right, vecDot_neg_right]
  have hsquare :
      vecDot (q - matVecMul M.kappa p)
          (matVecMul M.sigmaStarInv (q - matVecMul M.kappa p)) =
        vecDot q (matVecMul M.sigmaStarInv q) -
            vecDot q (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) -
            vecDot (matVecMul M.kappa p) (matVecMul M.sigmaStarInv q) +
          vecDot (matVecMul M.kappa p)
            (matVecMul M.sigmaStarInv (matVecMul M.kappa p)) := by
    rw [matVecMul_sub_right', vecDot_sub_left', vecDot_sub_right',
      vecDot_sub_right']
    ring
  have hdot :
      blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)) =
        vecDot p ((blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)).1) +
          vecDot q ((blockMatVecMul (blockMatrixOfCoarseMatrices M) (p, q)).2) :=
    rfl
  rw [hdot, hfst, hsnd, hsquare]
  ring

/-- The coarse package obtained by dropping the coupling matrix `kappa` by `h`,
leaving `sigma` and `sigmaStarInv` untouched.

This is the coarse-matrix shadow of the field shift `a |-> a - h` used: for a
constant skew `h` the manuscript's `bfA(U; a - h)` is assembled from the same
`sigma` and `sigmaStar` and from `kappa - h`. -/
def gaugeShiftCoarseMatrices (h : Mat d) (M : CoarseMatrices d) :
    CoarseMatrices d where
  sigma := M.sigma
  sigmaStarInv := M.sigmaStarInv
  kappa := M.kappa - h

/-- Gauge covariance of the doubled coarse quadratic form, in the direction and
shape of the first equality: shearing the load by `bfG_{-h}` exactly
compensates dropping the coupling matrix by `h`.

Unconditional: no skew-symmetry, symmetry, or invertibility hypothesis is used.
This is the block-algebra half only; see the module docstring for the
coarse-graining half, which is not proved here. -/
theorem blockVecDot_blockMatrixOfCoarseMatrices_gaugeShift
    (h : Mat d) (M : CoarseMatrices d) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (blockGauge (-h)) X)
        (blockMatVecMul
          (blockMatrixOfCoarseMatrices (gaugeShiftCoarseMatrices h M))
          (blockMatVecMul (blockGauge (-h)) X)) =
      blockVecDot X (blockMatVecMul (blockMatrixOfCoarseMatrices M) X) := by
  obtain ⟨p, q⟩ := X
  rw [blockMatVecMul_blockGauge]
  rw [blockVecDot_blockMatrixOfCoarseMatrices_load
    (gaugeShiftCoarseMatrices h M) p (matVecMul (-h) p + q),
    blockVecDot_blockMatrixOfCoarseMatrices_load M p q]
  have hsigma : (gaugeShiftCoarseMatrices h M).sigma = M.sigma := rfl
  have hstar :
      (gaugeShiftCoarseMatrices h M).sigmaStarInv = M.sigmaStarInv := rfl
  have hkappa : (gaugeShiftCoarseMatrices h M).kappa = M.kappa - h := rfl
  have hslot :
      matVecMul (-h) p + q -
          matVecMul (gaugeShiftCoarseMatrices h M).kappa p =
        q - matVecMul M.kappa p := by
    rw [hkappa, sub_matVecMul, neg_matVecMul]
    abel
  rw [hsigma, hstar, hslot]

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
