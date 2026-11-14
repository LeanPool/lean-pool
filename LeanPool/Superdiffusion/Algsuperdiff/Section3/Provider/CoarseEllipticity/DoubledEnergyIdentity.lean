/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.DoubledResponse
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Response
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.BlockResponse.Foundations.BasicIdentities
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.BlockMatrixField

/-!
# DoubledEnergyIdentity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The doubled-variable energy identity

ABK26 Remark `r.cg.poincare.doubled.variables` restates the coarse-grained
Poincare inequality `p.coarse.grained.Poincare` in terms of the
doubled-variable solution space `S(cu_m)` of `e.bfS`.  Its right-hand side is
the doubled energy `|| bfA^(1/2) X ||_{underline L^2(cu_m)}`, whereas the two
Poincare inequalities it is derived from are stated with the *scalar* energies
`|| s^(1/2) grad v ||_{underline L^2}` and `|| s^(1/2) grad v* ||`.

The bridge between the two is the pointwise algebraic identity proved here:
along the characterization `e.findSfull`

```
X = (grad v + grad v*, a grad v - a^t grad v*),
```

the block quadratic form collapses, by the swapping identity
`e.bfA.magic.swapping`, to twice the sum of the two scalar energy densities.
In CoarseGraining's normalization the block density carries a factor `1/2`, so
the identity reads

```
blockEnergyDensityAt a (X x) x
  = variationEnergyIntegrand U a v x + variationEnergyIntegrand U a^t v* x .
```

This is a pointwise statement about the *integrands*; it carries no integral
and therefore no integrability side condition.

## Scope

This file is infrastructure for `e.CG.Poincare.doubled.vars` and claims no node
status.  The displayed inequality of that node additionally requires a block
negative-Besov seminorm on `R^{2d}`-valued fields, the adjoint invariance of
the coarse-grained ellipticity constants, and a per-truncation form of the
CoarseGraining coarse-grained Poincare inequality; none of those are supplied
here.

## Main results

* `blockEnergyDensityAt_doubledFieldOfSolutions`: the pointwise identity.
* `add_le_sqrt_two_mul_add_sq`: the elementary two-term step that converts the
  pair of scalar energies into the single doubled energy.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Expansion of the doubled quadratic form once the swapping identity has been
applied.  Only bilinearity of `vecDot` and the transpose adjunction are used. -/
private theorem vecDot_swapped_pair_expand (A : Mat d) (p q : Vec d) :
    vecDot (p + q) (matVecMul A p + matVecMul (matTranspose A) q) +
        vecDot (matVecMul A p - matVecMul (matTranspose A) q) (p - q) =
      2 * vecDot p (matVecMul A p) +
        2 * vecDot q (matVecMul (matTranspose A) q) := by
  have h1 : vecDot q (matVecMul A p) = vecDot p (matVecMul (matTranspose A) q) := by
    rw [vecDot_comm q (matVecMul A p), ← vecDot_matVecMul_transpose p q A]
  have h2 : vecDot (matVecMul A p) p = vecDot p (matVecMul A p) :=
    vecDot_comm _ _
  have h3 : vecDot (matVecMul A p) q = vecDot p (matVecMul (matTranspose A) q) :=
    (vecDot_matVecMul_transpose p q A).symm
  have h4 : vecDot (matVecMul (matTranspose A) q) p =
      vecDot p (matVecMul (matTranspose A) q) :=
    vecDot_comm _ _
  have h5 : vecDot (matVecMul (matTranspose A) q) q =
      vecDot q (matVecMul (matTranspose A) q) :=
    vecDot_comm _ _
  simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
    vecDot_neg_right, h1, h2, h3, h4, h5]
  ring

/-- **The doubled-variable energy identity.**  For the doubled field generated
by a primal solution `v` and an adjoint solution `vStar`, the block energy
density is the sum of the two scalar energy densities. -/
theorem blockEnergyDensityAt_doubledFieldOfSolutions {U : Domain d}
    (a : CoeffOn U) (v : Solution U a) (vStar : Solution U a.transpose)
    {x : Vec d} (hdet : IsUnit (symmPart (a.toCoeffField x)).det) :
    blockEnergyDensityAt a ((doubledFieldOfSolutions a v vStar).eval x) x =
      variationEnergyIntegrand U a v x +
        variationEnergyIntegrand U a.transpose vStar x := by
  set A : Mat d := a.toCoeffField x with hA
  set p : Vec d := v.toH1.grad x with hp
  set q : Vec d := vStar.toH1.grad x with hq
  have heval : (doubledFieldOfSolutions a v vStar).eval x =
      (p + q, matVecMul A p - matVecMul (matTranspose A) q) := rfl
  have hmagic : blockMatVecMul (blockMatrixField a x)
      (p + q, matVecMul A p - matVecMul (matTranspose A) q) =
      (matVecMul A p + matVecMul (matTranspose A) q, p - q) := by
    have hswap := HCPolySupport.blockMatVecMul_blockCoeffField_pair_of_isUnit_det_symmPart
      a.toCoeffField x hdet p q
    rw [HCPolySupport.Internal.Ch02.BookCh02.book_blockMatrixField_eq_blockCoeffField]
    exact hswap
  have hsymmA : vecDot p (matVecMul A p) = vecDot p (matVecMul (symmPart A) p) :=
    HCPolySupport.vecDot_matVecMul_self_eq_symmPart A p
  have hsymmAt : vecDot q (matVecMul (matTranspose A) q) =
      vecDot q (matVecMul (symmPart (matTranspose A)) q) :=
    HCPolySupport.vecDot_matVecMul_self_eq_symmPart (matTranspose A) q
  have hden : blockEnergyDensityAt a ((doubledFieldOfSolutions a v vStar).eval x) x =
      (1 / 2 : ℝ) *
        (vecDot (p + q) (matVecMul A p + matVecMul (matTranspose A) q) +
          vecDot (matVecMul A p - matVecMul (matTranspose A) q) (p - q)) := by
    rw [blockEnergyDensityAt, heval, hmagic, blockVecDot]
  rw [hden, vecDot_swapped_pair_expand, hsymmA, hsymmAt]
  rw [variationEnergyIntegrand, variationEnergyIntegrand, hA, hp, hq,
    CoeffOn.transpose_apply]
  ring


/-- The elementary two-term step: a sum of two nonnegative quantities is
dominated by the square root of twice the sum of their squares.  With
`A = || s^(1/2) grad v ||` and `B = || s^(1/2) grad v* ||` the right-hand side
is exactly the doubled energy `|| bfA^(1/2) X ||`, by the identity above. -/
theorem add_le_sqrt_two_mul_add_sq {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A + B ≤ Real.sqrt (2 * (A ^ 2 + B ^ 2)) := by
  have hsq : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by nlinarith [sq_nonneg (A - B)]
  have habs : |A + B| ≤ Real.sqrt (2 * (A ^ 2 + B ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  rwa [abs_of_nonneg (add_nonneg hA hB)] at habs

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
