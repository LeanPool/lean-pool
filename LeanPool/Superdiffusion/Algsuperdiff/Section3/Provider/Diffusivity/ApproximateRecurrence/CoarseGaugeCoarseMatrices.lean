/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.CoarseGaugeResponse
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseGauge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixPositivity

/-!
# CoarseGaugeCoarseMatrices

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: coarse graining intertwines with a constant skew shift of the field

This module closes the obligation named in the module docstring of
`Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseGauge`:
the *coefficient-field* half of ABK26.  Where that module proved the
block-algebra identity `blockVecDot_blockMatrixOfCoarseMatrices_gaugeShift` at
the coarse package carrier, here we show that the coarse package of the shifted
field really is the gauge shift of the coarse package:

```
coarseMatrices U (a - hbar) = gaugeShiftCoarseMatrices hbar (coarseMatrices U a)
```

for a *constant skew* `hbar`, i.e. `sigma` and `sigmaStar^{-1}` are unchanged
and `kappa` drops by `hbar`.  Combining the two gives the manuscript's opening
equality of Step 3 at the coefficient-field carrier,
`blockVecDot_coarseBlockMatrix_sub_const_skew`.

## How it is proved

`CoarseGaugeResponse.responseJ_sub_const_skew` turns the field shift into the
load shear `J(U,p,q;a - hbar) = J(U,p,q - hbar p;a)`.  CoarseGraining's
`Homogenization.Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical`
(unconditional) writes `J(U,p,q;a)` as `(1/2) p.sigma p + (1/2) (q + kappa
p).sigmaStarInv (q + kappa p) - p.q`.  Because `hbar` is skew, `p. hbar p = 0`,
so the shear absorbs entirely into the completed square and reproduces the same
normal form with `kappa` replaced by `kappa - hbar`.  The canonical
CoarseGraining entry formulas -- polarizations of `J(U,0,.)`, of
`mixedResponse`, and of the corrected `p`-response -- are then read off one at
a time.  The single nondegeneracy input is CoarseGraining's unconditional
`Homogenization.Book.Ch02.isUnit_det_sigmaStarInvCoarse`, needed only because
`kappaCoarse` is *defined* as `sigmaStar * (sigmaStarInv kappa)`.

Every hypothesis is a source premise: `hbar` skew (it is an average of skew
matrices) and `b` a coefficient object representing `a - hbar`.  No proof step
is carried as a hypothesis.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02

variable {d : ℕ}

/-! ## Two quadratic-form helpers -/

private theorem vecDot_add_matVecMul_add_of_isSymm {S : Mat d} (hS : S.IsSymm)
    (x y : Vec d) :
    vecDot (x + y) (matVecMul S (x + y)) =
      vecDot x (matVecMul S x) + 2 * vecDot x (matVecMul S y) +
        vecDot y (matVecMul S y) := by
  rw [matVecMul_add, vecDot_add_left, vecDot_add_right, vecDot_add_right,
    vecDot_matVecMul_comm_of_isSymm hS y x]
  ring

private theorem vecDot_single_matVecMul_single' (M : Mat d) (i j : Fin d) :
    vecDot (Pi.single i (1 : ℝ)) (matVecMul M (Pi.single j (1 : ℝ))) = M i j := by
  have hleft : vecDot (basisVec i) (matVecMul M (basisVec j)) =
      matVecMul M (basisVec j) i := vecDot_basisVec_left i _
  have hright : matVecMul M (basisVec j) i = M i j := by
    change ∑ k : Fin d, M i k * basisVec j k = M i j
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _hk hkj
      simp [hkj]
    · intro hj
      simp at hj
  exact hleft.trans hright

/-! ## The coarse matrices of the shifted field -/

variable {U : Domain d} {a b : CoeffOn U} {hbar : Mat d}

/-- The pure-flux coarse matrix does not see a constant skew shift. -/
theorem sigmaStarInvCoarse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.sigmaStarInvCoarse U b = Book.Ch02.sigmaStarInvCoarse U a := by
  have h0 : ∀ q : Vec d, responseJ U b 0 q = responseJ U a 0 q := by
    intro q
    rw [responseJ_sub_const_skew hskew hab 0 q, matVecMul_zero, sub_zero]
  ext i j
  change Book.Ch02.sigmaStarInvEntry U b i j = Book.Ch02.sigmaStarInvEntry U a i j
  unfold Book.Ch02.sigmaStarInvEntry
  by_cases hij : i = j <;> simp [hij, h0]

theorem sigmaStarCoarse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.sigmaStarCoarse U b = Book.Ch02.sigmaStarCoarse U a := by
  unfold Book.Ch02.sigmaStarCoarse
  rw [sigmaStarInvCoarse_sub_const_skew hskew hab]

/-- The normal form of `J(U,.,.;a - hbar)`: the same `sigma` and
`sigmaStarInv`, with `kappa` replaced by `kappa - hbar`. -/
theorem responseJ_formula_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) (p q : Vec d) :
    responseJ U b p q =
      (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) +
        (1 / 2 : ℝ) *
          vecDot (q + matVecMul (Book.Ch02.kappaCoarse U a - hbar) p)
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
              (q + matVecMul (Book.Ch02.kappaCoarse U a - hbar) p)) -
        vecDot p q := by
  rw [responseJ_sub_const_skew hskew hab p q,
    responseJ_eq_coarseMatrices_formula_canonical U a p (q - matVecMul hbar p)]
  have hsquare :
      q - matVecMul hbar p + matVecMul (Book.Ch02.kappaCoarse U a) p =
        q + matVecMul (Book.Ch02.kappaCoarse U a - hbar) p := by
    rw [sub_matVecMul]
    abel
  have hcross : vecDot p (q - matVecMul hbar p) = vecDot p q := by
    rw [vecDot_sub_right,
      vecDot_matVecMul_self_eq_zero_of_transpose_eq_neg hskew p, sub_zero]
  rw [hsquare, hcross]

theorem mixedResponse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) (p q : Vec d) :
    mixedResponse U b p q =
      vecDot q
        (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
          (matVecMul (Book.Ch02.kappaCoarse U a - hbar) p)) := by
  unfold mixedResponse
  rw [responseJ_formula_sub_const_skew hskew hab p q,
    responseJ_formula_sub_const_skew hskew hab p 0,
    responseJ_formula_sub_const_skew hskew hab 0 q]
  rw [zero_add, matVecMul_zero (Book.Ch02.kappaCoarse U a - hbar), add_zero,
    vecDot_zero_right p, vecDot_zero_left q,
    vecDot_zero_left (matVecMul (Book.Ch02.sigmaCoarse U a) 0),
    vecDot_add_matVecMul_add_of_isSymm (Book.Ch02.sigmaStarInvCoarse_isSymm U a) q
      (matVecMul (Book.Ch02.kappaCoarse U a - hbar) p)]
  ring

theorem sigmaStarInvKappaCoarse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.sigmaStarInvKappaCoarse U b =
      Book.Ch02.sigmaStarInvCoarse U a * (Book.Ch02.kappaCoarse U a - hbar) := by
  ext i j
  change mixedResponse U b (Pi.single j 1) (Pi.single i 1) = _
  rw [mixedResponse_sub_const_skew hskew hab, matVecMul_mul]
  exact vecDot_single_matVecMul_single' _ i j

/-- The coupling matrix drops by the constant skew shift. -/
theorem kappaCoarse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.kappaCoarse U b = Book.Ch02.kappaCoarse U a - hbar := by
  have hdef : Book.Ch02.kappaCoarse U b =
      Book.Ch02.sigmaStarCoarse U b * Book.Ch02.sigmaStarInvKappaCoarse U b := rfl
  rw [hdef, sigmaStarCoarse_sub_const_skew hskew hab,
    sigmaStarInvKappaCoarse_sub_const_skew hskew hab, ← Matrix.mul_assoc,
    sigmaStarCoarse_mul_sigmaStarInvCoarse (isUnit_det_sigmaStarInvCoarse U a),
    Matrix.one_mul]

theorem canonicalSigmaCorrectedResponse_sub_const_skew
    (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) (p : Vec d) :
    canonicalSigmaCorrectedResponse U b p =
      canonicalSigmaCorrectedResponse U a p := by
  rw [canonicalSigmaCorrectedResponse_eq_sigmaCoarse U a p]
  unfold canonicalSigmaCorrectedResponse
  rw [kappaCoarse_sub_const_skew hskew hab,
    sigmaStarInvCoarse_sub_const_skew hskew hab,
    responseJ_formula_sub_const_skew hskew hab p 0]
  rw [zero_add, vecDot_zero_right p,
    vecDot_matVecMul_transpose p
      (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
        (matVecMul (Book.Ch02.kappaCoarse U a - hbar) p))
      (Book.Ch02.kappaCoarse U a - hbar)]
  ring

/-- The diffusivity matrix does not see a constant skew shift. -/
theorem sigmaCoarse_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.sigmaCoarse U b = Book.Ch02.sigmaCoarse U a := by
  ext i j
  change Book.Ch02.sigmaEntry U b i j = Book.Ch02.sigmaEntry U a i j
  unfold Book.Ch02.sigmaEntry
  by_cases hij : i = j <;>
    simp [hij, canonicalSigmaCorrectedResponse_sub_const_skew hskew hab]

/-! ## The intertwining -/

/-- **Coarse graining intertwines with a constant skew shift of the field.**

For a constant skew `hbar` and any coefficient object `b` representing `a -
hbar`, the coarse matrix package of `b` is the gauge shift of the coarse matrix
package of `a`: `sigma` and `sigmaStarInv` are unchanged and `kappa` drops by
`hbar`.  This is the coefficient-field half of ABK26. -/
theorem coarseMatrices_sub_const_skew (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) :
    Book.Ch02.coarseMatrices U b =
      gaugeShiftCoarseMatrices hbar (Book.Ch02.coarseMatrices U a) := by
  refine CoarseMatrices.ext ?_ ?_ ?_
  · exact sigmaCoarse_sub_const_skew hskew hab
  · exact sigmaStarInvCoarse_sub_const_skew hskew hab
  · exact kappaCoarse_sub_const_skew hskew hab

/-- **ABK26 at the coefficient-field carrier.**

Shearing the doubled load by `bfG_{-hbar}` exactly compensates the constant skew
shift `a |-> a - hbar` of the coefficient field, in the doubled quadratic form
of the coarse block matrix `bfA(U; .)`.

The block-algebra half is
`blockVecDot_blockMatrixOfCoarseMatrices_gaugeShift`; the coarse-graining half
is `coarseMatrices_sub_const_skew`. -/
theorem blockVecDot_coarseBlockMatrix_sub_const_skew
    (hskew : matTranspose hbar = -hbar)
    (hab : ∀ x, b.toCoeffField x = a.toCoeffField x - hbar) (X : BlockVec d) :
    blockVecDot (blockMatVecMul (blockGauge (-hbar)) X)
        (blockMatVecMul (Book.Ch02.coarseBlockMatrix U b)
          (blockMatVecMul (blockGauge (-hbar)) X)) =
      blockVecDot X (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) X) := by
  have hbmat : Book.Ch02.coarseBlockMatrix U b =
      blockMatrixOfCoarseMatrices
        (gaugeShiftCoarseMatrices hbar (Book.Ch02.coarseMatrices U a)) := by
    change blockMatrixOfCoarseMatrices (Book.Ch02.coarseMatrices U b) = _
    rw [coarseMatrices_sub_const_skew hskew hab]
  have hamat : Book.Ch02.coarseBlockMatrix U a =
      blockMatrixOfCoarseMatrices (Book.Ch02.coarseMatrices U a) := rfl
  rw [hbmat, hamat]
  exact blockVecDot_blockMatrixOfCoarseMatrices_gaugeShift hbar
    (Book.Ch02.coarseMatrices U a) X

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
