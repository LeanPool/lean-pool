/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedBlockBridge
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAnnealed
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.DomainBridge
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewBlock

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew congruence of coarse blocks

Subtracting a constant skew matrix from a coefficient sample conjugates its
coarse response by the corresponding lower triangular shear.  This file proves
that covariance from the response functional and then records its adapted-cell
and annealed consequences.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- Congruence of a doubled block by the constant-skew shear. -/
@[expose]
def skewBlockCongr (g : Mat d) (A : BlockMat d) : BlockMat d :=
  ofFullBlockMat ((fullBlockShear g)ᴴ * toFullBlockMat A * fullBlockShear g)

/-- Flattening exposes constant-skew congruence as ordinary matrix
congruence. -/
theorem toFullBlockMat_skewBlockCongr (g : Mat d) (A : BlockMat d) :
    toFullBlockMat (skewBlockCongr g A) =
      (fullBlockShear g)ᴴ * toFullBlockMat A * fullBlockShear g := by
  rw [skewBlockCongr, toFullBlockMat_ofFullBlockMat]

/-- The shear sends `(x,y)` to `(x,gx+y)`. -/
theorem blockVector_skewShift (g : Mat d) (X : BlockVec d) :
    fullBlockShear g *ᵥ toFullBlockVec X =
      toFullBlockVec (X.1, matVecMul g X.1 + X.2) := by
  have hX : toFullBlockVec X = Sum.elim X.1 X.2 := by
    funext α
    cases α <;> rfl
  have hshift :
      toFullBlockVec (X.1, matVecMul g X.1 + X.2) =
        Sum.elim X.1 (matVecMul g X.1 + X.2) := by
    funext α
    cases α <;> rfl
  rw [hX, hshift]
  exact fullBlockShear_mulVec g X.1 X.2

/-- A skew congruence reads the original quadratic form at the shifted doubled
vector. -/
theorem blockQuadratic_skewBlockCongr (g : Mat d) (A : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (skewBlockCongr g A) X) =
      blockVecDot (X.1, matVecMul g X.1 + X.2)
        (blockMatVecMul A (X.1, matVecMul g X.1 + X.2)) := by
  rw [blockVecDot_blockMatVecMul_eq_dotProduct,
    blockVecDot_blockMatVecMul_eq_dotProduct,
    toFullBlockMat_skewBlockCongr, Initialization.quad_conj,
    blockVector_skewShift]

/-- Congruence preserves symmetry. -/
theorem isSymmetricBlockMat_skewBlockCongr {g : Mat d} {A : BlockMat d}
    (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (skewBlockCongr g A) := by
  refine isSymmetricBlockMat_of_isSymm ?_
  exact isSymm_of_isHermitian
    (Matrix.isHermitian_conjTranspose_mul_mul _
      (isHermitian_toFullBlockMat hA))

/-- Congruence by a shear preserves positive definiteness. -/
theorem blockPosDef_skewBlockCongr {g : Mat d} {A : BlockMat d}
    (hA : BlockPosDef A) : BlockPosDef (skewBlockCongr g A) := by
  intro X hX
  rw [blockQuadratic_skewBlockCongr]
  apply hA
  intro hshift
  have hfull : fullBlockShear g *ᵥ toFullBlockVec X = 0 := by
    rw [blockVector_skewShift]
    exact (toFullBlockVec_eq_zero_iff _).mpr hshift
  have hzero : toFullBlockVec X = 0 := by
    apply Matrix.mulVec_injective_of_isUnit (isUnit_fullBlockShear g)
    rw [Matrix.mulVec_zero]
    exact hfull
  exact hX ((toFullBlockVec_eq_zero_iff X).mp hzero)

private theorem vecDot_skew_self (g : Mat d) (hg : IsSkewMat g)
    (x : Vec d) : vecDot x (matVecMul g x) = 0 := by
  have hgstar : gᴴ = -g := by
    rwa [conjTranspose_eq_transpose']
  simpa [vecDot, matVecMul] using! dotProduct_mulVec_of_skew hgstar x

/-- The quadratic form of the recentered coarse response is the original
quadratic form at the shear-shifted doubled vector. -/
theorem blockQuadratic_coarseBlock_subSkew (U : Domain d)
    (a : CoeffSpace d) (g : Mat d) (hg : IsSkewMat g) (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) (a.subSkew g hg)) X) =
      blockVecDot (X.1, matVecMul g X.1 + X.2)
        (blockMatVecMul (coarseBlock (U : Set (Vec d)) a)
          (X.1, matVecMul g X.1 + X.2)) := by
  let p : Vec d := -X.1
  let q : Vec d := X.2
  have hresponse := responseJ_subSkew U a g hg p q
  rw [responseJ_eq_coarseBlock, responseJ_eq_coarseBlock] at hresponse
  have hload : q - matVecMul g p = matVecMul g X.1 + X.2 := by
    dsimp only [p, q]
    rw [matVecMul_neg]
    abel
  have hpair : vecDot p (q - matVecMul g p) = vecDot p q := by
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right,
      vecDot_skew_self g hg p, neg_zero, add_zero]
  rw [hpair, hload] at hresponse
  dsimp only [p, q] at hresponse
  simp only [neg_neg] at hresponse
  linarith only [hresponse]

/-- **Constant-skew covariance of the coarse response.** -/
theorem coarseBlock_subSkew (U : Domain d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    coarseBlock (U : Set (Vec d)) (a.subSkew g hg) =
      skewBlockCongr g (coarseBlock (U : Set (Vec d)) a) := by
  apply toFullBlockMat_injective
  apply le_antisymm
  · refine Initialization.le_of_dotProduct_mulVec_le
      (isHermitian_toFullBlockMat
        (isSymmetricBlockMat_coarseBlock _ (a.subSkew g hg)))
      (isHermitian_toFullBlockMat
        (isSymmetricBlockMat_skewBlockCongr
          (isSymmetricBlockMat_coarseBlock _ a))) fun x => ?_
    let X : BlockVec d := ofFullBlockVec x
    have hquad := blockQuadratic_coarseBlock_subSkew U a g hg X
    rw [blockVecDot_blockMatVecMul_eq_dotProduct,
      blockVecDot_blockMatVecMul_eq_dotProduct,
      toFullBlockVec_ofFullBlockVec] at hquad
    rw [toFullBlockMat_skewBlockCongr, Initialization.quad_conj,
      ← toFullBlockVec_ofFullBlockVec x, blockVector_skewShift]
    simpa only [X, toFullBlockVec_ofFullBlockVec] using hquad.le
  · refine Initialization.le_of_dotProduct_mulVec_le
      (isHermitian_toFullBlockMat
        (isSymmetricBlockMat_skewBlockCongr
          (isSymmetricBlockMat_coarseBlock _ a)))
      (isHermitian_toFullBlockMat
        (isSymmetricBlockMat_coarseBlock _ (a.subSkew g hg))) fun x => ?_
    let X : BlockVec d := ofFullBlockVec x
    have hquad := blockQuadratic_coarseBlock_subSkew U a g hg X
    rw [blockVecDot_blockMatVecMul_eq_dotProduct,
      blockVecDot_blockMatVecMul_eq_dotProduct,
      toFullBlockVec_ofFullBlockVec] at hquad
    rw [toFullBlockMat_skewBlockCongr, Initialization.quad_conj,
      ← toFullBlockVec_ofFullBlockVec x, blockVector_skewShift]
    simpa only [X, toFullBlockVec_ofFullBlockVec] using hquad.ge

/-- Constant-skew covariance on a translated adapted cell. -/
theorem adaptedResponse_subSkew {q : Mat d} (hq : q.PosDef)
    (k : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) :
    adaptedResponse q k w (a.subSkew g hg) =
      skewBlockCongr g (adaptedResponse q k w a) := by
  simpa only [adaptedResponse, adaptedDomainAt_carrier] using
    coarseBlock_subSkew (adaptedDomainAt hq k w) a g hg

/-- The expected recentered coarse response is the congruence of the annealed
block. -/
theorem integral_coarseBlock_subSkew
    {P : Measure (CoeffSpace d)} (U : Domain d)
    (hint : HasIntegrableCoarseBlock P (U : Set (Vec d)))
    (g : Mat d) (hg : IsSkewMat g) :
    (∫ a, toFullBlockMat (coarseBlock (U : Set (Vec d)) (a.subSkew g hg)) ∂P) =
      toFullBlockMat (skewBlockCongr g (annealedBlock P (U : Set (Vec d)))) := by
  simp_rw [coarseBlock_subSkew U]
  simp_rw [toFullBlockMat_skewBlockCongr]
  rw [integral_mul_left_mul_right _ _ (integrable_toFullBlockMat hint),
    ← toFullBlockMat_annealedBlock hint]

end

end HCPolySupport.HighContrast.Response
