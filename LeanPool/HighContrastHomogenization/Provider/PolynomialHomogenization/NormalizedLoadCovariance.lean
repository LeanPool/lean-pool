/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewResponse
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormState
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DeterministicIdentities
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SubadditivityScaling

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedLoadCovariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Covariance of normalized response loads

The primal and dual loads transform differently under constant-skew removal,
positive scalar normalization, and affine pullback.  These load maps preserve
the doubled pairing and the first two coefficient changes preserve the doubled
response.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Primal load after subtracting a constant skew matrix. -/
@[expose]
def skewCenteredPrimalLoad (g : Mat d) (P : BlockVec d) : BlockVec d :=
  (P.1, P.2 - matVecMul g P.1)

/-- Dual load after subtracting a constant skew matrix. -/
@[expose]
def skewCenteredDualLoad (g : Mat d) (Q : BlockVec d) : BlockVec d :=
  (Q.1 - matVecMul g Q.2, Q.2)

/-- Primal load after multiplying the coefficient by a positive scalar. -/
@[expose]
def scalarNormalizedPrimalLoad (alpha : ℝ) (P : BlockVec d) : BlockVec d :=
  (alpha⁻¹ • P.1, alpha • P.2)

/-- Dual load after multiplying the coefficient by a positive scalar. -/
@[expose]
def scalarNormalizedDualLoad (alpha : ℝ) (Q : BlockVec d) : BlockVec d :=
  (alpha • Q.1, alpha⁻¹ • Q.2)

/-- Primal load under the affine pullback `x = q y`. -/
@[expose]
def affineReferencePrimalLoad (q : Mat d) (P : BlockVec d) : BlockVec d :=
  (matVecMul (matTranspose q) P.1, matVecMul q⁻¹ P.2)

/-- Dual load under the affine pullback `x = q y`. -/
@[expose]
def affineReferenceDualLoad (q : Mat d) (Q : BlockVec d) : BlockVec d :=
  (matVecMul q⁻¹ Q.1, matVecMul (matTranspose q) Q.2)

/-- The physical-to-reference primal load for exact normalization at `abar`. -/
@[expose]
def normalizedReferencePrimalLoad
    (abar : Mat d) (P : BlockVec d) : BlockVec d :=
  let S := symmPart abar
  let g := skewPart abar
  let alpha := Real.sqrt (specBound S⁻¹)
  let q := Selection.normalizedRoot S
  affineReferencePrimalLoad q
    (scalarNormalizedPrimalLoad alpha (skewCenteredPrimalLoad g P))

/-- The physical-to-reference dual load for exact normalization at `abar`. -/
@[expose]
def normalizedReferenceDualLoad
    (abar : Mat d) (Q : BlockVec d) : BlockVec d :=
  let S := symmPart abar
  let g := skewPart abar
  let alpha := Real.sqrt (specBound S⁻¹)
  let q := Selection.normalizedRoot S
  affineReferenceDualLoad q
    (scalarNormalizedDualLoad alpha (skewCenteredDualLoad g Q))

private theorem vecDot_skew_mulVec_swap (g : Mat d) (hg : IsSkewMat g)
    (x y : Vec d) :
    vecDot x (matVecMul g y) = -vecDot (matVecMul g x) y := by
  have htranspose : Matrix.transpose g = -g := hg
  calc
    vecDot x (matVecMul g y) =
        vecDot (matVecMul (Matrix.transpose g) x) y := by
      simpa [matTranspose] using
        vecDot_matVecMul_transpose x y (Matrix.transpose g)
    _ = -vecDot (matVecMul g x) y := by
      rw [htranspose]
      change dotProduct (Matrix.mulVec (-g) x) y =
        -dotProduct (Matrix.mulVec g x) y
      rw [Matrix.neg_mulVec, neg_dotProduct]

/-- Removing a constant skew matrix preserves the doubled response when the
primal and dual loads are recentered separately. -/
theorem doubledResponseJ_subSkew
    {U : Book.Ch02.Domain d} (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ U ((a.subSkew g hg).coeffOn U)
        (skewCenteredPrimalLoad g P) (skewCenteredDualLoad g Q) =
      Book.Ch02.doubledResponseJ U (a.coeffOn U) P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  have hcenterTranspose :=
    CoeffSpace.coeffOn_transpose_aeeq (a.subSkew g hg) U
  have haTranspose := CoeffSpace.coeffOn_transpose_aeeq a U
  have hadjoint (x y : Vec d) :
      Book.Ch02.responseJ U (((a.subSkew g hg).coeffOn U).transpose) x y =
        Book.Ch02.responseJ U ((a.coeffOn U).transpose) x
          (y + matVecMul g x) := by
    calc
      Book.Ch02.responseJ U (((a.subSkew g hg).coeffOn U).transpose) x y =
          Book.Ch02.responseJ U
            ((a.subSkew g hg).transpose.coeffOn U) x y :=
        Book.Ch02.responseJ_eq_ofAEEq hcenterTranspose.symm x y
      _ = Book.Ch02.responseJ U
          ((a.transpose.subSkew (-g) (Response.isSkewMat_neg hg)).coeffOn U) x y := by
        rw [CoeffSpace.transpose_subSkew]
      _ = Book.Ch02.responseJ U (a.transpose.coeffOn U) x
          (y - matVecMul (-g) x) :=
        Response.responseJ_subSkew U a.transpose (-g) (Response.isSkewMat_neg hg) x y
      _ = Book.Ch02.responseJ U (a.transpose.coeffOn U) x
          (y + matVecMul g x) := by
        have hneg : matVecMul (-g) x = -matVecMul g x := by
          ext i
          simp [matVecMul]
        rw [hneg]
        congr 2
        abel
      _ = Book.Ch02.responseJ U ((a.coeffOn U).transpose) x
          (y + matVecMul g x) :=
        Book.Ch02.responseJ_eq_ofAEEq haTranspose x _
  rw [Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum,
    Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  rw [Response.responseJ_subSkew, hadjoint]
  simp only [skewCenteredPrimalLoad, skewCenteredDualLoad]
  congr 1
  · congr 2
    ext i
    simp only [Pi.sub_apply, matVecMul]
    have hsum :
        (∑ x, g i x * (p x - pStar x)) =
          (∑ x, g i x * p x) - ∑ x, g i x * pStar x := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    ring
  · congr 2
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, matVecMul]
    have hsum :
        (∑ x, g i x * (pStar x + p x)) =
          (∑ x, g i x * pStar x) + ∑ x, g i x * p x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    ring

private theorem transpose_AEScaled {c : ℝ} {U : Book.Ch02.Domain d}
    {a b : Book.Ch02.CoeffOn U} (h : Book.Ch02.CoeffOn.AEScaled c a b) :
    Book.Ch02.CoeffOn.AEScaled c a.transpose b.transpose := by
  exact h.mono fun x hx => by
    simp only [Book.Ch02.CoeffOn.transpose_apply, hx, matTranspose]
    exact Matrix.transpose_smul c (a.toCoeffField x)

/-- Positive scalar normalization preserves the doubled response when the
primal and dual loads carry reciprocal square-root factors. -/
theorem doubledResponseJ_positiveScale
    (c : ℝ) (hc : 0 < c) (a : CoeffSpace d)
    (U : Book.Ch02.Domain d) (P Q : BlockVec d) :
    Book.Ch02.doubledResponseJ U ((a.positiveScale c hc).coeffOn U)
        (scalarNormalizedPrimalLoad (Real.sqrt c) P)
        (scalarNormalizedDualLoad (Real.sqrt c) Q) =
      Book.Ch02.doubledResponseJ U (a.coeffOn U) P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  let alpha := Real.sqrt c
  have halpha : 0 < alpha := Real.sqrt_pos.mpr hc
  have hscale := CoeffSpace.coeffOn_positiveScale_AEScaled c hc a U
  have hscaleT := transpose_AEScaled hscale
  have hprimal :=
    (Book.Ch02.responseSubadditivityAndScalingTheory U (a.coeffOn U)).responseJ_homogeneous
      hc hscale
  have hadjoint :=
    (Book.Ch02.responseSubadditivityAndScalingTheory U (a.coeffOn
      U).transpose).responseJ_homogeneous
      hc hscaleT
  rw [Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum,
    Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum]
  rw [hprimal, hadjoint]
  simp only [scalarNormalizedPrimalLoad, scalarNormalizedDualLoad]
  congr 1
  · congr 2
    · ext i
      dsimp [alpha]
      field_simp [halpha.ne']
    · ext i
      dsimp [alpha]
      field_simp [halpha.ne']
  · congr 2
    · ext i
      dsimp [alpha]
      field_simp [halpha.ne']
    · ext i
      dsimp [alpha]
      field_simp [halpha.ne']

private theorem blockVecDot_skewCenteredLoads
    (g : Mat d) (hg : IsSkewMat g) (P Q : BlockVec d) :
    blockVecDot (skewCenteredPrimalLoad g P) (skewCenteredDualLoad g Q) =
      blockVecDot P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  simp only [skewCenteredPrimalLoad, skewCenteredDualLoad, blockVecDot]
  rw [vecDot_sub_right, vecDot_sub_left,
    vecDot_skew_mulVec_swap g hg p pStar]
  ring

private theorem blockVecDot_scalarNormalizedLoads
    {alpha : ℝ} (halpha : 0 < alpha) (P Q : BlockVec d) :
    blockVecDot (scalarNormalizedPrimalLoad alpha P)
        (scalarNormalizedDualLoad alpha Q) = blockVecDot P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  simp only [scalarNormalizedPrimalLoad, scalarNormalizedDualLoad, blockVecDot,
    vecDot_smul_left, vecDot_smul_right]
  field_simp [halpha.ne']

private theorem blockVecDot_affineReferenceLoads
    {q : Mat d} (hq : q.PosDef) (P Q : BlockVec d) :
    blockVecDot (affineReferencePrimalLoad q P)
        (affineReferenceDualLoad q Q) = blockVecDot P Q := by
  rcases P with ⟨p, r⟩
  rcases Q with ⟨rStar, pStar⟩
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hleft :
      vecDot (matVecMul (matTranspose q) p) (matVecMul q⁻¹ rStar) =
        vecDot p rStar := by
    calc
      vecDot (matVecMul (matTranspose q) p) (matVecMul q⁻¹ rStar) =
          vecDot (matVecMul q⁻¹ rStar) (matVecMul (matTranspose q) p) :=
        vecDot_comm _ _
      _ = vecDot (matVecMul q (matVecMul q⁻¹ rStar)) p :=
        vecDot_matVecMul_transpose _ _ q
      _ = vecDot rStar p := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
      _ = vecDot p rStar := vecDot_comm _ _
  have hright :
      vecDot (matVecMul q⁻¹ r) (matVecMul (matTranspose q) pStar) =
        vecDot r pStar := by
    calc
      vecDot (matVecMul q⁻¹ r) (matVecMul (matTranspose q) pStar) =
          vecDot (matVecMul q (matVecMul q⁻¹ r)) pStar :=
        vecDot_matVecMul_transpose _ _ q
      _ = vecDot r pStar := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
  simp only [affineReferencePrimalLoad, affineReferenceDualLoad, blockVecDot,
    hleft, hright]

/-- The distinct normalized primal and dual load maps preserve their doubled
pairing. -/
theorem blockVecDot_normalizedReferenceLoads [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) (P Q : BlockVec d) :
    blockVecDot (normalizedReferencePrimalLoad abar P)
        (normalizedReferenceDualLoad abar Q) = blockVecDot P Q := by
  let S := symmPart abar
  let g := skewPart abar
  let c := specBound S⁻¹
  let alpha := Real.sqrt c
  let q := Selection.normalizedRoot S
  have hc : 0 < c := by simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by simpa only [alpha] using Real.sqrt_pos.mpr hc
  have hq : q.PosDef := by
    simpa only [q, S] using normalizedRoot_posDef_of_posDef hS
  change blockVecDot
      (affineReferencePrimalLoad q
        (scalarNormalizedPrimalLoad alpha (skewCenteredPrimalLoad g P)))
      (affineReferenceDualLoad q
        (scalarNormalizedDualLoad alpha (skewCenteredDualLoad g Q))) = _
  rw [blockVecDot_affineReferenceLoads hq,
    blockVecDot_scalarNormalizedLoads halpha,
    blockVecDot_skewCenteredLoads g (matTranspose_skewPart abar)]

end

end HighContrast
end HCPolySupport
