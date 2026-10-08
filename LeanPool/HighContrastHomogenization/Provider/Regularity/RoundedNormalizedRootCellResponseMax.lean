/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseCell
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# High-contrast homogenization: Provider.Regularity.RoundedNormalizedRootCellResponseMax

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Normalized-root cell responses below the reference response maximum

A unit doubled load on the identity reference cube has physical inverse
loads that are independent of the cell.  Exact normalized-response covariance
then bounds every corresponding normalized-root cell response by the canonical
one-cube response maximum.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

private def physicalNormalizedPrimalLoad
    (abar : Mat d) (X : BlockVec d) : BlockVec d :=
  let S := symmPart abar
  let g := skewPart abar
  let alpha := Real.sqrt (specBound S⁻¹)
  let q := Selection.normalizedRoot S
  let p := alpha • matVecMul q⁻¹ X.1
  (p, alpha⁻¹ • matVecMul q X.2 + matVecMul g p)

private def physicalNormalizedDualLoad
    (abar : Mat d) (X : BlockVec d) : BlockVec d :=
  let S := symmPart abar
  let g := skewPart abar
  let alpha := Real.sqrt (specBound S⁻¹)
  let q := Selection.normalizedRoot S
  let pStar := alpha • matVecMul q⁻¹ X.2
  (alpha⁻¹ • matVecMul q X.1 + matVecMul g pStar, pStar)

private theorem normalizedRoot_transpose_eq [NeZero d]
    {m : Mat d} (hm : m.PosDef) :
    matTranspose (Selection.normalizedRoot m) = Selection.normalizedRoot m := by
  have hq := normalizedRoot_posDef_of_posDef hm
  simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
    hq.isHermitian

private theorem normalizedReferencePrimalLoad_physicalNormalizedPrimalLoad
    [NeZero d] {abar : Mat d} (hS : (symmPart abar).PosDef)
    (X : BlockVec d) :
    normalizedReferencePrimalLoad abar (physicalNormalizedPrimalLoad abar X) = X := by
  rcases X with ⟨x, y⟩
  let S := symmPart abar
  let g := skewPart abar
  let c := specBound S⁻¹
  let alpha := Real.sqrt c
  let q := Selection.normalizedRoot S
  have hc : 0 < c := by
    simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by
    simpa only [alpha] using Real.sqrt_pos.mpr hc
  have hq : q.PosDef := by
    simpa only [q, S] using normalizedRoot_posDef_of_posDef hS
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqT : matTranspose q = q := by
    simpa only [q, S] using normalizedRoot_transpose_eq hS
  change
    (matVecMul (matTranspose q)
        (alpha⁻¹ • (alpha • matVecMul q⁻¹ x)),
      matVecMul q⁻¹
        (alpha • ((alpha⁻¹ • matVecMul q y +
          matVecMul g (alpha • matVecMul q⁻¹ x)) -
          matVecMul g (alpha • matVecMul q⁻¹ x)))) = (x, y)
  rw [Prod.mk.injEq]
  constructor
  · simp only [hqT, smul_smul, inv_mul_cancel₀ halpha.ne', one_smul,
      matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
  · simp only [add_sub_cancel_right, matVecMul_smul, smul_smul,
      mul_inv_cancel₀ halpha.ne', one_smul, matVecMul_mul,
      Matrix.nonsing_inv_mul q hqdet, matVecMul_one]

private theorem normalizedReferenceDualLoad_physicalNormalizedDualLoad
    [NeZero d] {abar : Mat d} (hS : (symmPart abar).PosDef)
    (X : BlockVec d) :
    normalizedReferenceDualLoad abar (physicalNormalizedDualLoad abar X) = X := by
  rcases X with ⟨x, y⟩
  let S := symmPart abar
  let g := skewPart abar
  let c := specBound S⁻¹
  let alpha := Real.sqrt c
  let q := Selection.normalizedRoot S
  have hc : 0 < c := by
    simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by
    simpa only [alpha] using Real.sqrt_pos.mpr hc
  have hq : q.PosDef := by
    simpa only [q, S] using normalizedRoot_posDef_of_posDef hS
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hqT : matTranspose q = q := by
    simpa only [q, S] using normalizedRoot_transpose_eq hS
  change
    (matVecMul q⁻¹
        (alpha • ((alpha⁻¹ • matVecMul q x +
          matVecMul g (alpha • matVecMul q⁻¹ y)) -
          matVecMul g (alpha • matVecMul q⁻¹ y))),
      matVecMul (matTranspose q)
        (alpha⁻¹ • (alpha • matVecMul q⁻¹ y))) = (x, y)
  rw [Prod.mk.injEq]
  constructor
  · simp only [add_sub_cancel_right, matVecMul_smul, smul_smul,
      mul_inv_cancel₀ halpha.ne', one_smul, matVecMul_mul,
      Matrix.nonsing_inv_mul q hqdet, matVecMul_one]
  · simp only [hqT, smul_smul, inv_mul_cancel₀ halpha.ne', one_smul,
      matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]

private theorem constantFullBlockMatrixSqrt_one :
    Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d) = 1 := by
  have hone : (1 : Mat d) = scalarMatrix (d := d) 1 := by
    ext i j
    simp [scalarMatrix, Matrix.one_apply]
  have hblock : Book.Ch02.constantBlockMatrix (1 : Mat d) =
      Book.Ch02.blockIdentity d := by
    rw [hone, Book.Ch02.constantBlockMatrix_scalarMatrix one_pos]
    apply blockMat_ext <;>
      simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, scalarMatrix]
  unfold Book.Ch02.constantFullBlockMatrixSqrt
  rw [show Book.Ch02.constantFullBlockMatrix (1 : Mat d) = 1 by
    unfold Book.Ch02.constantFullBlockMatrix
    rw [hblock]
    exact toFullBlockMat_blockIdentity]
  exact CFC.sqrt_one

/-- A unit identity-reference load has one pair of inverse physical loads,
independent of the cell, whose response on every exact normalized-root cell
is bounded by that reference cell's canonical normalized-response maximum. -/
theorem exists_normalizedRootCell_doubledResponseJ_le_normalizedBlockResponseMax
    [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (e : FullBlockVec d) (he : Book.Ch02.fullBlockVecNormSq e = 1) :
    ∃ P Q : BlockVec d,
      normalizedReferencePrimalLoad abar P = ofFullBlockVec e ∧
      normalizedReferenceDualLoad abar Q = ofFullBlockVec e ∧
      ∀ (k : ℤ) (w : Fin d → ℤ),
        Book.Ch02.doubledResponseJ
            (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
            (a.coeffOn
              (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)) P Q ≤
          Book.Ch02.normalizedBlockResponseMax
            (translateCube w (originCube d k)) aRef (1 : Mat d) := by
  let X : BlockVec d := ofFullBlockVec e
  let P : BlockVec d := physicalNormalizedPrimalLoad abar X
  let Q : BlockVec d := physicalNormalizedDualLoad abar X
  have hP : normalizedReferencePrimalLoad abar P = X := by
    simpa only [P] using
      normalizedReferencePrimalLoad_physicalNormalizedPrimalLoad hS X
  have hQ : normalizedReferenceDualLoad abar Q = X := by
    simpa only [Q] using
      normalizedReferenceDualLoad_physicalNormalizedDualLoad hS X
  refine ⟨P, Q, hP, hQ, ?_⟩
  intro k w
  let R : TriadicCube d := translateCube w (originCube d k)
  have hcov := doubledResponseJ_normalizedReferenceCell
    a abar hS t k w aRef haRef P Q
  rw [hP, hQ] at hcov
  have hloadInv :
      ofFullBlockVec
          (Matrix.mulVec
            (Book.Ch02.constantFullBlockMatrixInvSqrt (1 : Mat d)) e) = X := by
    simp only [Book.Ch02.constantFullBlockMatrixInvSqrt,
      constantFullBlockMatrixSqrt_one, inv_one, Matrix.one_mulVec, X]
  have hloadSqrt :
      ofFullBlockVec
          (Matrix.mulVec
            (Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d)) e) = X := by
    simp only [constantFullBlockMatrixSqrt_one, Matrix.one_mulVec, X]
  have hmem :
      Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
          (aRef.coeffOn R) X X ∈
        Book.Ch02.normalizedBlockResponseValueSet R aRef (1 : Mat d) := by
    refine ⟨e, he, ?_⟩
    rw [hloadInv, hloadSqrt]
  have hRself : R ∈ descendantsAtScale R R.scale := by
    simp only [descendantsAtScale_self, Finset.mem_singleton]
  have hbdd : BddAbove
      (Book.Ch02.normalizedBlockResponseValueSet R aRef (1 : Mat d)) :=
    Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      aRef (1 : Mat d) hRself
  calc
    Book.Ch02.doubledResponseJ
        (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
        (a.coeffOn
          (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)) P Q =
        Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R)
          (aRef.coeffOn R) X X := by
            simpa only [R] using hcov.symm
    _ ≤ Book.Ch02.normalizedBlockResponseMax R aRef (1 : Mat d) := by
      unfold Book.Ch02.normalizedBlockResponseMax
      exact le_csSup hbdd hmem

end

end HighContrast
end HCPolySupport
