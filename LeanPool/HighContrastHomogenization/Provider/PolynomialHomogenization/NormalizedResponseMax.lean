/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseCell
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedResponseExcess

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedResponseMax

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact normalized response maximum on adapted cells

Constant-skew removal, scalar normalization, and the exact affine pullback
compose with distinct transformed primal and dual loads.  The resulting
identity-reference cube response is controlled by the physical block excess
on the corresponding adapted cell.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

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
  have hc : 0 < c := by simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by simpa only [alpha] using Real.sqrt_pos.mpr hc
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
  · simp only [hqT, smul_smul,
      inv_mul_cancel₀ halpha.ne', one_smul, matVecMul_mul,
      Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
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
  have hc : 0 < c := by simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by simpa only [alpha] using Real.sqrt_pos.mpr hc
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
  · simp only [hqT, smul_smul,
      inv_mul_cancel₀ halpha.ne', one_smul, matVecMul_mul,
      Matrix.mul_nonsing_inv q hqdet, matVecMul_one]

private theorem symmPart_mul_normalizedPrimalCoordinate [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) (x : Vec d) :
    matVecMul (symmPart abar)
        (Real.sqrt (specBound (symmPart abar)⁻¹) •
          matVecMul (Selection.normalizedRoot (symmPart abar))⁻¹ x) =
      (Real.sqrt (specBound (symmPart abar)⁻¹))⁻¹ •
        matVecMul (Selection.normalizedRoot (symmPart abar)) x := by
  let S := symmPart abar
  let c := specBound S⁻¹
  let alpha := Real.sqrt c
  let q := Selection.normalizedRoot S
  have hc : 0 < c := by simpa only [c, S] using normalizedRootScale_pos hS
  have halpha : 0 < alpha := by simpa only [alpha] using Real.sqrt_pos.mpr hc
  have halphaSq : alpha * alpha = c := by
    simpa only [alpha] using Real.mul_self_sqrt hc.le
  have hq : q.PosDef := by
    simpa only [q, S] using normalizedRoot_posDef_of_posDef hS
  have hqdet : IsUnit q.det := isUnit_det_of_posDef hq
  have hsq : q * q = c • S := by
    simpa only [q, c, S] using normalizedRoot_mul_self hS
  have hcancel : matVecMul q (matVecMul q⁻¹ x) = x := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv q hqdet, matVecMul_one]
  have hbase :
      matVecMul q x = c • matVecMul S (matVecMul q⁻¹ x) := by
    calc
      matVecMul q x =
          matVecMul q (matVecMul q (matVecMul q⁻¹ x)) := by
        rw [hcancel]
      _ = matVecMul (q * q) (matVecMul q⁻¹ x) := by
        rw [matVecMul_mul]
      _ = c • matVecMul S (matVecMul q⁻¹ x) := by
        rw [hsq, smul_matVecMul]
  change matVecMul S (alpha • matVecMul q⁻¹ x) =
    alpha⁻¹ • matVecMul q x
  rw [matVecMul_smul]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [congrFun hbase i, ← halphaSq]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [halpha.ne']

private theorem symmPart_inv_mul_normalizedDualCoordinate [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef) (x : Vec d) :
    matVecMul (symmPart abar)⁻¹
        ((Real.sqrt (specBound (symmPart abar)⁻¹))⁻¹ •
          matVecMul (Selection.normalizedRoot (symmPart abar)) x) =
      Real.sqrt (specBound (symmPart abar)⁻¹) •
        matVecMul (Selection.normalizedRoot (symmPart abar))⁻¹ x := by
  have hSdet : IsUnit (symmPart abar).det := isUnit_det_of_posDef hS
  apply Matrix.mulVec_injective_of_isUnit hS.isUnit
  calc
    matVecMul (symmPart abar)
        (matVecMul (symmPart abar)⁻¹
          ((Real.sqrt (specBound (symmPart abar)⁻¹))⁻¹ •
            matVecMul (Selection.normalizedRoot (symmPart abar)) x)) =
      (Real.sqrt (specBound (symmPart abar)⁻¹))⁻¹ •
        matVecMul (Selection.normalizedRoot (symmPart abar)) x := by
          rw [matVecMul_mul,
            Matrix.mul_nonsing_inv (symmPart abar) hSdet, matVecMul_one]
    _ = matVecMul (symmPart abar)
        (Real.sqrt (specBound (symmPart abar)⁻¹) •
          matVecMul (Selection.normalizedRoot (symmPart abar))⁻¹ x) :=
      (symmPart_mul_normalizedPrimalCoordinate hS x).symm

private theorem blockMatVecMul_blockMatrixOfCoeff_shift
    (abar : Mat d) (p z : Vec d) :
    blockMatVecMul (blockMatrixOfCoeff abar)
        (p, z + matVecMul (skewPart abar) p) =
      (matVecMul (symmPart abar) p +
          matVecMul (skewPart abar) (matVecMul (symmPart abar)⁻¹ z),
        matVecMul (symmPart abar)⁻¹ z) := by
  have htranspose : matTranspose (skewPart abar) = -skewPart abar :=
    matTranspose_skewPart abar
  have hupperLeft :
      symmPart abar + matTranspose (skewPart abar) *
          (symmPart abar)⁻¹ * skewPart abar =
        symmPart abar - skewPart abar * (symmPart abar)⁻¹ *
          skewPart abar := by
    rw [htranspose]
    noncomm_ring
  have hupperRight :
      -(matTranspose (skewPart abar) * (symmPart abar)⁻¹) =
        skewPart abar * (symmPart abar)⁻¹ := by
    rw [htranspose]
    noncomm_ring
  rw [Prod.mk.injEq]
  constructor
  · simp only [blockMatVecMul, blockMatrixOfCoeff]
    rw [hupperLeft, hupperRight]
    simp only [sub_matVecMul, matVecMul_add, matVecMul_mul]
    abel
  · simp only [blockMatVecMul, blockMatrixOfCoeff, matVecMul_add,
      matVecMul_mul, neg_matVecMul]
    abel

private theorem blockMatVecMul_constantBlockMatrix_physicalNormalizedPrimalLoad
    [NeZero d] {abar : Mat d} (hS : (symmPart abar).PosDef)
    (X : BlockVec d) :
    blockMatVecMul (Book.Ch02.constantBlockMatrix abar)
        (physicalNormalizedPrimalLoad abar X) =
      physicalNormalizedDualLoad abar X := by
  rcases X with ⟨x, y⟩
  simp only [physicalNormalizedPrimalLoad, physicalNormalizedDualLoad]
  rw [show Book.Ch02.constantBlockMatrix abar = blockMatrixOfCoeff abar by
    simp [Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff]]
  rw [blockMatVecMul_blockMatrixOfCoeff_shift]
  rw [symmPart_mul_normalizedPrimalCoordinate hS x,
    symmPart_inv_mul_normalizedDualCoordinate hS y]

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

/-- The identity-reference normalized response on an aligned cube is bounded
by the physical block excess on its exact adapted-cell image. -/
theorem normalizedBlockResponseMax_le_adaptedCell_blockExcess [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (t k : ℤ) (w : Fin d → ℤ) (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField) :
    Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) aRef (1 : Mat d) ≤
      blockExcess
        (Book.Ch02.coarseBlockMatrix
          (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)
          (a.coeffOn
            (Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w)))
        (Book.Ch02.constantBlockMatrix abar) := by
  let R := translateCube w (originCube d k)
  let U := Response.adaptedDomainAt (normalizedRoot_posDef_of_posDef hS) k w
  unfold Book.Ch02.normalizedBlockResponseMax
  refine csSup_le (Book.Ch02.normalizedBlockResponseValueSet_nonempty R aRef 1) ?_
  rintro m ⟨e, he, rfl⟩
  let X := ofFullBlockVec e
  let P := physicalNormalizedPrimalLoad abar X
  let Q := physicalNormalizedDualLoad abar X
  have hloadInv :
      ofFullBlockVec
          (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixInvSqrt (1 : Mat d)) e) = X := by
    simp only [Book.Ch02.constantFullBlockMatrixInvSqrt,
      constantFullBlockMatrixSqrt_one, inv_one, Matrix.one_mulVec, X]
  have hloadSqrt :
      ofFullBlockVec
          (Matrix.mulVec (Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d)) e) = X := by
    simp only [constantFullBlockMatrixSqrt_one, Matrix.one_mulVec, X]
  have hprimal := normalizedReferencePrimalLoad_physicalNormalizedPrimalLoad hS X
  have hdual := normalizedReferenceDualLoad_physicalNormalizedDualLoad hS X
  have hblock :=
    blockMatVecMul_constantBlockMatrix_physicalNormalizedPrimalLoad hS X
  have hquad : blockVecDot P
      (blockMatVecMul (Book.Ch02.constantBlockMatrix abar) P) = 1 := by
    rw [show blockMatVecMul (Book.Ch02.constantBlockMatrix abar) P = Q by
      simpa only [P, Q] using hblock]
    calc
      blockVecDot P Q = blockVecDot
          (normalizedReferencePrimalLoad abar P)
          (normalizedReferenceDualLoad abar Q) :=
        (blockVecDot_normalizedReferenceLoads hS P Q).symm
      _ = blockVecDot X X := by rw [hprimal, hdual]
      _ = Book.Ch02.fullBlockVecNormSq e := by
        simpa only [X] using! blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq e
      _ = 1 := he
  rw [hloadInv, hloadSqrt]
  calc
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain R) (aRef.coeffOn R) X X =
        Book.Ch02.doubledResponseJ U (a.coeffOn U) P Q := by
      have hcov :=
        doubledResponseJ_normalizedReferenceCell a abar hS t k w aRef haRef P Q
      rw [hprimal, hdual] at hcov
      simpa only [R, U, P, Q] using
        hcov
    _ = Book.Ch02.doubledResponseJ U (a.coeffOn U) P
        (blockMatVecMul (Book.Ch02.constantBlockMatrix abar) P) := by
      rw [show blockMatVecMul (Book.Ch02.constantBlockMatrix abar) P = Q by
        simpa only [P, Q] using hblock]
    _ ≤ blockExcess (Book.Ch02.coarseBlockMatrix U (a.coeffOn U))
        (Book.Ch02.constantBlockMatrix abar) :=
      doubledResponseJ_le_blockExcess_of_constantBlockQuadratic_eq_one
        (a.coeffOn U) hS P hquad

end

end HighContrast
end HCPolySupport
