/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentQuadratic

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentEnergyMap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The energy map for a recent optimizer difference

On a recent child the local optimizer and the restricted parent optimizer are
solutions for one coefficient representative.  Their doubled difference is
therefore a response field, so the coarse energy-map estimate applies to its
cell average.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The metric square of the averaged optimizer difference on one child is
controlled by the child's response size and the actual difference energy. -/
theorem metricBlockNormSq_recent_difference_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    metricBlockNormSq m
        (blockCellAverage (adaptedCellAt q k w) (fun x =>
          diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x)) ≤
      diagonalWeakMetricFactor m E ^ 2 *
        blockSize (adaptedResponse q k w a) E *
          Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
            blockVecDot
              (diagonalWeakChildState hq k w a p r x -
                diagonalWeakState hq t a p r x)
              (blockMatVecMul
                (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
                (diagonalWeakChildState hq k w a p r x -
                  diagonalWeakState hq t a p r x))) := by
  obtain ⟨f, hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ :=
    hfamily (adaptedDomainAt hq k w)
  obtain ⟨u, hu⟩ := exists_diagonalWeakOptimizer_restrict_child
    hq hkt hw a p r
  let v := diagonalWeakChildOptimizer hq k w a p r
  let vc : Solution (adaptedDomainAt hq k w) c := Solution.ofAEEq hca v
  let uc : Solution (adaptedDomainAt hq k w) c := Solution.ofAEEq hca u
  let Y : DoubledField d :=
    { potential := fun x => vc.toH1.grad x - uc.toH1.grad x
      flux := fun x => matVecMul (c.toCoeffField x) (vc.toH1.grad x) -
        matVecMul (c.toCoeffField x) (uc.toH1.grad x) }
  have hEllC : IsEllipticFieldOn c.lam c.Lam (adaptedCellAt q k w)
      c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hY : IsDoubledResponseField (adaptedDomainAt hq k w) c Y :=
    isDoubledResponseField_grad_sub hEllC vc uc
  have hcblock : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
      adaptedResponse q k w a := by
    calc
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
          Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w)
            (a.coeffOn (adaptedDomainAt hq k w)) :=
        (Book.Ch02.coarseBlockMatrix_eq_ofAEEq hca).symm
      _ = coarseBlock (adaptedCellAt q k w) a :=
        (coarseBlock_eq_coarseBlockMatrix a (adaptedDomainAt hq k w)).symm
      _ = adaptedResponse q k w a := rfl
  have hpot : Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.potential =
      (blockCellAverage (adaptedCellAt q k w) (fun x =>
        diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)).1 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards with x
    change v.toH1.grad x - u.toH1.grad x =
      v.toH1.grad x - (diagonalWeakOptimizer hq t a p r).toH1.grad x
    rw [hu]
  have hflux : Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.flux =
      (blockCellAverage (adaptedCellAt q k w) (fun x =>
        diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)).2 := by
    apply Book.Ch02.averageVec_eq_of_ae_eq
    filter_upwards [ae_restrict_of_ae hae] with x hx
    change matVecMul (c.toCoeffField x) (v.toH1.grad x) -
        matVecMul (c.toCoeffField x) (u.toH1.grad x) =
      matVecMul ((⇑a.1 : CoeffField d) x) (v.toH1.grad x) -
        matVecMul ((⇑a.1 : CoeffField d) x)
          ((diagonalWeakOptimizer hq t a p r).toH1.grad x)
    rw [hcf, hx, hu]
  have henergy :
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockMatrixField c x) (Y.eval x))) =
      Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
        blockVecDot
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x)
          (blockMatVecMul
            (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
            (diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) := by
    apply Book.Ch02.average_eq_of_ae_eq
    filter_upwards [ae_restrict_of_ae hae] with x hx
    change blockVecDot
        ((v.toH1.grad x - u.toH1.grad x,
          matVecMul (c.toCoeffField x) (v.toH1.grad x) -
            matVecMul (c.toCoeffField x) (u.toH1.grad x)) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff (c.toCoeffField x))
          ((v.toH1.grad x - u.toH1.grad x,
            matVecMul (c.toCoeffField x) (v.toH1.grad x) -
              matVecMul (c.toCoeffField x) (u.toH1.grad x)) : BlockVec d)) = _
    rw [hcf, hx, hu, diagonalWeakChildState_eq, diagonalWeakState_eq]
    simp only [CoeffSpace.coeffOn_toCoeffField]
    rw [hx]
    rfl
  have hmap := metricBlockNormSq_average_le_adaptedCellAt hq k w
    hcblock hEllC hY hm hE hEpd
  rw [hpot, hflux, henergy] at hmap
  exact hmap

end

end Response
end HighContrast
end HCPolySupport
