/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormOld

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentState

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local optimizers on the recent child cells

The recent-scale decomposition inserts the canonical optimizer on each
aligned child.  Its doubled state uses the same coefficient sample as the
parent state and has the coarse-response average prescribed by the child
block.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ} {q : Mat d}

/-- The canonical optimizer `v(U_k(z),p,r;a)` on an aligned child cell. -/
@[expose]
def diagonalWeakChildOptimizer (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    Solution (adaptedDomainAt hq k w) (a.coeffOn (adaptedDomainAt hq k w)) :=
  (canonicalMaximizer
    (responseExistenceTheory (adaptedDomainAt hq k w)
      (a.coeffOn (adaptedDomainAt hq k w))) p r).toSolution

/-- The child optimizer realizes the response functional at the printed
load. -/
theorem diagonalWeakChildOptimizer_isMaximizer (hq : q.PosDef) (k : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) (p r : Vec d) :
    Book.Ch02.IsResponseMaximizer (adaptedDomainAt hq k w)
      (a.coeffOn (adaptedDomainAt hq k w)) p r
      (diagonalWeakChildOptimizer hq k w a p r) :=
  (canonicalMaximizer
    (responseExistenceTheory (adaptedDomainAt hq k w)
      (a.coeffOn (adaptedDomainAt hq k w))) p r).isMaximizer

/-- The doubled child-optimizer state `X(U_k(z))`. -/
@[expose]
def diagonalWeakChildState (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (p r : Vec d) : Vec d → BlockVec d :=
  fun x =>
    ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x,
      matVecMul ((a.coeffOn (adaptedDomainAt hq k w)).toCoeffField x)
        ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x))

/-- Defining equation of the doubled child state. -/
theorem diagonalWeakChildState_eq (hq : q.PosDef) (k : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) (p r : Vec d) (x : Vec d) :
    diagonalWeakChildState hq k w a p r x =
      ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x,
        matVecMul ((a.coeffOn (adaptedDomainAt hq k w)).toCoeffField x)
          ((diagonalWeakChildOptimizer hq k w a p r).toH1.grad x)) := rfl

/-- The child-state average is the average-gradient/average-flux pair of its
optimizer. -/
theorem blockCellAverage_diagonalWeakChildState (hq : q.PosDef) (k : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) (p r : Vec d) :
    blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakChildState hq k w a p r) =
      ((averageGradient (adaptedDomainAt hq k w)
          (a.coeffOn (adaptedDomainAt hq k w))
          (diagonalWeakChildOptimizer hq k w a p r),
        averageFlux (adaptedDomainAt hq k w)
          (a.coeffOn (adaptedDomainAt hq k w))
          (diagonalWeakChildOptimizer hq k w a p r)) : BlockVec d) :=
  blockCellAverage_gradFlux (adaptedDomainAt hq k w)
    (a.coeffOn (adaptedDomainAt hq k w))
    (diagonalWeakChildOptimizer hq k w a p r)

/-- The child average is `(R A_k(z)+I)(-p,r)`. -/
theorem blockCellAverage_diagonalWeakChildState_eq_response [NeZero d]
    (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakChildState hq k w a p r) =
      blockMatVecMul (blockR d)
          (blockMatVecMul (adaptedResponse q k w a)
            ((-p, r) : BlockVec d)) +
        ((-p, r) : BlockVec d) := by
  rw [blockCellAverage_diagonalWeakChildState]
  exact blockAverage_adaptedCellAt hq k w
    (coarseBlock_eq_coarseBlockMatrix a (adaptedDomainAt hq k w)).symm
    (diagonalWeakChildOptimizer_isMaximizer hq k w a p r)

/-- The parent optimizer restricts to a solution on each aligned child, with
exactly the same gradient after transport through a shared pointwise
coefficient representative. -/
theorem exists_diagonalWeakOptimizer_restrict_child [NeZero d]
    (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t) (a : CoeffSpace d) (p r : Vec d) :
    ∃ u : Solution (adaptedDomainAt hq k w)
        (a.coeffOn (adaptedDomainAt hq k w)),
      u.toH1.grad = (diagonalWeakOptimizer hq t a p r).toH1.grad := by
  obtain ⟨_f, _hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨bParent, _bParentLam, _bParentLamUpper, hbParentField, _hbParentLam,
      _hbParentLamUpper, _hbParentEll, hbParentAE⟩ := hfamily (adaptedDomain hq t)
  obtain ⟨bChild, lamChild, LamChild, hbChildField, _hbChildLam,
      _hbChildLamUpper, hbChildEll, hbChildAE⟩ := hfamily (adaptedDomainAt hq k w)
  let uParent : Solution (adaptedDomain hq t) bParent :=
    Solution.ofAEEq hbParentAE (diagonalWeakOptimizer hq t a p r)
  have hrep : bChild.toCoeffField = bParent.toCoeffField := by
    rw [hbChildField, hbParentField]
  have hbChildEll' : IsEllipticFieldOn lamChild LamChild
      (adaptedCellAt q k w) bChild.toCoeffField := by
    rw [hbChildField]
    exact hbChildEll
  obtain ⟨uChild, huChild⟩ := exists_restrict_solution hrep
    (adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw)
    hbChildEll' uParent
  let u : Solution (adaptedDomainAt hq k w)
      (a.coeffOn (adaptedDomainAt hq k w)) :=
    Solution.ofAEEq hbChildAE.symm uChild
  refine ⟨u, ?_⟩
  simpa only [u, uParent, Solution.toH1_ofAEEq] using huChild

end

end HCPolySupport.HighContrast.Response

end HighContrast

end HCPolySupport

end
