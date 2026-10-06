/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AlignedIdentities
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentState

/-!
# High-contrast homogenization: Provider.Response.SubcellDoubledResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Doubled response fields on aligned child cells

The optimizer on an adapted parent cell restricts to every aligned child.
Subtracting the child's canonical optimizer therefore gives a doubled response
field on the child for the actual coefficient-space representative.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The parent optimizer state minus the child optimizer state belongs to the
doubled response space on the child cell. -/
theorem isDoubledResponseField_diagonalWeakState_sub_childState [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    IsDoubledResponseField (adaptedDomainAt hq k w)
      (a.coeffOn (adaptedDomainAt hq k w))
      { potential := fun x =>
          (diagonalWeakState hq t a p r x -
            diagonalWeakChildState hq k w a p r x).1
        flux := fun x =>
          (diagonalWeakState hq t a p r x -
            diagonalWeakChildState hq k w a p r x).2 } := by
  let U := adaptedDomainAt hq k w
  let b := a.coeffOn U
  obtain ⟨_f, _hae, hfamily⟩ :=
    CoeffSpace.exists_pointwise_coeffOn_family_aeeq a
  obtain ⟨c, _clam, _cLam, hcf, hclam, hcLam, hcEll, hca⟩ := hfamily U
  obtain ⟨u, hu⟩ := exists_diagonalWeakOptimizer_restrict_child
    hq hkt hw a p r
  let v := diagonalWeakChildOptimizer hq k w a p r
  let uc : Solution U c := Solution.ofAEEq hca u
  let vc : Solution U c := Solution.ofAEEq hca v
  let Yc : DoubledField d :=
    { potential := fun x => uc.toH1.grad x - vc.toH1.grad x
      flux := fun x =>
        matVecMul (c.toCoeffField x) (uc.toH1.grad x) -
          matVecMul (c.toCoeffField x) (vc.toH1.grad x) }
  have hEllC : IsEllipticFieldOn c.lam c.Lam
      (adaptedCellAt q k w) c.toCoeffField := by
    rw [hcf, hclam, hcLam]
    exact hcEll
  have hYc : IsDoubledResponseField U c Yc := by
    exact isDoubledResponseField_grad_sub hEllC uc vc
  have hYb : IsDoubledResponseField U b Yc :=
    hYc.ofAEEq hca.symm
  refine Internal.Ch02.BookCh02.isDoubledResponseField_of_sameAE U b ?_ hYb
  constructor
  · filter_upwards with x
    change
      (diagonalWeakOptimizer hq t a p r).toH1.grad x - v.toH1.grad x =
        u.toH1.grad x - v.toH1.grad x
    rw [hu]
  · filter_upwards [hca] with x hx
    change
      matVecMul (b.toCoeffField x)
            ((diagonalWeakOptimizer hq t a p r).toH1.grad x) -
          matVecMul (b.toCoeffField x) (v.toH1.grad x) =
        matVecMul (c.toCoeffField x) (u.toH1.grad x) -
          matVecMul (c.toCoeffField x) (v.toH1.grad x)
    rw [hu, hx]

end

end HCPolySupport.HighContrast.Response
