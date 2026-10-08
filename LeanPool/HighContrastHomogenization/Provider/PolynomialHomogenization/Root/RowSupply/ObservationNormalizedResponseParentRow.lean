/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterMajorant
public import LeanPool.HighContrastHomogenization.Provider.Initialization.IdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseFillingSummable
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.EpsilonAffineDoubledResponseRealization
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.ObservationNormalizedResponseParentRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Observation normalized responses priced by one parent row

The geometric parent is selected before the unit load.  Hence the exact
observation realization and the adapted-target filling estimate may be
maximized over all normalized identity loads without changing that parent.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

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

/-- A prescribed enclosing parent controls the normalized observation
response; the estimate is uniform over the unit identity load. -/
theorem observationNormalizedBlockResponseMax_le_normalizedParentRow_of_enclosed
    [NeZero d] {s epsilon : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hepsilon : 0 < epsilon) (center : Vec d)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (t : ℤ) (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (k M : ℤ) (hkM : k ≤ M) (w : Fin d → ℤ)
    (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (translateCube w (originCube d k))).toCoeffField
      =ᵐ[volumeMeasureOn
        (openCubeSet (translateCube w (originCube d k)))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center))
    (hEnclose : adaptedCellTranslate (epsilonAffineGrid epsilon abar) k
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) k w) ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) M) :
    Book.Ch02.normalizedBlockResponseMax
        (translateCube w (originCube d k)) aObs (1 : Mat d) ≤
      ∑' u : ℕ,
        (if u = 0 then 1 else
          6 * (d : ℝ) * Real.sqrt d *
            ‖(epsilonAffineGrid epsilon abar)⁻¹ *
              Selection.normalizedRoot (symmPart abar)‖ *
            (3 : ℝ) ^ (-(u : ℤ))) *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d M) (k - (u : ℤ)) aRef (1 : Mat d) := by
  let p := epsilonAffineGrid epsilon abar
  let q := Selection.normalizedRoot (symmPart abar)
  let y := epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
    adaptedCellCenter p k w
  have hp : p.PosDef := by
    simpa only [p] using epsilonAffineGrid_posDef hepsilon hS
  unfold Book.Ch02.normalizedBlockResponseMax
  refine csSup_le
    (Book.Ch02.normalizedBlockResponseValueSet_nonempty
      (translateCube w (originCube d k)) aObs (1 : Mat d)) ?_
  rintro _ ⟨e, he, rfl⟩
  let X : BlockVec d := ofFullBlockVec e
  have hloadInv :
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixInvSqrt (1 : Mat d)) e) = X := by
    simp only [Book.Ch02.constantFullBlockMatrixInvSqrt,
      constantFullBlockMatrixSqrt_one, inv_one, Matrix.one_mulVec, X]
  have hloadSqrt :
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixSqrt (1 : Mat d)) e) = X := by
    simp only [constantFullBlockMatrixSqrt_one, Matrix.one_mulVec, X]
  obtain ⟨P, Q, _Z, hP, hQ, _hZ, hbound⟩ :=
    exists_normalizedRootLoads_adaptedTarget_le_enclosingParentRow_summable
      hs hsHalf a abar hS t aRef haRef hp k k M hkM y
        (by simpa only [p, y] using hEnclose) e he
  have hreal := doubledResponseJ_observation_epsilonAffine_eq
    hepsilon center a abar hS k w
      (aObs.coeffOn (translateCube w (originCube d k))) hObs P Q
  rw [hloadInv, hloadSqrt]
  calc
    Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aObs.coeffOn (translateCube w (originCube d k))) X X =
      Book.Ch02.doubledResponseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        (aObs.coeffOn (translateCube w (originCube d k)))
        (normalizedReferencePrimalLoad abar P)
        (normalizedReferenceDualLoad abar Q) := by rw [hP, hQ]
    _ = Transport.coeffSpaceDoubledResponse (adaptedCellTranslate p k y) a P Q := by
      simpa only [p, y] using hreal
    _ ≤ ∑' u : ℕ,
        (if u = 0 then 1 else
          6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
            (3 : ℝ) ^ ((k - (u : ℤ)) - k)) *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d M) (k - (u : ℤ)) aRef (1 : Mat d) := by
      simpa only [p, q, y] using hbound
    _ = ∑' u : ℕ,
        (if u = 0 then 1 else
          6 * (d : ℝ) * Real.sqrt d * ‖p⁻¹ * q‖ *
            (3 : ℝ) ^ (-(u : ℤ))) *
          Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
            (originCube d M) (k - (u : ℤ)) aRef (1 : Mat d) := by
      apply tsum_congr
      intro u
      have hexponent : (k - (u : ℤ)) - k = -(u : ℤ) := by omega
      rw [hexponent]

end

end RowSupply
end HighContrast
end HCPolySupport
