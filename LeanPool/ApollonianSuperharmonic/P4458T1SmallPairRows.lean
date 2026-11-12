/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AncestorOdometerInnerSupportNormalization
public import LeanPool.ApollonianSuperharmonic.BandCircleEuclideanData
public import LeanPool.ApollonianSuperharmonic.BandOrientedBoundaryOccurrenceGenealogy
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandVectorOrientationDichotomy
public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.LeftLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryFrame
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundaryPlacement
public import LeanPool.ApollonianSuperharmonic.P4458T1BoundarySide
public import LeanPool.ApollonianSuperharmonic.P4458T1RestrictionFamily
public import LeanPool.ApollonianSuperharmonic.ParentVectorsInTilingLattice
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerSupportTransport
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.UnitTriangularStep
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.VectorSquareProduct
public import LeanPool.ApollonianSuperharmonic.P4536T1AFrameB
public import LeanPool.ApollonianSuperharmonic.P4536T1AFrameD
public import LeanPool.ApollonianSuperharmonic.P4536T1EndpointDifferences
public import LeanPool.ApollonianSuperharmonic.P4536T1RegularJoin
public import LeanPool.ApollonianSuperharmonic.P4536T1SmallUnitSides

-- [TABLET NODE: P4458T1SmallPairRows]

/-!
# P4458T1SmallPairRows

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4458T1SmallPairRows
    {C : BandCircle} {orientation : Bool} {base Rminus Rplus : ProtoTile}
    {hminus hplus : PartialOdometer}
    (F : P4458T1BoundaryFrame C orientation base Rminus Rplus hminus hplus)
    (D : P4458T1RestrictionFamily F)
    (a : Fin 3) (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
    (hstep : ![F.q 0, F.q a.succ, F.q (a + 1).succ, F.q (a + 2).succ] =
      ![(2 * (p 0).1 + 2 * (p 2).1 + 2 * (p 3).1 - (p 1).1,
          2 * (p 0).2 + 2 * (p 2).2 + 2 * (p 3).2 - (p 1).2),
        p 0, p 2, p 3])
    (hB : F.slot = a + 1 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 1 orientation)
    (hD : F.slot = a + 2 → C.1.1.1 = 1 →
      UnitOccurrenceOrientation p 2 orientation)
    (selected : F.slot ≠ a)
    (small : ((p 2).1 = 0 ∨ (p 2).1 = 1) ∧
      ((p 3).1 = 0 ∨ (p 3).1 = 1)) :
    Nonempty (P4458T1BoundaryPlacement F D) := by
-- BODY
  obtain ⟨s, hs, hcenter, _⟩ := P4536T1EndpointDifferences F D
  obtain ⟨J, hfamily, hcent, hcells, hodo, hanc, hocc⟩ :=
    P4536T1RegularJoin F D hcenter
  have direct := P4536T1SmallUnitSides F D a p hp hstep small J hfamily hodo hcent
  have hqA : F.q a.succ = p 0 := by simpa using congrFun hstep 1
  have hpos : 0 < (F.q a.succ).1 := by
    rw [hqA]
    exact (ProperBandCurvatureStructure p hp).1
  have hancA := D.ancestors a true hpos
  have hslots : F.slot = a + 1 ∨ F.slot = a + 2 := by
    have hne : F.slot.val ≠ a.val := fun he => selected (Fin.ext he)
    have hi := F.slot.isLt
    have ha := a.isLt
    have hv : F.slot.val = (a.val + 1) % 3 ∨
        F.slot.val = (a.val + 2) % 3 := by omega
    rcases hv with h | h
    · exact Or.inl (Fin.ext (by simpa [Fin.val_add] using h))
    · exact Or.inr (Fin.ext (by simpa [Fin.val_add] using h))
  rcases hslots with hslot | hslot
  · obtain ⟨G, _, _, houter, htile, hfunction⟩ :=
      P4536T1AFrameB F D a p hp hstep hslot (hB hslot) J hfamily hodo hcent
    have hancestor : AncestorOdometer G.outer.1.1 F.outer.1.1
        G.tile F.tile G.odometer F.odometer := by
      rw [houter, htile, hfunction]
      exact hancA
    exact ⟨⟨J, hcells, hodo, hanc, hocc,
      .direct (direct.1 hslot).1 (direct.1 hslot).2,
      .recursive G a houter hancestor⟩⟩
  · obtain ⟨G, _, _, houter, htile, hfunction⟩ :=
      P4536T1AFrameD F D a p hp hstep hslot (hD hslot) J hfamily hodo hcent
    have hancestor : AncestorOdometer G.outer.1.1 F.outer.1.1
        G.tile F.tile G.odometer F.odometer := by
      rw [houter, htile, hfunction]
      exact hancA
    exact ⟨⟨J, hcells, hodo, hanc, hocc,
      .recursive G a houter hancestor,
      .direct (direct.2 hslot).1 (direct.2 hslot).2⟩⟩

end ApollonianSuperharmonic

end
