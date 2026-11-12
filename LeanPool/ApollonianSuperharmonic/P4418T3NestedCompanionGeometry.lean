/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3996T1SRowAlignment
public import LeanPool.ApollonianSuperharmonic.P3996T1AdjacentParentPlacement
public import LeanPool.ApollonianSuperharmonic.P3996T1CenteredQuarterTurnInclusion
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentRightEndpoint
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.TileT2QuarterTurn

-- [TABLET NODE: P4418T3NestedCompanionGeometry]

/-!
# P4418T3NestedCompanionGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4418T3NestedCompanionGeometry
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b)
    (z : P3996T1SRowParameters)
    (hz : P3996T1SRowTable q cfg C T cert row = some z) :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    let newRight := TileTranslation (occurrence z.childIndex) z.rightShift
    Nonempty (ExactTileInterfaceTriple
        (occurrence z.childIndex) newRight (occurrence z.parentIndex)) ∧
      newRight.cells ⊆ (TileTranslation T z.oldShift).cells ∧
      FootprintVertices newRight ⊆
        FootprintVertices (TileTranslation T z.oldShift) := by
-- BODY
  let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let newRight := TileTranslation (occurrence z.childIndex) z.rightShift
  obtain ⟨hp, hp0, hV, hW, hVpos, hWpos, _, _, hd, hWcent, hcent⟩ :=
    P3996T1SRowAlignment q cfg C T cert a b row z hz
  dsimp only at hV hW hWcent hcent ⊢
  have hExact : Nonempty (ExactTileInterfaceTriple
      (occurrence z.childIndex) newRight (occurrence z.parentIndex)) := by
    obtain ⟨Z, hZ, hZcent⟩ := P3996T1AdjacentParentPlacement
      z.predecessor hp z.parentSlot z.rotation (occurrence z.childIndex) hV
    have ep := BandOrientedChildParentRightEndpoint z.predecessor hp
      z.parentSlot z.rotation (occurrence z.childIndex)
      (occurrence z.parentIndex) Z hV hW hZ hVpos hWpos hWcent hZcent
    simpa only [newRight, hd] using ep
  have hsubP : (cert.P z.childSlot z.sourceSign).cells ⊆ T.cells := by
    intro y hy
    exact (cert.outer_union y).mpr ⟨z.childSlot, z.sourceSign, hy⟩
  obtain ⟨t, p, _, _, htransport⟩ :=
    P3996T1CenteredQuarterTurnInclusion T (cert.P z.childSlot z.sourceSign)
      (TileT2QuarterTurn q cfg C T cert)
      (cert.parent_quarter_turn z.childSlot z.sourceSign) hsubP
  let rotatedPiece := TileTranslation (cert.P z.childSlot z.sourceSign)
    (z.oldShift + t - p)
  have htransported := htransport z.oldShift
  have hnewBand : BandPrototile (q z.childSlot.succ) newRight := by
    rw [← hp0]
    exact BandPrototileTranslation _ _ z.rightShift hV
  have hrotatedBand : BandPrototile (q z.childSlot.succ) rotatedPiece :=
    BandPrototileTranslation _ _ _
      (cert.outer_occurrence z.childSlot z.sourceSign).1
  have hcentEqual : TileCentroid newRight = TileCentroid rotatedPiece :=
    sub_left_inj.mp (hcent.trans htransported.2.symm)
  have hcells := (BandPrototileCentroidUnique _ _ _
    hnewBand hrotatedBand hcentEqual).1
  have hsub : newRight.cells ⊆ (TileTranslation T z.oldShift).cells := by
    rw [hcells]
    exact htransported.1
  have hne : newRight.cells.Nonempty := by
    obtain ⟨E⟩ := hExact
    obtain ⟨path, _, hlen, _, _, _, _, hedges⟩ := E.pathAB
    cases path with
    | nil => simp at hlen
    | cons v tail =>
        cases tail with
        | nil => simp at hlen
        | cons w rest =>
            have he : {v, w} ∈ FootprintEdges (occurrence z.childIndex) ∩
                FootprintEdges newRight :=
              (hedges {v, w}).mpr ⟨v, w, [], rest, rfl, rfl⟩
            obtain ⟨cell, hcell, _⟩ := he.2
            exact ⟨cell, hcell⟩
  refine ⟨hExact, hsub, ?_⟩
  have hneOld := hne.mono hsub
  change FootprintVertices newRight ⊆ FootprintVertices (TileTranslation T z.oldShift)
  simp only [FootprintVertices, ite_eq_left hne, ite_eq_left hneOld]
  rintro y ⟨cell, hcell, hcorner⟩
  exact ⟨cell, hsub hcell, hcorner⟩

end ApollonianSuperharmonic

end
