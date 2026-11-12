/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P1BandOrderedGeneralMixedAggregateJunctionData
public import LeanPool.ApollonianSuperharmonic.P1BandOrderedGeneralMixedAggregatePairedEndpoints

-- [TABLET NODE: BandOrderedGeneralMixedAggregatePatches]

/-!
# BandOrderedGeneralMixedAggregatePatches

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralMixedAggregatePatches
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hsym : QuarterTurnSymmetric T) :
    let junctionData : ProtoTile → ProtoTile → ProtoTile → Prop :=
      fun A B C ↦ ∃ AB BC CA ABC : ProtoTile,
        LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
        LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧
        LatticeTile ABC ∧
        Disjoint A.cells B.cells ∧ Disjoint B.cells C.cells ∧
        Disjoint C.cells A.cells ∧
        (∀ z : LatticeCell,
          z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧
        (∀ z : LatticeCell,
          z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) ∧
        (∀ z : LatticeCell,
          z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) ∧
        (∀ z : LatticeCell,
          z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) ∧
        (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧
        (FootprintEdges B ∩ FootprintEdges C).Nonempty ∧
        (FootprintEdges C ∩ FootprintEdges A).Nonempty
    let pairedEndpointData : Fin 3 → Fin 4 → ProtoTile → ProtoTile → Prop :=
      fun i s U V ↦
        let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q 0) (q i.succ)
            else BandVectors.1 (q i.succ) (q 0))
        let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
          (if Even s.val then BandVectors.1 (q i.succ) (q 0)
            else BandVectors.1 (q 0) (q i.succ))
        ∃ rightData : ExactTileInterfaceTriple T
            (TileTranslation T uR) U,
          ∃ incomingData : ExactTileInterfaceTriple T
            (TileTranslation T uL) U,
            ∃ t5Data : ExactTileInterfaceTriple T U V,
              rightData.point = t5Data.point ∧
              incomingData.point ≠ t5Data.point ∧
              incomingData.otherCA = t5Data.point ∧
              rightData.otherCA = incomingData.point ∧
              t5Data.otherAB = incomingData.point
    (∀ (i : Fin 3) (U : ProtoTile), BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      junctionData T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3) (U V : ProtoTile), BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      junctionData T U V) ∧
    (∀ (i : Fin 3) (s : Fin 4) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile
        (q ((if Even s.val then i + 1 else i - 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ))
            else
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0))) →
      pairedEndpointData i s U V) := by
-- BODY
  have junctions := P1BandOrderedGeneralMixedAggregateJunctionData q cfg C₀ T cert hsym
  exact ⟨junctions.1, junctions.2,
    P1BandOrderedGeneralMixedAggregatePairedEndpoints q cfg C₀ T cert hsym⟩

end ApollonianSuperharmonic

end
