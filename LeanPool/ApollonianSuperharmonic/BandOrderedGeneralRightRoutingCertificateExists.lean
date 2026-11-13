/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandParentVectorQuarterTurn
public import LeanPool.ApollonianSuperharmonic.BandVectorParentSums

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightRoutingCertificate
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralShiftedRoutedBoundaryLocalization
public import LeanPool.ApollonianSuperharmonic.CoveredInterfaceOppositeIncidentCells
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile

-- [TABLET NODE: BandOrderedGeneralRightRoutingCertificateExists]

/-!
# BandOrderedGeneralRightRoutingCertificateExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightRoutingGeometry

private theorem hedge :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
            (BandOrderedGeneralRightInterfaceCertificate normalization) → (exists edge : Finset
            GaussianInt, normalization.normalizedPoint ∈ edge ∧ edge ∈ FootprintEdges
            normalization.normalizedRoot ∩ FootprintEdges normalization.normalizedFixed) ) := by
  classical
  intro C T N h k x normalization interface
  rcases interface.startData.pathAB with
    ⟨p, hp, hlen, _, _, hvertices, hsteps, hedges⟩
  exact SimpleGridPathVertexIncidentEdge _ _
    ⟨p, hp, hlen, hvertices, hsteps, hedges⟩
    normalization.normalizedPoint interface.normalized_point_on_start_path

private theorem hrootBand :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), BandPrototile
            normalization.normalizedCircle.1.1 normalization.normalizedRoot ) := by
  classical
  intro C T N h k x normalization
  rw [← normalization.normalized_circle_eq]
  exact normalization.root_band

private theorem hend :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (interface :
            BandOrderedGeneralRightInterfaceCertificate normalization),
            interface.startData.otherAB ∈ FootprintVertices normalization.normalizedRoot ∩
            FootprintVertices normalization.normalizedFixed ∩ FootprintVertices
            interface.endCompanion ) := by
  classical
  intro C T N h k x normalization interface
  rw [← interface.interface_endpoints.1]
  exact (interface.endData.unique_common interface.endData.point).2 rfl

private theorem period2 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2) + BandVectors.1 (q 0) (q 3) = 0) →
            ((BandVectors.1 (q 0) (q 1) = normalization.layout.u) → ((BandVectors.1 (q 0) (q 2) =
            normalization.layout.v) → (BandVectors.1 (q 0) (q 3) = -normalization.layout.u -
            normalization.layout.v))) ) := by
  classical
  intro C T N h k x normalization q outgoing_relation period0 period1
  rw [← period0, ← period1]
  have heq : BandVectors.1 (q 0) (q 3) =
      -(BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2)) :=
    eq_neg_of_add_eq_zero_left (by
      simpa [add_assoc, add_comm, add_left_comm] using outgoing_relation)
  calc
    _ = -(BandVectors.1 (q 0) (q 1) + BandVectors.1 (q 0) (q 2)) := heq
    _ = _ := by abel

private theorem hdisplacement :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        (BandVectors.1 (q 0) (q 1) = normalization.layout.u) → ((BandVectors.1 (q 0) (q 2) =
            normalization.layout.v) → ((BandVectors.1 (q 0) (q 3) = -normalization.layout.u -
            normalization.layout.v) → (
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        normalization.rightNeighborDisplacement = (m : GaussianInt) * normalization.layout.u + (n
            : GaussianInt) * normalization.layout.v))) ) := by
  classical
  intro C T N h k x normalization q period0 period1 period2 m n
  rw [normalization.right_neighbor_displacement]
  have hd : normalization.rightDirectionSlot = 0 ∨
      normalization.rightDirectionSlot = 1 ∨
        normalization.rightDirectionSlot = 2 := by omega
  rcases hd with hd | hd | hd <;>
    cases hp : normalization.rightNeighborPositive <;>
    simp [q, m, n, hd, hp, period0, period1, period2] <;> abel

private theorem hshift :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (selectedSlot : Fin
            (3 : ℕ)), ∀ (selectedSign : Bool),
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        (normalization.rightNeighborPositive = true ∧ ((normalization.rightDirectionSlot = 0 ∧
            exteriorIndex.first = 1 ∧ exteriorIndex.second = 0) ∨
            (normalization.rightDirectionSlot = 1 ∧ exteriorIndex.first = 0 ∧
            exteriorIndex.second = 1) ∨ (normalization.rightDirectionSlot = 2 ∧
            exteriorIndex.first = -1 ∧ exteriorIndex.second = -1))) ∨
            (normalization.rightNeighborPositive = false ∧ ((normalization.rightDirectionSlot = 0
            ∧ exteriorIndex.first = -1 ∧ exteriorIndex.second = 0) ∨
            (normalization.rightDirectionSlot = 1 ∧ exteriorIndex.first = 0 ∧
            exteriorIndex.second = -1) ∨ (normalization.rightDirectionSlot = 2 ∧
            exteriorIndex.first = 1 ∧ exteriorIndex.second = 1))) ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign m n labelOf exteriorIndex
  have hd : normalization.rightDirectionSlot = 0 ∨
      normalization.rightDirectionSlot = 1 ∨
        normalization.rightDirectionSlot = 2 := by omega
  rcases hd with hd | hd | hd <;>
    cases hp : normalization.rightNeighborPositive <;>
    simp [exteriorIndex, m, n, hd, hp]

private theorem hcentralIndex :
    (by
      classical
      exact
        ∀ (centralSlot : Fin (3 : ℕ)),
          ∀ (centralSign : Bool),
            let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
              if i = 0 then if s = true then .A else .B
              else
                if i = 1 then if s = true then .C else .D else if s = true then .E else .F
            let centralIndex : PeriodicSubtileIndex :=
              ⟨labelOf centralSlot centralSign, 0, 0⟩
            centralIndex = ⟨.A, 0, 0⟩ ∨
              centralIndex = ⟨.B, 0, 0⟩ ∨
                centralIndex = ⟨.C, 0, 0⟩ ∨
                  centralIndex = ⟨.D, 0, 0⟩ ∨
                    centralIndex = ⟨.E, 0, 0⟩ ∨ centralIndex = ⟨.F, 0, 0⟩
    )
            := by
  classical
  intro centralSlot centralSign labelOf centralIndex
  fin_cases centralSlot <;> cases centralSign <;>
    simp [centralIndex, labelOf]


private theorem hcentralOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (centralSlot : Fin (3
            : ℕ)), ∀ (centralSign : Bool),
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let centralIndex : PeriodicSubtileIndex :=
          ⟨labelOf centralSlot centralSign, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v centralIndex =
            normalization.layout.P centralSlot centralSign) ) := by
  classical
  intro C T N h k x normalization centralSlot centralSign labelOf centralIndex translation_zero
  have aux : ∀ (i : Fin 3) (s : Bool),
      SubtileOccurrenceInterpretation normalization.layout.P
        normalization.layout.u normalization.layout.v
          ⟨labelOf i s, 0, 0⟩ = normalization.layout.P i s := by
    intro i s
    fin_cases i <;> cases s <;>
      simp [labelOf, SubtileOccurrenceInterpretation, translation_zero]
  exact aux centralSlot centralSign

private theorem hexteriorOccurrence :
    (by
      classical
      exact
        ∀ (C : BandCircle),
          ∀ (T : ProtoTile),
            ∀ (N : ProtoTile),
              ∀ (h : PartialOdometer),
                ∀ (k : PartialOdometer),
                  ∀ (x : GaussianInt),
                    ∀
                      (normalization :
                        BandOrderedGeneralRightNormalizationCertificate C T N h k x),
                      ∀ (selectedSlot : Fin (3 : ℕ)),
                        ∀ (selectedSign : Bool),
                          let m : Int :=
                            if normalization.rightDirectionSlot = 0 then
                              if normalization.rightNeighborPositive = true then 1 else -1
                            else
                              if normalization.rightDirectionSlot = 1 then 0
                              else
                                if normalization.rightNeighborPositive = true then -1
                              else 1
                          let n : Int :=
                            if normalization.rightDirectionSlot = 0 then 0
                            else
                              if normalization.rightDirectionSlot = 1 then
                                if normalization.rightNeighborPositive = true then 1
                              else -1
                              else
                                if normalization.rightNeighborPositive = true then -1
                              else 1
                          normalization.rightNeighborDisplacement =
                              (m : GaussianInt) * normalization.layout.u +
                                (n : GaussianInt) * normalization.layout.v →
                            let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
                              if i = 0 then if s = true then .A else .B
                              else
                                if i = 1 then if s = true then .C else .D
                              else if s = true then .E else .F
                            let exteriorIndex : PeriodicSubtileIndex :=
                              ⟨labelOf selectedSlot selectedSign, m, n⟩
                            normalization.rightNeighborPositive = true ∧
                                (normalization.rightDirectionSlot = 0 ∧
                                exteriorIndex.first = 1 ∧ exteriorIndex.second = 0 ∨
                                normalization.rightDirectionSlot = 1 ∧
                                exteriorIndex.first = 0 ∧ exteriorIndex.second = 1 ∨
                                normalization.rightDirectionSlot = 2 ∧
                                exteriorIndex.first = -1 ∧ exteriorIndex.second = -1) ∨
                                normalization.rightNeighborPositive = false ∧
                                (normalization.rightDirectionSlot = 0 ∧
                                exteriorIndex.first = -1 ∧ exteriorIndex.second = 0 ∨
                                normalization.rightDirectionSlot = 1 ∧
                                exteriorIndex.first = 0 ∧ exteriorIndex.second = -1 ∨
                                normalization.rightDirectionSlot = 2 ∧
                                exteriorIndex.first = 1 ∧ exteriorIndex.second = 1) →
                              SubtileOccurrenceInterpretation normalization.layout.P
                                normalization.layout.u normalization.layout.v
                                exteriorIndex =
                                TileTranslation
                                (normalization.layout.P selectedSlot selectedSign)
                                normalization.rightNeighborDisplacement
    ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign m n hdisplacement labelOf
      exteriorIndex hshift
  rw [hdisplacement]
  fin_cases selectedSlot <;> cases selectedSign <;>
    simp [exteriorIndex, labelOf, SubtileOccurrenceInterpretation]

private theorem hcentroidAlign :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (selectedSlot : Fin
            (3 : ℕ)), ∀ (selectedSign : Bool), (FootprintVertices normalization.normalizedRoot =
            FootprintVertices (TileTranslation normalization.normalizedFixed
            normalization.rightNeighborDisplacement) ∧ BoundaryFootprintVertices
            normalization.normalizedRoot = BoundaryFootprintVertices (TileTranslation
            normalization.normalizedFixed normalization.rightNeighborDisplacement) ∧
            BoundaryFootprintEdges normalization.normalizedRoot = BoundaryFootprintEdges
            (TileTranslation normalization.normalizedFixed
            normalization.rightNeighborDisplacement) ∧ TileRealization
            normalization.normalizedRoot = TileRealization (TileTranslation
            normalization.normalizedFixed normalization.rightNeighborDisplacement) ∧ TileCentroid
            normalization.normalizedRoot = TileCentroid (TileTranslation
            normalization.normalizedFixed normalization.rightNeighborDisplacement)) →
            (TileCentroid (normalization.pieces selectedSlot selectedSign) = TileCentroid
            (TileTranslation (normalization.layout.P selectedSlot selectedSign)
            normalization.rightNeighborDisplacement)) ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign houterObservables
  rw [(TileTranslationFormulas
    (normalization.layout.P selectedSlot selectedSign)
    normalization.rightNeighborDisplacement).2.2.2.2.1]
  have hp1 := congrArg Prod.fst
    (normalization.piece_centroid selectedSlot selectedSign)
  have hp2 := congrArg Prod.snd
    (normalization.piece_centroid selectedSlot selectedSign)
  have hl1 := congrArg Prod.fst
    (normalization.layout.outer_occurrence selectedSlot selectedSign).2.2
  have hl2 := congrArg Prod.snd
    (normalization.layout.outer_occurrence selectedSlot selectedSign).2.2
  have hr1 := congrArg Prod.fst houterObservables.2.2.2.2
  have hr2 := congrArg Prod.snd houterObservables.2.2.2.2
  rw [(TileTranslationFormulas normalization.normalizedFixed
    normalization.rightNeighborDisplacement).2.2.2.2.1] at hr1 hr2
  apply Prod.ext <;> simp only []
  · change (TileCentroid
        (normalization.pieces selectedSlot selectedSign)).1 -
        (TileCentroid normalization.normalizedRoot).1 = _ at hp1
    change (TileCentroid
        (normalization.layout.P selectedSlot selectedSign)).1 -
        (TileCentroid normalization.normalizedFixed).1 = _ at hl1
    change (TileCentroid normalization.normalizedRoot).1 =
      (TileCentroid normalization.normalizedFixed).1 + _ at hr1
    linarith
  · change (TileCentroid
        (normalization.pieces selectedSlot selectedSign)).2 -
        (TileCentroid normalization.normalizedRoot).2 = _ at hp2
    change (TileCentroid
        (normalization.layout.P selectedSlot selectedSign)).2 -
        (TileCentroid normalization.normalizedFixed).2 = _ at hl2
    change (TileCentroid normalization.normalizedRoot).2 =
      (TileCentroid normalization.normalizedFixed).2 + _ at hr2
    linarith

private theorem hselectedCells :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (selectedSlot : Fin
            (3 : ℕ)), ∀ (selectedSign : Bool),
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex = TileTranslation (normalization.layout.P
            selectedSlot selectedSign) normalization.rightNeighborDisplacement) →
            (((normalization.pieces selectedSlot selectedSign).cells = (TileTranslation
            (normalization.layout.P selectedSlot selectedSign)
            normalization.rightNeighborDisplacement).cells ∧ ((normalization.pieces selectedSlot
            selectedSign).cells = ∅ → (normalization.pieces selectedSlot selectedSign).anchor =
            (TileTranslation (normalization.layout.P selectedSlot selectedSign)
            normalization.rightNeighborDisplacement).anchor)) → ((normalization.pieces
            selectedSlot selectedSign).cells = (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v
            exteriorIndex).cells)) ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign m n labelOf exteriorIndex
      hexteriorOccurrence hselectedUnique
  rw [hexteriorOccurrence]
  exact hselectedUnique.1

private theorem hselectedAnchor :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (selectedSlot : Fin
            (3 : ℕ)), ∀ (selectedSign : Bool),
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex = TileTranslation (normalization.layout.P
            selectedSlot selectedSign) normalization.rightNeighborDisplacement) →
            (((normalization.pieces selectedSlot selectedSign).cells = (TileTranslation
            (normalization.layout.P selectedSlot selectedSign)
            normalization.rightNeighborDisplacement).cells ∧ ((normalization.pieces selectedSlot
            selectedSign).cells = ∅ → (normalization.pieces selectedSlot selectedSign).anchor =
            (TileTranslation (normalization.layout.P selectedSlot selectedSign)
            normalization.rightNeighborDisplacement).anchor)) → ((normalization.pieces
            selectedSlot selectedSign).cells = ∅ → (normalization.pieces selectedSlot
            selectedSign).anchor = (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v exteriorIndex).anchor)) ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign m n labelOf exteriorIndex
      hexteriorOccurrence hselectedUnique
  rw [hexteriorOccurrence]
  exact hselectedUnique.2

private theorem hparentPositive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        ∀ (selectedSlot : Fin (3 : ℕ)), (0 ≤ (q selectedSlot.succ).1) → (0 < (q
            selectedSlot.succ).1) ) := by
  classical
  intro C T N h k x normalization q selectedSlot hparentNonnegative
  have hn : (q selectedSlot.succ).1 ≠ 0 := by
    simpa [q] using normalization.configuration.noLine selectedSlot.succ
  omega

private theorem hselectedDomain :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x),
        let q := normalization.normalizedPresentation
        ∀ (selectedSlot : Fin (3 : ℕ)), ∀ (selectedSign : Bool),
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        (FootprintVertices (normalization.pieces selectedSlot selectedSign) = FootprintVertices
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex)) → ((0 < (q selectedSlot.succ).1) →
            (((normalization.functions selectedSlot selectedSign).domain : Set GaussianInt) =
            FootprintVertices (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v exteriorIndex))) ) := by
  classical
  intro C T N h k x normalization q selectedSlot selectedSign m n labelOf exteriorIndex
      hselectedFootprint hparentPositive
  calc
    _ = FootprintVertices (normalization.pieces selectedSlot selectedSign) :=
      PositiveCurvatureTileOdometerDomain _ _ _ hparentPositive
        (normalization.piece_odometer selectedSlot selectedSign)
    _ = _ := hselectedFootprint

private theorem hexteriorCell :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (j : Fin (4 : ℕ)), ∀
            (selectedSlot : Fin (3 : ℕ)), ∀ (selectedSign : Bool), (LatticeVertexIncidentCell
            normalization.normalizedPoint j ∈ (normalization.pieces selectedSlot
            selectedSign).cells) → (
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        ((normalization.pieces selectedSlot selectedSign).cells =
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex).cells) → (LatticeVertexIncidentCell
            normalization.normalizedPoint j ∈ (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v
            exteriorIndex).cells)) ) := by
  classical
  intro C T N h k x normalization j selectedSlot selectedSign hselected m n labelOf exteriorIndex
      hselectedCells
  rw [← hselectedCells]
  exact hselected

private theorem hcentralCell :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (j : Fin (4 : ℕ)), ∀
            (centralSlot : Fin (3 : ℕ)), ∀ (centralSign : Bool), (LatticeVertexIncidentCell
            normalization.normalizedPoint (j + (2 : Fin (4 : ℕ))) ∈ (normalization.layout.P
            centralSlot centralSign).cells) → (
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let centralIndex : PeriodicSubtileIndex :=
          ⟨labelOf centralSlot centralSign, 0, 0⟩
        (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v centralIndex = normalization.layout.P centralSlot centralSign)
            → (LatticeVertexIncidentCell normalization.normalizedPoint (j + 2) ∈
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v centralIndex).cells)) ) := by
  classical
  intro C T N h k x normalization j centralSlot centralSign hcentral labelOf centralIndex
      hcentralOccurrence
  rw [hcentralOccurrence]
  exact hcentral

private theorem footprint_of_cell :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (c : GaussianInt), (c ∈ U.cells) → (c ∈ FootprintVertices U ∧ c + 1
            ∈ FootprintVertices U ∧ c + ⟨0, 1⟩ ∈ FootprintVertices U ∧ c + 1 + ⟨0, 1⟩ ∈
            FootprintVertices U) ) := by
  classical
  intro U c hc
  have hne : U.cells.Nonempty := ⟨c, hc⟩
  simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
  exact ⟨⟨c, hc, Or.inl rfl⟩,
    ⟨c, hc, Or.inr (Or.inl rfl)⟩,
    ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩,
    ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩⟩

private theorem hstar :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (j : Fin (4 : ℕ)),
                                                  (
                                                   (∀ (selectedSlot : Fin (3 : ℕ)), ∀
            (selectedSign : Bool),
                                                                      (∀ (centralSlot : Fin (3 :
            ℕ)), ∀ (centralSign : Bool),
                                                                                                (
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        let centralIndex : PeriodicSubtileIndex :=
          ⟨labelOf centralSlot centralSign, 0, 0⟩
        (LatticeVertexIncidentCell normalization.normalizedPoint j ∈
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex).cells) → ((LatticeVertexIncidentCell
            normalization.normalizedPoint (j + 2) ∈ (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v
            centralIndex).cells) → ((LatticeVertexIncidentCell normalization.normalizedPoint j ∈
            FootprintVertices (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v exteriorIndex) ∧
            LatticeVertexIncidentCell normalization.normalizedPoint j + (1 : GaussianInt) ∈
            FootprintVertices (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v exteriorIndex) ∧
            LatticeVertexIncidentCell normalization.normalizedPoint j + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ FootprintVertices (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v exteriorIndex) ∧
            LatticeVertexIncidentCell normalization.normalizedPoint j + (1 : GaussianInt) + (⟨(0
            : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v exteriorIndex))
            → ((LatticeVertexIncidentCell normalization.normalizedPoint (j + (2 : Fin (4 : ℕ))) ∈
            FootprintVertices (SubtileOccurrenceInterpretation normalization.layout.P
            normalization.layout.u normalization.layout.v centralIndex) ∧
            LatticeVertexIncidentCell normalization.normalizedPoint (j + (2 : Fin (4 : ℕ))) + (1
            : GaussianInt) ∈ FootprintVertices (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v centralIndex) ∧
            LatticeVertexIncidentCell normalization.normalizedPoint (j + (2 : Fin (4 : ℕ))) +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v centralIndex) ∧ LatticeVertexIncidentCell
            normalization.normalizedPoint (j + (2 : Fin (4 : ℕ))) + (1 : GaussianInt) + (⟨(0 :
            ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ FootprintVertices (SubtileOccurrenceInterpretation
            normalization.layout.P normalization.layout.u normalization.layout.v centralIndex)) →
            (forall y, y = normalization.normalizedPoint ∨ y = normalization.normalizedPoint + 1
            ∨ y = normalization.normalizedPoint - 1 ∨ y = normalization.normalizedPoint + ⟨0, 1⟩
            ∨ y = normalization.normalizedPoint - ⟨0, 1⟩ -> y ∈ FootprintVertices
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v exteriorIndex) ∨ y ∈ FootprintVertices
            (SubtileOccurrenceInterpretation normalization.layout.P normalization.layout.u
            normalization.layout.v centralIndex))))))))) ) := by
  classical
  intro C T N h k x normalization j selectedSlot selectedSign centralSlot centralSign m n
      labelOf exteriorIndex centralIndex hexteriorCell hcentralCell exteriorCorners
      centralCorners y hy
  fin_cases j <;>
    simp only [LatticeVertexIncidentCell, sub_eq_add_neg, Int.reduceNeg, add_assoc,
        Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, add_comm,
        add_left_comm, add_neg_cancel, add_zero, Fin.reduceAdd, Matrix.cons_val, zero_add,
        Fin.reduceFinMk, add_neg_cancel_left, Fin.zero_eta] at exteriorCorners centralCorners
  · rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl exteriorCorners.1
    · exact Or.inl exteriorCorners.2.1
    · exact Or.inr centralCorners.2.2.1
    · exact Or.inl exteriorCorners.2.2.1
    · exact Or.inr centralCorners.2.1
  · rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl exteriorCorners.2.1
    · exact Or.inr centralCorners.2.2.2
    · exact Or.inl exteriorCorners.1
    · exact Or.inl exteriorCorners.2.2.2
    · exact Or.inr centralCorners.1
  · rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr centralCorners.1
    · exact Or.inr centralCorners.2.1
    · exact Or.inl exteriorCorners.2.2.1
    · exact Or.inr centralCorners.2.2.1
    · exact Or.inl exteriorCorners.2.1
  · rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl exteriorCorners.2.2.1
    · exact Or.inl exteriorCorners.2.2.2
    · exact Or.inr centralCorners.1
    · exact Or.inr centralCorners.2.2.2
    · exact Or.inl exteriorCorners.1

private theorem hexteriorIndex :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h : PartialOdometer), ∀ (k :
            PartialOdometer), ∀ (x : GaussianInt), ∀ (normalization :
            BandOrderedGeneralRightNormalizationCertificate C T N h k x), ∀ (selectedSlot : Fin
            (3 : ℕ)), ∀ (selectedSign : Bool),
        let m : Int := if normalization.rightDirectionSlot = 0 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightDirectionSlot = 1 then 0
          else if normalization.rightNeighborPositive = true then -1 else 1
        let n : Int := if normalization.rightDirectionSlot = 0 then 0
          else if normalization.rightDirectionSlot = 1 then
            (if normalization.rightNeighborPositive = true then 1 else -1)
          else if normalization.rightNeighborPositive = true then -1 else 1
        let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
          if i = 0 then (if s = true then .A else .B)
          else if i = 1 then (if s = true then .C else .D)
          else (if s = true then .E else .F)
        let exteriorIndex : PeriodicSubtileIndex :=
          ⟨labelOf selectedSlot selectedSign, m, n⟩
        (normalization.rightNeighborPositive = true ∧ (normalization.rightDirectionSlot = (0 :
            Fin (3 : ℕ)) ∧ (exteriorIndex = (⟨SixSubtileLabel.C, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) ∨ exteriorIndex = (⟨SixSubtileLabel.F, (1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex)) ∨ normalization.rightDirectionSlot = (1 : Fin (3 : ℕ)) ∧
            (exteriorIndex = (⟨SixSubtileLabel.E, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            exteriorIndex = (⟨SixSubtileLabel.B, (0 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex)) ∨
            normalization.rightDirectionSlot = (2 : Fin (3 : ℕ)) ∧ (exteriorIndex =
            (⟨SixSubtileLabel.A, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∨ exteriorIndex =
            (⟨SixSubtileLabel.D, (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex))) ∨
            normalization.rightNeighborPositive = false ∧ (normalization.rightDirectionSlot = (0
            : Fin (3 : ℕ)) ∧ (exteriorIndex = (⟨SixSubtileLabel.D, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex) ∨ exteriorIndex = (⟨SixSubtileLabel.E, (-1 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex)) ∨ normalization.rightDirectionSlot = (1 : Fin (3 : ℕ)) ∧
            (exteriorIndex = (⟨SixSubtileLabel.F, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex) ∨
            exteriorIndex = (⟨SixSubtileLabel.A, (0 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileIndex)) ∨
            normalization.rightDirectionSlot = (2 : Fin (3 : ℕ)) ∧ (exteriorIndex =
            (⟨SixSubtileLabel.B, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex) ∨ exteriorIndex =
            (⟨SixSubtileLabel.C, (1 : ℤ), (1 : ℤ)⟩ : PeriodicSubtileIndex)))) → (exteriorIndex =
            ⟨.A, -1, -1⟩ ∨ exteriorIndex = ⟨.A, 0, -1⟩ ∨ exteriorIndex = ⟨.C, 1, 0⟩ ∨
            exteriorIndex = ⟨.C, 1, 1⟩ ∨ exteriorIndex = ⟨.E, 0, 1⟩ ∨ exteriorIndex = ⟨.E, -1, 0⟩
            ∨ exteriorIndex = ⟨.B, 1, 1⟩ ∨ exteriorIndex = ⟨.B, 0, 1⟩ ∨ exteriorIndex = ⟨.D, -1,
            0⟩ ∨ exteriorIndex = ⟨.D, -1, -1⟩ ∨ exteriorIndex = ⟨.F, 0, -1⟩ ∨ exteriorIndex =
            ⟨.F, 1, 0⟩) ) := by
  classical
  intro C T N h k x normalization selectedSlot selectedSign m n labelOf exteriorIndex
      hclassification
  have hc := hclassification
  rcases hc with ⟨_, h0 | h1 | h2⟩ | ⟨_, h0 | h1 | h2⟩
  · rcases h0 with ⟨_, ha | ha⟩
    · exact Or.inr <| Or.inr <| Or.inl ha
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ha
  · rcases h1 with ⟨_, ha | ha⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ha
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inl ha
  · rcases h2 with ⟨_, ha | ha⟩
    · exact Or.inl ha
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ha
  · rcases h0 with ⟨_, ha | ha⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inl ha
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ha
  · rcases h1 with ⟨_, ha | ha⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ha
    · exact Or.inr <| Or.inl ha
  · rcases h2 with ⟨_, ha | ha⟩
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl ha
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ha

private theorem boundaryLabelSelection
    (first second direction selected : Fin 3)
    (positive firstSign secondSign selectedSign : Bool) (m n : Int)
    (hslots : (first = 0 ∧ second = 1 ∧ direction = 2) ∨
      (first = 1 ∧ second = 2 ∧ direction = 0) ∨
      (first = 2 ∧ second = 0 ∧ direction = 1))
    (hsigns : (positive = true ∧ firstSign = true ∧ secondSign = false) ∨
      (positive = false ∧ firstSign = false ∧ secondSign = true)) :
    let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
      if i = 0 then (if s then .A else .B)
      else if i = 1 then (if s then .C else .D)
      else (if s then .E else .F)
    let exterior : PeriodicSubtileIndex := ⟨labelOf selected selectedSign, m, n⟩
    (positive = true ∧
      (direction = 0 ∧ (exterior = ⟨.C, 1, 0⟩ ∨ exterior = ⟨.F, 1, 0⟩) ∨
       direction = 1 ∧ (exterior = ⟨.E, 0, 1⟩ ∨ exterior = ⟨.B, 0, 1⟩) ∨
       direction = 2 ∧ (exterior = ⟨.A, -1, -1⟩ ∨ exterior = ⟨.D, -1, -1⟩)) ∨
     positive = false ∧
      (direction = 0 ∧ (exterior = ⟨.D, -1, 0⟩ ∨ exterior = ⟨.E, -1, 0⟩) ∨
       direction = 1 ∧ (exterior = ⟨.F, 0, -1⟩ ∨ exterior = ⟨.A, 0, -1⟩) ∨
       direction = 2 ∧ (exterior = ⟨.B, 1, 1⟩ ∨ exterior = ⟨.C, 1, 1⟩))) →
      (selected = first ∧ selectedSign = firstSign) ∨
        (selected = second ∧ selectedSign = secondSign) := by
  intro labelOf exterior hclassification
  rcases hslots with hslots | hslots | hslots <;>
    rcases hslots with ⟨hfirst, hsecond, hdirection⟩ <;>
    rcases hsigns with hsigns | hsigns <;>
    rcases hsigns with ⟨hpositive, hfirstSign, hsecondSign⟩ <;>
    fin_cases selected <;> cases selectedSign <;>
    simp [exterior, labelOf, hfirst, hsecond, hdirection,
      hpositive, hfirstSign, hsecondSign] at hclassification ⊢

end RightRoutingGeometry

theorem BandOrderedGeneralRightRoutingCertificateExists
    {C : BandCircle} {T N : ProtoTile} {h k : PartialOdometer}
    {x : GaussianInt}
    {normalization :
      BandOrderedGeneralRightNormalizationCertificate C T N h k x}
    (interface : BandOrderedGeneralRightInterfaceCertificate normalization) :
    Nonempty (BandOrderedGeneralRightRoutingCertificate interface) := by
-- BODY
  let q := normalization.normalizedPresentation
  have hedge := RightRoutingGeometry.hedge C T N h k x normalization interface
  have hfixedBand : BandPrototile normalization.normalizedFixedCircle.1.1
      normalization.normalizedFixed :=
    TileOdometerBandPrototile _ _ _ normalization.normalized_fixed_odometer
  have hrootRegular := LatticeEdgeRegularity normalization.normalizedCircle
    normalization.normalizedRoot (RightRoutingGeometry.hrootBand C T N h k x normalization)
        interface.root_lattice
  have hfixedRegular := LatticeEdgeRegularity normalization.normalizedFixedCircle
    normalization.normalizedFixed hfixedBand interface.fixed_lattice
  have hstart : interface.startData.point ∈
      FootprintVertices normalization.normalizedRoot ∩
        FootprintVertices normalization.normalizedFixed ∩
          FootprintVertices interface.startCompanion :=
    (interface.startData.unique_common interface.startData.point).2 rfl
  have hend := RightRoutingGeometry.hend C T N h k x normalization interface
  obtain ⟨j, hjroot, hjfixed⟩ := CoveredInterfaceOppositeIncidentCells
    normalization.normalizedRoot normalization.normalizedFixed
    interface.startCompanion interface.endCompanion
    interface.startData.point interface.startData.otherAB
    normalization.normalizedPoint interface.root_lattice interface.fixed_lattice
    interface.start_lattice interface.end_lattice interface.root_fixed_disjoint
    interface.root_start_disjoint interface.fixed_start_disjoint
    interface.root_end_disjoint interface.fixed_end_disjoint
    interface.startData.pathAB hedge interface.start_touching
    interface.end_touching hstart hend hrootRegular.2.1 hfixedRegular.2.1
    normalization.normalized_star
  obtain ⟨selectedSlot, selectedSign, hselected⟩ :=
    (normalization.piece_cell_cover _).mp hjroot
  obtain ⟨centralSlot, centralSign, hcentral⟩ :=
    (normalization.layout.outer_union _).mp hjfixed
  have period0 : BandVectors.1 (q 0) (q 1) = normalization.layout.u :=
    normalization.layout.period_u.symm
  have period1 : BandVectors.1 (q 0) (q 2) = normalization.layout.v :=
    normalization.layout.period_v.symm
  let m : Int := if normalization.rightDirectionSlot = 0 then
      (if normalization.rightNeighborPositive = true then 1 else -1)
    else if normalization.rightDirectionSlot = 1 then 0
    else if normalization.rightNeighborPositive = true then -1 else 1
  let n : Int := if normalization.rightDirectionSlot = 0 then 0
    else if normalization.rightDirectionSlot = 1 then
      (if normalization.rightNeighborPositive = true then 1 else -1)
    else if normalization.rightNeighborPositive = true then -1 else 1
  let labelOf : Fin 3 → Bool → SixSubtileLabel := fun i s =>
    if i = 0 then (if s = true then .A else .B)
    else if i = 1 then (if s = true then .C else .D)
    else (if s = true then .E else .F)
  let exteriorIndex : PeriodicSubtileIndex :=
    ⟨labelOf selectedSlot selectedSign, m, n⟩
  let centralIndex : PeriodicSubtileIndex :=
    ⟨labelOf centralSlot centralSign, 0, 0⟩
  have hshift := RightRoutingGeometry.hshift C T N h k x normalization selectedSlot selectedSign
  have hcentralIndex := RightRoutingGeometry.hcentralIndex
      centralSlot centralSign
  have hexteriorOccurrence := RightRoutingGeometry.hexteriorOccurrence C T N h k x normalization
      selectedSlot selectedSign (RightRoutingGeometry.hdisplacement C T N h k x
      normalization period0 period1 (RightRoutingGeometry.period2 C T N h k x normalization
      (BandVectorOutgoingSum q normalization.configuration.proper) period0 period1))
      hshift
  have houterObservables := ProtoTileObservableExtensionality
    normalization.normalizedRoot
    (TileTranslation normalization.normalizedFixed
      normalization.rightNeighborDisplacement)
    normalization.right_neighbor_cells normalization.right_neighbor_empty_anchor
  have hpieceBand : BandPrototile (q selectedSlot.succ)
      (normalization.pieces selectedSlot selectedSign) :=
    TileOdometerBandPrototile _ _ _
      (normalization.piece_odometer selectedSlot selectedSign)
  have hlayoutBand : BandPrototile (q selectedSlot.succ)
      (normalization.layout.P selectedSlot selectedSign) :=
    (normalization.layout.outer_occurrence selectedSlot selectedSign).1
  have htranslatedLayout : BandPrototile (q selectedSlot.succ)
      (TileTranslation (normalization.layout.P selectedSlot selectedSign)
        normalization.rightNeighborDisplacement) :=
    BandPrototileTranslation _ _ _ hlayoutBand
  have hcentroidAlign := RightRoutingGeometry.hcentroidAlign C T N h k x normalization
      selectedSlot selectedSign houterObservables
  have hselectedUnique := BandPrototileCentroidUnique (q selectedSlot.succ)
    (normalization.pieces selectedSlot selectedSign)
    (TileTranslation (normalization.layout.P selectedSlot selectedSign)
      normalization.rightNeighborDisplacement)
    hpieceBand htranslatedLayout hcentroidAlign
  have hselectedObservables := ProtoTileObservableExtensionality
    (normalization.pieces selectedSlot selectedSign)
    (TileTranslation (normalization.layout.P selectedSlot selectedSign)
      normalization.rightNeighborDisplacement)
    hselectedUnique.1 hselectedUnique.2
  have hselectedCells := RightRoutingGeometry.hselectedCells C T N h k x normalization
      selectedSlot selectedSign hexteriorOccurrence hselectedUnique
  have hselectedAnchor := RightRoutingGeometry.hselectedAnchor C T N h k x normalization
      selectedSlot selectedSign hexteriorOccurrence hselectedUnique
  have hselectedFootprint :
      FootprintVertices (normalization.pieces selectedSlot selectedSign) =
        FootprintVertices (SubtileOccurrenceInterpretation normalization.layout.P
          normalization.layout.u normalization.layout.v exteriorIndex) := by
    rw [hexteriorOccurrence]
    exact hselectedObservables.1
  have hparentNonnegative : 0 ≤ (q selectedSlot.succ).1 :=
    (ProperBandCurvatureStructure q normalization.configuration.proper).2.1
      selectedSlot
  have hparentPositive := RightRoutingGeometry.hparentPositive C T N h k x normalization
      selectedSlot hparentNonnegative
  have hselectedDomain := RightRoutingGeometry.hselectedDomain C T N h k x normalization
      selectedSlot selectedSign hselectedFootprint hparentPositive
  have hexteriorCell := RightRoutingGeometry.hexteriorCell C T N h k x normalization j
      selectedSlot selectedSign hselected hselectedCells
  have hcentralCell := RightRoutingGeometry.hcentralCell C T N h k x normalization j centralSlot
      centralSign hcentral (RightRoutingGeometry.hcentralOccurrence C T N h k x normalization
      centralSlot centralSign (TileTranslationProperties.zero))
  have footprint_of_cell := RightRoutingGeometry.footprint_of_cell
  have exteriorCorners := footprint_of_cell _ _ hexteriorCell
  have centralCorners := footprint_of_cell _ _ hcentralCell
  have hstar := RightRoutingGeometry.hstar C T N h k x normalization j
      selectedSlot selectedSign centralSlot centralSign hexteriorCell
      hcentralCell exteriorCorners centralCorners
  obtain ⟨localizedEdge, hlocalizedPoint, hlocalizedCommon,
      hclassification, hcontact⟩ :=
    BandOrderedGeneralShiftedRoutedBoundaryLocalization q
      normalization.configuration normalization.normalizedCircle
      normalization.normalizedFixed normalization.layout exteriorIndex
      centralIndex normalization.normalizedPoint j
      normalization.rightDirectionSlot normalization.rightNeighborPositive
      hshift hcentralIndex hexteriorCell hcentralCell hstar
  have hexteriorIndex := RightRoutingGeometry.hexteriorIndex C T N h k x normalization
      selectedSlot selectedSign hclassification
  exact ⟨
    { edgeAtPoint := hedge
      root_induced := hrootRegular.2.1
      fixed_induced := hfixedRegular.2.1
      routedDirection := j
      routed_root_cell := hjroot
      routed_fixed_cell := hjfixed
      selectedSlot := selectedSlot
      selectedSign := selectedSign
      selected_piece_cell := hselected
      selected_boundary_piece := (RightRoutingGeometry.boundaryLabelSelection
          normalization.rightFirstSlot normalization.rightSecondSlot
          normalization.rightDirectionSlot selectedSlot normalization.rightNeighborPositive
          normalization.firstBoundarySign normalization.secondBoundarySign selectedSign m n
          normalization.right_slots_cyclic normalization.boundary_signs hclassification)
      exteriorIndex := exteriorIndex
      centralIndex := centralIndex
      exterior_index := hexteriorIndex
      central_index := hcentralIndex
      selected_exterior_cells := hselectedCells
      selected_exterior_empty_anchor := hselectedAnchor
      selected_exterior_footprint := hselectedFootprint
      selected_exterior_domain := hselectedDomain
      exterior_routed_cell := hexteriorCell
      central_routed_cell := hcentralCell
      selected_star := hstar
      localizedEdge := localizedEdge
      localized_edge_at_point := hlocalizedPoint
      localized_edge_common := hlocalizedCommon
      localized_contact := hcontact }⟩

end ApollonianSuperharmonic

end
