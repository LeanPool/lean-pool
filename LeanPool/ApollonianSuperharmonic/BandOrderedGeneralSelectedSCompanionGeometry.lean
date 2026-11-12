/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedContactRow
public import LeanPool.ApollonianSuperharmonic.P3996T1CenteredQuarterTurnInclusion
public import LeanPool.ApollonianSuperharmonic.P3996T1PlacementCompanionBlocks
public import LeanPool.ApollonianSuperharmonic.P3996T1AdjacentParentPlacement
public import LeanPool.ApollonianSuperharmonic.BandOrientedChildParentRightEndpoint
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowAlignment

-- [TABLET NODE: BandOrderedGeneralSelectedSCompanionGeometry]

/-!
# BandOrderedGeneralSelectedSCompanionGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SelectedSCompanionGeometry

private theorem solve :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
            BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection),
        let occurrence := SubtileOccurrenceInterpretation placement.layout.P
          placement.layout.u placement.layout.v
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (rrow :
            BandOrderedGeneralSelectedContactRow
            bundle.normalizedPresentation bundle.configuration bundle.normalizedCircle
            bundle.normalizedFixed placement.layout a b), ∀ (z : P3996T1SRowParameters),
                (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedFixed placement.layout rrow = some z) → (
        let newRight := TileTranslation (occurrence z.childIndex) z.rightShift;
          (newRight.cells = (TileTranslation
              (placement.layout.P z.childSlot z.childSign)
              (z.childShift + z.rightShift)).cells ∧
            (newRight.cells = ∅ → newRight.anchor = (TileTranslation
              (placement.layout.P z.childSlot z.childSign)
              (z.childShift + z.rightShift)).anchor)) ∧
          (Nonempty (ExactTileInterfaceTriple (occurrence a) newRight (occurrence b)) ∨
            Nonempty (ExactTileInterfaceTriple (occurrence b) newRight (occurrence a))) ∧
          newRight.cells ⊆ (TileTranslation bundle.normalizedFixed z.oldShift).cells ∧
          FootprintVertices newRight ⊆
            FootprintVertices (TileTranslation bundle.normalizedFixed z.oldShift)) ) := by
  classical
  intro C D T N h k x bundle placement occurrence a b rrow z hz
  obtain ⟨hp, hp0, hV, hW, hVpos, hWpos, hindices, hObs, hd,
    hWcent, hcent⟩ := P3996T1SRowAlignment bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedFixed
      placement.layout a b rrow z hz
  dsimp only at hV hW hObs hWcent hcent ⊢
  let newRight := TileTranslation (occurrence z.childIndex) z.rightShift
  have hExact : Nonempty (ExactTileInterfaceTriple
      (occurrence z.childIndex) newRight (occurrence z.parentIndex)) := by
    obtain ⟨Z, hZ, hZcent⟩ := P3996T1AdjacentParentPlacement
      z.predecessor hp z.parentSlot z.rotation (occurrence z.childIndex) hV
    have ep := BandOrientedChildParentRightEndpoint z.predecessor hp
      z.parentSlot z.rotation (occurrence z.childIndex)
      (occurrence z.parentIndex) Z hV hW hZ hVpos hWpos hWcent hZcent
    simpa only [newRight, hd] using ep
  have hsubP : (placement.layout.P z.childSlot z.sourceSign).cells ⊆
      bundle.normalizedFixed.cells := by
    intro y hy
    exact (placement.layout.outer_union y).mpr
      ⟨z.childSlot, z.sourceSign, hy⟩
  obtain ⟨t, p, ht, hp', htransport⟩ :=
    P3996T1CenteredQuarterTurnInclusion bundle.normalizedFixed
      (placement.layout.P z.childSlot z.sourceSign)
      (TileT2QuarterTurn bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout)
      (placement.layout.parent_quarter_turn z.childSlot z.sourceSign) hsubP
  let rotatedPiece := TileTranslation
    (placement.layout.P z.childSlot z.sourceSign) (z.oldShift + t - p)
  have htransported := htransport z.oldShift
  have hnewBand : BandPrototile
      (bundle.normalizedPresentation z.childSlot.succ) newRight := by
    rw [← hp0]
    exact BandPrototileTranslation _ _ z.rightShift hV
  have hrotatedBand : BandPrototile
      (bundle.normalizedPresentation z.childSlot.succ) rotatedPiece :=
    BandPrototileTranslation _ _ _
      (placement.layout.outer_occurrence z.childSlot z.sourceSign).1
  have hcentEqual : TileCentroid newRight = TileCentroid rotatedPiece := by
    exact sub_left_inj.mp (hcent.trans htransported.2.symm)
  have hcells := (BandPrototileCentroidUnique _ _ _ hnewBand hrotatedBand
    hcentEqual).1
  have hsub : newRight.cells ⊆
      (TileTranslation bundle.normalizedFixed z.oldShift).cells := by
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
  have hfoot : FootprintVertices newRight ⊆
      FootprintVertices (TileTranslation bundle.normalizedFixed z.oldShift) := by
    have hneOld := hne.mono hsub
    simp only [FootprintVertices, ite_eq_left hne, ite_eq_left hneOld]
    rintro y ⟨cell, hcell, hcorner⟩
    exact ⟨cell, hsub hcell, hcorner⟩
  refine ⟨hObs, ?_, hsub, hfoot⟩
  cases hflag : z.childIsExterior
  · simp only [hflag, Bool.false_eq_true, ↓reduceIte] at hindices
    right
    simpa only [← hindices.1, ← hindices.2] using hExact
  · simp only [hflag, ↓reduceIte] at hindices
    left
    simpa only [← hindices.1, ← hindices.2] using hExact

end SelectedSCompanionGeometry

theorem BandOrderedGeneralSelectedSCompanionGeometry :
    ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
        PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
        BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (placement :
        BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection), ∀ (selectedEdge : Finset GaussianInt), (bundle.normalizedPoint ∈
          selectedEdge) → ((selectedEdge ∈
      FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex)) → (∀ (row :
                BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed placement.layout
      placement.exteriorIndex placement.centralIndex),
    let q := bundle.normalizedPresentation
    let occurrence := SubtileOccurrenceInterpretation placement.layout.P
      placement.layout.u placement.layout.v
    let observableEq := fun A B : ProtoTile =>
      A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
    let companionGeometry := fun (newRight signedPiece oldRight : ProtoTile) =>
      observableEq newRight signedPiece ∧
        (Nonempty (ExactTileInterfaceTriple
            (occurrence placement.exteriorIndex) newRight
            (occurrence placement.centralIndex)) ∨
          Nonempty (ExactTileInterfaceTriple
            (occurrence placement.centralIndex) newRight
            (occurrence placement.exteriorIndex))) ∧
        newRight.cells ⊆ oldRight.cells ∧
        FootprintVertices newRight ⊆ FootprintVertices oldRight
    let rowGeometry := fun (a b : PeriodicSubtileIndex)
        (selectedRow : BandOrderedGeneralSelectedContactRow
          bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedFixed placement.layout a b)
        (oldRight : ProtoTile) =>
      match selectedRow with
      | .positiveL1 _ _ => True
      | .positiveL2 _ _ => True
      | .positiveL3 _ _ => True
      | .reflectedL1 _ _ => True
      | .reflectedL2 _ _ => True
      | .reflectedL3 _ _ => True
      | .positiveS1 _ =>
          let d := BandVectors.1
            (bundle.configuration.firstPredecessor 0)
            (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.A, -1, -1⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 true)
              (-placement.layout.u - placement.layout.v + d)) oldRight
      | .positiveS2 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.A, 0, -1⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 true)
              (-placement.layout.v + d)) oldRight
      | .positiveS3 _ =>
          let d := BandVectors.1
            (bundle.configuration.secondPredecessor 0)
            (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.C, 1, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 1 true)
              (placement.layout.u + d)) oldRight
      | .positiveS4 _ =>
          let d := BandVectors.1
            (bundle.configuration.firstPredecessor 0)
            (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.A, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 true) d) oldRight
      | .positiveS5 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.A, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 true) d) oldRight
      | .positiveS6 _ =>
          let d := BandVectors.1
            (bundle.configuration.secondPredecessor 0)
            (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.C, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 1 true) d) oldRight
      | .reflectedS1 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 0)
              (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.B, 1, 1⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 false)
              (placement.layout.u + placement.layout.v + d)) oldRight
      | .reflectedS2 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 1⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 false)
              (placement.layout.v + d)) oldRight
      | .reflectedS3 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.secondPredecessor 0)
              (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.D, -1, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 1 false)
              (-placement.layout.u + d)) oldRight
      | .reflectedS4 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 0)
              (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 false) d) oldRight
      | .reflectedS5 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 0 false) d) oldRight
      | .reflectedS6 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.secondPredecessor 0)
              (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.D, 0, 0⟩) d
          companionGeometry newRight
            (TileTranslation (placement.layout.P 1 false) d) oldRight
    let positiveFirst := TileTranslation bundle.normalizedFixed
      (-BandVectors.1 (q 0) (q placement.rightFirstSlot.succ))
    let positiveSecond := TileTranslation bundle.normalizedFixed
      (-BandVectors.1 (q 0) (q placement.rightSecondSlot.succ))
    let reflectedFirst := TileTranslation bundle.normalizedFixed
      (BandVectors.1 (q 0) (q placement.rightFirstSlot.succ))
    let reflectedSecond := TileTranslation bundle.normalizedFixed
      (BandVectors.1 (q 0) (q placement.rightSecondSlot.succ))
    (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧
          bundle.selectedSign = true →
            rowGeometry placement.exteriorIndex placement.centralIndex row
              positiveFirst) ∧
      (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = false →
            rowGeometry placement.exteriorIndex placement.centralIndex row
              positiveSecond) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧
          bundle.selectedSign = false →
            rowGeometry placement.exteriorIndex placement.centralIndex row
              reflectedFirst) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = true →
            rowGeometry placement.exteriorIndex placement.centralIndex row
              reflectedSecond))) := by
  intro C D T N h k x bundle placement selectedEdge hx hedge row
-- BODY
  let occurrence := SubtileOccurrenceInterpretation placement.layout.P
    placement.layout.u placement.layout.v
  have solve := SelectedSCompanionGeometry.solve C D T N h k x bundle placement
  generalize hExt : placement.exteriorIndex = ext at row ⊢
  generalize hCentral : placement.centralIndex = central at row ⊢
  cases row <;> dsimp only at ⊢
  case positiveL1 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case positiveL2 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case positiveL3 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case reflectedL1 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case reflectedL2 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case reflectedL3 => exact ⟨fun _ => True.intro, fun _ => True.intro,
    fun _ => True.intro, fun _ => True.intro⟩
  case' positiveS1 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS1 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' positiveS2 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS2 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' positiveS3 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS3 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' positiveS4 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS4 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' positiveS5 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS5 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' positiveS6 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.positiveS6 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS1 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS1 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS2 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS2 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS3 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS3 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS4 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS4 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS5 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS5 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  case' reflectedS6 presentation =>
    let rowLit := BandOrderedGeneralSelectedContactRow.reflectedS6 presentation
    let z : P3996T1SRowParameters :=
      (P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
        bundle.normalizedCircle bundle.normalizedFixed placement.layout rowLit).get (by rfl)
    have geometry := solve _ _ rowLit z rfl
    have blocks := P3996T1PlacementCompanionBlocks C D T N h k x bundle
      placement _ _ rowLit hExt hCentral z rfl
    dsimp only at blocks
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hbranch
      rw [blocks.1 hbranch]
      simpa only [z, rowLit, P3996T1SRowTable, Option.get_some, occurrence, zero_add] using
          geometry
    · intro hbranch
      rw [blocks.2.1 hbranch]
      simpa only [z, rowLit, P3996T1SRowTable, Option.get_some, occurrence, zero_add] using
          geometry
    · intro hbranch
      rw [blocks.2.2.1 hbranch]
      simpa only [z, rowLit, P3996T1SRowTable, Option.get_some, occurrence, zero_add] using
          geometry
    · intro hbranch
      rw [blocks.2.2.2 hbranch]
      simpa only [z, rowLit, P3996T1SRowTable, Option.get_some, occurrence, zero_add] using
          geometry

end ApollonianSuperharmonic

end
