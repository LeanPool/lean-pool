/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightSelectedRowGeometry
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralSelectedSCompanionGeometry
public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceExists
public import LeanPool.ApollonianSuperharmonic.P4418T3RoutedBlockCriterion
public import LeanPool.ApollonianSuperharmonic.P5478T1ExteriorPlacementIndex

-- [TABLET NODE: BandOrderedGeneralMarkedSectorTransport]

/-!
# BandOrderedGeneralMarkedSectorTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralMarkedSectorTransport
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign
      bundle.routedDirection)
    (selectedEdge : Finset GaussianInt)
    (hx : bundle.normalizedPoint ∈ selectedEdge)
    (hedge : selectedEdge ∈
      FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.exteriorIndex) ∩
        FootprintEdges
          (SubtileOccurrenceInterpretation placement.layout.P placement.layout.u
            placement.layout.v placement.centralIndex))
    (row : BandOrderedGeneralSelectedContactRow
      bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed placement.layout
      placement.exteriorIndex placement.centralIndex) :
    let q := bundle.normalizedPresentation
    let occurrence := SubtileOccurrenceInterpretation placement.layout.P
      placement.layout.u placement.layout.v
    let observableEq := fun A B : ProtoTile =>
      A.cells = B.cells ∧ (A.cells = ∅ → A.anchor = B.anchor)
    let rowConclusion := fun (a b : PeriodicSubtileIndex)
        (selectedRow : BandOrderedGeneralSelectedContactRow
          bundle.normalizedPresentation bundle.configuration
          bundle.normalizedCircle bundle.normalizedFixed placement.layout a b)
        (oldRight : ProtoTile) =>
      match selectedRow with
      | .positiveL1 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .positiveL2 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .positiveL3 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .reflectedL1 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .reflectedL2 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .reflectedL3 _ _ =>
          bundle.normalizedPoint ∉ FootprintVertices oldRight
      | .positiveS1 _ =>
          let d := BandVectors.1
            (bundle.configuration.firstPredecessor 0)
            (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.A, -1, -1⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 true)
                (-placement.layout.u - placement.layout.v + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .positiveS2 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.A, 0, -1⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 true)
                (-placement.layout.v + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .positiveS3 _ =>
          let d := BandVectors.1
            (bundle.configuration.secondPredecessor 0)
            (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.C, 1, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 1 true)
                (placement.layout.u + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .positiveS4 _ =>
          let d := BandVectors.1
            (bundle.configuration.firstPredecessor 0)
            (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.A, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 true) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .positiveS5 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (3 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.A, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 true) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .positiveS6 _ =>
          let d := BandVectors.1
            (bundle.configuration.secondPredecessor 0)
            (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.C, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 1 true) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS1 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 0)
              (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.B, 1, 1⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 false)
                (placement.layout.u + placement.layout.v + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS2 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 1⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 false)
                (placement.layout.v + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS3 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.secondPredecessor 0)
              (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.D, -1, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 1 false)
                (-placement.layout.u + d)) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS4 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.firstPredecessor 0)
              (bundle.configuration.firstPredecessor 2)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 false) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS5 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (bundle.configuration.firstPredecessor 3)
              (bundle.configuration.firstPredecessor 0)
          let newRight := TileTranslation (occurrence ⟨.B, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 0 false) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
      | .reflectedS6 _ =>
          let d := (⟨0, 1⟩ : GaussianInt) ^ (2 : Nat) *
            BandVectors.1 (bundle.configuration.secondPredecessor 0)
              (bundle.configuration.secondPredecessor 1)
          let newRight := TileTranslation (occurrence ⟨.D, 0, 0⟩) d
          observableEq newRight
              (TileTranslation (placement.layout.P 1 false) d) ∧
            (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
              bundle.normalizedPoint ∈ FootprintVertices newRight)
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
            rowConclusion placement.exteriorIndex placement.centralIndex row
              positiveFirst) ∧
      (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = false →
            rowConclusion placement.exteriorIndex placement.centralIndex row
              positiveSecond) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧
          bundle.selectedSign = false →
            rowConclusion placement.exteriorIndex placement.centralIndex row
              reflectedFirst) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧
          bundle.selectedSign = true →
            rowConclusion placement.exteriorIndex placement.centralIndex row
              reflectedSecond) := by
-- BODY
  classical
  let occurrence := SubtileOccurrenceInterpretation placement.layout.P
    placement.layout.u placement.layout.v
  have hindex := P5478T1ExteriorPlacementIndex C D T N h k x bundle placement
  have hgeometry := BandOrderedGeneralRightSelectedRowGeometry
    C D T N h k x bundle placement selectedEdge hx hedge row
  have hsGeometry := BandOrderedGeneralSelectedSCompanionGeometry
    C D T N h k x bundle placement selectedEdge hx hedge row
  obtain ⟨data⟩ := P4418T3SelectedInterfaceExists bundle.normalizedPresentation
    bundle.configuration bundle.normalizedCircle bundle.normalizedFixed
    placement.layout placement.exteriorIndex placement.centralIndex row
  have hrouted := P4418T3RoutedBlockCriterion bundle.normalizedPresentation
    bundle.configuration bundle.normalizedCircle bundle.normalizedFixed
    placement.layout placement.exteriorIndex placement.centralIndex row
    bundle.fixed_lattice data bundle.normalizedPoint bundle.routedDirection
    selectedEdge hx hedge placement.exterior_routed_cell placement.central_routed_cell
  have hL (hnone : P3996T1SRowTable bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedFixed
      placement.layout row = none) :
      bundle.normalizedPoint ∉ FootprintVertices (TileTranslation bundle.normalizedFixed
        (match placement.exteriorIndex.label with
          | .A => if placement.exteriorIndex.first = -1 then -placement.layout.u else
              placement.layout.u
          | .B => if placement.exteriorIndex.first = 1 then placement.layout.u else
              -placement.layout.u
          | .C => -placement.layout.v
          | .D => placement.layout.v
          | .E | .F => 0)) := by
    dsimp only at hrouted
    rw [hnone] at hrouted
    exact fun hy => (hrouted.mp hy).elim
  clear hrouted data
  have exterior_in : FootprintVertices (occurrence placement.exteriorIndex) ⊆
      FootprintVertices bundle.normalizedRoot := by
    rw [← placement.selected_exterior_footprint]
    exact bundle.piece_footprint _ _
  have zeroTranslation : GaussianTranslation 0 = id := by
    funext z
    simp [GaussianTranslation]
  have central_in : FootprintVertices (occurrence placement.centralIndex) ⊆
      FootprintVertices bundle.normalizedFixed := by
    rcases placement.central_index with hc | hc | hc | hc | hc | hc
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 0 true).2.1
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 0 false).2.1
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 1 true).2.1
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 1 false).2.1
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 2 true).2.1
    · simpa [occurrence, hc, SubtileOccurrenceInterpretation, TileTranslation,
        zeroTranslation] using (placement.layout.outer_occurrence 2 false).2.1
  have incident_footprint (U : ProtoTile) (z : GaussianInt) (j : Fin 4)
      (hc : LatticeVertexIncidentCell z j ∈ U.cells) : z ∈ FootprintVertices U := by
    simp only [FootprintVertices, ite_eq_left (show U.cells.Nonempty from ⟨_, hc⟩),
      Set.mem_ofPred_eq]
    refine ⟨_, hc, ?_⟩
    fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm]
  have hxExterior := incident_footprint _ _ _ placement.exterior_routed_cell
  have hxCentral := incident_footprint _ _ _ placement.central_routed_cell
  have fullData :
      (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧ bundle.selectedSign = true →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightFirstSlot.succ))))) ∧
      (placement.rightNeighborPositive = true ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧ bundle.selectedSign = false →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (-BandVectors.1
            (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightSecondSlot.succ))))) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightFirstSlot ∧ bundle.selectedSign = false →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightFirstSlot.succ))))) ∧
      (placement.rightNeighborPositive = false ∧
          bundle.selectedSlot = placement.rightSecondSlot ∧ bundle.selectedSign = true →
        Nonempty (ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed
          (TileTranslation bundle.normalizedFixed (BandVectors.1
            (bundle.normalizedPresentation 0)
            (bundle.normalizedPresentation placement.rightSecondSlot.succ))))) := by
    rcases hgeometry with ⟨hp, _, _, _, _, F, S, _⟩ | ⟨hp, _, _, _, _, F, S, _⟩ |
      ⟨hp, _, _, _, _, F, S, _⟩ | ⟨hp, _, _, _, _, F, S, _⟩
    all_goals refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro hbranch
    all_goals first
      | exact ⟨by simpa only [neg_one_mul, one_mul] using F⟩
      | exact ⟨by simpa only [neg_one_mul, one_mul] using S⟩
      | exact False.elim (Bool.noConfusion (hp.symm.trans hbranch.1))
  have finishS (oldRight newRight signedPiece : ProtoTile)
      (full : Nonempty (ExactTileInterfaceTriple bundle.normalizedRoot
        bundle.normalizedFixed oldRight))
      (geom :
        (newRight.cells = signedPiece.cells ∧
          (newRight.cells = ∅ → newRight.anchor = signedPiece.anchor)) ∧
        (Nonempty (ExactTileInterfaceTriple (occurrence placement.exteriorIndex)
            newRight (occurrence placement.centralIndex)) ∨
          Nonempty (ExactTileInterfaceTriple (occurrence placement.centralIndex)
            newRight (occurrence placement.exteriorIndex))) ∧
        newRight.cells ⊆ oldRight.cells ∧
        FootprintVertices newRight ⊆ FootprintVertices oldRight) :
      (newRight.cells = signedPiece.cells ∧
        (newRight.cells = ∅ → newRight.anchor = signedPiece.anchor)) ∧
      (bundle.normalizedPoint ∈ FootprintVertices oldRight ↔
        bundle.normalizedPoint ∈ FootprintVertices newRight) := by
    obtain ⟨E⟩ := full
    obtain ⟨hobs, htriple, _, hsub⟩ := geom
    refine ⟨hobs, ⟨?_, fun hy => hsub hy⟩⟩
    intro hold
    have hxE := (E.unique_common bundle.normalizedPoint).mp
      ⟨⟨exterior_in hxExterior, central_in hxCentral⟩, hold⟩
    rcases htriple with hG | hG
    · obtain ⟨G⟩ := hG
      have hg := (G.unique_common G.point).mpr rfl
      have hp := (E.unique_common G.point).mp
        ⟨⟨exterior_in hg.1.1, central_in hg.2⟩, hsub hg.1.2⟩
      simpa only [hxE, ← hp] using hg.1.2
    · obtain ⟨G⟩ := hG
      have hg := (G.unique_common G.point).mpr rfl
      have hp := (E.unique_common G.point).mp
        ⟨⟨exterior_in hg.2, central_in hg.1.1⟩, hsub hg.1.2⟩
      simpa only [hxE, ← hp] using hg.1.2
  have hu := placement.layout.period_u.symm
  have hv := placement.layout.period_v.symm
  generalize hExt : placement.exteriorIndex = ext at row hL hsGeometry ⊢
  generalize hCentral : placement.centralIndex = central at row hL hsGeometry ⊢
  cases row <;> dsimp only at hsGeometry ⊢
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro hbranch
  all_goals first
    | exact finishS _ _ _ (fullData.1 hbranch) (by
        simpa only [← hExt, ← hCentral] using hsGeometry.1 hbranch)
    | exact finishS _ _ _ (fullData.2.1 hbranch) (by
        simpa only [← hExt, ← hCentral] using hsGeometry.2.1 hbranch)
    | exact finishS _ _ _ (fullData.2.2.1 hbranch) (by
        simpa only [← hExt, ← hCentral] using hsGeometry.2.2.1 hbranch)
    | exact finishS _ _ _ (fullData.2.2.2 hbranch) (by
        simpa only [← hExt, ← hCentral] using hsGeometry.2.2.2 hbranch)
    | (have hrouted := hL rfl
       have hi := hindex.symm.trans hExt
       rcases placement.right_slots_cyclic with ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩ | ⟨hr, ht, hd⟩
       all_goals simp [hbranch.1, hbranch.2.1, hbranch.2.2, hr, ht, hd] at hi
       all_goals simpa [hr, ht, hd, hu, hv] using hrouted)

end ApollonianSuperharmonic

end
