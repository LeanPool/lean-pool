/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralRightSelectedRowGeometry
public import LeanPool.ApollonianSuperharmonic.P5478T1ExteriorPlacementIndex
public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceExists
public import LeanPool.ApollonianSuperharmonic.P5485T1OtherCompanionCoordinates
public import LeanPool.ApollonianSuperharmonic.P5485T1RoutedInterfaceAvoidance
public import LeanPool.ApollonianSuperharmonic.P5485T1FullInterfaceMarking

-- [TABLET NODE: BandOrderedGeneralRightOuterMarkingCriterion]

/-!
# BandOrderedGeneralRightOuterMarkingCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOrderedGeneralRightOuterMarkingCriterion
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
    let oldRight := TileTranslation bundle.normalizedFixed
      ((if placement.rightNeighborPositive = true then (-1 : GaussianInt)
          else 1) *
        BandVectors.1 (q 0) (q bundle.selectedSlot.succ))
    (¬ (∀ z, z = bundle.normalizedPoint ∨
          z = bundle.normalizedPoint - 1 ∨
          z = bundle.normalizedPoint - ⟨0, 1⟩ ∨
          z = bundle.normalizedPoint - 1 - ⟨0, 1⟩ →
        z ∈ bundle.normalizedRoot.cells ∨
          z ∈ bundle.normalizedFixed.cells) ↔
      bundle.normalizedPoint ∈ FootprintVertices oldRight) := by
-- BODY
  classical
  let q := bundle.normalizedPresentation
  let cert := placement.layout
  let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let other := if bundle.selectedSlot = placement.rightFirstSlot then
      placement.rightSecondSlot else placement.rightFirstSlot
  let otherTile := TileTranslation bundle.normalizedFixed
    ((if placement.rightNeighborPositive then (-1 : GaussianInt) else 1) *
      BandVectors.1 (q 0) (q other.succ))
  let coord : Int × Int := match other.val with
    | 0 => (1, 0) | 1 => (0, 1) | _ => (-1, -1)
  let scale : Int := if placement.rightNeighborPositive then -1 else 1
  let m := scale * coord.1
  let n := scale * coord.2
  have hselected :
      (bundle.selectedSlot = placement.rightFirstSlot ∧
        bundle.selectedSign = placement.rightNeighborPositive) ∨
      (bundle.selectedSlot = placement.rightSecondSlot ∧
        bundle.selectedSign = !placement.rightNeighborPositive) := by
    rcases placement.boundary_signs with ⟨hp, hf, hs⟩ | ⟨hp, hf, hs⟩
    all_goals rcases placement.selected_boundary_piece with h | h
    all_goals simp_all
  have coordinates := P5485T1OtherCompanionCoordinates q bundle.configuration
    bundle.normalizedCircle bundle.normalizedFixed cert
    placement.exteriorIndex placement.centralIndex row
    placement.rightFirstSlot placement.rightSecondSlot placement.rightDirectionSlot
    bundle.selectedSlot placement.rightNeighborPositive bundle.selectedSign
    placement.right_slots_cyclic hselected
    (P5478T1ExteriorPlacementIndex C D T N h k x bundle placement)
  change ((if placement.rightNeighborPositive then (-1 : GaussianInt) else 1) *
      BandVectors.1 (q 0) (q other.succ) =
      (m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v) ∧ _ at coordinates
  obtain ⟨data⟩ := P4418T3SelectedInterfaceExists q bundle.configuration
    bundle.normalizedCircle bundle.normalizedFixed cert
    placement.exteriorIndex placement.centralIndex row
  have parent_cells (i : Fin 3) (s : Bool) (d c : GaussianInt)
      (hc : c ∈ (TileTranslation (cert.P i s) d).cells) :
      c ∈ (TileTranslation bundle.normalizedFixed d).cells := by
    rw [(TileTranslationFormulas _ d).1] at hc ⊢
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨i, s, hy⟩, heq⟩
  have original_block (o : PeriodicSubtileIndex) (c : GaussianInt)
      (hc : c ∈ (occurrence o).cells) :
      c ∈ (TileTranslation bundle.normalizedFixed
        ((o.first : GaussianInt) * cert.u + (o.second : GaussianInt) * cert.v)).cells := by
    rcases o with ⟨label, r, s⟩
    cases label with
    | A => exact parent_cells 0 true _ c hc
    | B => exact parent_cells 0 false _ c hc
    | C => exact parent_cells 1 true _ c hc
    | D => exact parent_cells 1 false _ c hc
    | E => exact parent_cells 2 true _ c hc
    | F => exact parent_cells 2 false _ c hc
  have block_disjoint (o : PeriodicSubtileIndex)
      (hcoord : (o.first, o.second) ≠ (m, n)) :
      Disjoint (occurrence o).cells otherTile.cells := by
    have hblocks := (BandOrderedGeneralPeriodicBlockCells q bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed cert).2
      o.first o.second m n hcoord
    rw [Finset.disjoint_left]
    intro c hc ho
    apply Finset.disjoint_left.mp hblocks (original_block o c hc)
    change c ∈ (TileTranslation bundle.normalizedFixed _).cells at ho
    rwa [coordinates.1] at ho
  have other_lattice : LatticeTile otherTile :=
    (TileDiskAreaCovariance bundle.normalizedFixed _).1.mp bundle.fixed_lattice
  have not_other : bundle.normalizedPoint ∉ FootprintVertices otherTile :=
    P5485T1RoutedInterfaceAvoidance _ _ _ _ otherTile data
      (LatticeTileGridStructure otherTile other_lattice).1.1
      (block_disjoint _ coordinates.2.1)
      (block_disjoint _ coordinates.2.2.1)
      (block_disjoint _ coordinates.2.2.2.1)
      (block_disjoint _ coordinates.2.2.2.2)
      bundle.normalizedPoint bundle.routedDirection selectedEdge hx hedge
      placement.exterior_routed_cell placement.central_routed_cell
  let oldRight := TileTranslation bundle.normalizedFixed
    ((if placement.rightNeighborPositive = true then (-1 : GaussianInt) else 1) *
      BandVectors.1 (q 0) (q bundle.selectedSlot.succ))
  have finish (U V : ProtoTile)
      (eU : ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed U)
      (eV : ExactTileInterfaceTriple bundle.normalizedRoot bundle.normalizedFixed V)
      (hU : U = oldRight) (hV : V = otherTile)
      (hUl : LatticeTile U)
      (hTU : Disjoint bundle.normalizedRoot.cells U.cells)
      (hNU : Disjoint bundle.normalizedFixed.cells U.cells)
      (ht : TouchingTriple bundle.normalizedRoot bundle.normalizedFixed U)
      (hcross : eU.otherAB = eV.point) :
      (¬ (∀ z, z = bundle.normalizedPoint ∨
          z = bundle.normalizedPoint - 1 ∨
          z = bundle.normalizedPoint - ⟨0, 1⟩ ∨
          z = bundle.normalizedPoint - 1 - ⟨0, 1⟩ →
        z ∈ bundle.normalizedRoot.cells ∨ z ∈ bundle.normalizedFixed.cells) ↔
        bundle.normalizedPoint ∈ FootprintVertices oldRight) := by
    have hother : bundle.normalizedPoint ≠ eU.otherAB := by
      intro he
      have hcommon := (eV.unique_common bundle.normalizedPoint).2 (he.trans hcross)
      exact not_other (hV ▸ hcommon.2)
    simpa only [hU] using P5485T1FullInterfaceMarking
      bundle.normalizedRoot bundle.normalizedFixed U eU
      bundle.root_lattice bundle.fixed_lattice hUl bundle.root_fixed_disjoint
      hTU hNU ht bundle.normalizedPoint bundle.edgeAtPoint hother
  have slots_ne : placement.rightFirstSlot ≠ placement.rightSecondSlot := by
    rcases placement.right_slots_cyclic with ⟨hi, hj, _⟩ | ⟨hi, hj, _⟩ | ⟨hi, hj, _⟩
    all_goals simp [hi, hj]
  have geometry := BandOrderedGeneralRightSelectedRowGeometry C D T N h k x
    bundle placement selectedEdge hx hedge row
  rcases geometry with ⟨hp, hs, hsign, hg⟩ | ⟨hp, hs, hsign, hg⟩ |
    ⟨hp, hs, hsign, hg⟩ | ⟨hp, hs, hsign, hg⟩
  all_goals rcases hg with ⟨fb, sb, fd, sd, _, _, _, _, hl1, hl2,
    hd1, hd2, hd3, hd4, _, ht1, ht2, _, hc1, hc2, _⟩
  · exact finish _ _ fd sd (by simp [oldRight, hp, hs, q])
      (by simp [otherTile, other, hp, hs, q]) hl1 hd1 hd2 ht1 hc1.symm
  · exact finish _ _ sd fd (by simp [oldRight, hp, hs, q])
      (by simp [otherTile, other, hp, hs, Ne.symm slots_ne, q]) hl2 hd3 hd4 ht2 hc2
  · exact finish _ _ fd sd (by simp [oldRight, hp, hs, q])
      (by simp [otherTile, other, hp, hs, q]) hl1 hd1 hd2 ht1 hc1.symm
  · exact finish _ _ sd fd (by simp [oldRight, hp, hs, q])
      (by simp [otherTile, other, hp, hs, Ne.symm slots_ne, q]) hl2 hd3 hd4 ht2 hc2

end ApollonianSuperharmonic

end
