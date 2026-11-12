/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3996T1SRowTable
public import LeanPool.ApollonianSuperharmonic.P3045T1RightBoundaryDisplacementAlgebra
public import LeanPool.ApollonianSuperharmonic.P3055T1ParentVectorNormalForms
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralNormalizedOccurrenceBundle
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction

-- [TABLET NODE: P3996T1PlacementCompanionBlocks]

/-!
# P3996T1PlacementCompanionBlocks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PlacementCompanionGeometry

private theorem area_of_band :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (V : ProtoTile), BandPrototile c V → TileArea V = Int.toNat
            c.1 ) := by
  classical
  intro c V hV
  cases hV with
  | line w x hw => simp [TileArea]
  | unit z x anchor => simp [TileArea]
  | @decompose q hq S T hS hcells hfoot hcentroid =>
      exact (BandTileSimultaneousInduction q hq V
        (BandPrototile.decompose hq hS hcells hfoot hcentroid)).2.1

private theorem area_cells :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (W : ProtoTile), (V.cells = W.cells) → (TileArea V = TileArea W) )
            := by
  classical
  intro V W hc
  simp [TileArea, hc]

private theorem selected_area :
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
        (∀ (V : ProtoTile), ∀ (d : GaussianInt), TileArea (TileTranslation V d) = TileArea V) →
            ((∀ (V : ProtoTile), ∀ (W : ProtoTile), (V.cells = W.cells) → (TileArea V = TileArea
            W)) → (TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) =
            TileArea (occurrence placement.exteriorIndex))) ) := by
  classical
  intro C D T N h k x bundle placement occurrence area_translation area_cells
  have first_area (hi : bundle.selectedSlot = placement.rightFirstSlot)
      (he : bundle.selectedSign = placement.firstBoundarySign) :
      TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) =
        TileArea (occurrence placement.exteriorIndex) := by
    have hP : placement.layout.P bundle.selectedSlot bundle.selectedSign =
        placement.layout.P placement.rightFirstSlot placement.firstBoundarySign :=
      congrArg₂ placement.layout.P hi he
    have hpiece : bundle.pieces bundle.selectedSlot bundle.selectedSign =
        bundle.pieces placement.rightFirstSlot placement.firstBoundarySign :=
      congrArg₂ bundle.pieces hi he
    calc
      TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) =
          TileArea (placement.layout.P placement.rightFirstSlot placement.firstBoundarySign) :=
            congrArg TileArea hP
      _ = TileArea (bundle.pieces bundle.selectedSlot bundle.selectedSign) := by
            calc
              _ = TileArea (TileTranslation
                  (placement.layout.P placement.rightFirstSlot placement.firstBoundarySign)
                  placement.rightNeighborDisplacement) := (area_translation _ _).symm
              _ = TileArea (bundle.pieces placement.rightFirstSlot placement.firstBoundarySign) :=
                    area_cells _ _ placement.first_boundary_cells.symm
              _ = _ := congrArg TileArea hpiece.symm
      _ = TileArea (occurrence placement.exteriorIndex) := by
            apply area_cells
            exact placement.selected_exterior_cells
  have second_area (hi : bundle.selectedSlot = placement.rightSecondSlot)
      (he : bundle.selectedSign = placement.secondBoundarySign) :
      TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) =
        TileArea (occurrence placement.exteriorIndex) := by
    have hP : placement.layout.P bundle.selectedSlot bundle.selectedSign =
        placement.layout.P placement.rightSecondSlot placement.secondBoundarySign :=
      congrArg₂ placement.layout.P hi he
    have hpiece : bundle.pieces bundle.selectedSlot bundle.selectedSign =
        bundle.pieces placement.rightSecondSlot placement.secondBoundarySign :=
      congrArg₂ bundle.pieces hi he
    calc
      TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) =
          TileArea (placement.layout.P placement.rightSecondSlot placement.secondBoundarySign) :=
            congrArg TileArea hP
      _ = TileArea (bundle.pieces bundle.selectedSlot bundle.selectedSign) := by
            calc
              _ = TileArea (TileTranslation
                  (placement.layout.P placement.rightSecondSlot placement.secondBoundarySign)
                  placement.rightNeighborDisplacement) := (area_translation _ _).symm
              _ = TileArea (bundle.pieces placement.rightSecondSlot
                  placement.secondBoundarySign) :=
                    area_cells _ _ placement.second_boundary_cells.symm
              _ = _ := congrArg TileArea hpiece.symm
      _ = TileArea (occurrence placement.exteriorIndex) := by
            apply area_cells
            exact placement.selected_exterior_cells
  rcases placement.selected_boundary_piece with ⟨hi, he⟩ | ⟨hi, he⟩
  · exact first_area hi he
  · exact second_area hi he

private theorem occurrence_area :
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
            bundle.routedDirection), (∀ (c : CircleCoordinates), ∀ (V : ProtoTile), BandPrototile
            c V → TileArea V = Int.toNat c.1) → (
        let occurrence := SubtileOccurrenceInterpretation placement.layout.P
          placement.layout.u placement.layout.v
        (∀ (V : ProtoTile), ∀ (d : GaussianInt), TileArea (TileTranslation V d) = TileArea V) →
            (∀ (idx : PeriodicSubtileIndex), TileArea (occurrence idx) = Int.toNat
            (bundle.normalizedPresentation (match idx.label with
              | .A | .B => (0 : Fin 3).succ
              | .C | .D => (1 : Fin 3).succ
              | .E | .F => (2 : Fin 3).succ)).1)) ) := by
  classical
  intro C D T N h k x bundle placement area_of_band occurrence area_translation idx
  have base_area (i : Fin 3) (s : Bool) (d : GaussianInt) :
      TileArea (TileTranslation (placement.layout.P i s) d) =
        Int.toNat (bundle.normalizedPresentation i.succ).1 := by
    rw [area_translation]
    exact area_of_band _ _ (placement.layout.outer_occurrence i s).1
  cases idx with
  | mk label m n =>
    cases label <;> simp [occurrence, SubtileOccurrenceInterpretation, base_area]

private theorem positive_parent :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection) → (∀ (i : Fin 3), 0 < (bundle.normalizedPresentation
            i.succ).1) ) := by
  classical
  intro C D T N h k x bundle placement i
  have hn := (ProperBandCurvatureStructure bundle.normalizedPresentation
    bundle.configuration.proper).2.1 i
  have hne := bundle.configuration.noLine i.succ
  omega

private theorem strict_parent23 :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (bundle.normalizedPresentation 3).1 < (bundle.normalizedPresentation 2).1 ) := by
  classical
  intro C D T N h k x bundle
  have h := bundle.configuration.secondProper.2 (0 : Fin 3)
  simpa [bundle.configuration.secondChild,
    bundle.configuration.secondParentOne] using h

private theorem slot_of_count :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
            (BandOrderedGeneralRightPlacement bundle.normalizedPresentation bundle.configuration
            bundle.normalizedCircle bundle.normalizedRoot bundle.normalizedFixed
            bundle.normalizedRootFunction bundle.normalizedFixedFunction bundle.normalizedPoint
            bundle.pieces bundle.functions bundle.selectedSlot bundle.selectedSign
            bundle.routedDirection) → ((PeriodicSubtileIndex) → ((∀ (i : Fin 3), 0 <
            (bundle.normalizedPresentation i.succ).1) → (((bundle.normalizedPresentation 2).1 <
            (bundle.normalizedPresentation 1).1) → (((bundle.normalizedPresentation 3).1 <
            (bundle.normalizedPresentation 2).1) → (∀ (s : Fin 3), ∀ (i : Fin 3), (Int.toNat
            (bundle.normalizedPresentation s.succ).1 =
            Int.toNat (bundle.normalizedPresentation i.succ).1) → (s = i)))))) ) := by
  classical
  intro C D T N h k x bundle placement a positive_parent strict_parent12 strict_parent23 s i hcount
  have hn12 : Int.toNat (bundle.normalizedPresentation 2).1 <
      Int.toNat (bundle.normalizedPresentation 1).1 :=
    (Int.toNat_lt_toNat (positive_parent 0)).2 strict_parent12
  have hn23 : Int.toNat (bundle.normalizedPresentation 3).1 <
      Int.toNat (bundle.normalizedPresentation 2).1 :=
    (Int.toNat_lt_toNat (positive_parent 1)).2 strict_parent23
  fin_cases s <;> fin_cases i <;> simp_all <;> omega

private theorem slot_of_exterior :
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
            bundle.routedDirection), (∀ (c : CircleCoordinates), ∀ (V : ProtoTile), BandPrototile
            c V → TileArea V = Int.toNat c.1) → (
        let occurrence := SubtileOccurrenceInterpretation placement.layout.P
          placement.layout.u placement.layout.v
        (TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) = TileArea
            (occurrence placement.exteriorIndex)) → ((∀ (s : Fin 3), ∀ (i : Fin 3), (Int.toNat
            (bundle.normalizedPresentation s.succ).1 = Int.toNat (bundle.normalizedPresentation
            i.succ).1) → (s = i)) → (∀ (i : Fin 3), (TileArea (occurrence placement.exteriorIndex) =
            Int.toNat (bundle.normalizedPresentation i.succ).1) → (bundle.selectedSlot = i)))) )
                := by
  classical
  intro C D T N h k x bundle placement area_of_band occurrence selected_area slot_of_count i harea
  apply slot_of_count bundle.selectedSlot i
  calc
    Int.toNat (bundle.normalizedPresentation bundle.selectedSlot.succ).1 =
        TileArea (placement.layout.P bundle.selectedSlot bundle.selectedSign) :=
          (area_of_band _ _
            (placement.layout.outer_occurrence bundle.selectedSlot bundle.selectedSign).1).symm
    _ = TileArea (occurrence placement.exteriorIndex) := selected_area
    _ = Int.toNat (bundle.normalizedPresentation i.succ).1 := harea

private theorem exterior_area :
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
        (∀ (idx : PeriodicSubtileIndex), TileArea (occurrence idx) = Int.toNat
            (bundle.normalizedPresentation (match idx.label with
              | .A | .B => (0 : Fin 3).succ
              | .C | .D => (1 : Fin 3).succ
              | .E | .F => (2 : Fin 3).succ)).1) → (
        let exteriorSlot : Fin 3 :=
          match placement.exteriorIndex.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        TileArea (occurrence placement.exteriorIndex) = Int.toNat (bundle.normalizedPresentation
            exteriorSlot.succ).1) ) := by
  classical
  intro C D T N h k x bundle placement occurrence occurrence_area exteriorSlot
  rw [occurrence_area]
  cases he : placement.exteriorIndex.label <;> simp [exteriorSlot, he]

private theorem selected_center :
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
        let pieceOffset : Real × Real :=
          GaussianRealPoint
              (BandVectors.1
                (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
                (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ))) -
            (-((GaussianRealPoint
                (BandVectors.1
                  (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
                  (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ)))).2),
              (GaussianRealPoint
                (BandVectors.1
                  (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
                  (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ)))).1)
        TileCentroid (occurrence placement.exteriorIndex) - TileCentroid bundle.normalizedFixed =
            (if bundle.selectedSign = true then (1 : Real) else -1) • ((1 / 2 : Real) •
            pieceOffset) + GaussianRealPoint placement.rightNeighborDisplacement ) := by
  classical
  intro C D T N h k x bundle placement occurrence pieceOffset
  obtain ⟨_, _, _, _, hoccCent⟩ :=
    ProtoTileObservableExtensionality (bundle.pieces bundle.selectedSlot
      bundle.selectedSign) (occurrence placement.exteriorIndex)
      placement.selected_exterior_cells placement.selected_exterior_empty_anchor
  obtain ⟨_, _, _, _, hrootCent⟩ :=
    ProtoTileObservableExtensionality bundle.normalizedRoot
      (TileTranslation bundle.normalizedFixed placement.rightNeighborDisplacement)
      placement.right_neighbor_cells placement.right_neighbor_empty_anchor
  calc
    _ = TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) -
          TileCentroid bundle.normalizedFixed := by rw [hoccCent]
    _ = (TileCentroid (bundle.pieces bundle.selectedSlot bundle.selectedSign) -
          TileCentroid bundle.normalizedRoot) +
          (TileCentroid bundle.normalizedRoot -
            TileCentroid bundle.normalizedFixed) := by
          ext <;> dsimp <;> ring
    _ = (if bundle.selectedSign = true then (1 : Real) else -1) •
          ((1 / 2 : Real) • pieceOffset) +
          GaussianRealPoint placement.rightNeighborDisplacement := by
          rw [bundle.piece_centroid]
          rw [hrootCent, (TileTranslationFormulas bundle.normalizedFixed
            placement.rightNeighborDisplacement).2.2.2.2.1]
          ext <;> dsimp [pieceOffset, GaussianRealPoint, sub_eq_add_neg] <;> ring

private theorem incoming_nonzero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), (∀ (i : Fin 3), 0 <
            (bundle.normalizedPresentation i.succ).1) → (∀ (i : Fin 3), BandVectors.1
            (bundle.normalizedPresentation i.succ) (bundle.normalizedPresentation 0) ≠ 0) ) := by
  classical
  intro C D T N h k x bundle positive_parent i
  have hij : i.succ ≠ (0 : Fin 4) := by
    fin_cases i <;> decide
  apply VectorNonvanishing bundle.normalizedPresentation
    bundle.configuration.proper.1 i.succ 0 hij
  exact Or.inl (positive_parent i)

private theorem flip_incoming :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), ∀ (i : Fin 3),
            BandVectors.1 (bundle.normalizedPresentation 0) (bundle.normalizedPresentation
            i.succ) = (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (bundle.normalizedPresentation
            i.succ) (bundle.normalizedPresentation 0) ) := by
  classical
  intro C D T N h k x bundle i
  exact (VectorRecursionLaws bundle.normalizedPresentation
    bundle.configuration.proper.1).2.2.2.2 bundle.configuration.proper i |>.1

private theorem realPoint_injective :
    (by
      classical
      exact
        Function.Injective GaussianRealPoint ) := by
  classical
  intro v w h
  apply Zsqrtd.ext
  · have h' := congrArg Prod.fst h
    dsimp [GaussianRealPoint] at h'
    exact_mod_cast h'
  · have h' := congrArg Prod.snd h
    dsimp [GaussianRealPoint] at h'
    exact_mod_cast h'

private theorem branchDisplacement_nonzero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), (∀ (i : Fin 3),
            BandVectors.1 (bundle.normalizedPresentation i.succ) (bundle.normalizedPresentation
            0) ≠ 0) → ((Function.Injective GaussianRealPoint) → (
        let I : GaussianInt := ⟨0, 1⟩
        let branchDisplacement (i : Fin 3) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
            BandVectors.1 (bundle.normalizedPresentation i.succ)
              (bundle.normalizedPresentation 0))
        ∀ (i : Fin 3), branchDisplacement i ≠ (0, 0))) ) := by
  classical
  intro C D T N h k x bundle incoming_nonzero realPoint_injective I branchDisplacement i hzero
  have hpoint : GaussianRealPoint ((I - 1) *
      BandVectors.1 (bundle.normalizedPresentation i.succ)
        (bundle.normalizedPresentation 0)) = (0, 0) := by
    have h' := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact h'
  have hpoint0 : GaussianRealPoint (0 : GaussianInt) = (0, 0) := by
    ext <;> simp [GaussianRealPoint]
  have hmul := realPoint_injective
    (hpoint.trans hpoint0.symm)
  have hI : I - 1 ≠ (0 : GaussianInt) := by
    intro hz
    have := congrArg (fun z : GaussianInt => z.im) hz
    norm_num [I] at this
  exact (mul_ne_zero hI (incoming_nonzero i)) hmul

private theorem four_centers_distinct :
    (by
      classical
      exact
        let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
        let branchCenter (E : Real × Real) (b : Fin 4) : Real × Real :=
          if b = 0 then -E
          else if b = 1 then quarterTurn E
          else if b = 2 then E
          else -quarterTurn E
        ∀ (E : Real × Real), (E ≠ (0, 0)) → (∀ (b : Fin 4), ∀ (c : Fin 4), (b ≠ c) →
            (branchCenter E b ≠ branchCenter E c)) ) := by
  classical
  intro quarterTurn branchCenter E hE b c hbc heq
  fin_cases b <;> fin_cases c
  all_goals
    first
    | exact (hbc rfl).elim
    | simp only [branchCenter, quarterTurn] at heq
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      have hzero : E = (0, 0) := by
        apply Prod.ext
        · dsimp at hx hy ⊢
          linarith
        · dsimp at hx hy ⊢
          linarith
      exact hE hzero

private theorem cancel2 :
    (by
      classical
      exact
        ∀ (p : Real × Real), ∀ (q : Real × Real), ((2 : Real) • p = (2 : Real) • q) → (p = q) )
            := by
  classical
  intro p q h
  have h' := congrArg (fun v : Real × Real => (1 / 2 : Real) • v) h
  rw [smul_smul, smul_smul] at h'
  norm_num at h'
  exact h'

private theorem centerAlgFirst :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let edgeCenter (a : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) * a)
        (∀ (p : Real × Real), ∀ (q : Real × Real), ((2 : Real) • p = (2 : Real) • q) → (p = q)) →
            (∀ (e : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (b = I * a) → (((1 - I) * e + 2 * d = -I * (a + b)) → (cOff e + GaussianRealPoint d =
            -edgeCenter a))) ) := by
  classical
  intro I cOff edgeCenter cancel2 e d a b hflip halg
  have hI2 : I * I = -1 := by ext <;> norm_num [I]
  have hNegI2 : -I * I = 1 := by
    rw [neg_mul, hI2]
    norm_num
  have hvec : (1 - I) * e + 2 * d = (1 - I) * a := by
    rw [halg, hflip]
    have hcoef : -I * (1 + I) = 1 - I := by
      calc
        -I * (1 + I) = -I + -I * I := by rw [mul_add, mul_one]
        _ = 1 - I := by rw [hNegI2]; ring
    calc
      -I * (a + I * a) = (-I * (1 + I)) * a := by ring
      _ = _ := by rw [hcoef]
  have hleft : (2 : Real) • (cOff e + GaussianRealPoint d) =
      GaussianRealPoint ((1 - I) * e + 2 * d) := by
    apply Prod.ext <;>
      norm_num [cOff, GaussianRealPoint, I, Prod.smul_mk,
        Prod.add_def, Prod.sub_def] <;> ring
  have hright : GaussianRealPoint ((1 - I) * a) =
      (2 : Real) • (-edgeCenter a) := by
    apply Prod.ext <;>
      norm_num [edgeCenter, GaussianRealPoint, I, Prod.smul_mk] <;> ring
  have hreal := congrArg GaussianRealPoint hvec
  exact cancel2 _ _ (hleft.trans (hreal.trans hright))

private theorem centerAlgSecond :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let edgeCenter (a : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) * a)
        (∀ (p : Real × Real), ∀ (q : Real × Real), ((2 : Real) • p = (2 : Real) • q) → (p = q)) →
            (∀ (e : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (b = I * a) → ((-(1 - I) * e + 2 * d = -(a + b)) → (-cOff e + GaussianRealPoint d =
            quarterTurn (edgeCenter a)))) ) := by
  classical
  intro I quarterTurn cOff edgeCenter cancel2 e d a b hflip halg
  have hvec : -(1 - I) * e + 2 * d = -(1 + I) * a := by
    rw [halg, hflip]
    ring
  have hleft : (2 : Real) • (-cOff e + GaussianRealPoint d) =
      GaussianRealPoint (-(1 - I) * e + 2 * d) := by
    apply Prod.ext <;>
      norm_num [cOff, GaussianRealPoint, I, Prod.smul_mk,
        Prod.add_def, Prod.sub_def] <;> ring
  have hright : GaussianRealPoint (-(1 + I) * a) =
      (2 : Real) • quarterTurn (edgeCenter a) := by
    apply Prod.ext <;>
      norm_num [edgeCenter, GaussianRealPoint, I, quarterTurn, Prod.smul_mk] <;> ring
  have hreal := congrArg GaussianRealPoint hvec
  exact cancel2 _ _ (hleft.trans (hreal.trans hright))

private theorem gp_neg_any :
    (by
      classical
      exact
        ∀ (g : GaussianInt), GaussianRealPoint (-g) = -GaussianRealPoint g ) := by
  classical
  intro g
  ext <;> simp [GaussianRealPoint]

private theorem first_center :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x), (∀ (i : Fin 3),
            BandVectors.1 (bundle.normalizedPresentation 0) (bundle.normalizedPresentation
            i.succ) = (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (bundle.normalizedPresentation
            i.succ) (bundle.normalizedPresentation 0)) → (
        let I : GaussianInt := ⟨0, 1⟩
        let branchDisplacement (i : Fin 3) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
            BandVectors.1 (bundle.normalizedPresentation i.succ)
              (bundle.normalizedPresentation 0))
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let edgeCenter (a : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) * a)
        (∀ (e : GaussianInt), ∀ (d : GaussianInt), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (b =
            I * a) → (((1 - I) * e + 2 * d = -I * (a + b)) → (cOff e + GaussianRealPoint d =
            -edgeCenter a))) → (
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        ∀ (i : Fin 3), d i + GaussianRealPoint (o (i + 2)) = -branchDisplacement i)) ) := by
  classical
  intro C D T N h k x bundle flip_incoming I branchDisplacement cOff edgeCenter centerAlgFirst q
      o e d i
  have hcyc : (i = 0 ∧ i + 1 = 1 ∧ i + 2 = 2) ∨
      (i = 1 ∧ i + 1 = 2 ∧ i + 2 = 0) ∨
      (i = 2 ∧ i + 1 = 0 ∧ i + 2 = 1) := by
    fin_cases i <;> decide
  have halg := (P3045T1RightBoundaryDisplacementAlgebra q
    bundle.configuration.proper i (i + 1) (i + 2) hcyc).1
  exact centerAlgFirst _ _ _ _ (flip_incoming i) halg

private theorem cyclic_slots :
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
            bundle.routedDirection), placement.rightSecondSlot = placement.rightFirstSlot + 1 ∧
            placement.rightDirectionSlot = placement.rightFirstSlot + 2 ∧
            placement.rightFirstSlot = placement.rightSecondSlot + 2 ∧
            placement.rightDirectionSlot = placement.rightSecondSlot + 1 ) := by
  classical
  intro C D T N h k x bundle placement
  rcases placement.right_slots_cyclic with ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩ | ⟨hr, ht, hk⟩
  all_goals simp [hr, ht, hk]

private theorem displacement :
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
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        placement.rightNeighborDisplacement = if placement.rightNeighborPositive = true then o
            placement.rightDirectionSlot else -o placement.rightDirectionSlot ) := by
  classical
  intro C D T N h k x bundle placement q o
  rw [placement.right_neighbor_displacement]
  split_ifs <;> simp [o, q]

private theorem placement_centers :
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
        let I : GaussianInt := ⟨0, 1⟩
        let branchDisplacement (i : Fin 3) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
            BandVectors.1 (bundle.normalizedPresentation i.succ)
              (bundle.normalizedPresentation 0))
        let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
        let branchCenter (E : Real × Real) (b : Fin 4) : Real × Real :=
          if b = 0 then -E
          else if b = 1 then quarterTurn E
          else if b = 2 then E
          else -quarterTurn E
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (g : GaussianInt), GaussianRealPoint (-g) = -GaussianRealPoint g) → (
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        (∀ (i : Fin 3), d i + GaussianRealPoint (o (i + 2)) = -branchDisplacement i) → ((∀ (i :
            Fin 3), -d i + GaussianRealPoint (o (i + 1)) = quarterTurn (branchDisplacement i)) → (
        let exteriorCenter := TileCentroid (occurrence placement.exteriorIndex) -
          TileCentroid bundle.normalizedFixed
        (exteriorCenter = (if bundle.selectedSign = true then (1 : Real) else -1) • d
            bundle.selectedSlot + GaussianRealPoint placement.rightNeighborDisplacement) →
            ((placement.rightSecondSlot = placement.rightFirstSlot + 1 ∧
            placement.rightDirectionSlot = placement.rightFirstSlot + 2 ∧
            placement.rightFirstSlot = placement.rightSecondSlot + 2 ∧
            placement.rightDirectionSlot = placement.rightSecondSlot + 1) →
            ((placement.rightNeighborDisplacement = if placement.rightNeighborPositive = true
            then o placement.rightDirectionSlot else -o placement.rightDirectionSlot) →
            ((placement.rightNeighborPositive = true ∧ bundle.selectedSlot =
            placement.rightFirstSlot ∧ bundle.selectedSign = true → exteriorCenter = branchCenter
            (branchDisplacement bundle.selectedSlot) 0) ∧ (placement.rightNeighborPositive = true
            ∧ bundle.selectedSlot = placement.rightSecondSlot ∧ bundle.selectedSign = false →
            exteriorCenter = branchCenter (branchDisplacement bundle.selectedSlot) 1) ∧
            (placement.rightNeighborPositive = false ∧ bundle.selectedSlot =
            placement.rightFirstSlot ∧ bundle.selectedSign = false → exteriorCenter =
            branchCenter (branchDisplacement bundle.selectedSlot) 2) ∧
            (placement.rightNeighborPositive = false ∧ bundle.selectedSlot =
            placement.rightSecondSlot ∧ bundle.selectedSign = true → exteriorCenter =
            branchCenter (branchDisplacement bundle.selectedSlot) 3))))))) ) := by
  classical
  intro C D T N h k x bundle placement occurrence I branchDisplacement quarterTurn branchCenter
      cOff gp_neg_any q o e d first_center second_center exteriorCenter placement_center
      cyclic_slots displacement
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨hp, hi, hs⟩
    change exteriorCenter = -branchDisplacement bundle.selectedSlot
    rw [placement_center, displacement]
    simpa only [hs, hp, ite_true, one_smul, hi, cyclic_slots.2.1] using
      first_center placement.rightFirstSlot
  · rintro ⟨hp, hi, hs⟩
    change exteriorCenter = quarterTurn (branchDisplacement bundle.selectedSlot)
    rw [placement_center, displacement]
    simpa only [hs, hp, Bool.false_eq_true, ite_false, ite_true, neg_one_smul, hi,
      cyclic_slots.2.2.2] using
      second_center placement.rightSecondSlot
  · rintro ⟨hp, hi, hs⟩
    change exteriorCenter = branchDisplacement bundle.selectedSlot
    rw [placement_center, displacement]
    simp only [hs, hp, Bool.false_eq_true, ite_false, neg_one_smul, hi,
      cyclic_slots.2.1, gp_neg_any]
    calc
      _ = -(d placement.rightFirstSlot +
        GaussianRealPoint (o (placement.rightFirstSlot + 2))) := by abel
      _ = _ := by rw [first_center, neg_neg]
  · rintro ⟨hp, hi, hs⟩
    change exteriorCenter = -quarterTurn (branchDisplacement bundle.selectedSlot)
    rw [placement_center, displacement]
    simp only [hs, hp, Bool.false_eq_true, ite_false, ite_true, one_smul, hi,
      cyclic_slots.2.2.2, gp_neg_any]
    calc
      _ = -(-d placement.rightSecondSlot +
        GaussianRealPoint (o (placement.rightSecondSlot + 1))) := by abel
      _ = _ := by rw [second_center]

private theorem third_period :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        o 2 = -o 0 - o 1 ) := by
  classical
  intro C D T N h k x bundle q o
  obtain ⟨_, _, _, _, h1, h2, h3, _⟩ :=
    P3055T1ParentVectorNormalForms q bundle.configuration
  change BandVectors.1 (q 0) (q 3) =
    -BandVectors.1 (q 0) (q 1) - BandVectors.1 (q 0) (q 2)
  rw [h1, h2, h3]
  ring

private theorem gp_add :
    (by
      classical
      exact
        ∀ (v : GaussianInt), ∀ (w : GaussianInt), GaussianRealPoint (v + w) = GaussianRealPoint v
            + GaussianRealPoint w ) := by
  classical
  intro v w
  ext <;> simp [GaussianRealPoint]

private theorem parent_center :
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
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let q := bundle.normalizedPresentation
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        ∀ (i : Fin 3), ∀ (s : Bool), TileCentroid (placement.layout.P i s) = TileCentroid
            bundle.normalizedFixed + (if s = true then (1 : Real) else -1) • d i ) := by
  classical
  intro C D T N h k x bundle placement cOff q e d i s
  have hp : TileCentroid (placement.layout.P i s) - TileCentroid bundle.normalizedFixed =
      (if s = true then (1 : Real) else -1) • d i :=
    (placement.layout.outer_occurrence i s).2.2
  rw [sub_eq_iff_eq_add] at hp
  exact hp.trans (add_comm _ _)

private theorem occurrence_center :
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
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let q := bundle.normalizedPresentation
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        (∀ (i : Fin 3), ∀ (s : Bool), TileCentroid (placement.layout.P i s) = TileCentroid
            bundle.normalizedFixed + (if s = true then (1 : Real) else -1) • d i) → ((∀ (V :
            ProtoTile), ∀ (w : GaussianInt), TileCentroid (TileTranslation V w) = TileCentroid V
            + GaussianRealPoint w) → (∀ (idx : PeriodicSubtileIndex), TileCentroid (occurrence
            idx) - TileCentroid bundle.normalizedFixed = (match idx.label with
              | .A => d 0
              | .B => -d 0
              | .C => d 1
              | .D => -d 1
              | .E => d 2
              | .F => -d 2) + GaussianRealPoint
            ((idx.first : GaussianInt) * placement.layout.u + (idx.second : GaussianInt) *
            placement.layout.v))) ) := by
  classical
  intro C D T N h k x bundle placement occurrence cOff q e d parent_center translate_center idx
  rcases idx with ⟨label, m, n⟩
  cases label <;>
    simp only [occurrence, SubtileOccurrenceInterpretation, translate_center,
      parent_center, Bool.false_eq_true, ite_false, ite_true, one_smul, neg_one_smul]
  all_goals abel

private theorem raw_centers :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (D : BandCircle), ∀ (T : ProtoTile), ∀ (N : ProtoTile), ∀ (h :
            PartialOdometer), ∀ (k : PartialOdometer), ∀ (x : GaussianInt), ∀ (bundle :
            BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x),
        let I : GaussianInt := ⟨0, 1⟩
        let branchDisplacement (i : Fin 3) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
            BandVectors.1 (bundle.normalizedPresentation i.succ)
              (bundle.normalizedPresentation 0))
        let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
        let branchCenter (E : Real × Real) (b : Fin 4) : Real × Real :=
          if b = 0 then -E
          else if b = 1 then quarterTurn E
          else if b = 2 then E
          else -quarterTurn E
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        (∀ (i : Fin 3), d i + GaussianRealPoint (o (i + 2)) = -branchDisplacement i) → ((∀ (i :
            Fin 3), -d i + GaussianRealPoint (o (i + 1)) = quarterTurn (branchDisplacement i)) →
            (∀ (i : Fin 3), (d i + GaussianRealPoint (o (i + 2)) = branchCenter
            (branchDisplacement i) 0) ∧ (-d i + GaussianRealPoint (o (i + 1)) = branchCenter
            (branchDisplacement i) 1) ∧ (-d i - GaussianRealPoint (o (i + 2)) = branchCenter
            (branchDisplacement i) 2) ∧ (d i - GaussianRealPoint (o (i + 1)) = branchCenter
            (branchDisplacement i) 3))) ) := by
  classical
  intro C D T N h k x bundle I branchDisplacement quarterTurn branchCenter cOff q o e d
      first_center second_center i
  refine ⟨first_center i, second_center i, ?_, ?_⟩
  · change -d i - GaussianRealPoint (o (i + 2)) = branchDisplacement i
    calc
      _ = -(d i + GaussianRealPoint (o (i + 2))) := by abel
      _ = _ := by rw [first_center, neg_neg]
  · change d i - GaussianRealPoint (o (i + 1)) =
      -quarterTurn (branchDisplacement i)
    calc
      _ = -(-d i + GaussianRealPoint (o (i + 1))) := by abel
      _ = _ := by rw [second_center]

private theorem row_data :
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
            bundle.routedDirection), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            ∀ (row : BandOrderedGeneralSelectedContactRow bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedFixed placement.layout
            a b), (placement.exteriorIndex = a) → ((placement.centralIndex = b) → (∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable bundle.normalizedPresentation
            bundle.configuration bundle.normalizedCircle bundle.normalizedFixed placement.layout
            row = some z) → (
        let occurrence := SubtileOccurrenceInterpretation placement.layout.P
          placement.layout.u placement.layout.v
        let exteriorSlot : Fin 3 :=
          match placement.exteriorIndex.label with
          | .A | .B => 0
          | .C | .D => 1
          | .E | .F => 2
        (bundle.selectedSlot = exteriorSlot) → (
        let I : GaussianInt := ⟨0, 1⟩
        let branchDisplacement (i : Fin 3) : Real × Real :=
          (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
            BandVectors.1 (bundle.normalizedPresentation i.succ)
              (bundle.normalizedPresentation 0))
        let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
        let branchCenter (E : Real × Real) (b : Fin 4) : Real × Real :=
          if b = 0 then -E
          else if b = 1 then quarterTurn E
          else if b = 2 then E
          else -quarterTurn E
        let cOff (w : GaussianInt) : Real × Real :=
          (1 / 2 : Real) • (GaussianRealPoint w -
            (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
        (∀ (g : GaussianInt), GaussianRealPoint (-g) = -GaussianRealPoint g) → (
        let q := bundle.normalizedPresentation
        let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
        let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
        let d (i : Fin 3) := cOff (e i)
        let exteriorCenter := TileCentroid (occurrence placement.exteriorIndex) -
          TileCentroid bundle.normalizedFixed
        (placement.layout.u = o 0) → ((placement.layout.v = o 1) → ((o 2 = -o 0 - o 1) → ((∀ (v :
            GaussianInt), ∀ (w : GaussianInt), GaussianRealPoint (v + w) = GaussianRealPoint v +
            GaussianRealPoint w) → ((∀ (idx : PeriodicSubtileIndex), TileCentroid (occurrence
            idx) - TileCentroid bundle.normalizedFixed = (match idx.label with
              | .A => d 0
              | .B => -d 0
              | .C => d 1
              | .D => -d 1
              | .E => d 2
              | .F => -d 2) + GaussianRealPoint
            ((idx.first : GaussianInt) * placement.layout.u + (idx.second : GaussianInt) *
            placement.layout.v)) → ((∀ (i : Fin 3), (d i + GaussianRealPoint (o (i + 2)) =
            branchCenter (branchDisplacement i) 0) ∧ (-d i + GaussianRealPoint (o (i + 1)) =
            branchCenter (branchDisplacement i) 1) ∧ (-d i - GaussianRealPoint (o (i + 2)) =
            branchCenter (branchDisplacement i) 2) ∧ (d i - GaussianRealPoint (o (i + 1)) =
            branchCenter (branchDisplacement i) 3)) → (∃ n : Fin 4, exteriorCenter = branchCenter
            (branchDisplacement bundle.selectedSlot) n ∧ z.oldShift = if n.val < 2 then -o
            bundle.selectedSlot else o bundle.selectedSlot))))))))))) ) := by
  classical
  intro C D T N h k x bundle placement a b row ha hb z hz occurrence exteriorSlot selected_slot I
      branchDisplacement quarterTurn branchCenter cOff gp_neg_any q o e d exteriorCenter period0
      period1 third_period gp_add occurrence_center raw_centers
  -- Evaluate the twelve literal exterior occurrences using the shared centers.
  cases row <;> simp only [P3996T1SRowTable] at hz <;> cases hz
  case positiveS1 =>
    have hs : bundle.selectedSlot = 0 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨0, ?_, ?_⟩
    · have hc := (raw_centers 0).1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0]
  case positiveS2 =>
    have hs : bundle.selectedSlot = 0 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨3, ?_, ?_⟩
    · have hc := (raw_centers 0).2.2.2
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0]
  case positiveS3 =>
    have hs : bundle.selectedSlot = 1 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨0, ?_, ?_⟩
    · have hc := (raw_centers 1).1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period1]
  case positiveS4 =>
    have hs : bundle.selectedSlot = 1 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨3, ?_, ?_⟩
    · have hc := (raw_centers 1).2.2.2
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      convert hc using 1
      simp [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, Fin.add_def]
      abel
    · simp [hs, period1]
  case positiveS5 =>
    have hs : bundle.selectedSlot = 2 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨0, ?_, ?_⟩
    · have hc := (raw_centers 2).1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0, period1, third_period]
      abel
  case positiveS6 =>
    have hs : bundle.selectedSlot = 2 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨3, ?_, ?_⟩
    · have hc := (raw_centers 2).2.2.2
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0, period1, third_period]
  case reflectedS1 =>
    have hs : bundle.selectedSlot = 0 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨2, ?_, ?_⟩
    · have hc := (raw_centers 0).2.2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      convert hc using 1
      simp [ha, period0, period1, third_period, gp_add, gp_neg_any, sub_eq_add_neg]
      abel
    · simp [hs, period0]
  case reflectedS2 =>
    have hs : bundle.selectedSlot = 0 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨1, ?_, ?_⟩
    · have hc := (raw_centers 0).2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0]
  case reflectedS3 =>
    have hs : bundle.selectedSlot = 1 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨2, ?_, ?_⟩
    · have hc := (raw_centers 1).2.2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period1]
  case reflectedS4 =>
    have hs : bundle.selectedSlot = 1 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨1, ?_, ?_⟩
    · have hc := (raw_centers 1).2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period1]
  case reflectedS5 =>
    have hs : bundle.selectedSlot = 2 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨2, ?_, ?_⟩
    · have hc := (raw_centers 2).2.2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0, period1, third_period]
  case reflectedS6 =>
    have hs : bundle.selectedSlot = 2 := by simpa [exteriorSlot, ha] using selected_slot
    refine ⟨1, ?_, ?_⟩
    · have hc := (raw_centers 2).2.1
      simp only [hs]
      change TileCentroid (occurrence placement.exteriorIndex) -
        TileCentroid bundle.normalizedFixed = _
      rw [occurrence_center]
      simpa [ha, period0, period1, third_period, gp_add, gp_neg_any,
        sub_eq_add_neg, neg_add, Fin.add_def] using hc
    · simp [hs, period0, period1, third_period]
      abel

end PlacementCompanionGeometry

theorem P3996T1PlacementCompanionBlocks
    (C D : BandCircle) (T N : ProtoTile) (h k : PartialOdometer)
    (x : GaussianInt)
    (bundle : BandOrderedGeneralNormalizedOccurrenceBundle C D T N h k x)
    (placement : BandOrderedGeneralRightPlacement bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedRoot
      bundle.normalizedFixed bundle.normalizedRootFunction
      bundle.normalizedFixedFunction bundle.normalizedPoint bundle.pieces
      bundle.functions bundle.selectedSlot bundle.selectedSign bundle.routedDirection)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow bundle.normalizedPresentation
      bundle.configuration bundle.normalizedCircle bundle.normalizedFixed
      placement.layout a b)
    (ha : placement.exteriorIndex = a) (hb : placement.centralIndex = b)
    (z : P3996T1SRowParameters)
    (hz : P3996T1SRowTable bundle.normalizedPresentation bundle.configuration
      bundle.normalizedCircle bundle.normalizedFixed placement.layout row = some z) :
    let q := bundle.normalizedPresentation
    (placement.rightNeighborPositive = true ∧
        bundle.selectedSlot = placement.rightFirstSlot ∧ bundle.selectedSign = true →
      -BandVectors.1 (q 0) (q placement.rightFirstSlot.succ) = z.oldShift) ∧
    (placement.rightNeighborPositive = true ∧
        bundle.selectedSlot = placement.rightSecondSlot ∧ bundle.selectedSign = false →
      -BandVectors.1 (q 0) (q placement.rightSecondSlot.succ) = z.oldShift) ∧
    (placement.rightNeighborPositive = false ∧
        bundle.selectedSlot = placement.rightFirstSlot ∧ bundle.selectedSign = false →
      BandVectors.1 (q 0) (q placement.rightFirstSlot.succ) = z.oldShift) ∧
    (placement.rightNeighborPositive = false ∧
        bundle.selectedSlot = placement.rightSecondSlot ∧ bundle.selectedSign = true →
      BandVectors.1 (q 0) (q placement.rightSecondSlot.succ) = z.oldShift) := by
-- BODY
  classical
  -- Distinct parent areas identify the selected slot without assuming its sign.
  have area_of_band := PlacementCompanionGeometry.area_of_band
  let occurrence := SubtileOccurrenceInterpretation placement.layout.P
    placement.layout.u placement.layout.v
  have area_translation (V : ProtoTile) (d : GaussianInt) :
      TileArea (TileTranslation V d) = TileArea V :=
    (TileDiskAreaCovariance V d).2.2.2.1
  have positive_parent := PlacementCompanionGeometry.positive_parent C D T N h k x bundle placement
  have strict_parent12 :
      (bundle.normalizedPresentation 2).1 <
        (bundle.normalizedPresentation 1).1 := bundle.configuration.order12
  let exteriorSlot : Fin 3 :=
    match placement.exteriorIndex.label with
    | .A | .B => 0
    | .C | .D => 1
    | .E | .F => 2
  have selected_slot : bundle.selectedSlot = exteriorSlot :=
    (PlacementCompanionGeometry.slot_of_exterior C D T N h k x bundle placement area_of_band
        (PlacementCompanionGeometry.selected_area C D T N h k x bundle placement area_translation
        (PlacementCompanionGeometry.area_cells)) (PlacementCompanionGeometry.slot_of_count C D T
        N h k x bundle placement a positive_parent strict_parent12
        (PlacementCompanionGeometry.strict_parent23 C D T N h k x bundle))) exteriorSlot
        (PlacementCompanionGeometry.exterior_area C D T N h k x bundle placement
        (PlacementCompanionGeometry.occurrence_area C D T N h k x bundle placement area_of_band
        area_translation))
  let pieceOffset : Real × Real :=
    GaussianRealPoint
        (BandVectors.1
          (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
          (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ))) -
      (-((GaussianRealPoint
          (BandVectors.1
            (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
            (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ)))).2),
        (GaussianRealPoint
          (BandVectors.1
            (bundle.normalizedPresentation ((bundle.selectedSlot + 2).succ))
            (bundle.normalizedPresentation ((bundle.selectedSlot + 1).succ)))).1)
  have flip_incoming := PlacementCompanionGeometry.flip_incoming C D T N h k x bundle
  let I : GaussianInt := ⟨0, 1⟩
  let branchDisplacement (i : Fin 3) : Real × Real :=
    (1 / 2 : Real) • GaussianRealPoint ((I - 1) *
      BandVectors.1 (bundle.normalizedPresentation i.succ)
        (bundle.normalizedPresentation 0))
  have branchDisplacement_nonzero := PlacementCompanionGeometry.branchDisplacement_nonzero C D T
      N h k x bundle (PlacementCompanionGeometry.incoming_nonzero C D T N h k x bundle
      positive_parent) (PlacementCompanionGeometry.realPoint_injective)
  let quarterTurn (p : Real × Real) : Real × Real := (-p.2, p.1)
  -- The four possible placement centers are distinct at every parent slot.
  let branchCenter (E : Real × Real) (b : Fin 4) : Real × Real :=
    if b = 0 then -E
    else if b = 1 then quarterTurn E
    else if b = 2 then E
    else -quarterTurn E
  have four_centers_distinct := PlacementCompanionGeometry.four_centers_distinct
  let cOff (w : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • (GaussianRealPoint w -
      (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))
  let edgeCenter (a : GaussianInt) : Real × Real :=
    (1 / 2 : Real) • GaussianRealPoint ((I - 1) * a)
  have cancel2 := PlacementCompanionGeometry.cancel2
  have gp_neg_any := PlacementCompanionGeometry.gp_neg_any
  let q := bundle.normalizedPresentation
  let o (i : Fin 3) := BandVectors.1 (q 0) (q i.succ)
  let e (i : Fin 3) := BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let d (i : Fin 3) := cOff (e i)
  have first_center := PlacementCompanionGeometry.first_center C D T N h k x bundle flip_incoming
      (PlacementCompanionGeometry.centerAlgFirst cancel2)
  have second_center := (show
      ∀ (i : Fin 3), -d i + GaussianRealPoint (o (i + 1)) = quarterTurn
      (branchDisplacement i)
    from by
      classical
      intro i
      have hcyc : (i + 2 = 0 ∧ i = 1 ∧ i + 1 = 2) ∨
          (i + 2 = 1 ∧ i = 2 ∧ i + 1 = 0) ∨
          (i + 2 = 2 ∧ i = 0 ∧ i + 1 = 1) := by
        fin_cases i <;> decide
      have halg := (P3045T1RightBoundaryDisplacementAlgebra q
        bundle.configuration.proper (i + 2) i (i + 1) hcyc).2.1
      exact ((PlacementCompanionGeometry.centerAlgSecond cancel2)) _ _ _ _ (flip_incoming i) halg)
  let exteriorCenter := TileCentroid (occurrence placement.exteriorIndex) -
    TileCentroid bundle.normalizedFixed
  have placement_center : exteriorCenter =
      (if bundle.selectedSign = true then (1 : Real) else -1) •
        d bundle.selectedSlot + GaussianRealPoint placement.rightNeighborDisplacement :=
    (PlacementCompanionGeometry.selected_center C D T N h k x bundle placement)
  have placement_centers := PlacementCompanionGeometry.placement_centers C D T N h k x bundle
      placement
            gp_neg_any first_center second_center placement_center
                (PlacementCompanionGeometry.cyclic_slots C D T N h k x bundle placement)
                (PlacementCompanionGeometry.displacement C D T N h k x bundle placement)
  have period0 : placement.layout.u = o 0 := placement.layout.period_u
  have period1 : placement.layout.v = o 1 := placement.layout.period_v
  have translate_center (V : ProtoTile) (w : GaussianInt) :
      TileCentroid (TileTranslation V w) = TileCentroid V + GaussianRealPoint w :=
    (TileTranslationFormulas V w).2.2.2.2.1
  have row_data := PlacementCompanionGeometry.row_data C D T N h k x bundle placement a b row ha
      hb z hz
          selected_slot gp_neg_any period0 period1 (PlacementCompanionGeometry.third_period C D T
              N h k x bundle) (PlacementCompanionGeometry.gp_add)
              (PlacementCompanionGeometry.occurrence_center C D T N h k x bundle placement
              (PlacementCompanionGeometry.parent_center C D T N h k x bundle placement)
              translate_center) (PlacementCompanionGeometry.raw_centers C D T N h k x bundle
              first_center second_center)
  obtain ⟨n, hrow, hshift⟩ := row_data
  have identify := (show
      ∀ (m : Fin 4), (exteriorCenter = branchCenter (branchDisplacement
      bundle.selectedSlot) m) → (n = m)
    from by
      classical
      intro m hc
      by_contra hne
      exact (four_centers_distinct _ (branchDisplacement_nonzero _) n m hne)
        (hrow.symm.trans hc))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbranch
    have hn := identify 0 (placement_centers.1 hbranch)
    have hs : z.oldShift = -o bundle.selectedSlot := by simpa [hn] using hshift
    change -o placement.rightFirstSlot = z.oldShift
    simpa only [hbranch.2.1] using hs.symm
  · intro hbranch
    have hn := identify 1 (placement_centers.2.1 hbranch)
    have hs : z.oldShift = -o bundle.selectedSlot := by simpa [hn] using hshift
    change -o placement.rightSecondSlot = z.oldShift
    simpa only [hbranch.2.1] using hs.symm
  · intro hbranch
    have hn := identify 2 (placement_centers.2.2.1 hbranch)
    have hs : z.oldShift = o bundle.selectedSlot := by simpa [hn] using hshift
    change o placement.rightFirstSlot = z.oldShift
    simpa only [hbranch.2.1] using hs.symm
  · intro hbranch
    have hn := identify 3 (placement_centers.2.2.2 hbranch)
    have hs : z.oldShift = o bundle.selectedSlot := by simpa [hn] using hshift
    change o placement.rightSecondSlot = z.oldShift
    simpa only [hbranch.2.1] using hs.symm

end ApollonianSuperharmonic

end
