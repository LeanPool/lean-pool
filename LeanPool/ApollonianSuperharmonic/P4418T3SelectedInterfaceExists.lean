/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties
public import LeanPool.ApollonianSuperharmonic.BandOriginalParentContainment

public import LeanPool.ApollonianSuperharmonic.P4418T3EndpointOwnerIndices
public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceData
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.FootprintDeletionRetention
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionPaths
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance

-- [TABLET NODE: P4418T3SelectedInterfaceExists]

/-!
# P4418T3SelectedInterfaceExists

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def selectedFirstFace (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) :
    PeriodicSubtileFaceIndex :=
  match row with
  | .positiveL1 _ _ => ⟨.J3,-1,-1⟩
  | .positiveL2 _ _ => ⟨.J1,0,-1⟩
  | .positiveL3 _ _ => ⟨.J7,1,0⟩
  | .reflectedL1 _ _ => ⟨.J3,0,0⟩
  | .reflectedL2 _ _ => ⟨.J1,0,0⟩
  | .reflectedL3 _ _ => ⟨.J7,0,0⟩
  | .positiveS1 _ => ⟨.J3,-1,-1⟩
  | .positiveS2 _ => ⟨.J1,0,-1⟩
  | .positiveS3 _ => ⟨.J5,0,-1⟩
  | .positiveS4 _ => ⟨.J3,0,0⟩
  | .positiveS5 _ => ⟨.J1,0,0⟩
  | .positiveS6 _ => ⟨.J5,-1,-1⟩
  | .reflectedS1 _ => ⟨.J4,0,0⟩
  | .reflectedS2 _ => ⟨.J2,0,0⟩
  | .reflectedS3 _ => ⟨.J6,0,1⟩
  | .reflectedS4 _ => ⟨.J4,-1,-1⟩
  | .reflectedS5 _ => ⟨.J2,0,-1⟩
  | .reflectedS6 _ => ⟨.J6,1,1⟩

private def selectedSecondFace (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) :
    PeriodicSubtileFaceIndex :=
  match row with
  | .positiveL1 _ _ => ⟨.J4,-1,-1⟩
  | .positiveL2 _ _ => ⟨.J2,0,-1⟩
  | .positiveL3 _ _ => ⟨.J8,1,0⟩
  | .reflectedL1 _ _ => ⟨.J4,0,0⟩
  | .reflectedL2 _ _ => ⟨.J2,0,0⟩
  | .reflectedL3 _ _ => ⟨.J8,0,0⟩
  | .positiveS1 _ => ⟨.J5,-1,-1⟩
  | .positiveS2 _ => ⟨.J5,0,-1⟩
  | .positiveS3 _ => ⟨.J7,1,0⟩
  | .positiveS4 _ => ⟨.J5,0,0⟩
  | .positiveS5 _ => ⟨.J5,0,0⟩
  | .positiveS6 _ => ⟨.J7,0,0⟩
  | .reflectedS1 _ => ⟨.J6,1,1⟩
  | .reflectedS2 _ => ⟨.J6,0,1⟩
  | .reflectedS3 _ => ⟨.J8,0,0⟩
  | .reflectedS4 _ => ⟨.J6,0,0⟩
  | .reflectedS5 _ => ⟨.J6,0,0⟩
  | .reflectedS6 _ => ⟨.J8,1,0⟩

namespace SelectedInterfaceGeometry

private abbrev hOA :=
  BandOriginalParentContainment.positiveParent

private abbrev hOB :=
  BandOriginalParentContainment.negativeParent

private theorem isolated :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v)), ∀ x : GaussianInt, z ∈ FootprintVertices
            (⟨{x}, x⟩ : ProtoTile) → x ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells
            ∨ x ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells ) := by
  classical
  intro q cfg C T cert P O u v m n z hz x hy
  by_cases hn : (TileTranslation O
      ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells.Nonempty
  · have hz' : z ∈ FootprintVertices (TileTranslation O
        ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
      simpa [CellSupportedFootprintVertices, FootprintVertices, hn] using hz
    exact cert.precursor_isolated m n z hz' x hy
  · rcases hz with ⟨w, hw, _⟩
    exact (hn ⟨w, hw⟩).elim

private theorem translatedNonempty :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d)) → (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d :
            GaussianInt), (TileTranslation X d).cells.Nonempty)) ) := by
  classical
  intro translatedCells X hX d
  rw [translatedCells]
  obtain ⟨x, hx⟩ := hX
  exact ⟨GaussianTranslation d x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

private theorem parentNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let u := cert.u
        let v := cert.v
        (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d : GaussianInt), (TileTranslation X
            d).cells.Nonempty)) → (∀ (x : PeriodicSubtileIndex), (SubtileOccurrenceInterpretation
            P u v x).cells.Nonempty) ) := by
  classical
  intro q cfg C T cert P u v translatedNonempty x
  cases x with
  | mk label m n =>
    cases label with
      | A =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 0 true)
            ((LatticeTileGridStructure (P 0 true) (cert.parent_lattice 0 true)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)
      | B =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 0 false)
            ((LatticeTileGridStructure (P 0 false) (cert.parent_lattice 0 false)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)
      | C =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 1 true)
            ((LatticeTileGridStructure (P 1 true) (cert.parent_lattice 1 true)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)
      | D =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 1 false)
            ((LatticeTileGridStructure (P 1 false) (cert.parent_lattice 1 false)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)
      | E =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 2 true)
            ((LatticeTileGridStructure (P 2 true) (cert.parent_lattice 2 true)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)
      | F =>
        simpa [SubtileOccurrenceInterpretation, P, u, v] using
          translatedNonempty (P 2 false)
            ((LatticeTileGridStructure (P 2 false) (cert.parent_lattice 2 false)).1.1)
            ((m : GaussianInt) * u + (n : GaussianInt) * v)

private theorem complementNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d : GaussianInt), (TileTranslation X
            d).cells.Nonempty)) → (∀ (m : Int), ∀ (n : Int), (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty) ) := by
  classical
  intro q cfg C T cert P O u v translatedNonempty m n
  have ht := translatedNonempty (TileCellComplement (P 0 true) O)
    ((LatticeTileGridStructure _ cert.precursor_complement_lattice.1).1.1)
    ((m : GaussianInt) * u + (n : GaussianInt) * v)
  rw [(TileCellComplementCovariance _ _ _).1] at ht
  simpa [SubtileOccurrenceInterpretation, P, u, v] using ht

private theorem deleteEdge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (d : GaussianInt), (TileTranslation X d).cells ⊆ (TileTranslation Y
            d).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ x :
            GaussianInt, z ∈ FootprintVertices (⟨{x}, x⟩ : ProtoTile) → x ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ x ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.B,m,n⟩).cells) → (FootprintEdges (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintEdges Y = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintEdges Y))))) ) := by
  classical
  intro q cfg C T cert P O u v hOA cellInclusion isolated m n Y hYA hYB
  exact (FootprintDeletionRetention _ _ _ _
    (cellInclusion O (P 0 true) hOA _) (isolated m n) hYA hYB).2.1

private theorem deleteVertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (d : GaussianInt), (TileTranslation X d).cells ⊆ (TileTranslation Y
            d).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ x :
            GaussianInt, z ∈ FootprintVertices (⟨{x}, x⟩ : ProtoTile) → x ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ x ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → ((∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Y.cells.Nonempty) → ((TileTranslation O ((m : GaussianInt)
            * u + (n : GaussianInt) * v)).cells = ∅ ∨ ((TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧ Y.cells.Nonempty))) → (∀
            (m : Int), ∀ (n : Int), ∀ (Y : ProtoTile), (Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩).cells) → ((Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.B,m,n⟩).cells) → ((Y.cells.Nonempty) →
            (FootprintVertices (TileCellComplement (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
            FootprintVertices Y = FootprintVertices (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩) ∩ FootprintVertices Y))))))) ) := by
  classical
  intro q cfg C T cert P O u v hOA cellInclusion isolated deletionSupport m n Y hYA hYB hY
  exact (FootprintDeletionRetention _ _ _ _
    (cellInclusion O (P 0 true) hOA _) (isolated m n) hYA hYB).2.2
    (deletionSupport m n Y hY)

private theorem modifiedA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (m : Int), ∀ (n : Int), ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩ =
            TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation
            O ((m : GaussianInt) * u + (n : GaussianInt) * v)) ) := by
  classical
  intro q cfg C T cert P O u v m n
  change TileTranslation (TileCellComplement (P 0 true) O)
    ((m : GaussianInt) * u + (n : GaussianInt) * v) = _
  rw [(TileCellComplementCovariance _ _ _).1]
  rfl

private theorem modifiedOther :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (x : PeriodicSubtileIndex), (x.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P
            O u v x = SubtileOccurrenceInterpretation P u v x) ) := by
  classical
  intro q cfg C T cert P O u v x hx
  cases x with
  | mk label m n => cases label <;> simp_all
    [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]

private theorem modifiedAFootprintSubset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), (TileCellComplement (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → (∀ (m : Int), ∀ (n : Int),
            FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ⊆
            FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩))) ) := by
  classical
  intro q cfg C T cert P O u v complementNonempty modifiedA m n
  rw [modifiedA m n]
  have hcomp := complementNonempty m n
  have hparent :
      (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩).cells.Nonempty :=
    hcomp.mono (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
  intro z hz
  simp only [FootprintVertices, ite_eq_left hcomp, ite_eq_left hparent] at hz ⊢
  rcases hz with ⟨x, hx, hcorner⟩
  exact ⟨x, (Finset.mem_sdiff.mp hx).1, hcorner⟩

private theorem modifiedFootSubset :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O
            u v ⟨.A,m,n⟩) ⊆ FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)) →
            (∀ (x : PeriodicSubtileIndex), FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v x) ⊆ FootprintVertices
            (SubtileOccurrenceInterpretation P u v x)) ) := by
  classical
  intro q cfg C T cert P O u v modifiedAFootprintSubset x
  cases x with
  | mk label m n => cases label with
    | A => exact modifiedAFootprintSubset m n
    | B => simp [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]
    | C => simp [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]
    | D => simp [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]
    | E => simp [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]
    | F => simp [ModifiedSubtileOccurrenceInterpretation, SubtileOccurrenceInterpretation]

private theorem modifiedAEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (x : PeriodicSubtileIndex), ∀ (y : PeriodicSubtileIndex), (x ≠ y) → ((¬ ((x.label = .A
            ∧ y.label = .B ∨ x.label = .B ∧ y.label = .A) ∧ x.first = y.first ∧ x.second =
            y.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v x).cells
            (SubtileOccurrenceInterpretation P u v y).cells))) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y
            : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.B,m,n⟩).cells) → (FootprintEdges (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintEdges Y = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintEdges Y))) → ((∀ (m :
            Int), ∀ (n : Int), ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩ =
            TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation
            O ((m : GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (x : PeriodicSubtileIndex),
            (x.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O u v x =
            SubtileOccurrenceInterpretation P u v x)) → (∀ (m : Int), ∀ (n : Int), ∀ (x :
            PeriodicSubtileIndex), (x.label ≠ .A) → ((¬ (x.label = .B ∧ x.first = m ∧ x.second =
            n)) → (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩
            FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v x) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v x))))))) ) := by
  classical
  intro q cfg C T cert P O u v pairCells deleteEdge modifiedA modifiedOther m n x hx hpair
  have hneA : (⟨.A,m,n⟩ : PeriodicSubtileIndex) ≠ x := by
    intro he
    exact hx (by simpa using (congrArg PeriodicSubtileIndex.label he).symm)
  have hneB : (⟨.B,m,n⟩ : PeriodicSubtileIndex) ≠ x := by
    intro he
    apply hpair
    exact ⟨by simpa using (congrArg PeriodicSubtileIndex.label he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.first he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.second he).symm⟩
  have h := deleteEdge m n (SubtileOccurrenceInterpretation P u v x)
    (pairCells x ⟨.A,m,n⟩ hneA.symm (by
      intro hp
      rcases hp with ⟨hl, hf, hs⟩
      rcases hl with ⟨hxA, hAB⟩ | ⟨hxB, hBA⟩
      · exact hx hxA
      · exact hpair ⟨hxB, by simpa using hf, by simpa using hs⟩))
    (pairCells x ⟨.B,m,n⟩ hneB.symm (by
      intro hp
      rcases hp with ⟨hl, hf, hs⟩
      rcases hl with ⟨hxA, hAB⟩ | ⟨hxB, hBA⟩
      · exact hx hxA
      · cases hBA))
  rw [modifiedA m n, modifiedOther x hx]
  exact h

private theorem modifiedAVertices :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (x : PeriodicSubtileIndex), ∀ (y : PeriodicSubtileIndex), (x ≠ y) → ((¬ ((x.label = .A
            ∧ y.label = .B ∨ x.label = .B ∧ y.label = .A) ∧ x.first = y.first ∧ x.second =
            y.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v x).cells
            (SubtileOccurrenceInterpretation P u v y).cells))) → ((∀ (x : PeriodicSubtileIndex),
            (SubtileOccurrenceInterpretation P u v x).cells.Nonempty) → ((∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.A,m,n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.B,m,n⟩).cells) → ((Y.cells.Nonempty) → (FootprintVertices (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintVertices Y)))) → ((∀ (m :
            Int), ∀ (n : Int), ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩ =
            TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) (TileTranslation
            O ((m : GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (x : PeriodicSubtileIndex),
            (x.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O u v x =
            SubtileOccurrenceInterpretation P u v x)) → (∀ (m : Int), ∀ (n : Int), ∀ (x :
            PeriodicSubtileIndex), (x.label ≠ .A) → ((¬ (x.label = .B ∧ x.first = m ∧ x.second =
            n)) → (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩
            FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v x) =
            FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩
            FootprintVertices (SubtileOccurrenceInterpretation P u v x)))))))) ) := by
  classical
  intro q cfg C T cert P O u v pairCells parentNonempty deleteVertex modifiedA modifiedOther m n
      x hx hpair
  have hneA : (⟨.A,m,n⟩ : PeriodicSubtileIndex) ≠ x := by
    intro he
    exact hx (by simpa using (congrArg PeriodicSubtileIndex.label he).symm)
  have hneB : (⟨.B,m,n⟩ : PeriodicSubtileIndex) ≠ x := by
    intro he
    apply hpair
    exact ⟨by simpa using (congrArg PeriodicSubtileIndex.label he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.first he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.second he).symm⟩
  have h := deleteVertex m n (SubtileOccurrenceInterpretation P u v x)
    (pairCells x ⟨.A,m,n⟩ hneA.symm (by
      intro hp
      rcases hp with ⟨hl, hf, hs⟩
      rcases hl with ⟨hxA, hAB⟩ | ⟨hxB, hBA⟩
      · exact hx hxA
      · exact hpair ⟨hxB, by simpa using hf, by simpa using hs⟩))
    (pairCells x ⟨.B,m,n⟩ hneB.symm (by
      intro hp
      rcases hp with ⟨hl, hf, hs⟩
      rcases hl with ⟨hxA, hAB⟩ | ⟨hxB, hBA⟩
      · exact hx hxA
      · cases hBA))
    (parentNonempty x)
  rw [modifiedA m n, modifiedOther x hx]
  exact h

private theorem retargeted :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            (BandOrderedGeneralSelectedContactRow q cfg C T cert a b) → (
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), ∀ (x : PeriodicSubtileIndex), (x.label ≠ .A) → ((¬ (x.label =
            .B ∧ x.first = m ∧ x.second = n)) → (FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v x) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v x)))) → ((∀ (m : Int), ∀ (n : Int), ∀ (x :
            PeriodicSubtileIndex), (x.label ≠ .A) → ((¬ (x.label = .B ∧ x.first = m ∧ x.second =
            n)) → (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩
            FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v x) =
            FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩
            FootprintVertices (SubtileOccurrenceInterpretation P u v x)))) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)) ∧ (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b))))) ) := by
  classical
  intro q cfg C T cert a b row P O u v modifiedAEdges modifiedAVertices
  cases row with
  | positiveL1 => exact ⟨modifiedAEdges (-1) (-1) _ (by decide) (by decide),
      modifiedAVertices (-1) (-1) _ (by decide) (by decide)⟩
  | positiveL2 => exact ⟨modifiedAEdges 0 (-1) _ (by decide) (by decide),
      modifiedAVertices 0 (-1) _ (by decide) (by decide)⟩
  | positiveL3 => exact ⟨rfl, rfl⟩
  | positiveS1 => exact ⟨modifiedAEdges (-1) (-1) _ (by decide) (by decide),
      modifiedAVertices (-1) (-1) _ (by decide) (by decide)⟩
  | positiveS2 => exact ⟨modifiedAEdges 0 (-1) _ (by decide) (by decide),
      modifiedAVertices 0 (-1) _ (by decide) (by decide)⟩
  | positiveS3 => exact ⟨rfl, rfl⟩
  | positiveS4 =>
      have he := modifiedAEdges 0 0 ⟨.C,1,1⟩ (by decide) (by decide)
      have hv := modifiedAVertices 0 0 ⟨.C,1,1⟩ (by decide) (by decide)
      exact ⟨by simpa [Set.inter_comm] using he,
        by simpa [Set.inter_comm] using hv⟩
  | positiveS5 =>
      have he := modifiedAEdges 0 0 ⟨.E,0,1⟩ (by decide) (by decide)
      have hv := modifiedAVertices 0 0 ⟨.E,0,1⟩ (by decide) (by decide)
      exact ⟨by simpa [Set.inter_comm] using he,
        by simpa [Set.inter_comm] using hv⟩
  | positiveS6 => exact ⟨rfl, rfl⟩
  | reflectedL1 =>
      have he := modifiedAEdges 0 0 ⟨.B,1,1⟩ (by decide) (by decide)
      have hv := modifiedAVertices 0 0 ⟨.B,1,1⟩ (by decide) (by decide)
      exact ⟨by simpa [Set.inter_comm] using he,
        by simpa [Set.inter_comm] using hv⟩
  | reflectedL2 =>
      have he := modifiedAEdges 0 0 ⟨.B,0,1⟩ (by decide) (by decide)
      have hv := modifiedAVertices 0 0 ⟨.B,0,1⟩ (by decide) (by decide)
      exact ⟨by simpa [Set.inter_comm] using he,
        by simpa [Set.inter_comm] using hv⟩
  | reflectedL3 => exact ⟨rfl, rfl⟩
  | reflectedS1 => exact ⟨rfl, rfl⟩
  | reflectedS2 => exact ⟨rfl, rfl⟩
  | reflectedS3 => exact ⟨rfl, rfl⟩
  | reflectedS4 => exact ⟨rfl, rfl⟩
  | reflectedS5 => exact ⟨rfl, rfl⟩
  | reflectedS6 => exact ⟨rfl, rfl⟩

private theorem faceVertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f : PeriodicSubtileFaceIndex), ∀ (i : Fin 3), cert.modified.plane.faceVertex
            (cert.modifiedFaceEquivalence.symm f) i = SixSubtileFaceVertices f i ) := by
  classical
  intro q cfg C T cert f i
  simpa using cert.modified_face_vertices (cert.modifiedFaceEquivalence.symm f) i

private theorem faceDistinct :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (a : PeriodicSubtileIndex),
                    ∀ (b : PeriodicSubtileIndex),
                      ∀ (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
                        let face0 : PeriodicSubtileFaceIndex :=
                          selectedFirstFace q cfg C T cert a b row
                        let face1 : PeriodicSubtileFaceIndex :=
                          selectedSecondFace q cfg C T cert a b row
                        let F0 := cert.modifiedFaceEquivalence.symm face0
                        let F1 := cert.modifiedFaceEquivalence.symm face1
                        F0 ≠ F1
    ) := by
  classical
  intro q cfg C T cert a b row face0 face1 F0 F1 h
  have hf := congrArg cert.modifiedFaceEquivalence h
  cases row <;> simp [F0, F1, face0, face1, selectedFirstFace, selectedSecondFace] at hf

private theorem faceTable :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates)
          (cfg : BandOrderedGeneralConfiguration q)
          (C : BandCircle)
          (T : ProtoTile)
          (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
          (a b : PeriodicSubtileIndex)
          (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert
              a b),
          let owners :=
            P4418T3EndpointOwnerIndices q cfg C T cert a b row;
          let face0 :=
            selectedFirstFace q cfg C T cert a b row;
          let face1 :=
            selectedSecondFace q cfg C T cert a b row;
          let F0 :=
            (cert.modifiedFaceEquivalence.symm :
                PeriodicSubtileFaceIndex →
                  cert.modified.plane.Face)
              face0;
          let F1 :=
            (cert.modifiedFaceEquivalence.symm :
                PeriodicSubtileFaceIndex →
                  cert.modified.plane.Face)
              face1;
          (∀ (f : PeriodicSubtileFaceIndex) (i : Fin (3 : ℕ)),
              cert.modified.plane.faceVertex
                  ((cert.modifiedFaceEquivalence.symm :
                      PeriodicSubtileFaceIndex →
                        cert.modified.plane.Face)
                    f)
                  i =
                SixSubtileFaceVertices f i) →
            (∃ (iA : Fin (3 : ℕ)) (iB : Fin (3 : ℕ)) (iO : Fin (3 : ℕ)),
                cert.modified.plane.faceVertex F0 iA = a ∧
                  cert.modified.plane.faceVertex F0 iB = b ∧
                    cert.modified.plane.faceVertex F0 iO = owners.1) ∧
              ∃ (jA : Fin (3 : ℕ)) (jB : Fin (3 : ℕ)) (jO : Fin (3 : ℕ)),
                cert.modified.plane.faceVertex F1 jA = a ∧
                  cert.modified.plane.faceVertex F1 jB = b ∧
                    cert.modified.plane.faceVertex F1 jO = owners.2) := by
  classical
  intro q cfg C T cert a b row owners face0 face1 F0 F1 faceVertex
  cases row <;>
    simp only [selectedFirstFace, Int.reduceNeg, faceVertex, SixSubtileFaceVertices,
        neg_add_cancel, P4418T3EndpointOwnerIndices, exists_and_left, exists_and_right,
        selectedSecondFace, F0, face0, owners, F1, face1, zero_add, zero_sub, sub_self] <;> decide

private abbrev reversePath := @SimpleGridPathBetween.reverse

private theorem allowed :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (a : PeriodicSubtileIndex),
                    ∀ (b : PeriodicSubtileIndex),
                      (BandOrderedGeneralSelectedContactRow q cfg C T cert a b) →
                        (AllowedSubtileIncidence a b)) := by
  classical
  intro q cfg C T cert a b row
  cases row with
  | positiveL1 => exact .AB11 (-1) (-1)
  | positiveL2 => exact .AB01 0 (-1)
  | positiveL3 => exact .CDm10 1 0
  | positiveS1 => exact .AC11 (-1) (-1)
  | positiveS2 => exact .AE01 0 (-1)
  | positiveS3 => exact .CEm10 1 0
  | positiveS4 => exact .symm (.AC11 0 0)
  | positiveS5 => exact .symm (.AE01 0 0)
  | positiveS6 => exact .symm (.CEm10 0 0)
  | reflectedL1 => exact .symm (.AB11 0 0)
  | reflectedL2 => exact .symm (.AB01 0 0)
  | reflectedL3 => exact .symm (.CDm10 0 0)
  | reflectedS1 => exact .BDm1m1 1 1
  | reflectedS2 => exact .BF0m1 0 1
  | reflectedS3 => exact .DF10 (-1) 0
  | reflectedS4 => exact .symm (.BDm1m1 0 0)
  | reflectedS5 => exact .symm (.BF0m1 0 0)
  | reflectedS6 => exact .symm (.DF10 0 0)

private theorem modifiedEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (a ≠ b) → ((AllowedSubtileIncidence a b) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty)) ) := by
  classical
  intro q cfg C T cert a b P O u v hne allowed
  have hadj := (cert.modified_adjacency a b).2 allowed
  have hclass := PeriodicTileIntersectionClassification cert.modified
  have := (hclass.1 a b hne).1.mpr hadj
  simpa only [cert.modified_tile] using this

private theorem headLastNe :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), (p.Nodup) → ((2 ≤ p.length) → (p.head? ≠ p.getLast?)) ) := by
  classical
  intro p hnd hlen
  cases p with
  | nil => simp at hlen
  | cons x xs =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      intro heq
      have hxnot : x ∉ y :: ys := (List.nodup_cons.mp hnd).1
      have hlast : x = (y :: ys).getLast (by simp) := by
        simpa [List.getLast?_eq_some_getLast] using heq
      exact hxnot (hlast ▸ List.getLast_mem (by simp))

private theorem pathAtOwners :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ((FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)) ∧ (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b))) → (
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
        let face0 : PeriodicSubtileFaceIndex := selectedFirstFace q cfg C T cert a b row
        let face1 : PeriodicSubtileFaceIndex := selectedSecondFace q cfg C T cert a b row
        let F0 := cert.modifiedFaceEquivalence.symm face0
        let F1 := cert.modifiedFaceEquivalence.symm face1
        (F0 ≠ F1) → (((∃ iA iB iO : Fin 3, cert.modified.plane.faceVertex F0 iA = a ∧
            cert.modified.plane.faceVertex F0 iB = b ∧ cert.modified.plane.faceVertex F0 iO =
            owners.1) ∧ (∃ jA jB jO : Fin 3, cert.modified.plane.faceVertex F1 jA = a ∧
            cert.modified.plane.faceVertex F1 jB = b ∧ cert.modified.plane.faceVertex F1 jO =
            owners.2)) → ((∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween V E y x)) → ((a ≠ b) → (((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty) →
            (SimpleGridPathBetween (FootprintVertices (occurrence a) ∩ FootprintVertices
            (occurrence b)) (FootprintEdges (occurrence a) ∩ FootprintEdges (occurrence b))
            (cert.modified.rho F0) (cert.modified.rho F1))))))) ) := by
  classical
  intro q cfg C T cert a b row P O u v retargeted occurrence owners face0 face1 F0 F1
      faceDistinct faceTable reversePath hne modifiedEdges
  have hclass := PeriodicTileIntersectionClassification cert.modified
  have hpaths := PeriodicTileIntersectionPaths cert.modified hclass.2 a b hne
  have hedge :
      (FootprintEdges (cert.modified.tile a) ∩
        FootprintEdges (cert.modified.tile b)).Nonempty := by
    simpa only [cert.modified_tile] using modifiedEdges
  rcases hpaths.1.mpr hedge with ⟨_, f, g, hfg, hf, hg, hall, hp⟩
  have hraw := (hclass.1 a b hne).2.1 hedge
  rw [← hraw.2] at hp
  have hp' :
      SimpleGridPathBetween
        (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b))
        (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b))
        (cert.modified.rho f) (cert.modified.rho g) := by
    simpa only [cert.modified_tile] using hp
  rcases faceTable with ⟨⟨iA,iB,iO,ha0,hb0,ho0⟩,
    ⟨jA,jB,jO,ha1,hb1,ho1⟩⟩
  have hF0 := hall F0 ⟨⟨iA, ha0⟩, ⟨iB, hb0⟩⟩
  have hF1 := hall F1 ⟨⟨jA, ha1⟩, ⟨jB, hb1⟩⟩
  rcases hF0 with hF0 | hF0 <;> rcases hF1 with hF1 | hF1
  · exact (faceDistinct (hF0.trans hF1.symm)).elim
  · have hOrient : f = F0 ∧ g = F1 := ⟨hF0.symm, hF1.symm⟩
    rw [retargeted.2, retargeted.1] at hp'
    simpa [hOrient.1, hOrient.2] using hp'
  · have hpRev := reversePath hp'
    have hOrient : g = F0 ∧ f = F1 := ⟨hF0.symm, hF1.symm⟩
    rw [retargeted.2, retargeted.1] at hpRev
    simpa [hOrient.1, hOrient.2] using hpRev
  · exact (faceDistinct (hF0.trans hF1.symm)).elim

private theorem endpointsDistinct :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates)
          (cfg : BandOrderedGeneralConfiguration q)
          (C : BandCircle)
          (T : ProtoTile)
          (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
          (a b : PeriodicSubtileIndex)
          (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert
              a b),
          let occurrence :=
            SubtileOccurrenceInterpretation cert.P cert.u
              cert.v;
          let face0 :=
            selectedFirstFace q cfg C T cert a b row;
          let face1 :=
            selectedSecondFace q cfg C T cert a b row;
          let F0 :=
            (cert.modifiedFaceEquivalence.symm :
                PeriodicSubtileFaceIndex →
                  cert.modified.plane.Face)
              face0;
          let F1 :=
            (cert.modifiedFaceEquivalence.symm :
                PeriodicSubtileFaceIndex →
                  cert.modified.plane.Face)
              face1;
          (∀ (p : List GaussianInt),
              p.Nodup → (2 : ℕ) ≤ p.length → p.head? ≠ p.getLast?) →
            SimpleGridPathBetween
                (FootprintVertices (occurrence a) ∩
                  FootprintVertices (occurrence b))
                (FootprintEdges (occurrence a) ∩
                  FootprintEdges (occurrence b))
                (cert.modified.rho F0) (cert.modified.rho F1) →
              cert.modified.rho F0 ≠ cert.modified.rho F1) := by
  classical
  intro q cfg C T cert a b row occurrence face0 face1 F0 F1 headLastNe pathAtOwners
  rcases pathAtOwners with ⟨p, hnd, hlen, hh, hl, _, _, _⟩
  intro heq
  apply headLastNe p hnd hlen
  rw [hh, hl, heq]

private theorem latticeOccurrence :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        ∀ x : PeriodicSubtileIndex, LatticeTile (occurrence x) ) := by
  classical
  intro q cfg C T cert occurrence x
  let P := cert.P
  let u := cert.u
  let v := cert.v
  cases x with
  | mk label m n => cases label with
    | A =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 0 true)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 0 true)
    | B =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 0 false)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 0 false)
    | C =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 1 true)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 1 true)
    | D =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 1 false)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 1 false)
    | E =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 2 true)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 2 true)
    | F =>
      simpa [occurrence, SubtileOccurrenceInterpretation, P, u, v] using
        (TileDiskAreaCovariance (P 2 false)
          ((m : GaussianInt) * u + (n : GaussianInt) * v)).1.mp
          (cert.parent_lattice 2 false)

private theorem disjointData :
    (by
      classical
        exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (a : PeriodicSubtileIndex),
                    ∀ (b : PeriodicSubtileIndex),
                      ∀
                        (row :
                          BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
                        let P := cert.P;
                        let u := cert.u;
                        let v := cert.v;
                        (∀ (x : PeriodicSubtileIndex),
                            ∀ (y : PeriodicSubtileIndex),
                              (x ≠ y) →
                                ((¬((x.label = .A ∧ y.label = .B ∨
                                        x.label = .B ∧ y.label = .A) ∧
                                      x.first = y.first ∧ x.second = y.second)) →
                                  (Disjoint
                                    (SubtileOccurrenceInterpretation P u v x).cells
                                    (SubtileOccurrenceInterpretation P u v
                                        y).cells))) →
                          (let occurrence :=
                            SubtileOccurrenceInterpretation cert.P cert.u cert.v;
                          let owners :=
                            P4418T3EndpointOwnerIndices q cfg C T cert a b row;
                          (Disjoint (occurrence a).cells (occurrence b).cells ∧
                            Disjoint (occurrence a).cells
                                (occurrence owners.1).cells ∧
                              Disjoint (occurrence b).cells
                                  (occurrence owners.1).cells ∧
                                Disjoint (occurrence a).cells
                                    (occurrence owners.2).cells ∧
                                  Disjoint (occurrence b).cells
                                    (occurrence owners.2).cells))) := by
  classical
  intro q cfg C T cert a b row P u v pairCells occurrence owners
  cases row <;> dsimp [owners, P4418T3EndpointOwnerIndices] at *
  all_goals
    exact ⟨pairCells _ _ (by decide) (by decide),
      pairCells _ _ (by decide) (by decide),
      pairCells _ _ (by decide) (by decide),
      pairCells _ _ (by decide) (by decide),
      pairCells _ _ (by decide) (by decide)⟩

private abbrev translateAdd := ApollonianSuperharmonic.TileTranslationProperties.add

private abbrev translateZero := ApollonianSuperharmonic.TileTranslationProperties.zero

private theorem touchingData :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
                                                          (
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v;
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row;
                    (
                               (
                                                                (
                                                                             (
                                                                        (
                                      (
                                                                                       (
                                                         (
                 (
                                                                      (
              (
                                                            (
                             (
                                                                   (
            (
            (
            (
                              (
                                                (
                               ((∀ (X : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt),
            TileTranslation (TileTranslation X x) y = TileTranslation X (x + y)) → ((∀ (X :
            ProtoTile), TileTranslation X 0 = X) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z :
            ProtoTile), ∀ (d : GaussianInt), (TouchingTriple X Y Z) → (TouchingTriple
            (TileTranslation X d) (TileTranslation Y d) (TileTranslation Z d))) → ((∀
            {X : ProtoTile}, ∀ {Y : ProtoTile}, ∀ {Z : ProtoTile}, (TouchingTriple X Y Z) →
            (TouchingTriple X Z Y)) → ((∀ {X : ProtoTile}, ∀ {Y : ProtoTile}, ∀ {Z : ProtoTile},
            (TouchingTriple X Y Z) → (TouchingTriple Y X Z)) → ((∀ {X : ProtoTile}, ∀
            {Y : ProtoTile}, ∀ {Z : ProtoTile}, (TouchingTriple X Y Z) → (TouchingTriple Y Z X))
            → ((∀ {X : ProtoTile}, ∀ {Y : ProtoTile}, ∀ {Z : ProtoTile}, (TouchingTriple X Y Z) →
            (TouchingTriple Z X Y)) → ((∀ {X : ProtoTile}, ∀ {Y : ProtoTile}, ∀ {Z : ProtoTile},
            (TouchingTriple X Y Z) → (TouchingTriple Z Y X)) → ((TouchingTriple (cert.P (0 : Fin
            (3 : ℕ)) true) (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) cert.v)
            (TileTranslation (cert.P (2 : Fin (3 : ℕ)) true) cert.v)) → ((TouchingTriple (cert.P
            (0 : Fin (3 : ℕ)) true) (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) cert.v)
            (cert.P (2 : Fin (3 : ℕ)) false)) → ((TouchingTriple (cert.P (0 : Fin (3 : ℕ)) true)
            (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) (cert.u + cert.v)) (TileTranslation
            (cert.P (1 : Fin (3 : ℕ)) true) (cert.u + cert.v))) → ((TouchingTriple (cert.P (0 :
            Fin (3 : ℕ)) true) (TileTranslation (cert.P (0 : Fin (3 : ℕ)) false) (cert.u +
            cert.v)) (cert.P (1 : Fin (3 : ℕ)) false)) → ((TouchingTriple (cert.P (0 : Fin (3 :
            ℕ)) true) (TileTranslation (cert.P (1 : Fin (3 : ℕ)) true) (cert.u + cert.v))
            (TileTranslation (cert.P (2 : Fin (3 : ℕ)) true) cert.v)) → ((TouchingTriple (cert.P
            (0 : Fin (3 : ℕ)) false) (TileTranslation (cert.P (1 : Fin (3 : ℕ)) false) (-cert.u -
            cert.v)) (TileTranslation (cert.P (2 : Fin (3 : ℕ)) false) (-cert.v))) →
            ((TouchingTriple (cert.P (1 : Fin (3 : ℕ)) true) (TileTranslation (cert.P (1 : Fin (3
            : ℕ)) false) (-cert.u)) (TileTranslation (cert.P (2 : Fin (3 : ℕ)) true) (-cert.u)))
            → ((TouchingTriple (cert.P (1 : Fin (3 : ℕ)) true) (TileTranslation (cert.P (1 : Fin
            (3 : ℕ)) false) (-cert.u)) (cert.P (2 : Fin (3 : ℕ)) false)) → (TouchingTriple
            (occurrence a) (occurrence b) (occurrence owners.1) ∧ TouchingTriple (occurrence a)
            (occurrence b) (occurrence owners.2)))))))))))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C T cert a b row occurrence owners translateAdd translateZero touchTranslate
      touchXZY touchYXZ touchYZX touchZXY touchZYX out1 out2 out3 out4 out5 out6 out7 out8
  let u := cert.u
  let v := cert.v
  cases row with
  | positiveL1 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero,         u, v, add_assoc,
            add_comm, add_left_comm] using
        touchTranslate _ _ _ (-(u+v)) out3
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero,         u, v, add_assoc,
            add_comm, add_left_comm] using
        touchTranslate _ _ _ (-(u+v)) out4
  | positiveL2 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ (-v) out1
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ (-v) out2
  | positiveL3 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ u out7
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ u out8
  | reflectedL1 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out3
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out4
  | reflectedL2 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out1
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out2
  | reflectedL3 _ _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out7
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out8
  | positiveS1 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchXZY (touchTranslate _ _ _ (-(u+v)) out3)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ (-(u+v)) out5
  | positiveS2 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchXZY (touchTranslate _ _ _ (-v) out1)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchXZY (touchTranslate _ _ _ (-v) out5)
  | positiveS3 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchYZX (touchTranslate _ _ _ (-v) out5)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchXZY (touchTranslate _ _ _ u out7)
  | positiveS4 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchZXY out3
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYXZ out5
  | positiveS5 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchZXY out1
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchZXY out5
  | positiveS6 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchZYX (touchTranslate _ _ _ (-(u+v)) out5)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchZXY out7
  | reflectedS1 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYZX out4
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchTranslate _ _ _ (u+v) out6
  | reflectedS2 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYZX out2
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchXZY (touchTranslate _ _ _ v out6)
  | reflectedS3 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using touchYZX (touchTranslate _ _ _ v out6)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, u, v] using touchYZX out8
  | reflectedS4 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchZYX (touchTranslate _ _ _ (-(u+v)) out4)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, sub_eq_add_neg,
        u, v] using touchYXZ out6
  | reflectedS5 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchZYX (touchTranslate _ _ _ (-v) out2)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateZero, sub_eq_add_neg,
        u, v] using touchZXY out6
  | reflectedS6 _ =>
    constructor
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchZYX (touchTranslate _ _ _ (u+v) out6)
    · simpa [occurrence, owners, P4418T3EndpointOwnerIndices,
        SubtileOccurrenceInterpretation, translateAdd, translateZero, u, v,
        add_assoc, add_comm, add_left_comm] using
        touchZYX (touchTranslate _ _ _ u out8)

end SelectedInterfaceGeometry

namespace SelectedInterfaceCertificate

private theorem selectedCertificate :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (x : PeriodicSubtileIndex), ∀ (y : PeriodicSubtileIndex), (x ≠ y) → ((¬ ((x.label = .A
            ∧ y.label = .B ∨ x.label = .B ∧ y.label = .A) ∧ x.first = y.first ∧ x.second =
            y.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v x).cells
            (SubtileOccurrenceInterpretation P u v y).cells))) → ((∀ (x : PeriodicSubtileIndex),
            FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v x) ⊆
            FootprintVertices (SubtileOccurrenceInterpretation P u v x)) → (((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)) ∧ (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b))) → (
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
        let face0 : PeriodicSubtileFaceIndex := selectedFirstFace q cfg C T cert a b row
        let face1 : PeriodicSubtileFaceIndex := selectedSecondFace q cfg C T cert a b row
        let F0 := cert.modifiedFaceEquivalence.symm face0
        let F1 := cert.modifiedFaceEquivalence.symm face1
        (((∃ iA iB iO : Fin 3, cert.modified.plane.faceVertex F0 iA = a ∧
            cert.modified.plane.faceVertex F0 iB = b ∧ cert.modified.plane.faceVertex F0 iO =
            owners.1) ∧ (∃ jA jB jO : Fin 3, cert.modified.plane.faceVertex F1 jA = a ∧
            cert.modified.plane.faceVertex F1 jB = b ∧ cert.modified.plane.faceVertex F1 jO =
            owners.2)) → ((((((SimpleGridPathBetween
            (FootprintVertices (occurrence a) ∩ FootprintVertices (occurrence b)) (FootprintEdges
            (occurrence a) ∩ FootprintEdges (occurrence b)) (cert.modified.rho F0)
            (cert.modified.rho F1)) → ((cert.modified.rho F0 ≠ cert.modified.rho F1) → (
        let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
        Nonempty (P4418T3SelectedInterfaceData (occurrence a) (occurrence b)
          (occurrence owners.1) (occurrence owners.2))))))))))))) ) := by
  classical
  intro q cfg C T cert a b row P O u v pairCells modifiedFootSubset retargeted occurrence owners
      face0 face1 F0 F1 faceTable pathAtOwners endpointsDistinct
  rcases faceTable with ⟨⟨iA,iB,iO,ha0,hb0,ho0⟩,
    ⟨jA,jB,jO,ha1,hb1,ho1⟩⟩
  have commonPair0 :
      cert.modified.rho F0 ∈
        FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) := by
    exact ⟨by simpa only [ha0, cert.modified_tile] using cert.modified.rho_common F0 iA,
      by simpa only [hb0, cert.modified_tile] using cert.modified.rho_common F0 iB⟩
  have commonPair1 :
      cert.modified.rho F1 ∈
        FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) := by
    exact ⟨by simpa only [ha1, cert.modified_tile] using cert.modified.rho_common F1 jA,
      by simpa only [hb1, cert.modified_tile] using cert.modified.rho_common F1 jB⟩
  have ownerPoint0 : cert.modified.rho F0 ∈ FootprintVertices (occurrence owners.1) := by
    apply modifiedFootSubset owners.1
    simpa only [ho0, cert.modified_tile] using cert.modified.rho_common F0 iO
  have ownerPoint1 : cert.modified.rho F1 ∈ FootprintVertices (occurrence owners.2) := by
    apply modifiedFootSubset owners.2
    simpa only [ho1, cert.modified_tile] using cert.modified.rho_common F1 jO
  have originalPair0 : cert.modified.rho F0 ∈
      FootprintVertices (occurrence a) ∩ FootprintVertices (occurrence b) := by
    simpa only [retargeted.2] using commonPair0
  have originalPair1 : cert.modified.rho F1 ∈
      FootprintVertices (occurrence a) ∩ FootprintVertices (occurrence b) := by
    simpa only [retargeted.2] using commonPair1
  have latticeOccurrence : ∀ x : PeriodicSubtileIndex, LatticeTile (occurrence x) :=
      SelectedInterfaceGeometry.latticeOccurrence q cfg C T cert
  have disjointData :
      Disjoint (occurrence a).cells (occurrence b).cells ∧
      Disjoint (occurrence a).cells (occurrence owners.1).cells ∧
      Disjoint (occurrence b).cells (occurrence owners.1).cells ∧
      Disjoint (occurrence a).cells (occurrence owners.2).cells ∧
      Disjoint (occurrence b).cells (occurrence owners.2).cells :=
          SelectedInterfaceGeometry.disjointData q cfg C T cert a b row pairCells
  have translateAdd (X : ProtoTile) (x y : GaussianInt) :
      TileTranslation (TileTranslation X x) y = TileTranslation X (x + y) :=
          SelectedInterfaceGeometry.translateAdd X x y
  have translateZero (X : ProtoTile) : TileTranslation X 0 = X :=
      SelectedInterfaceGeometry.translateZero X
  have touchTranslate (X Y Z : ProtoTile) (d : GaussianInt)
      (h : TouchingTriple X Y Z) :
      TouchingTriple (TileTranslation X d) (TileTranslation Y d)
        (TileTranslation Z d) :=
    (TouchingTripleCovariance X Y Z d).1.mp h
  have touchXZY {X Y Z : ProtoTile} (h : TouchingTriple X Y Z) :
      TouchingTriple X Z Y := (TouchingTriplePermutations X Y Z).1 h |>.1
  have touchYXZ {X Y Z : ProtoTile} (h : TouchingTriple X Y Z) :
      TouchingTriple Y X Z := (TouchingTriplePermutations X Y Z).1 h |>.2.1
  have touchYZX {X Y Z : ProtoTile} (h : TouchingTriple X Y Z) :
      TouchingTriple Y Z X := (TouchingTriplePermutations X Y Z).1 h |>.2.2.1
  have touchZXY {X Y Z : ProtoTile} (h : TouchingTriple X Y Z) :
      TouchingTriple Z X Y := (TouchingTriplePermutations X Y Z).1 h |>.2.2.2.1
  have touchZYX {X Y Z : ProtoTile} (h : TouchingTriple X Y Z) :
      TouchingTriple Z Y X := (TouchingTriplePermutations X Y Z).1 h |>.2.2.2.2
  rcases cert.outer_touching with ⟨out1,out2,out3,out4,out5,out6,out7,out8⟩
  have touchingData :
      TouchingTriple (occurrence a) (occurrence b) (occurrence owners.1) ∧
      TouchingTriple (occurrence a) (occurrence b) (occurrence owners.2) :=
          SelectedInterfaceGeometry.touchingData q cfg C T cert a b row translateAdd translateZero
              touchTranslate touchXZY touchYXZ
          touchYZX touchZXY touchZYX out1 out2 out3 out4 out5 out6 out7 out8
  have touching0 := touchingData.1
  have touching1 := touchingData.2
  exact ⟨cert.modified.rho F0, cert.modified.rho F1, endpointsDistinct,
    pathAtOwners, latticeOccurrence a, latticeOccurrence b,
    latticeOccurrence owners.1, latticeOccurrence owners.2,
    disjointData.1, disjointData.2.1, disjointData.2.2.1,
    disjointData.2.2.2.1, disjointData.2.2.2.2,
    touching0, touching1, ⟨originalPair0, ownerPoint0⟩,
    ⟨originalPair1, ownerPoint1⟩⟩

end SelectedInterfaceCertificate

theorem P4418T3SelectedInterfaceExists
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
    Nonempty (P4418T3SelectedInterfaceData (occurrence a) (occurrence b)
      (occurrence owners.1) (occurrence owners.2)) := by
-- BODY
  classical
  let P := cert.P
  let O := cert.O
  let u := cert.u
  let v := cert.v
  have hOA : O.cells ⊆ (P 0 true).cells := SelectedInterfaceGeometry.hOA q cfg C T cert
  have hOB : O.cells ⊆ (P 0 false).cells := SelectedInterfaceGeometry.hOB q cfg C T cert
  have separation := BandOriginalPairSeparation P O u v hOA hOB cert.partition
  have pairCells (x y : PeriodicSubtileIndex) (hxy : x ≠ y)
      (hnot : ¬ ((x.label = .A ∧ y.label = .B ∨
        x.label = .B ∧ y.label = .A) ∧ x.first = y.first ∧ x.second = y.second)) :
      Disjoint (SubtileOccurrenceInterpretation P u v x).cells
        (SubtileOccurrenceInterpretation P u v y).cells :=
    separation.2 x y hxy hnot
  have translatedCells (X : ProtoTile) (d : GaussianInt) :
      (TileTranslation X d).cells = X.cells.image (GaussianTranslation d) :=
    (TileTranslationFormulas X d).1
  have cellInclusion (X Y : ProtoTile) (hXY : X.cells ⊆ Y.cells)
      (d : GaussianInt) :
      (TileTranslation X d).cells ⊆ (TileTranslation Y d).cells :=
          TileTranslationProperties.cellsSubset X Y hXY d
  have isolated (m n : Int) :
      ∀ z ∈ CellSupportedFootprintVertices
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)),
        ∀ x : GaussianInt, z ∈ FootprintVertices (⟨{x}, x⟩ : ProtoTile) →
            x ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨
              x ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells :=
                  SelectedInterfaceGeometry.isolated q cfg C T cert m n
  have translatedNonempty (X : ProtoTile) (hX : X.cells.Nonempty)
      (d : GaussianInt) : (TileTranslation X d).cells.Nonempty :=
          SelectedInterfaceGeometry.translatedNonempty translatedCells X hX d
  have parentNonempty (x : PeriodicSubtileIndex) :
      (SubtileOccurrenceInterpretation P u v x).cells.Nonempty :=
          SelectedInterfaceGeometry.parentNonempty q cfg C T cert translatedNonempty x
  have complementNonempty (m n : Int) :
      (TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty :=
            SelectedInterfaceGeometry.complementNonempty q cfg C T cert translatedNonempty m n
  have deletionSupport (m n : Int) (Y : ProtoTile) (hY : Y.cells.Nonempty) :
      (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells = ∅ ∨
        ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧
          Y.cells.Nonempty) := (Or.inr ⟨complementNonempty m n, hY⟩)
  have deleteEdge (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩).cells)
      (hYB : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B,m,n⟩).cells) :
      FootprintEdges (TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
        FootprintEdges Y =
      FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintEdges Y :=
          SelectedInterfaceGeometry.deleteEdge q cfg C T cert hOA cellInclusion isolated m n Y
          hYA hYB
  have deleteVertex (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩).cells)
      (hYB : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B,m,n⟩).cells)
      (hY : Y.cells.Nonempty) :
      FootprintVertices (TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
        FootprintVertices Y =
      FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩ FootprintVertices Y :=
          SelectedInterfaceGeometry.deleteVertex q cfg C T cert hOA cellInclusion isolated
          deletionSupport m n Y hYA hYB hY
  have modifiedA (m n : Int) :
      ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩ =
        TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩)
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) :=
              SelectedInterfaceGeometry.modifiedA q cfg C T cert m n
  have modifiedOther (x : PeriodicSubtileIndex) (hx : x.label ≠ .A) :
      ModifiedSubtileOccurrenceInterpretation P O u v x =
        SubtileOccurrenceInterpretation P u v x := SelectedInterfaceGeometry.modifiedOther q cfg
            C T cert x hx
  have modifiedAFootprintSubset (m n : Int) :
      FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ⊆
        FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) :=
            SelectedInterfaceGeometry.modifiedAFootprintSubset q cfg C T cert complementNonempty
            modifiedA m n
  have modifiedFootSubset (x : PeriodicSubtileIndex) :
      FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v x) ⊆
        FootprintVertices (SubtileOccurrenceInterpretation P u v x) :=
            SelectedInterfaceGeometry.modifiedFootSubset q cfg C T cert modifiedAFootprintSubset x
  have modifiedAEdges (m n : Int) (x : PeriodicSubtileIndex)
      (hx : x.label ≠ .A)
      (hpair : ¬ (x.label = .B ∧ x.first = m ∧ x.second = n)) :
      FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩
          FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v x) =
        FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v x) :=
              SelectedInterfaceGeometry.modifiedAEdges q cfg C T cert pairCells deleteEdge
              modifiedA modifiedOther m n x hx hpair
  have modifiedAVertices (m n : Int) (x : PeriodicSubtileIndex)
      (hx : x.label ≠ .A)
      (hpair : ¬ (x.label = .B ∧ x.first = m ∧ x.second = n)) :
      FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A,m,n⟩) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v x) =
        FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A,m,n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v x) :=
              SelectedInterfaceGeometry.modifiedAVertices q cfg C T cert pairCells parentNonempty
              deleteVertex modifiedA modifiedOther m n x hx hpair
  have retargeted :
      (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
        FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b) =
       FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
        FootprintEdges (SubtileOccurrenceInterpretation P u v b)) ∧
      (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
        FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) =
       FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
        FootprintVertices (SubtileOccurrenceInterpretation P u v b)) :=
            SelectedInterfaceGeometry.retargeted q cfg C T cert a b row modifiedAEdges
            modifiedAVertices
  let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
  let face0 : PeriodicSubtileFaceIndex := selectedFirstFace q cfg C T cert a b row
  let face1 : PeriodicSubtileFaceIndex := selectedSecondFace q cfg C T cert a b row
  let F0 := cert.modifiedFaceEquivalence.symm face0
  let F1 := cert.modifiedFaceEquivalence.symm face1
  have faceVertex (f : PeriodicSubtileFaceIndex) (i : Fin 3) :
      cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm f) i =
        SixSubtileFaceVertices f i := SelectedInterfaceGeometry.faceVertex q cfg C T cert f i
  have faceDistinct : F0 ≠ F1 := SelectedInterfaceGeometry.faceDistinct q cfg C T cert a b row
  have faceTable :
      (∃ iA iB iO : Fin 3,
        cert.modified.plane.faceVertex F0 iA = a ∧
        cert.modified.plane.faceVertex F0 iB = b ∧
        cert.modified.plane.faceVertex F0 iO = owners.1) ∧
      (∃ jA jB jO : Fin 3,
        cert.modified.plane.faceVertex F1 jA = a ∧
        cert.modified.plane.faceVertex F1 jB = b ∧
        cert.modified.plane.faceVertex F1 jO = owners.2) := SelectedInterfaceGeometry.faceTable q
            cfg C T cert a b row faceVertex
  have reversePath {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (h : SimpleGridPathBetween V E x y) :
      SimpleGridPathBetween V E y x := SelectedInterfaceGeometry.reversePath (V := V) (E := E) (x
          := x) (y := y) h
  have hne : a ≠ b := (show
      a ≠ b
    from by
      classical
      intro h
      cases row <;> cases h)
  have allowed : AllowedSubtileIncidence a b := SelectedInterfaceGeometry.allowed q cfg C T cert
      a b row
  have modifiedEdges :
      (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
        FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty :=
            SelectedInterfaceGeometry.modifiedEdges q cfg C T cert a b hne allowed
  have headLastNe (p : List GaussianInt) (hnd : p.Nodup)
      (hlen : 2 ≤ p.length) : p.head? ≠ p.getLast? := SelectedInterfaceGeometry.headLastNe p hnd
          hlen
  have pathAtOwners :
      SimpleGridPathBetween
        (FootprintVertices (occurrence a) ∩ FootprintVertices (occurrence b))
        (FootprintEdges (occurrence a) ∩ FootprintEdges (occurrence b))
        (cert.modified.rho F0) (cert.modified.rho F1) := SelectedInterfaceGeometry.pathAtOwners q
            cfg C T cert a b row retargeted faceDistinct faceTable reversePath hne modifiedEdges
  have endpointsDistinct : cert.modified.rho F0 ≠ cert.modified.rho F1 :=
      SelectedInterfaceGeometry.endpointsDistinct q cfg C T cert a b row headLastNe
      pathAtOwners
  have selectedCertificate :
    let occurrence := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
    Nonempty (P4418T3SelectedInterfaceData (occurrence a) (occurrence b)
      (occurrence owners.1) (occurrence owners.2)) :=
          SelectedInterfaceCertificate.selectedCertificate q cfg C T cert a b row pairCells
          modifiedFootSubset retargeted faceTable pathAtOwners endpointsDistinct
  exact selectedCertificate


end ApollonianSuperharmonic

end
