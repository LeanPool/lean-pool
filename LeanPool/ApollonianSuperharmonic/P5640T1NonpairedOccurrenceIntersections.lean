/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.FootprintDeletionRetention
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance

-- [TABLET NODE: P5640T1NonpairedOccurrenceIntersections]

/-!
# P5640T1NonpairedOccurrenceIntersections

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace NonpairedOccurrenceGeometry

private theorem precursorInPlus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        O.cells ⊆ (P 0 true).cells ) := by
  classical
  intro q cfg C₀ T layout P O z hz
  change z ∈ layout.O.cells at hz
  rw [layout.precursor_eq] at hz
  exact (layout.plus_union z).2 ⟨0, false, hz⟩

private theorem precursorInMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        O.cells ⊆ (P 0 false).cells ) := by
  classical
  intro q cfg C₀ T layout P O z hz
  change z ∈ layout.O.cells at hz
  rw [layout.precursor_cells] at hz
  exact (layout.minus_union z).2 ⟨0, true, hz⟩

private theorem pairCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        ((∀ (m : ℤ), ∀ (n : ℤ), (SubtileOccurrenceInterpretation P u v ⟨SixSubtileLabel.A, m,
            n⟩).cells ∩ (SubtileOccurrenceInterpretation P u v ⟨SixSubtileLabel.B, m, n⟩).cells =
            (TileTranslation O ((↑m : GaussianInt) * u + (↑n : GaussianInt) * v)).cells) ∧ ∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ¬((a.label =
            SixSubtileLabel.A ∧ b.label = SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧
            b.label = SixSubtileLabel.A) ∧ a.first = b.first ∧ a.second = b.second) → Disjoint
            (SubtileOccurrenceInterpretation P u v a).cells (SubtileOccurrenceInterpretation P u
            v b).cells) → (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) →
            ((¬ ((a.label = .A ∧ b.label = .B ∨
            a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second = b.second)) → (Disjoint
                (SubtileOccurrenceInterpretation P u v a).cells (SubtileOccurrenceInterpretation
                P u v b).cells))) ) := by
  classical
  intro q cfg C₀ T layout P O u v separation a b hab hnot
  exact separation.2 a b hab hnot


private theorem cellInclusion :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d)) → (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆ Y.cells)
            → (∀ (d : GaussianInt), (TileTranslation X d).cells ⊆ (TileTranslation Y d).cells)) )
            := by
  classical
  intro translationCells X Y hXY d
  rw [translationCells, translationCells]
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨w, hXY hw, rfl⟩

private theorem isolatedPrecursor :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        ∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v)), ∀ a : GaussianInt, z ∈ FootprintVertices
            (⟨{a}, a⟩ : ProtoTile) → a ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells
            ∨ a ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells ) := by
  classical
  intro q cfg C₀ T layout P O u v m n z hz a hza
  by_cases hnon : (TileTranslation O
      ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells.Nonempty
  · have hzraw : z ∈ FootprintVertices (TileTranslation O
        ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
      simpa [CellSupportedFootprintVertices, FootprintVertices, hnon] using hz
    exact layout.precursor_isolated m n z hzraw a hza
  · rcases hz with ⟨w, hw, _⟩
    exact (hnon ⟨w, hw⟩).elim

private theorem translatedNonempty :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (d : GaussianInt), (TileTranslation X d).cells = X.cells.image
            (GaussianTranslation d)) → (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d :
            GaussianInt), (TileTranslation X d).cells.Nonempty)) ) := by
  classical
  intro translationCells X hne d
  rw [translationCells]
  obtain ⟨z, hz⟩ := hne
  exact ⟨GaussianTranslation d z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩

private theorem deletionEdge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (d : GaussianInt), (TileTranslation X d).cells ⊆ (TileTranslation Y
            d).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a :
            GaussianInt, z ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.A, m, n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B,
            m, n⟩).cells) → (FootprintEdges (TileCellComplement (SubtileOccurrenceInterpretation
            P u v ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))) ∩ FootprintEdges Y = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A,
            m, n⟩) ∩ FootprintEdges Y))))) ) := by
  classical
  intro q cfg C₀ T layout P O u v precursorInPlus cellInclusion isolatedPrecursor m n Y hYA hYB
  have h := FootprintDeletionRetention
    (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
    (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩)
    (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) Y
    (cellInclusion O (P 0 true) precursorInPlus _) (isolatedPrecursor m n) hYA hYB
  exact h.2.1

private theorem deletionVertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (d : GaussianInt), (TileTranslation X d).cells ⊆ (TileTranslation Y
            d).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ z ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a :
            GaussianInt, z ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v
            ⟨.A, m, n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B,
            m, n⟩).cells) → (((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨
            ((TileCellComplement
              (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
              (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧
              Y.cells.Nonempty)) → (FootprintVertices (TileCellComplement
                  (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
                  GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y =
                  FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
                  FootprintVertices Y)))))) ) := by
  classical
  intro q cfg C₀ T layout P O u v precursorInPlus cellInclusion isolatedPrecursor m n Y hYA hYB
      hsupport
  have h := FootprintDeletionRetention
    (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
    (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩)
    (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) Y
    (cellInclusion O (P 0 true) precursorInPlus _) (isolatedPrecursor m n) hYA hYB
  exact h.2.2 hsupport

private theorem translateComplement :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (d : GaussianInt), TileTranslation
            (TileCellComplement A B) d = TileCellComplement (TileTranslation A d)
            (TileTranslation B d) ) := by
  classical
  intro A B d
  exact (TileCellComplementCovariance A B d).1

private theorem modifiedA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (d : GaussianInt), TileTranslation
            (TileCellComplement A B) d = TileCellComplement (TileTranslation A d)
            (TileTranslation B d)) → (∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ) := by
  classical
  intro q cfg C₀ T layout P O u v translateComplement m n
  change TileTranslation (TileCellComplement (P 0 true) O)
    ((m : GaussianInt) * u + (n : GaussianInt) * v) = _
  rw [translateComplement]
  rfl

private theorem modifiedOther :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        ∀ (b : PeriodicSubtileIndex), (b.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P
            O u v b = SubtileOccurrenceInterpretation P u v b) ) := by
  classical
  intro q cfg C₀ T layout P O u v b hb
  cases b with
  | mk label first second =>
    cases label with
    | A => exact (hb rfl).elim
    | B => rfl
    | C => rfl
    | D => rfl
    | E => rfl
    | F => rfl

private theorem parentNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let u := layout.u
        let v := layout.v
        (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d : GaussianInt), (TileTranslation X
            d).cells.Nonempty)) → (∀ (b : PeriodicSubtileIndex), (SubtileOccurrenceInterpretation
            P u v b).cells.Nonempty) ) := by
  classical
  intro q cfg C₀ T layout P u v translatedNonempty b
  cases b with
  | mk label first second =>
    cases label with
    | A =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 0 true) ((LatticeTileGridStructure (P 0 true)
            (layout.parent_lattice 0 true)).1.1) _
    | B =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 0 false) ((LatticeTileGridStructure (P 0 false)
            (layout.parent_lattice 0 false)).1.1) _
    | C =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 1 true) ((LatticeTileGridStructure (P 1 true)
            (layout.parent_lattice 1 true)).1.1) _
    | D =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 1 false) ((LatticeTileGridStructure (P 1 false)
            (layout.parent_lattice 1 false)).1.1) _
    | E =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 2 true) ((LatticeTileGridStructure (P 2 true)
            (layout.parent_lattice 2 true)).1.1) _
    | F =>
        simpa [SubtileOccurrenceInterpretation] using translatedNonempty
          (P 2 false) ((LatticeTileGridStructure (P 2 false)
            (layout.parent_lattice 2 false)).1.1) _

private theorem complementNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (d : GaussianInt), (TileTranslation X
            d).cells.Nonempty)) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (d : GaussianInt),
            TileTranslation (TileCellComplement A B) d = TileCellComplement (TileTranslation A d)
            (TileTranslation B d)) → (∀ (m : Int), ∀ (n : Int), (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty)) ) := by
  classical
  intro q cfg C₀ T layout P O u v translatedNonempty translateComplement m n
  have ht := translatedNonempty (TileCellComplement (P 0 true) O)
    ((LatticeTileGridStructure _ layout.precursor_complement_lattice.1).1.1)
    ((m : GaussianInt) * u + (n : GaussianInt) * v)
  rw [translateComplement] at ht
  simpa [SubtileOccurrenceInterpretation] using ht

private theorem deletionSupport :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (∀ (m : Int), ∀ (n : Int), (TileCellComplement (SubtileOccurrenceInterpretation P u v
            ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty) → (∀ (m : Int), ∀ (n : Int), ∀ (Y : ProtoTile),
            (Y.cells.Nonempty) → ((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty))) ) := by
  classical
  intro q cfg C₀ T layout P O u v complementNonempty m n Y hY
  by_cases hO : O.cells = ∅
  · exact Or.inl ((TileTranslationFormulas O
      ((m : GaussianInt) * u + (n : GaussianInt) * v)).2.2.1.mpr hO)
  · exact Or.inr ⟨complementNonempty m n, hY⟩

private theorem modifiedAEdges :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y
            : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (FootprintEdges (TileCellComplement (SubtileOccurrenceInterpretation P u
            v ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
            FootprintEdges Y = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
            ∩ FootprintEdges Y))) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (b : PeriodicSubtileIndex),
            (b.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O u v b =
            SubtileOccurrenceInterpretation P u v b)) → (∀ (m : Int), ∀ (n : Int), ∀ (b :
            PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label = .B ∧ b.first = m ∧ b.second =
            n)) → (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
            FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b))))))) ) := by
  classical
  intro q cfg C₀ T layout P O u v pairCells deletionEdge modifiedA modifiedOther m n b hbA hbpair
  have hneA : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    exact hbA (by simpa using (congrArg PeriodicSubtileIndex.label he).symm)
  have hneB : (⟨.B, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    apply hbpair
    exact ⟨by simpa using (congrArg PeriodicSubtileIndex.label he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.first he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.second he).symm⟩
  have hfirst := deletionEdge m n (SubtileOccurrenceInterpretation P u v b)
    (pairCells b ⟨.A, m, n⟩ hneA.symm (by
      intro hp
      rcases hp with ⟨hlabels, hfirst, hsecond⟩
      rcases hlabels with ⟨hbA', hAB⟩ | ⟨hbB, hBA⟩
      · cases hAB
      · exact hbpair ⟨hbB, by simpa using hfirst,
          by simpa using hsecond⟩))
    (pairCells b ⟨.B, m, n⟩ hneB.symm (by
      intro hp
      rcases hp with ⟨hlabels, hfirst, hsecond⟩
      rcases hlabels with ⟨hbA', hAB⟩ | ⟨hbB, hBA⟩
      · exact hbA hbA'
      · cases hBA))
  rw [modifiedA m n, modifiedOther b hbA]
  exact hfirst

private theorem modifiedAVertices :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := layout.P
        let O := layout.O
        let u := layout.u
        let v := layout.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y
            : ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty)) → (FootprintVertices (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices Y)))) → ((∀ (m
            : Int), ∀ (n : Int), ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ =
            TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (b :
            PeriodicSubtileIndex), (b.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O
            u v b = SubtileOccurrenceInterpretation P u v b)) → ((∀ (b : PeriodicSubtileIndex),
            (SubtileOccurrenceInterpretation P u v b).cells.Nonempty) → ((∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Y.cells.Nonempty) → ((TileTranslation O ((m : GaussianInt)
            * u + (n : GaussianInt) * v)).cells = ∅ ∨ ((TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧ Y.cells.Nonempty))) → (∀
            (m : Int), ∀ (n : Int), ∀ (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label =
            .B ∧ b.first = m ∧ b.second = n)) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b))))))))) ) := by
  classical
  intro q cfg C₀ T layout P O u v pairCells deletionVertex modifiedA modifiedOther parentNonempty
      deletionSupport m n b hbA hbpair
  have hneA : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    exact hbA (by simpa using (congrArg PeriodicSubtileIndex.label he).symm)
  have hneB : (⟨.B, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    apply hbpair
    exact ⟨by simpa using (congrArg PeriodicSubtileIndex.label he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.first he).symm,
      by simpa using (congrArg PeriodicSubtileIndex.second he).symm⟩
  have hfirst := deletionVertex m n (SubtileOccurrenceInterpretation P u v b)
    (pairCells b ⟨.A, m, n⟩ hneA.symm (by
      intro hp
      rcases hp with ⟨hlabels, hfirst, hsecond⟩
      rcases hlabels with ⟨hbA', hAB⟩ | ⟨hbB, hBA⟩
      · cases hAB
      · exact hbpair ⟨hbB, by simpa using hfirst,
          by simpa using hsecond⟩))
    (pairCells b ⟨.B, m, n⟩ hneB.symm (by
      intro hp
      rcases hp with ⟨hlabels, hfirst, hsecond⟩
      rcases hlabels with ⟨hbA', hAB⟩ | ⟨hbB, hBA⟩
      · exact hbA hbA'
      · cases hBA))
    (deletionSupport m n (SubtileOccurrenceInterpretation P u v b)
      (parentNonempty b))
  rw [modifiedA m n, modifiedOther b hbA]
  exact hfirst

private theorem allowedLabelNe :
    (by
      classical
      exact
        ∀ {a : PeriodicSubtileIndex}, ∀ {b : PeriodicSubtileIndex}, AllowedSubtileIncidence a b →
            a.label ≠ b.label ) := by
  classical
  intro a b hab
  induction hab with
  | AB => intro h; cases h
  | AB01 => intro h; cases h
  | AB11 => intro h; cases h
  | AC => intro h; cases h
  | AC11 => intro h; cases h
  | AD => intro h; cases h
  | AE01 => intro h; cases h
  | AF => intro h; cases h
  | BC => intro h; cases h
  | BDm1m1 => intro h; cases h
  | BD => intro h; cases h
  | BE => intro h; cases h
  | BF0m1 => intro h; cases h
  | CDm10 => intro h; cases h
  | CEm10 => intro h; cases h
  | CF => intro h; cases h
  | DE => intro h; cases h
  | DF10 => intro h; cases h
  | symm _ ih => exact ih.symm

private theorem hpairAt392 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), (¬(((⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex).label =
            SixSubtileLabel.A ∧ (⟨SixSubtileLabel.B, p, r⟩ : PeriodicSubtileIndex).label =
                SixSubtileLabel.B ∨
            (⟨SixSubtileLabel.A, m, n⟩ : PeriodicSubtileIndex).label = SixSubtileLabel.B ∧
                (⟨SixSubtileLabel.B, p, r⟩ : PeriodicSubtileIndex).label
            = SixSubtileLabel.A) ∧ (⟨SixSubtileLabel.A, m, n⟩ : PeriodicSubtileIndex).first =
                (⟨SixSubtileLabel.B, p,
            r⟩ : PeriodicSubtileIndex).first ∧ (⟨SixSubtileLabel.A, m, n⟩ :
                PeriodicSubtileIndex).second = (⟨SixSubtileLabel.B, p, r⟩ :
                PeriodicSubtileIndex).second)) → (¬
            ((.B : SixSubtileLabel) = .B ∧ p = m ∧ r = n)) ) := by
  classical
  intro m n p r hnot hp
  apply hnot
  exact ⟨Or.inl ⟨rfl, rfl⟩, by simpa using hp.2.1.symm,
    by simpa using hp.2.2.symm⟩

private theorem hpairAt410 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), (¬(((⟨SixSubtileLabel.B, m, n⟩ :
            PeriodicSubtileIndex).label =
            SixSubtileLabel.A ∧ (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex).label =
                SixSubtileLabel.B ∨
            (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex).label = SixSubtileLabel.B ∧
                (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex).label
            = SixSubtileLabel.A) ∧ (⟨SixSubtileLabel.B, m, n⟩ : PeriodicSubtileIndex).first =
                (⟨SixSubtileLabel.A, p,
            r⟩ : PeriodicSubtileIndex).first ∧ (⟨SixSubtileLabel.B, m, n⟩ :
                PeriodicSubtileIndex).second = (⟨SixSubtileLabel.A, p, r⟩ :
                PeriodicSubtileIndex).second)) → (¬
            ((.B : SixSubtileLabel) = .B ∧ m = p ∧ n = r)) ) := by
  classical
  intro m n p r hnot hp
  apply hnot
  exact ⟨Or.inr ⟨rfl, rfl⟩, by simpa using hp.2.1,
    by simpa using hp.2.2⟩

private theorem hpairAt427 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), ¬ ((.C : SixSubtileLabel) = .B ∧ m = p ∧ n =
            r) ) := by
  classical
  intro m n p r hp
  cases hp.1

private theorem hpairAt438 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), ¬ ((.D : SixSubtileLabel) = .B ∧ m = p ∧ n =
            r) ) := by
  classical
  intro m n p r hp
  cases hp.1

private theorem hpairAt449 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), ¬ ((.E : SixSubtileLabel) = .B ∧ m = p ∧ n =
            r) ) := by
  classical
  intro m n p r hp
  cases hp.1

private theorem hpairAt460 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), ¬ ((.F : SixSubtileLabel) = .B ∧ m = p ∧ n =
            r) ) := by
  classical
  intro m n p r hp
  cases hp.1

end NonpairedOccurrenceGeometry

theorem P5640T1NonpairedOccurrenceIntersections
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (layout : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (a b : PeriodicSubtileIndex)
    (hab : AllowedSubtileIncidence a b)
    (hnot : ¬ ((a.label = .A ∧ b.label = .B ∨
        a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second = b.second)) :
    (FootprintEdges
        (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v a) ∩
      FootprintEdges
        (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v b) =
      FootprintEdges (SubtileOccurrenceInterpretation layout.P layout.u layout.v a) ∩
        FootprintEdges (SubtileOccurrenceInterpretation layout.P layout.u layout.v b)) ∧
    (FootprintVertices
        (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v a) ∩
      FootprintVertices
        (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v b) =
      FootprintVertices (SubtileOccurrenceInterpretation layout.P layout.u layout.v a) ∩
        FootprintVertices (SubtileOccurrenceInterpretation layout.P layout.u layout.v b)) := by
-- BODY
  classical
  let P := layout.P
  let O := layout.O
  let u := layout.u
  let v := layout.v
  have precursorInPlus := NonpairedOccurrenceGeometry.precursorInPlus q cfg C₀ T layout
  have precursorInMinus := NonpairedOccurrenceGeometry.precursorInMinus q cfg C₀ T layout
  have separation := BandOriginalPairSeparation P O u v precursorInPlus
    precursorInMinus layout.partition
  have pairCells (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (hnot : ¬ ((a.label = .A ∧ b.label = .B ∨
        a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second = b.second)) :=
            NonpairedOccurrenceGeometry.pairCells q cfg C₀ T layout separation a b hab hnot
  have translationCells (X : ProtoTile) (d : GaussianInt) :=
      TileTranslationProperties.cells X d
  have cellInclusion (X Y : ProtoTile) (hXY : X.cells ⊆ Y.cells)
      (d : GaussianInt) := NonpairedOccurrenceGeometry.cellInclusion translationCells X Y hXY d
  have isolatedPrecursor (m n : Int) := NonpairedOccurrenceGeometry.isolatedPrecursor q cfg C₀ T
      layout m n
  have translatedNonempty (X : ProtoTile) (hne : X.cells.Nonempty)
      (d : GaussianInt) := NonpairedOccurrenceGeometry.translatedNonempty translationCells X hne d
  have deletionEdge (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells)
      (hYB : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) :=
          NonpairedOccurrenceGeometry.deletionEdge q cfg C₀ T layout precursorInPlus
          cellInclusion isolatedPrecursor m n Y hYA hYB
  have deletionVertex (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells)
      (hYB : Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells)
      (hsupport : (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells = ∅ ∨
        ((TileCellComplement
          (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
          (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧
          Y.cells.Nonempty)) := NonpairedOccurrenceGeometry.deletionVertex q cfg C₀ T layout
              precursorInPlus cellInclusion isolatedPrecursor m n Y hYA hYB hsupport
  have translateComplement (A B : ProtoTile) (d : GaussianInt) :=
      NonpairedOccurrenceGeometry.translateComplement A B d
  have modifiedA (m n : Int) := NonpairedOccurrenceGeometry.modifiedA q cfg C₀ T layout
      translateComplement m n
  have modifiedOther (b : PeriodicSubtileIndex) (hb : b.label ≠ .A) :=
      NonpairedOccurrenceGeometry.modifiedOther q cfg C₀ T layout b hb
  have parentNonempty (b : PeriodicSubtileIndex) := NonpairedOccurrenceGeometry.parentNonempty q
      cfg C₀ T layout translatedNonempty b
  have complementNonempty (m n : Int) := NonpairedOccurrenceGeometry.complementNonempty q cfg C₀
      T layout translatedNonempty translateComplement m n
  have deletionSupport (m n : Int) (Y : ProtoTile) (hY : Y.cells.Nonempty) :=
      NonpairedOccurrenceGeometry.deletionSupport q cfg C₀ T layout complementNonempty m n Y hY
  have modifiedAEdges (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A)
      (hbpair : ¬ (b.label = .B ∧ b.first = m ∧ b.second = n)) :
      FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b) =
        FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v b) :=
              NonpairedOccurrenceGeometry.modifiedAEdges q cfg C₀ T layout pairCells deletionEdge
              modifiedA modifiedOther m n b hbA hbpair
  have modifiedAVertices (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A)
      (hbpair : ¬ (b.label = .B ∧ b.first = m ∧ b.second = n)) :
      FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) =
        FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v b) :=
              NonpairedOccurrenceGeometry.modifiedAVertices q cfg C₀ T layout pairCells
              deletionVertex modifiedA modifiedOther parentNonempty deletionSupport m n b hbA hbpair
  have allowedLabelNe : ∀ {a b : PeriodicSubtileIndex},
      AllowedSubtileIncidence a b → a.label ≠ b.label :=
    @NonpairedOccurrenceGeometry.allowedLabelNe
  cases a with
  | mk la m n =>
    cases b with
    | mk lb p r =>
      cases la with
      | A =>
        cases lb with
        | A => exact (allowedLabelNe hab rfl).elim
        | B =>
          have hpair : ¬ ((.B : SixSubtileLabel) = .B ∧ p = m ∧ r = n) :=
              NonpairedOccurrenceGeometry.hpairAt392 m n p r hnot
          exact ⟨modifiedAEdges m n ⟨.B, p, r⟩ (by simp) hpair,
            modifiedAVertices m n ⟨.B, p, r⟩ (by simp) hpair⟩
        | C => exact ⟨modifiedAEdges m n ⟨.C, p, r⟩ (by simp) (by intro hp; cases hp.1),
            modifiedAVertices m n ⟨.C, p, r⟩ (by simp) (by intro hp; cases hp.1)⟩
        | D => exact ⟨modifiedAEdges m n ⟨.D, p, r⟩ (by simp) (by intro hp; cases hp.1),
            modifiedAVertices m n ⟨.D, p, r⟩ (by simp) (by intro hp; cases hp.1)⟩
        | E => exact ⟨modifiedAEdges m n ⟨.E, p, r⟩ (by simp) (by intro hp; cases hp.1),
            modifiedAVertices m n ⟨.E, p, r⟩ (by simp) (by intro hp; cases hp.1)⟩
        | F => exact ⟨modifiedAEdges m n ⟨.F, p, r⟩ (by simp) (by intro hp; cases hp.1),
            modifiedAVertices m n ⟨.F, p, r⟩ (by simp) (by intro hp; cases hp.1)⟩
      | B =>
        cases lb with
        | A =>
          have hpair : ¬ ((.B : SixSubtileLabel) = .B ∧ m = p ∧ n = r) :=
              NonpairedOccurrenceGeometry.hpairAt410 m n p r hnot
          have he := modifiedAEdges p r ⟨.B, m, n⟩ (by simp) hpair
          have hv := modifiedAVertices p r ⟨.B, m, n⟩ (by simp) hpair
          exact ⟨by simpa [Set.inter_comm] using he,
            by simpa [Set.inter_comm] using hv⟩
        | B => exact ⟨by rfl, by rfl⟩
        | C => exact ⟨by rfl, by rfl⟩
        | D => exact ⟨by rfl, by rfl⟩
        | E => exact ⟨by rfl, by rfl⟩
        | F => exact ⟨by rfl, by rfl⟩
      | C =>
        cases lb with
        | A =>
          have hpair : ¬ ((.C : SixSubtileLabel) = .B ∧ m = p ∧ n = r) :=
              NonpairedOccurrenceGeometry.hpairAt427 m n p r
          have he := modifiedAEdges p r ⟨.C, m, n⟩ (by simp) hpair
          have hv := modifiedAVertices p r ⟨.C, m, n⟩ (by simp) hpair
          exact ⟨by simpa [Set.inter_comm] using he,
            by simpa [Set.inter_comm] using hv⟩
        | B | C | D | E | F => exact ⟨by rfl, by rfl⟩
      | D =>
        cases lb with
        | A =>
          have hpair : ¬ ((.D : SixSubtileLabel) = .B ∧ m = p ∧ n = r) :=
              NonpairedOccurrenceGeometry.hpairAt438 m n p r
          have he := modifiedAEdges p r ⟨.D, m, n⟩ (by simp) hpair
          have hv := modifiedAVertices p r ⟨.D, m, n⟩ (by simp) hpair
          exact ⟨by simpa [Set.inter_comm] using he,
            by simpa [Set.inter_comm] using hv⟩
        | B | C | D | E | F => exact ⟨by rfl, by rfl⟩
      | E =>
        cases lb with
        | A =>
          have hpair : ¬ ((.E : SixSubtileLabel) = .B ∧ m = p ∧ n = r) :=
              NonpairedOccurrenceGeometry.hpairAt449 m n p r
          have he := modifiedAEdges p r ⟨.E, m, n⟩ (by simp) hpair
          have hv := modifiedAVertices p r ⟨.E, m, n⟩ (by simp) hpair
          exact ⟨by simpa [Set.inter_comm] using he,
            by simpa [Set.inter_comm] using hv⟩
        | B | C | D | E | F => exact ⟨by rfl, by rfl⟩
      | F =>
        cases lb with
        | A =>
          have hpair : ¬ ((.F : SixSubtileLabel) = .B ∧ m = p ∧ n = r) :=
              NonpairedOccurrenceGeometry.hpairAt460 m n p r
          have he := modifiedAEdges p r ⟨.F, m, n⟩ (by simp) hpair
          have hv := modifiedAVertices p r ⟨.F, m, n⟩ (by simp) hpair
          exact ⟨by simpa [Set.inter_comm] using he,
            by simpa [Set.inter_comm] using hv⟩
        | B | C | D | E | F => exact ⟨by rfl, by rfl⟩

end ApollonianSuperharmonic

end
