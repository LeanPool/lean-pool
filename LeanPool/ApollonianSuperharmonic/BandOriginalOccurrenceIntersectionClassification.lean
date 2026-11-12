/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeTileNonempty

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandOriginalPairSeparation
public import LeanPool.ApollonianSuperharmonic.FootprintDeletionRetention
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance

-- [TABLET NODE: BandOriginalOccurrenceIntersectionClassification]

/-!
# BandOriginalOccurrenceIntersectionClassification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OriginalIntersectionGeometry

private theorem hOA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        O.cells ⊆ (P 0 true).cells ) := by
  classical
  intro q cfg C₀ T cert P O
  change cert.O.cells ⊆ (cert.P 0 true).cells
  rw [cert.precursor_eq]
  intro x hx
  exact (cert.plus_union x).2 ⟨0, false, hx⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        O.cells ⊆ (P 0 false).cells ) := by
  classical
  intro q cfg C₀ T cert P O
  change cert.O.cells ⊆ (cert.P 0 false).cells
  rw [cert.precursor_cells]
  intro x hx
  exact (cert.minus_union x).2 ⟨0, true, hx⟩

private theorem hmodified :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (a : PeriodicSubtileIndex), cert.modified.tile a =
            ModifiedSubtileOccurrenceInterpretation P O u v a ) := by
  classical
  intro q cfg C₀ T cert P O u v a
  exact cert.modified_tile a


private theorem hmodA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (w : GaussianInt), TileTranslation
            (TileCellComplement A B) w = TileCellComplement (TileTranslation A w)
            (TileTranslation B w)) → (∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ) := by
  classical
  intro q cfg C₀ T cert P O u v htranslate_complement m n
  change TileTranslation (TileCellComplement (P 0 true) O)
      ((m : GaussianInt) * u + (n : GaussianInt) * v) = _
  rw [htranslate_complement]
  rfl

private theorem hmodother :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P
            O u v a = SubtileOccurrenceInterpretation P u v a) ) := by
  classical
  intro q cfg C₀ T cert P O u v a ha
  cases a with
  | mk label first second =>
    cases label <;> simp_all [ModifiedSubtileOccurrenceInterpretation,
      SubtileOccurrenceInterpretation]

private theorem hcell_inclusion :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (w : GaussianInt), (TileTranslation X w).cells = X.cells.image
            (GaussianTranslation w)) → (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆ Y.cells)
            → (∀ (w : GaussianInt), (TileTranslation X w).cells ⊆ (TileTranslation Y w).cells)) )
            := by
  classical
  intro htranscells X Y hXY w
  rw [htranscells, htranscells]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_image.2 ⟨z, hXY hz, rfl⟩

private theorem hisolated :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ∀ (m : Int), ∀ (n : Int), ∀ x ∈ CellSupportedFootprintVertices (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v)), ∀ a : GaussianInt, x ∈ FootprintVertices
            (⟨{a}, a⟩ : ProtoTile) → a ∈ (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells
            ∨ a ∈ (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells ) := by
  classical
  intro q cfg C₀ T cert P O u v m n x hx a hxa
  by_cases hnon : (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells.Nonempty
  · have hxraw : x ∈ FootprintVertices
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) := by
      simpa [CellSupportedFootprintVertices, FootprintVertices, hnon] using hx
    exact cert.precursor_isolated m n x hxraw a hxa
  · rcases hx with ⟨z, hz, hshape⟩
    exact False.elim (hnon ⟨z, hz⟩)

private theorem hdel_edge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (w : GaussianInt), (TileTranslation X w).cells ⊆ (TileTranslation Y
            w).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ x ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a :
            GaussianInt, x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells) → ((Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (FootprintEdges
                (TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
                (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
                FootprintEdges Y = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m,
                n⟩) ∩ FootprintEdges Y))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hOA hcell_inclusion hisolated m n Y hYA hYB
  have h := FootprintDeletionRetention
    (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
    (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩)
    (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) Y
    (by
      exact hcell_inclusion O (P 0 true) hOA _) (hisolated m n) hYA hYB
  exact h.2.1

private theorem htranslated_nonempty :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (w : GaussianInt), (TileTranslation X w).cells = X.cells.image
            (GaussianTranslation w)) → (∀ (X : ProtoTile), (X.cells.Nonempty) → (∀ (w :
            GaussianInt), (TileTranslation X w).cells.Nonempty)) ) := by
  classical
  intro htranscells X hX w
  rw [htranscells]
  obtain ⟨x, hx⟩ := hX
  exact ⟨GaussianTranslation w x, Finset.mem_image.2 ⟨x, hx, rfl⟩⟩

private theorem hdel_vertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (O.cells ⊆ (P 0 true).cells) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            Y.cells) → (∀ (w : GaussianInt), (TileTranslation X w).cells ⊆ (TileTranslation Y
            w).cells)) → ((∀ (m : Int), ∀ (n : Int), ∀ x ∈ CellSupportedFootprintVertices
            (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)), ∀ a :
            GaussianInt, x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) → a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells ∨ a ∈
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (∀ (m : Int), ∀ (n :
            Int), ∀ (Y : ProtoTile), (Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells) → ((Disjoint Y.cells
            (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) → (((TileTranslation O ((m
                : GaussianInt) * u + (n : GaussianInt) * v)).cells = ∅ ∨
              ((TileCellComplement
                  (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
                  (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
                      v))).cells.Nonempty ∧
                Y.cells.Nonempty)) → (FootprintVertices (TileCellComplement
                    (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
                    GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y =
                    FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
                    FootprintVertices Y)))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hOA hcell_inclusion hisolated m n Y hYA hYB hsupport
  have h := FootprintDeletionRetention
    (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
    (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩)
    (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)) Y
    (by
      exact hcell_inclusion O (P 0 true) hOA _) (hisolated m n) hYA hYB
  exact h.2.2 hsupport

private theorem hparent_nonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let u := cert.u
        let v := cert.v
        (∀ (X : ProtoTile), (LatticeTile X) → (X.cells.Nonempty)) → ((∀ (X : ProtoTile),
            (X.cells.Nonempty) → (∀ (w : GaussianInt), (TileTranslation X w).cells.Nonempty)) →
            (∀ (a : PeriodicSubtileIndex), (SubtileOccurrenceInterpretation P u v
            a).cells.Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert P u v hnonempty htranslated_nonempty a
  cases a with
  | mk label first second =>
    cases label with
    | A =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 0 true) (cert.parent_lattice 0 true)) _
    | B =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 0 false) (cert.parent_lattice 0 false)) _
    | C =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 1 true) (cert.parent_lattice 1 true)) _
    | D =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 1 false) (cert.parent_lattice 1 false)) _
    | E =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 2 true) (cert.parent_lattice 2 true)) _
    | F =>
      simpa [SubtileOccurrenceInterpretation] using
        htranslated_nonempty _ (hnonempty (P 2 false) (cert.parent_lattice 2 false)) _

private theorem hcomplement_nonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (X : ProtoTile), (LatticeTile X) → (X.cells.Nonempty)) → ((∀ (A : ProtoTile), ∀ (B :
            ProtoTile), ∀ (w : GaussianInt), TileTranslation (TileCellComplement A B) w =
            TileCellComplement (TileTranslation A w) (TileTranslation B w)) → ((∀ (X :
            ProtoTile), (X.cells.Nonempty) → (∀ (w : GaussianInt), (TileTranslation X
            w).cells.Nonempty)) → (∀ (m : Int), ∀ (n : Int), (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hnonempty htranslate_complement htranslated_nonempty m n
  have ht := htranslated_nonempty (TileCellComplement (P 0 true) O)
    (hnonempty _ cert.precursor_complement_lattice.1)
    ((m : GaussianInt) * u + (n : GaussianInt) * v)
  rw [htranslate_complement] at ht
  simpa [SubtileOccurrenceInterpretation] using ht

private theorem hsupport_for :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), (TileCellComplement (SubtileOccurrenceInterpretation P u v
            ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty) → (∀ (m : Int), ∀ (n : Int), ∀ (Y : ProtoTile),
            (Y.cells.Nonempty) → ((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hcomplement_nonempty m n Y hY
  by_cases ho : O.cells = ∅
  · left
    exact (TileTranslationFormulas O
      ((m : GaussianInt) * u + (n : GaussianInt) * v)).2.2.1.mpr ho
  · exact Or.inr ⟨hcomplement_nonempty m n, hY⟩

private theorem hAedge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (a : PeriodicSubtileIndex),
            (a.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O u v a =
            SubtileOccurrenceInterpretation P u v a)) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y :
            ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (FootprintEdges (TileCellComplement (SubtileOccurrenceInterpretation P u
            v ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
            FootprintEdges Y = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
            ∩ FootprintEdges Y))) → (∀ (m : Int), ∀ (n : Int), ∀ (b : PeriodicSubtileIndex),
            (b.label ≠ .A) → ((¬ (b.label = .B ∧ b.first = m ∧ b.second = n)) → (FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b))))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hpaircells hmodA hmodother hdel_edge m n b hbA hbpair
  have hneA : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    have := congrArg PeriodicSubtileIndex.label he
    exact hbA (by simpa using this.symm)
  have hneB : (⟨.B, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    have hl := congrArg PeriodicSubtileIndex.label he
    have hf := congrArg PeriodicSubtileIndex.first he
    have hs := congrArg PeriodicSubtileIndex.second he
    exact hbpair ⟨by simpa using hl.symm, by simpa using hf.symm, by simpa using hs.symm⟩
  have hfirst := hdel_edge m n
      (SubtileOccurrenceInterpretation P u v b)
      (hpaircells _ _ hneA.symm (by
        intro hp
        rcases hp with (⟨ha, hbb⟩ | ⟨ha, hbb⟩) <;> simp_all))
      (hpaircells _ _ hneB.symm (by
        intro hp
        rcases hp with (⟨ha, hbb⟩ | ⟨ha, hbb⟩) <;> simp_all))
  rw [hmodA m n, hmodother b hbA]
  exact hfirst

private theorem hAvertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (a : PeriodicSubtileIndex),
            (a.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation P O u v a =
            SubtileOccurrenceInterpretation P u v a)) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y :
            ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty)) → (FootprintVertices (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices Y)))) → ((∀ (a
            : PeriodicSubtileIndex), (SubtileOccurrenceInterpretation P u v a).cells.Nonempty) →
            ((∀ (m : Int), ∀ (n : Int), ∀ (Y : ProtoTile), (Y.cells.Nonempty) → ((TileTranslation
            O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells = ∅ ∨ ((TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧ Y.cells.Nonempty))) → (∀
            (m : Int), ∀ (n : Int), ∀ (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label =
            .B ∧ b.first = m ∧ b.second = n)) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b))))))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hpaircells hmodA hmodother hdel_vertex hparent_nonempty
      hsupport_for m n b hbA hbpair
  have hneA : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    exact hbA (by simpa using (congrArg PeriodicSubtileIndex.label he).symm)
  have hneB : (⟨.B, m, n⟩ : PeriodicSubtileIndex) ≠ b := by
    intro he
    have hl := congrArg PeriodicSubtileIndex.label he
    have hf := congrArg PeriodicSubtileIndex.first he
    have hs := congrArg PeriodicSubtileIndex.second he
    exact hbpair ⟨by simpa using hl.symm, by simpa using hf.symm, by simpa using hs.symm⟩
  have hfirst := hdel_vertex m n
      (SubtileOccurrenceInterpretation P u v b)
      (hpaircells _ _ hneA.symm (by
        intro hp
        rcases hp with (⟨ha, hbb⟩ | ⟨ha, hbb⟩) <;> simp_all))
      (hpaircells _ _ hneB.symm (by
        intro hp
        rcases hp with (⟨ha, hbb⟩ | ⟨ha, hbb⟩) <;> simp_all))
      (hsupport_for m n _ (hparent_nonempty b))
  rw [hmodA m n, hmodother b hbA]
  exact hfirst

private theorem hAAedge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y :
            ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (FootprintEdges (TileCellComplement (SubtileOccurrenceInterpretation P u
            v ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))) ∩
            FootprintEdges Y = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
            ∩ FootprintEdges Y))) → (∀ (m : Int), ∀ (n : Int), ∀ (p : Int), ∀ (r : Int), ((m, n)
            ≠ (p, r)) → (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m,
            n⟩) ∩ FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) =
            FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hpaircells hmodA hdel_edge m n p r hne
  have hmp : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ ⟨.A, p, r⟩ := by
    intro he
    apply hne
    exact Prod.ext (by simpa using congrArg PeriodicSubtileIndex.first he)
      (by simpa using congrArg PeriodicSubtileIndex.second he)
  have hfirst := hdel_edge m n
      (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩)
      (hpaircells _ _ hmp.symm (by simp))
      (hpaircells ⟨.A, p, r⟩ ⟨.B, m, n⟩ (by simp) (by
        intro hp
        rcases hp with ⟨hl, hf, hs⟩
        simp at hl
        apply hne
        exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm)))
  rw [← hmodA m n] at hfirst
  have hsecond := hdel_edge p r
      (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩)
      (by
        rw [hmodA m n]
        apply (hpaircells ⟨.A, p, r⟩ ⟨.A, m, n⟩ hmp.symm (by simp)).symm.mono
        · intro x hx
          exact Finset.mem_sdiff.mp hx |>.1
        · intro x hx
          exact hx)
      (by
        rw [hmodA m n]
        apply (hpaircells ⟨.B, p, r⟩ ⟨.A, m, n⟩ (by simp) (by
          intro hp
          rcases hp with ⟨hl, hf, hs⟩
          simp at hl
          apply hne
          exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm))).symm.mono
        · intro x hx
          exact Finset.mem_sdiff.mp hx |>.1
        · intro x hx
          exact hx)
  rw [← hmodA p r] at hsecond
  calc
    FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
        FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) =
        FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) ∩
          FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) := by rw
              [Set.inter_comm]
    _ = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) := hsecond
    _ = FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) := by rw
              [Set.inter_comm]
    _ = FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) := hfirst

private theorem hAAvertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬ ((a.label = .A
            ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second =
            b.second)) → (Disjoint (SubtileOccurrenceInterpretation P u v a).cells
            (SubtileOccurrenceInterpretation P u v b).cells))) → ((∀ (m : Int), ∀ (n : Int),
            ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩ = TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y :
            ProtoTile), (Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩).cells) → ((Disjoint Y.cells (SubtileOccurrenceInterpretation P u v ⟨.B, m,
            n⟩).cells) → (((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty)) → (FootprintVertices (TileCellComplement
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) (TileTranslation O ((m :
            GaussianInt) * u + (n : GaussianInt) * v))) ∩ FootprintVertices Y = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices Y)))) → ((∀ (a
            : PeriodicSubtileIndex), (SubtileOccurrenceInterpretation P u v a).cells.Nonempty) →
            ((∀ (m : Int), ∀ (n : Int), (TileCellComplement (SubtileOccurrenceInterpretation P u
            v ⟨.A, m, n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty) → ((∀ (m : Int), ∀ (n : Int), ∀ (Y : ProtoTile),
            (Y.cells.Nonempty) → ((TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v)).cells = ∅ ∨ ((TileCellComplement (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) *
            v))).cells.Nonempty ∧ Y.cells.Nonempty))) → (∀ (m : Int), ∀ (n : Int), ∀ (p : Int), ∀
            (r : Int), ((m, n) ≠ (p, r)) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩)))))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hpaircells hmodA hdel_vertex hparent_nonempty
      hcomplement_nonempty hsupport_for m n p r hne
  have hmp : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ ⟨.A, p, r⟩ := by
    intro he
    apply hne
    exact Prod.ext (by simpa using congrArg PeriodicSubtileIndex.first he)
      (by simpa using congrArg PeriodicSubtileIndex.second he)
  have hfirst := hdel_vertex m n
      (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩)
      (hpaircells _ _ hmp.symm (by simp))
      (hpaircells ⟨.A, p, r⟩ ⟨.B, m, n⟩ (by simp) (by
        intro hp
        rcases hp with ⟨hl, hf, hs⟩
        simp at hl
        apply hne
        exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm)))
      (hsupport_for m n _ (hparent_nonempty ⟨.A, p, r⟩))
  rw [← hmodA m n] at hfirst
  have hsecond := hdel_vertex p r
      (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩)
      (by
        rw [hmodA m n]
        apply (hpaircells ⟨.A, p, r⟩ ⟨.A, m, n⟩ hmp.symm (by simp)).symm.mono
        · intro x hx
          exact Finset.mem_sdiff.mp hx |>.1
        · intro x hx
          exact hx)
      (by
        rw [hmodA m n]
        apply (hpaircells ⟨.B, p, r⟩ ⟨.A, m, n⟩ (by simp) (by
          intro hp
          rcases hp with ⟨hl, hf, hs⟩
          simp at hl
          apply hne
          exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm))).symm.mono
        · intro x hx
          exact Finset.mem_sdiff.mp hx |>.1
        · intro x hx
          exact hx)
      (hsupport_for p r _ (by simpa [hmodA m n] using hcomplement_nonempty m n))
  rw [← hmodA p r] at hsecond
  calc
    FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
        FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) =
        FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) := by rw
              [Set.inter_comm]
    _ = FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) := hsecond
    _ = FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) := by rw
              [Set.inter_comm]
    _ = FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) := hfirst

private theorem hmod_edge_allowed :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b)).Nonempty ↔
            cert.modified.plane.adjacent a b) ∧ ((FootprintEdges (cert.modified.tile a) ∩
            FootprintEdges (cert.modified.tile b)).Nonempty → SimpleGridPath
            (CommonFootprintEdgeVertices (cert.modified.tile a) (cert.modified.tile b))
            (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b)) ∧
            FootprintVertices (cert.modified.tile a) ∩ FootprintVertices (cert.modified.tile b) =
            CommonFootprintEdgeVertices (cert.modified.tile a) (cert.modified.tile b)) ∧
            (¬(FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile
            b)).Nonempty → FootprintVertices (cert.modified.tile a) ∩ FootprintVertices
            (cert.modified.tile b) = ∅ ∨ (FootprintVertices (cert.modified.tile a) ∩
            FootprintVertices (cert.modified.tile b)).Subsingleton)) ∧
            PeriodicTileAdjacentContactRegularity cert.modified) → ((∀ (a :
            PeriodicSubtileIndex), cert.modified.tile a = ModifiedSubtileOccurrenceInterpretation
            P O u v a) → ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            cert.modified.plane.adjacent a b ↔ AllowedSubtileIncidence a b) → (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty →
            AllowedSubtileIncidence a b)))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hclass hmodified hmodadj a b hab he
  have hc := hclass.1 a b (by
    intro heq
    apply hab
    exact heq)
  apply hmodadj a b |>.mp
  exact hc.1.mp (by simpa [hmodified a, hmodified b] using he)

private theorem hmod_vertex_alt :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), a ≠ b → ((FootprintEdges
            (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b)).Nonempty ↔
            cert.modified.plane.adjacent a b) ∧ ((FootprintEdges (cert.modified.tile a) ∩
            FootprintEdges (cert.modified.tile b)).Nonempty → SimpleGridPath
            (CommonFootprintEdgeVertices (cert.modified.tile a) (cert.modified.tile b))
            (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b)) ∧
            FootprintVertices (cert.modified.tile a) ∩ FootprintVertices (cert.modified.tile b) =
            CommonFootprintEdgeVertices (cert.modified.tile a) (cert.modified.tile b)) ∧
            (¬(FootprintEdges (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile
            b)).Nonempty → FootprintVertices (cert.modified.tile a) ∩ FootprintVertices
            (cert.modified.tile b) = ∅ ∨ (FootprintVertices (cert.modified.tile a) ∩
            FootprintVertices (cert.modified.tile b)).Subsingleton)) ∧
            PeriodicTileAdjacentContactRegularity cert.modified) → ((∀ (a :
            PeriodicSubtileIndex), cert.modified.tile a = ModifiedSubtileOccurrenceInterpretation
            P O u v a) → ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex),
            cert.modified.plane.adjacent a b ↔ AllowedSubtileIncidence a b) → (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬
            AllowedSubtileIncidence a b) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = ∅ ∨ (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Subsingleton))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hclass hmodified hmodadj a b hab hna
  have hc := hclass.1 a b hab
  have hne : ¬ (FootprintEdges (cert.modified.tile a) ∩
      FootprintEdges (cert.modified.tile b)).Nonempty := by
    intro he
    apply hna
    exact hmodadj a b |>.mp (hc.1.mp he)
  have hv := hc.2.2 hne
  simpa [hmodified a, hmodified b] using hv

private theorem hAraw :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), ∀ (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label =
            .B ∧ b.first = m ∧ b.second = n)) → (FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)))) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), (a ≠ b) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty →
            AllowedSubtileIncidence a b)) → (∀ (m : Int), ∀ (n : Int), ∀ (b :
            PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label = .B ∧ b.first = m ∧ b.second =
            n)) → (((⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b) → (((FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
              FootprintEdges (SubtileOccurrenceInterpretation P u v b)).Nonempty) →
                  (AllowedSubtileIncidence ⟨.A, m, n⟩ b)))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hAedge hmod_edge_allowed m n b hbA hbpair hab he
  apply hmod_edge_allowed _ _ hab
  rw [hAedge m n b hbA hbpair]
  exact he

private theorem hAAraw :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (m : Int), ∀ (n : Int), ∀ (p : Int), ∀ (r : Int), ((m, n) ≠ (p, r)) → (FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) = FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩))) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty →
            AllowedSubtileIncidence a b)) → (∀ (m : Int), ∀ (n : Int), ∀ (p : Int), ∀ (r : Int),
            ((m, n) ≠ (p, r)) → (((FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m,
            n⟩) ∩
              FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩)).Nonempty) →
                  (AllowedSubtileIncidence ⟨.A, m, n⟩ ⟨.A, p, r⟩)))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hAAedge hmod_edge_allowed m n p r hne he
  apply hmod_edge_allowed _ _ (by
    intro heq
    apply hne
    exact Prod.ext (by simpa using congrArg PeriodicSubtileIndex.first heq)
      (by simpa using congrArg PeriodicSubtileIndex.second heq))
  rw [hAAedge m n p r hne]
  exact he

private theorem hneAt625 :
    (by
      classical
      exact
        ∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), (¬(⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex) = (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex)) →
            ((¬AllowedSubtileIncidence (⟨SixSubtileLabel.A, m, n⟩ : PeriodicSubtileIndex)
            (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex)) → ((m, n) ≠ (p, r))) ) := by
  classical
  intro m n p r hab hna heq
  apply hab
  cases heq
  rfl

end OriginalIntersectionGeometry

namespace OriginalIntersectionAssembly

private theorem edgeImplication :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation
            P O u v a = SubtileOccurrenceInterpretation P u v a)) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintEdges
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty →
            AllowedSubtileIncidence a b)) → ((∀ (m : Int), ∀ (n : Int), ∀ (b :
            PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label = .B ∧ b.first = m ∧ b.second =
            n)) → (((⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b) → (((FootprintEdges
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintEdges
            (SubtileOccurrenceInterpretation P u v b)).Nonempty) → (AllowedSubtileIncidence ⟨.A,
            m, n⟩ b))))) → ((∀ (m : ℤ), ∀ (n : ℤ), ∀ (p : ℤ), ∀ (r : ℤ), (m, n) ≠ (p, r) →
            (FootprintEdges (SubtileOccurrenceInterpretation P u v (⟨SixSubtileLabel.A, m, n⟩ :
            PeriodicSubtileIndex)) ∩ FootprintEdges (SubtileOccurrenceInterpretation P u v
            (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex))).Nonempty →
            AllowedSubtileIncidence (⟨SixSubtileLabel.A, m, n⟩ : PeriodicSubtileIndex)
            (⟨SixSubtileLabel.A, p, r⟩ : PeriodicSubtileIndex)) → (∀ (a : PeriodicSubtileIndex),
            ∀ (b : PeriodicSubtileIndex), (a ≠ b) → (((FootprintEdges
            (SubtileOccurrenceInterpretation P u v a) ∩
            FootprintEdges (SubtileOccurrenceInterpretation P u v b)).Nonempty) →
                (AllowedSubtileIncidence a b)))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hmodother hmod_edge_allowed hAraw hAAraw a b hab he
  rcases a with ⟨la, m, n⟩
  rcases b with ⟨lb, p, r⟩
  cases la with
  | A =>
    cases lb with
    | A =>
      apply hAAraw m n p r
      · intro heq
        apply hab
        cases heq
        rfl
      · exact he
    | B =>
      by_cases hcoord : (m, n) = (p, r)
      · have hp : m = p := congrArg Prod.fst hcoord
        have hr : n = r := congrArg Prod.snd hcoord
        subst p
        subst r
        exact AllowedSubtileIncidence.AB m n
      · apply hAraw m n ⟨.B, p, r⟩ (by simp) (by
          intro hp
          rcases hp with ⟨_, hf, hs⟩
          apply hcoord
          exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm)) hab he
    | C => exact hAraw m n ⟨.C, p, r⟩ (by simp) (by simp) hab he
    | D => exact hAraw m n ⟨.D, p, r⟩ (by simp) (by simp) hab he
    | E => exact hAraw m n ⟨.E, p, r⟩ (by simp) (by simp) hab he
    | F => exact hAraw m n ⟨.F, p, r⟩ (by simp) (by simp) hab he
  | B =>
    by_cases hba : lb = .A
    · subst lb
      have he' : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩)).Nonempty :=
              by simpa [Set.inter_comm] using he
      by_cases hc : (m, n) = (p, r)
      · have hm : m = p := congrArg Prod.fst hc
        have hn : n = r := congrArg Prod.snd hc
        subst p
        subst r
        exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AB m n)
      · exact AllowedSubtileIncidence.symm
          (hAraw p r ⟨.B, m, n⟩ (by simp) (by
            intro hp
            rcases hp with ⟨_, hf, hs⟩
            apply hc
            exact Prod.ext (by simpa using hf) (by simpa using hs))
            (by intro heq; apply hab; exact heq.symm) he')
    · apply hmod_edge_allowed _ _ hab
      simpa [hmodother ⟨.B, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using he
  | C =>
    by_cases hba : lb = .A
    · subst lb
      have he' : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.C, m, n⟩)).Nonempty :=
          by simpa [Set.inter_comm] using he
      exact AllowedSubtileIncidence.symm (hAraw p r ⟨.C, m, n⟩ (by simp) (by simp) (by
            intro heq
            apply hab
            exact heq.symm) he')
    · apply hmod_edge_allowed _ _ hab
      simpa [hmodother ⟨.C, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using he
  | D =>
    by_cases hba : lb = .A
    · subst lb
      have he' : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.D, m, n⟩)).Nonempty :=
          by simpa [Set.inter_comm] using he
      exact AllowedSubtileIncidence.symm (hAraw p r ⟨.D, m, n⟩ (by simp) (by simp) (by
            intro heq
            apply hab
            exact heq.symm) he')
    · apply hmod_edge_allowed _ _ hab
      simpa [hmodother ⟨.D, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using he
  | E =>
    by_cases hba : lb = .A
    · subst lb
      have he' : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.E, m, n⟩)).Nonempty :=
          by simpa [Set.inter_comm] using he
      exact AllowedSubtileIncidence.symm (hAraw p r ⟨.E, m, n⟩ (by simp) (by simp) (by
            intro heq
            apply hab
            exact heq.symm) he')
    · apply hmod_edge_allowed _ _ hab
      simpa [hmodother ⟨.E, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using he
  | F =>
    by_cases hba : lb = .A
    · subst lb
      have he' : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.F, m, n⟩)).Nonempty :=
          by simpa [Set.inter_comm] using he
      exact AllowedSubtileIncidence.symm (hAraw p r ⟨.F, m, n⟩ (by simp) (by simp) (by
            intro heq
            apply hab
            exact heq.symm) he')
    · apply hmod_edge_allowed _ _ hab
      simpa [hmodother ⟨.F, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using he

private theorem vertexAlternative :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let P := cert.P
        let O := cert.O
        let u := cert.u
        let v := cert.v
        (∀ (a : PeriodicSubtileIndex), (a.label ≠ .A) → (ModifiedSubtileOccurrenceInterpretation
            P O u v a = SubtileOccurrenceInterpretation P u v a)) → ((∀ (m : Int), ∀ (n : Int), ∀
            (b : PeriodicSubtileIndex), (b.label ≠ .A) → ((¬ (b.label = .B ∧ b.first = m ∧
            b.second = n)) → (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v
            ⟨.A, m, n⟩) ∩ FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) =
            FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
            FootprintVertices (SubtileOccurrenceInterpretation P u v b)))) → ((∀ (m : Int), ∀ (n
            : Int), ∀ (p : Int), ∀ (r : Int), ((m, n) ≠ (p, r)) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) = FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩))) → ((∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬
            AllowedSubtileIncidence a b) → (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) = ∅ ∨ (FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩ FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b)).Subsingleton))) → (∀ (a :
            PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), (a ≠ b) → ((¬
            AllowedSubtileIncidence a b) → (FootprintVertices (SubtileOccurrenceInterpretation P
            u v a) ∩ FootprintVertices (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
            (FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩ FootprintVertices
            (SubtileOccurrenceInterpretation P u v b)).Subsingleton)))))) ) := by
  classical
  intro q cfg C₀ T cert P O u v hmodother hAvertex hAAvertex hmod_vertex_alt a b hab hna
  rcases a with ⟨la, m, n⟩
  rcases b with ⟨lb, p, r⟩
  cases la with
  | A =>
    cases lb with
    | A =>
      have hne : (m, n) ≠ (p, r) := OriginalIntersectionGeometry.hneAt625 m n p r hab hna
      have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.A, p, r⟩ (by
        intro heq
        apply hab
        exact heq) hna
      rw [hAAvertex m n p r hne] at hv
      exact hv
    | B =>
      by_cases hcoord : (m, n) = (p, r)
      · have hp : m = p := congrArg Prod.fst hcoord
        have hr : n = r := congrArg Prod.snd hcoord
        subst p
        subst r
        exact False.elim (hna (AllowedSubtileIncidence.AB m n))
      · have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.B, p, r⟩ hab hna
        rw [hAvertex m n ⟨.B, p, r⟩ (by simp) (by
          intro hp
          rcases hp with ⟨_, hf, hs⟩
          apply hcoord
          exact Prod.ext (by simpa using hf.symm) (by simpa using hs.symm))] at hv
        exact hv
    | C =>
      have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.C, p, r⟩ hab hna
      rw [hAvertex m n ⟨.C, p, r⟩ (by simp) (by simp)] at hv
      exact hv
    | D =>
      have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.D, p, r⟩ hab hna
      rw [hAvertex m n ⟨.D, p, r⟩ (by simp) (by simp)] at hv
      exact hv
    | E =>
      have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.E, p, r⟩ hab hna
      rw [hAvertex m n ⟨.E, p, r⟩ (by simp) (by simp)] at hv
      exact hv
    | F =>
      have hv := hmod_vertex_alt ⟨.A, m, n⟩ ⟨.F, p, r⟩ hab hna
      rw [hAvertex m n ⟨.F, p, r⟩ (by simp) (by simp)] at hv
      exact hv
  | B =>
    by_cases hba : lb = .A
    · subst lb
      have hv := hmod_vertex_alt ⟨.A, p, r⟩ ⟨.B, m, n⟩ (by intro heq; apply hab; exact heq.symm)
        (by intro hp; exact hna (AllowedSubtileIncidence.symm hp))
      rw [hAvertex p r ⟨.B, m, n⟩ (by simp) (by
        intro hp
        rcases hp with ⟨_, hf, hs⟩
        apply hna
        subst p
        subst r
        exact AllowedSubtileIncidence.symm (AllowedSubtileIncidence.AB m n))] at hv
      simpa [Set.inter_comm] using hv
    · have hv := hmod_vertex_alt ⟨.B, m, n⟩ ⟨lb, p, r⟩ hab hna
      simpa [hmodother ⟨.B, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using hv
  | C =>
    by_cases hba : lb = .A
    · subst lb
      have hv := hmod_vertex_alt ⟨.A, p, r⟩ ⟨.C, m, n⟩ (by intro heq; apply hab; exact heq.symm)
        (by intro hp; exact hna (AllowedSubtileIncidence.symm hp))
      rw [hAvertex p r ⟨.C, m, n⟩ (by simp) (by simp)] at hv
      simpa [Set.inter_comm] using hv
    · have hv := hmod_vertex_alt ⟨.C, m, n⟩ ⟨lb, p, r⟩ hab hna
      simpa [hmodother ⟨.C, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using hv
  | D =>
    by_cases hba : lb = .A
    · subst lb
      have hv := hmod_vertex_alt ⟨.A, p, r⟩ ⟨.D, m, n⟩ (by intro heq; apply hab; exact heq.symm)
        (by intro hp; exact hna (AllowedSubtileIncidence.symm hp))
      rw [hAvertex p r ⟨.D, m, n⟩ (by simp) (by simp)] at hv
      simpa [Set.inter_comm] using hv
    · have hv := hmod_vertex_alt ⟨.D, m, n⟩ ⟨lb, p, r⟩ hab hna
      simpa [hmodother ⟨.D, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using hv
  | E =>
    by_cases hba : lb = .A
    · subst lb
      have hv := hmod_vertex_alt ⟨.A, p, r⟩ ⟨.E, m, n⟩ (by intro heq; apply hab; exact heq.symm)
        (by intro hp; exact hna (AllowedSubtileIncidence.symm hp))
      rw [hAvertex p r ⟨.E, m, n⟩ (by simp) (by simp)] at hv
      simpa [Set.inter_comm] using hv
    · have hv := hmod_vertex_alt ⟨.E, m, n⟩ ⟨lb, p, r⟩ hab hna
      simpa [hmodother ⟨.E, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using hv
  | F =>
    by_cases hba : lb = .A
    · subst lb
      have hv := hmod_vertex_alt ⟨.A, p, r⟩ ⟨.F, m, n⟩ (by intro heq; apply hab; exact heq.symm)
        (by intro hp; exact hna (AllowedSubtileIncidence.symm hp))
      rw [hAvertex p r ⟨.F, m, n⟩ (by simp) (by simp)] at hv
      simpa [Set.inter_comm] using hv
    · have hv := hmod_vertex_alt ⟨.F, m, n⟩ ⟨lb, p, r⟩ hab hna
      simpa [hmodother ⟨.F, m, n⟩ (by simp), hmodother ⟨lb, p, r⟩ hba] using hv

end OriginalIntersectionAssembly

theorem BandOriginalOccurrenceIntersectionClassification
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    (let u := cert.u
     let v := cert.v
     ∀ a b : PeriodicSubtileIndex, a ≠ b →
       ((FootprintEdges (SubtileOccurrenceInterpretation cert.P u v a) ∩
           FootprintEdges
             (SubtileOccurrenceInterpretation cert.P u v b)).Nonempty →
         AllowedSubtileIncidence a b) ∧
       (¬ AllowedSubtileIncidence a b →
         FootprintVertices (SubtileOccurrenceInterpretation cert.P u v a) ∩
             FootprintVertices
               (SubtileOccurrenceInterpretation cert.P u v b) = ∅ ∨
           (FootprintVertices
                (SubtileOccurrenceInterpretation cert.P u v a) ∩
              FootprintVertices
                (SubtileOccurrenceInterpretation cert.P u v b)).Subsingleton)) := by
-- BODY
  classical
  let P := cert.P
  let O := cert.O
  let u := cert.u
  let v := cert.v
  have hOA := OriginalIntersectionGeometry.hOA q cfg C₀ T cert
  have hOB := OriginalIntersectionGeometry.hOB q cfg C₀ T cert
  have hseparation := BandOriginalPairSeparation P O u v hOA hOB cert.partition
  have hpaircells (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (hnot : ¬ ((a.label = .A ∧ b.label = .B ∨
        a.label = .B ∧ b.label = .A) ∧ a.first = b.first ∧ a.second = b.second)) :
      Disjoint (SubtileOccurrenceInterpretation P u v a).cells
        (SubtileOccurrenceInterpretation P u v b).cells :=
    hseparation.2 a b hab hnot
  have hclass := PeriodicTileIntersectionClassification cert.modified
  have hmodified (a : PeriodicSubtileIndex) := OriginalIntersectionGeometry.hmodified q cfg C₀ T
      cert a
  have hmodadj (a b : PeriodicSubtileIndex) :
      cert.modified.plane.adjacent a b ↔ AllowedSubtileIncidence a b :=
    cert.modified_adjacency a b
  have htranscells (X : ProtoTile) (w : GaussianInt) :
      (TileTranslation X w).cells = X.cells.image (GaussianTranslation w) :=
    (TileTranslationFormulas X w).1
  have hnonempty (X : ProtoTile) (hX : LatticeTile X) := LatticeTileNonempty.cells X hX
  have htranslate_complement (A B : ProtoTile) (w : GaussianInt) :
      TileTranslation (TileCellComplement A B) w =
        TileCellComplement (TileTranslation A w) (TileTranslation B w) :=
    (TileCellComplementCovariance A B w).1
  have hmodA (m n : Int) := OriginalIntersectionGeometry.hmodA q cfg C₀ T cert
      htranslate_complement m n
  have hmodother (a : PeriodicSubtileIndex) (ha : a.label ≠ .A) :
      ModifiedSubtileOccurrenceInterpretation P O u v a =
        SubtileOccurrenceInterpretation P u v a := OriginalIntersectionGeometry.hmodother q cfg
            C₀ T cert a ha
  have hcell_inclusion (X Y : ProtoTile) (hXY : X.cells ⊆ Y.cells)
      (w : GaussianInt) := OriginalIntersectionGeometry.hcell_inclusion htranscells X Y hXY w
  have hisolated (m n : Int) := OriginalIntersectionGeometry.hisolated q cfg C₀ T cert m n
  have hdel_edge (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells
        (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells)
      (hYB : Disjoint Y.cells
        (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells) :=
            OriginalIntersectionGeometry.hdel_edge q cfg C₀ T cert hOA hcell_inclusion hisolated
            m n Y hYA hYB
  have htranslated_nonempty (X : ProtoTile) (hX : X.cells.Nonempty)
      (w : GaussianInt) := OriginalIntersectionGeometry.htranslated_nonempty htranscells X hX w
  have hdel_vertex (m n : Int) (Y : ProtoTile)
      (hYA : Disjoint Y.cells
        (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩).cells)
      (hYB : Disjoint Y.cells
        (SubtileOccurrenceInterpretation P u v ⟨.B, m, n⟩).cells)
      (hsupport :
        (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v)).cells = ∅ ∨
          ((TileCellComplement
              (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩)
              (TileTranslation O ((m : GaussianInt) * u + (n : GaussianInt) * v))).cells.Nonempty ∧
            Y.cells.Nonempty)) := OriginalIntersectionGeometry.hdel_vertex q cfg C₀ T cert hOA
                hcell_inclusion hisolated m n Y hYA hYB hsupport
  have hparent_nonempty (a : PeriodicSubtileIndex) :=
      OriginalIntersectionGeometry.hparent_nonempty q cfg C₀ T cert hnonempty htranslated_nonempty a
  have hcomplement_nonempty (m n : Int) := OriginalIntersectionGeometry.hcomplement_nonempty q
      cfg C₀ T cert hnonempty htranslate_complement htranslated_nonempty m n
  have hsupport_for (m n : Int) (Y : ProtoTile) (hY : Y.cells.Nonempty) :=
      OriginalIntersectionGeometry.hsupport_for q cfg C₀ T cert hcomplement_nonempty m n Y hY
  have hAedge (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A)
      (hbpair : ¬ (b.label = .B ∧ b.first = m ∧ b.second = n)) :=
          OriginalIntersectionGeometry.hAedge q cfg C₀ T cert hpaircells hmodA hmodother
          hdel_edge m n b hbA hbpair
  have hAvertex (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A)
      (hbpair : ¬ (b.label = .B ∧ b.first = m ∧ b.second = n)) :
      FootprintVertices
          (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v b) =
        FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v b) :=
              OriginalIntersectionGeometry.hAvertex q cfg C₀ T cert hpaircells hmodA hmodother
              hdel_vertex hparent_nonempty hsupport_for m n b hbA hbpair
  have hAAedge (m n p r : Int) (hne : (m, n) ≠ (p, r)) := OriginalIntersectionGeometry.hAAedge q
      cfg C₀ T cert hpaircells hmodA hdel_edge m n p r hne
  have hAAvertex (m n p r : Int) (hne : (m, n) ≠ (p, r)) :
      FootprintVertices
          (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, m, n⟩) ∩
          FootprintVertices
            (ModifiedSubtileOccurrenceInterpretation P O u v ⟨.A, p, r⟩) =
        FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩) :=
              OriginalIntersectionGeometry.hAAvertex q cfg C₀ T cert hpaircells hmodA hdel_vertex
              hparent_nonempty hcomplement_nonempty hsupport_for m n p r hne
  have hmod_edge_allowed (a b : PeriodicSubtileIndex) (hab : a ≠ b) :
      (FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
        FootprintEdges (ModifiedSubtileOccurrenceInterpretation P O u v b)).Nonempty →
      AllowedSubtileIncidence a b  := OriginalIntersectionGeometry.hmod_edge_allowed q cfg C₀ T
          cert hclass hmodified hmodadj a b
      hab
  have hmod_vertex_alt (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (hna : ¬ AllowedSubtileIncidence a b) :
      FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b) = ∅ ∨
        (FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v a) ∩
          FootprintVertices (ModifiedSubtileOccurrenceInterpretation P O u v b)).Subsingleton  :=
              OriginalIntersectionGeometry.hmod_vertex_alt q cfg
          C₀ T cert hclass hmodified hmodadj a b hab hna
  have hAraw (m n : Int) (b : PeriodicSubtileIndex)
      (hbA : b.label ≠ .A)
      (hbpair : ¬ (b.label = .B ∧ b.first = m ∧ b.second = n))
      (hab : (⟨.A, m, n⟩ : PeriodicSubtileIndex) ≠ b)
      (he : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v b)).Nonempty) :
      AllowedSubtileIncidence ⟨.A, m, n⟩ b := OriginalIntersectionGeometry.hAraw q cfg C₀ T cert
          hAedge hmod_edge_allowed m n b hbA hbpair hab he
  have hAAraw (m n p r : Int) (hne : (m, n) ≠ (p, r))
      (he : (FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, m, n⟩) ∩
          FootprintEdges (SubtileOccurrenceInterpretation P u v ⟨.A, p, r⟩)).Nonempty) :=
              OriginalIntersectionGeometry.hAAraw q cfg C₀ T cert hAAedge hmod_edge_allowed m n p
              r hne he
  have edgeImplication (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (he : (FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
        FootprintEdges (SubtileOccurrenceInterpretation P u v b)).Nonempty) :
      AllowedSubtileIncidence a b := OriginalIntersectionAssembly.edgeImplication q cfg C₀ T cert
          hmodother hmod_edge_allowed hAraw hAAraw a b hab he
  have vertexAlternative (a b : PeriodicSubtileIndex) (hab : a ≠ b)
      (hna : ¬ AllowedSubtileIncidence a b) :
      FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v b) = ∅ ∨
        (FootprintVertices (SubtileOccurrenceInterpretation P u v a) ∩
          FootprintVertices (SubtileOccurrenceInterpretation P u v b)).Subsingleton :=
              OriginalIntersectionAssembly.vertexAlternative q cfg C₀ T cert hmodother hAvertex
              hAAvertex hmod_vertex_alt a b hab hna
  dsimp [P, O, u, v]
  intro a b hab
  constructor
  · exact edgeImplication a b hab
  · exact vertexAlternative a b hab

end ApollonianSuperharmonic

end
