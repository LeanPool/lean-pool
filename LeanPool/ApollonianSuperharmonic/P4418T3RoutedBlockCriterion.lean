/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4418T3EndpointOwnerIndices
public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceData
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowTable
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPeriodicBlockCells
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.OppositeRoutedCommonEdgeOutsideCellUnique
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: P4418T3RoutedBlockCriterion]

/-!
# P4418T3RoutedBlockCriterion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def routedOldCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C : BandCircle} {T : ProtoTile}
    {cert : BandOrderedGeneralLayoutCertificate q cfg C T}
    {a b : PeriodicSubtileIndex}
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) : Int × Int :=
  match row with
    | .positiveL1 _ _ => (-1, 0)
    | .positiveS1 _ => (-1, 0)
    | .positiveL2 _ _ => (1, 0)
    | .positiveS2 _ => (1, 0)
    | .positiveL3 _ _ => (0, -1)
    | .positiveS3 _ => (0, -1)
    | .positiveS4 _ => (0, 1)
    | .positiveS5 _ => (1, 1)
    | .positiveS6 _ => (-1, -1)
    | .reflectedL1 _ _ => (1, 0)
    | .reflectedS1 _ => (1, 0)
    | .reflectedL2 _ _ => (-1, 0)
    | .reflectedS2 _ => (-1, 0)
    | .reflectedL3 _ _ => (0, 1)
    | .reflectedS3 _ => (0, 1)
    | .reflectedS4 _ => (0, -1)
    | .reflectedS5 _ => (-1, -1)
    | .reflectedS6 _ => (1, 1)

namespace RoutedBlockGeometry

private theorem hshift :
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
                        let shift : GaussianInt :=
                          match P3996T1SRowTable q cfg C T cert row with
                          | some z => z.oldShift
                          | none =>
                            match a.label with
                            | .A => if a.first = -1 then -cert.u else cert.u
                            | .B => if a.first = 1 then cert.u else -cert.u
                            | .C => -cert.v
                            | .D => cert.v
                            | .E | .F => 0
                        let oldCoord : Int × Int := routedOldCoordinates row
                        shift =
                          (oldCoord.1 : GaussianInt) * cert.u +
                            (oldCoord.2 : GaussianInt) * cert.v
    )
            := by
  classical
  intro q cfg C T cert a b row shift oldCoord
  cases row <;> simp [shift, oldCoord, routedOldCoordinates, P3996T1SRowTable] <;> ring

private theorem root_disjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (m : Int), ∀ (n : Int), ∀ (r : Int), ∀ (s : Int), ((m, n) ≠ (r, s)) → (Disjoint
            (TileTranslation T ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells
            (TileTranslation T ((r : GaussianInt) * cert.u + (s : GaussianInt) * cert.v)).cells)
            ) := by
  classical
  intro q cfg C T cert m n r s hne
  exact (BandOrderedGeneralPeriodicBlockCells q cfg C T cert).2 m n r s hne

private theorem footprint_incident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (z : GaussianInt), (z ∈ FootprintVertices U) →
            (∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells)) ) := by
  classical
  intro U hne z hz
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hz
  rcases hz with ⟨c, hc, rfl | rfl | rfl | rfl⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
  · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
  · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
  · refine ⟨2, ?_⟩
    simpa [LatticeVertexIncidentCell, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm] using hc

private theorem incident_footprint :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (z : GaussianInt), ∀ (k : Fin 4),
            (LatticeVertexIncidentCell z k ∈ U.cells) → (z ∈ FootprintVertices U)) ) := by
  classical
  intro U hne z k hk
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
  refine ⟨LatticeVertexIncidentCell z k, hk, ?_⟩
  fin_cases k <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]

private theorem root_cells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (o : PeriodicSubtileIndex), ∀ (c : LatticeCell), (c ∈
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v o).cells) → (c ∈
            (TileTranslation T ((o.first : GaussianInt) * cert.u + (o.second : GaussianInt) *
            cert.v)).cells) ) := by
  classical
  intro q cfg C T cert o c hc
  let d := (o.first : GaussianInt) * cert.u + (o.second : GaussianInt) * cert.v
  have hbase (z : LatticeCell) := (BandOrderedGeneralPeriodicBlockCells q cfg C T cert).1
    o.first o.second z
  cases hl : o.label with
  | A =>
      simp only [SubtileOccurrenceInterpretation, hl] at hc
      rw [(TileTranslationFormulas (cert.P 0 true) d).1] at hc
      rcases Finset.mem_image.mp hc with ⟨y, hy, hcy⟩
      by_cases hO : y ∈ cert.O.cells
      · have hprec : y ∈ (cert.S 0 true).cells := by
          rw [← cert.precursor_cells]
          exact hO
        have hB : y ∈ (cert.P 0 false).cells :=
          (cert.minus_union y).2 ⟨0, true, hprec⟩
        have hmod : GaussianTranslation d y ∈
            (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
              cert.u cert.v ⟨.B, o.first, o.second⟩).cells := by
          simpa [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
            GaussianTranslation, d] using hB
        simpa [hcy] using (hbase (GaussianTranslation d y)).mpr ⟨.B, hmod⟩
      · have hmod : GaussianTranslation d y ∈
            (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
              cert.u cert.v ⟨.A, o.first, o.second⟩).cells := by
          simp [ModifiedSubtileOccurrenceInterpretation, TileTranslation,
            GaussianTranslation, TileCellComplement, hO, hy, d]
        simpa [hcy] using (hbase (GaussianTranslation d y)).mpr ⟨.A, hmod⟩
  | B =>
      have hc' : c ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
        cert.u cert.v o).cells := by
        simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
          hl] using hc
      exact (hbase c).mpr ⟨.B, by
        simpa [ModifiedSubtileOccurrenceInterpretation, hl] using hc'⟩
  | C =>
      have hc' : c ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
        cert.u cert.v o).cells := by
        simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
          hl] using hc
      exact (hbase c).mpr ⟨.C, by
        simpa [ModifiedSubtileOccurrenceInterpretation, hl] using hc'⟩
  | D =>
      have hc' : c ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
        cert.u cert.v o).cells := by
        simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
          hl] using hc
      exact (hbase c).mpr ⟨.D, by
        simpa [ModifiedSubtileOccurrenceInterpretation, hl] using hc'⟩
  | E =>
      have hc' : c ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
        cert.u cert.v o).cells := by
        simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
          hl] using hc
      exact (hbase c).mpr ⟨.E, by
        simpa [ModifiedSubtileOccurrenceInterpretation, hl] using hc'⟩
  | F =>
      have hc' : c ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O
        cert.u cert.v o).cells := by
        simpa [SubtileOccurrenceInterpretation, ModifiedSubtileOccurrenceInterpretation,
          hl] using hc
      exact (hbase c).mpr ⟨.F, by
        simpa [ModifiedSubtileOccurrenceInterpretation, hl] using hc'⟩

private theorem hVroot :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex),
        let V := SubtileOccurrenceInterpretation cert.P cert.u cert.v a
        (∀ (o : PeriodicSubtileIndex), ∀ (c : LatticeCell), (c ∈ (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v o).cells) → (c ∈ (TileTranslation T ((o.first : GaussianInt) *
            cert.u + (o.second : GaussianInt) * cert.v)).cells)) → (∀ c : LatticeCell, c ∈
            V.cells → c ∈ (TileTranslation T ((a.first : GaussianInt) * cert.u + (a.second :
            GaussianInt) * cert.v)).cells) ) := by
  classical
  intro q cfg C T cert a V root_cells c hc
  exact root_cells a c (by simpa [V] using hc)

private abbrev hWroot := ApollonianSuperharmonic.RoutedBlockGeometry.hVroot

private theorem hG₀root :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
        let G₀ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
        (∀ (o : PeriodicSubtileIndex), ∀ (c : LatticeCell), (c ∈ (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v o).cells) → (c ∈ (TileTranslation T ((o.first : GaussianInt) *
            cert.u + (o.second : GaussianInt) * cert.v)).cells)) → (∀ c : LatticeCell, c ∈
            G₀.cells → c ∈ (TileTranslation T (((P4418T3EndpointOwnerIndices q cfg C T cert a b
            row).1.first : GaussianInt) * cert.u + ((P4418T3EndpointOwnerIndices q cfg C T cert
            a b row).1.second : GaussianInt) * cert.v)).cells) ) := by
  classical
  intro q cfg C T cert a b row G₀ root_cells c hc
  let o := (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
  exact root_cells o c (by simpa [G₀, o] using hc)

private theorem hG₁root :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
        let G₁ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
        (∀ (o : PeriodicSubtileIndex), ∀ (c : LatticeCell), (c ∈ (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v o).cells) → (c ∈ (TileTranslation T ((o.first : GaussianInt) *
            cert.u + (o.second : GaussianInt) * cert.v)).cells)) → (∀ c : LatticeCell, c ∈
            G₁.cells → c ∈ (TileTranslation T (((P4418T3EndpointOwnerIndices q cfg C T cert a b
            row).2.first : GaussianInt) * cert.u + ((P4418T3EndpointOwnerIndices q cfg C T cert
            a b row).2.second : GaussianInt) * cert.v)).cells) ) := by
  classical
  intro q cfg C T cert a b row G₁ root_cells c hc
  let o := (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
  exact root_cells o c (by simpa [G₁, o] using hc)

private theorem hVold :
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
                        (let shift : GaussianInt :=
                          match P3996T1SRowTable q cfg C T cert row with
                          | some z => z.oldShift
                          | none =>
                            match a.label with
                            | .A => if a.first = -1 then -cert.u else cert.u
                            | .B => if a.first = 1 then cert.u else -cert.u
                            | .C => -cert.v
                            | .D => cert.v
                            | .E | .F => 0;
                        let oldCoord : Int × Int := routedOldCoordinates row;
                        (shift =
                            (oldCoord.1 : GaussianInt) * cert.u +
                              (oldCoord.2 : GaussianInt) * cert.v) →
                          (((a.first, a.second) ≠ oldCoord) →
                            ((∀ (m : Int),
                                ∀ (n : Int),
                                  ∀ (r : Int),
                                    ∀ (s : Int),
                                      ((m, n) ≠ (r, s)) →
                                        (Disjoint
                                          (TileTranslation T
                                              ((m : GaussianInt) * cert.u +
                                                (n : GaussianInt) * cert.v)).cells
                                          (TileTranslation T
                                              ((r : GaussianInt) * cert.u +
                                                (s : GaussianInt) *
                                                  cert.v)).cells)) →
                              (let V :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                  a;
                              (∀ c : LatticeCell,
                                  c ∈ V.cells →
                                    c ∈
                                      (TileTranslation T
                                          ((a.first : GaussianInt) * cert.u +
                                            (a.second : GaussianInt) *
                                              cert.v)).cells) →
                                (Disjoint V.cells
                                  (TileTranslation T shift).cells)))))) := by
  classical
  intro q cfg C T cert a b row shift oldCoord hshift a_coord_ne root_disjoint V hVroot
  rw [Finset.disjoint_left]
  intro c hcV hcOld
  have hV := hVroot c hcV
  have hOld : c ∈ (TileTranslation T
      ((oldCoord.1 : GaussianInt) * cert.u + (oldCoord.2 : GaussianInt) * cert.v)).cells := by
    simpa [hshift] using hcOld
  exact (Finset.disjoint_left.mp
    (root_disjoint a.first a.second oldCoord.1 oldCoord.2 a_coord_ne)) hV hOld

private theorem hWold :
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
                        (let shift : GaussianInt :=
                          match P3996T1SRowTable q cfg C T cert row with
                          | some z => z.oldShift
                          | none =>
                            match a.label with
                            | .A => if a.first = -1 then -cert.u else cert.u
                            | .B => if a.first = 1 then cert.u else -cert.u
                            | .C => -cert.v
                            | .D => cert.v
                            | .E | .F => 0;
                        let oldCoord : Int × Int := routedOldCoordinates row;
                        (shift =
                            (oldCoord.1 : GaussianInt) * cert.u +
                              (oldCoord.2 : GaussianInt) * cert.v) →
                          (((b.first, b.second) ≠ oldCoord) →
                            ((∀ (m : Int),
                                ∀ (n : Int),
                                  ∀ (r : Int),
                                    ∀ (s : Int),
                                      ((m, n) ≠ (r, s)) →
                                        (Disjoint
                                          (TileTranslation T
                                              ((m : GaussianInt) * cert.u +
                                                (n : GaussianInt) * cert.v)).cells
                                          (TileTranslation T
                                              ((r : GaussianInt) * cert.u +
                                                (s : GaussianInt) *
                                                  cert.v)).cells)) →
                              (let W :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                  b;
                              (∀ c : LatticeCell,
                                  c ∈ W.cells →
                                    c ∈
                                      (TileTranslation T
                                          ((b.first : GaussianInt) * cert.u +
                                            (b.second : GaussianInt) *
                                              cert.v)).cells) →
                                (Disjoint W.cells
                                  (TileTranslation T shift).cells)))))) := by
  classical
  intro q cfg C T cert a b row shift oldCoord hshift b_coord_ne root_disjoint W hWroot
  rw [Finset.disjoint_left]
  intro c hcW hcOld
  have hW := hWroot c hcW
  have hOld : c ∈ (TileTranslation T
      ((oldCoord.1 : GaussianInt) * cert.u + (oldCoord.2 : GaussianInt) * cert.v)).cells := by
    simpa [hshift] using hcOld
  exact (Finset.disjoint_left.mp
    (root_disjoint b.first b.second oldCoord.1 oldCoord.2 b_coord_ne)) hW hOld

private theorem hxedge :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates)
          (cfg : BandOrderedGeneralConfiguration q)
          (C : BandCircle)
          (T : ProtoTile)
          (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
          (a b : PeriodicSubtileIndex) (x : GaussianInt)
          (edge : Finset GaussianInt),
          x ∈ edge →
            edge ∈
                FootprintEdges
                    (SubtileOccurrenceInterpretation cert.P
                      cert.u cert.v a) ∩
                  FootprintEdges
                    (SubtileOccurrenceInterpretation cert.P
                      cert.u cert.v b) →
              let V :=
                SubtileOccurrenceInterpretation cert.P cert.u
                  cert.v a;
              let W :=
                SubtileOccurrenceInterpretation cert.P cert.u
                  cert.v b;
              ∃ (e : Finset GaussianInt),
                x ∈ e ∧
                  e ∈
                    FootprintEdges V ∩
                      FootprintEdges W) := by
  classical
  intro q cfg C T cert a b x edge hx hedge V W
  rcases hedge with ⟨heV, heW⟩
  exact ⟨edge, hx, by simpa [V, W] using ⟨heV, heW⟩⟩

private theorem hfirst_criterion :
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
                        ∀
                          (data :
                            P4418T3SelectedInterfaceData
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)),
                          ∀ (x : GaussianInt),
                            ∀ (j : Fin 4),
                              ∀ (edge : Finset GaussianInt),
                                x ∈ edge →
                                edge ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) →
                                LatticeVertexIncidentCell x j ∈
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                a).cells →
                                LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                b).cells →
                                let shift : GaussianInt :=
                                match P3996T1SRowTable q cfg C T cert row with
                              | some z => z.oldShift
                              | none =>
                                match a.label with
                              | .A => if a.first = -1 then -cert.u else cert.u
                              | .B => if a.first = 1 then cert.u else -cert.u
                              | .C => -cert.v
                              | .D => cert.v
                              | .E | .F => 0;
                              let oldCoord : Int × Int := routedOldCoordinates row;
                              shift =
                                (oldCoord.1 : GaussianInt) * cert.u +
                                (oldCoord.2 : GaussianInt) * cert.v →
                                (∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (r : Int),
                                ∀ (s : Int),
                                (m, n) ≠ (r, s) →
                                Disjoint
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells
                                (TileTranslation T
                                ((r : GaussianInt) * cert.u +
                                (s : GaussianInt) * cert.v)).cells) →
                                (TileTranslation T shift).cells.Nonempty →
                                (∀ (U : ProtoTile),
                                U.cells.Nonempty →
                                ∀ (z : GaussianInt),
                                z ∈ FootprintVertices U →
                                ∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells) →
                                (∀ (U : ProtoTile),
                                U.cells.Nonempty →
                                ∀ (z : GaussianInt),
                                ∀ (k : Fin 4),
                                LatticeVertexIncidentCell z k ∈ U.cells →
                                z ∈ FootprintVertices U) →
                                let V :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v a;
                              let W :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v b;
                              let G₀ :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1;
                              (∀ c : LatticeCell,
                                c ∈ G₀.cells →
                                c ∈
                                (TileTranslation T
                                (((P4418T3EndpointOwnerIndices q cfg C T cert a b
                                row).1.first :
                                GaussianInt) *
                                cert.u +
                                ((P4418T3EndpointOwnerIndices q cfg C T cert a b
                                row).1.second :
                                GaussianInt) *
                                cert.v)).cells) →
                                Disjoint V.cells (TileTranslation T shift).cells →
                                Disjoint W.cells (TileTranslation T shift).cells →
                                (x = data.first ∨
                                x = data.last ∨
                                ∃ (e : Finset GaussianInt) (f : Finset GaussianInt),
                                e ≠ f ∧
                                x ∈ e ∧
                                x ∈ f ∧
                                e ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) ∧
                                f ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                b)) →
                                let o₀ :=
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
                              x = data.first →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                oldCoord = (o₀.first, o₀.second))
    ) := by
  classical
  intro q cfg C T cert a b row data x j edge hx hedge ha hb shift oldCoord hshift root_disjoint
      old_nonempty footprint_incident incident_footprint V W G₀ hG₀root hVold hWold htri o₀
      hfirst
  subst x
  obtain ⟨k, hk⟩ :=
    ((LocalLatticeInterfaceSectors.1 V W G₀ data.first data.latticeV
      data.latticeW data.latticeG₀ data.touching₀ data.common₀).2.2.2.1)
  have hkG : LatticeVertexIncidentCell data.first k ∈ G₀.cells := by
    simpa [G₀] using hk
  constructor
  · intro hfoot
    obtain ⟨l, hl⟩ := footprint_incident _ old_nonempty _ hfoot
    have huniq := OppositeRoutedCommonEdgeOutsideCellUnique V W data.first j edge
      data.disjointVW hx (by simpa [V, W] using hedge)
      (by simpa [V] using ha) (by simpa [W] using hb)
    have heq := huniq k l
      (by
        intro hc
        exact (Finset.disjoint_left.mp
          (by simpa [V, G₀] using data.disjointVG₀) hc hkG)
      )
      (by
        intro hc
        exact (Finset.disjoint_left.mp
          (by simpa [W, G₀] using data.disjointWG₀) hc hkG)
      )
      (by intro hc; exact (Finset.disjoint_left.mp hVold) hc hl)
      (by intro hc; exact (Finset.disjoint_left.mp hWold) hc hl)
    have hgroot := hG₀root _ hkG
    have hgroot' : LatticeVertexIncidentCell data.first k ∈
        (TileTranslation T
          ((o₀.first : GaussianInt) * cert.u +
            (o₀.second : GaussianInt) * cert.v)).cells := by
      simpa [o₀] using hgroot
    have holdroot : LatticeVertexIncidentCell data.first l ∈
        (TileTranslation T
          ((oldCoord.1 : GaussianInt) * cert.u +
            (oldCoord.2 : GaussianInt) * cert.v)).cells := by
      simpa [hshift] using hl
    by_contra hcoord
    have hneq : (o₀.first, o₀.second) ≠ oldCoord := by
      intro he
      exact hcoord he.symm
    exact (Finset.disjoint_left.mp
      (root_disjoint o₀.first o₀.second oldCoord.1 oldCoord.2 hneq))
      hgroot' (by simpa using heq ▸ holdroot)
  · intro hcoord
    have hgroot := hG₀root _ hkG
    have hold : LatticeVertexIncidentCell data.first k ∈
        (TileTranslation T shift).cells := by
      simpa [hshift, hcoord, o₀] using hgroot
    exact incident_footprint _ old_nonempty _ k hold

private theorem hlast_criterion :
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
                        ∀
                          (data :
                            P4418T3SelectedInterfaceData
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)),
                          ∀ (x : GaussianInt),
                            ∀ (j : Fin 4),
                              ∀ (edge : Finset GaussianInt),
                                x ∈ edge →
                                edge ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) →
                                LatticeVertexIncidentCell x j ∈
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                a).cells →
                                LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                b).cells →
                                let shift : GaussianInt :=
                                match P3996T1SRowTable q cfg C T cert row with
                              | some z => z.oldShift
                              | none =>
                                match a.label with
                              | .A => if a.first = -1 then -cert.u else cert.u
                              | .B => if a.first = 1 then cert.u else -cert.u
                              | .C => -cert.v
                              | .D => cert.v
                              | .E | .F => 0;
                              let oldCoord : Int × Int := routedOldCoordinates row;
                              shift =
                                (oldCoord.1 : GaussianInt) * cert.u +
                                (oldCoord.2 : GaussianInt) * cert.v →
                                (∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (r : Int),
                                ∀ (s : Int),
                                (m, n) ≠ (r, s) →
                                Disjoint
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells
                                (TileTranslation T
                                ((r : GaussianInt) * cert.u +
                                (s : GaussianInt) * cert.v)).cells) →
                                (TileTranslation T shift).cells.Nonempty →
                                (∀ (U : ProtoTile),
                                U.cells.Nonempty →
                                ∀ (z : GaussianInt),
                                z ∈ FootprintVertices U →
                                ∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells) →
                                (∀ (U : ProtoTile),
                                U.cells.Nonempty →
                                ∀ (z : GaussianInt),
                                ∀ (k : Fin 4),
                                LatticeVertexIncidentCell z k ∈ U.cells →
                                z ∈ FootprintVertices U) →
                                let V :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v a;
                              let W :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v b;
                              let G₁ :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2;
                              (∀ c : LatticeCell,
                                c ∈ G₁.cells →
                                c ∈
                                (TileTranslation T
                                (((P4418T3EndpointOwnerIndices q cfg C T cert a b
                                row).2.first :
                                GaussianInt) *
                                cert.u +
                                ((P4418T3EndpointOwnerIndices q cfg C T cert a b
                                row).2.second :
                                GaussianInt) *
                                cert.v)).cells) →
                                Disjoint V.cells (TileTranslation T shift).cells →
                                Disjoint W.cells (TileTranslation T shift).cells →
                                (x = data.first ∨
                                x = data.last ∨
                                ∃ (e : Finset GaussianInt) (f : Finset GaussianInt),
                                e ≠ f ∧
                                x ∈ e ∧
                                x ∈ f ∧
                                e ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) ∧
                                f ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                b)) →
                                let o₀ :=
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
                              let o₁ :=
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
                              (x = data.first →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                oldCoord = (o₀.first, o₀.second))) →
                                x = data.last →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                oldCoord = (o₁.first, o₁.second))
    ) := by
  classical
  intro q cfg C T cert a b row data x j edge hx hedge ha hb shift oldCoord hshift root_disjoint
      old_nonempty footprint_incident incident_footprint V W G₁ hG₁root hVold hWold htri o₀ o₁
      hfirst_criterion hlast
  subst x
  obtain ⟨k, hk⟩ :=
    ((LocalLatticeInterfaceSectors.1 V W G₁ data.last data.latticeV
      data.latticeW data.latticeG₁ data.touching₁ data.common₁).2.2.2.1)
  have hkG : LatticeVertexIncidentCell data.last k ∈ G₁.cells := by
    simpa [G₁] using hk
  constructor
  · intro hfoot
    obtain ⟨l, hl⟩ := footprint_incident _ old_nonempty _ hfoot
    have huniq := OppositeRoutedCommonEdgeOutsideCellUnique V W data.last j edge
      data.disjointVW hx (by simpa [V, W] using hedge)
      (by simpa [V] using ha) (by simpa [W] using hb)
    have heq := huniq k l
      (by
        intro hc
        exact (Finset.disjoint_left.mp
          (by simpa [V, G₁] using data.disjointVG₁) hc hkG)
      )
      (by
        intro hc
        exact (Finset.disjoint_left.mp
          (by simpa [W, G₁] using data.disjointWG₁) hc hkG)
      )
      (by intro hc; exact (Finset.disjoint_left.mp hVold) hc hl)
      (by intro hc; exact (Finset.disjoint_left.mp hWold) hc hl)
    have hgroot := hG₁root _ hkG
    have hgroot' : LatticeVertexIncidentCell data.last k ∈
        (TileTranslation T
          ((o₁.first : GaussianInt) * cert.u +
            (o₁.second : GaussianInt) * cert.v)).cells := by
      simpa [o₁] using hgroot
    have holdroot : LatticeVertexIncidentCell data.last l ∈
        (TileTranslation T
          ((oldCoord.1 : GaussianInt) * cert.u +
            (oldCoord.2 : GaussianInt) * cert.v)).cells := by
      simpa [hshift] using hl
    by_contra hcoord
    have hneq : (o₁.first, o₁.second) ≠ oldCoord := by
      intro he
      exact hcoord he.symm
    exact (Finset.disjoint_left.mp
      (root_disjoint o₁.first o₁.second oldCoord.1 oldCoord.2 hneq))
      hgroot' (by simpa using heq ▸ holdroot)
  · intro hcoord
    have hgroot := hG₁root _ hkG
    have hold : LatticeVertexIncidentCell data.last k ∈
        (TileTranslation T shift).cells := by
      simpa [hshift, hcoord, o₁] using hgroot
    exact incident_footprint _ old_nonempty _ k hold

private theorem hcriterion :
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
                        ∀
                          (data :
                            P4418T3SelectedInterfaceData
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1)
                              (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)),
                          ∀ (x : GaussianInt),
                            let shift : GaussianInt :=
                              match P3996T1SRowTable q cfg C T cert row with
                              | some z => z.oldShift
                              | none =>
                                match a.label with
                              | .A => if a.first = -1 then -cert.u else cert.u
                              | .B => if a.first = 1 then cert.u else -cert.u
                              | .C => -cert.v
                              | .D => cert.v
                              | .E | .F => 0
                            let oldCoord : Int × Int := routedOldCoordinates row
                            (TileTranslation T shift).cells.Nonempty →
                              (∀ (U : ProtoTile),
                                U.cells.Nonempty →
                                ∀ (z : GaussianInt),
                                z ∈ FootprintVertices U →
                                ∃ k : Fin 4, LatticeVertexIncidentCell z k ∈ U.cells) →
                                let V :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v a
                              let W :=
                                SubtileOccurrenceInterpretation cert.P cert.u cert.v b
                              Disjoint V.cells (TileTranslation T shift).cells →
                                Disjoint W.cells (TileTranslation T shift).cells →
                                (x = data.first ∨
                                x = data.last ∨
                                ∃ (e : Finset GaussianInt) (f : Finset GaussianInt),
                                e ≠ f ∧
                                x ∈ e ∧
                                x ∈ f ∧
                                e ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v b) ∧
                                f ∈
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
                                FootprintEdges
                                (SubtileOccurrenceInterpretation cert.P cert.u cert.v
                                b)) →
                                let o₀ :=
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
                              let o₁ :=
                                (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
                              (x = data.first →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                oldCoord = (o₀.first, o₀.second))) →
                                (x = data.last →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                oldCoord = (o₁.first, o₁.second))) →
                                (x ∈ FootprintVertices (TileTranslation T shift) ↔
                                x = data.first ∧ oldCoord = (o₀.first, o₀.second) ∨
                                x = data.last ∧ oldCoord = (o₁.first, o₁.second))
    ) := by
  classical
  intro q cfg C T cert a b row data x shift oldCoord old_nonempty footprint_incident V W hVold
      hWold htri o₀ o₁ hfirst_criterion hlast_criterion
  rcases htri with hfirst | hlast | hinside
  · have hnotlast : x ≠ data.last := by
      intro h
      exact data.distinct (hfirst.symm.trans h)
    rw [hfirst_criterion hfirst]
    constructor
    · intro h
      exact Or.inl ⟨hfirst, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact (hnotlast h).elim
  · have hnotfirst : x ≠ data.first := by
      intro h
      exact data.distinct (h.symm.trans hlast)
    rw [hlast_criterion hlast]
    constructor
    · intro h
      exact Or.inr ⟨hlast, h⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact (hnotfirst h).elim
      · exact h
  · rcases hinside with ⟨e, f, hef, hxe, hxf, heE, hfE⟩
    have hsector := LocalLatticeInterfaceSectors.2 V W x data.latticeV
      data.latticeW data.disjointVW ⟨e, f, hef, hxe, hxf,
        by simpa [V, W] using heE, by simpa [V, W] using hfE⟩
    have hnotold : x ∉ FootprintVertices (TileTranslation T shift) := by
      intro hfoot
      obtain ⟨k, hk⟩ := footprint_incident _ old_nonempty _ hfoot
      rcases hsector.1 k with hv | hw
      · exact (Finset.disjoint_left.mp hVold) hv hk
      · exact (Finset.disjoint_left.mp hWold) hw hk
    constructor
    · intro h
      exact (hnotold h).elim
    · rintro (⟨hfirst, hcoord⟩ | ⟨hlast, hcoord⟩)
      · exact (hnotold ((hfirst_criterion hfirst).2 hcoord)).elim
      · exact (hnotold ((hlast_criterion hlast).2 hcoord)).elim

end RoutedBlockGeometry

theorem P4418T3RoutedBlockCriterion
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b)
    (hT : LatticeTile T)
    (data : P4418T3SelectedInterfaceData
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2))
    (x : GaussianInt) (j : Fin 4) (edge : Finset GaussianInt)
    (hx : x ∈ edge)
    (hedge : edge ∈ FootprintEdges
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v a) ∩
      FootprintEdges (SubtileOccurrenceInterpretation cert.P cert.u cert.v b))
    (ha : LatticeVertexIncidentCell x j ∈
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a).cells)
    (hb : LatticeVertexIncidentCell x (j + 2) ∈
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v b).cells) :
    let oldShift := match P3996T1SRowTable q cfg C T cert row with
      | some z => z.oldShift
      | none => match a.label with
        | .A => if a.first = -1 then -cert.u else cert.u
        | .B => if a.first = 1 then cert.u else -cert.u
        | .C => -cert.v
        | .D => cert.v
        | .E | .F => 0
    x ∈ FootprintVertices (TileTranslation T oldShift) ↔
      match P3996T1SRowTable q cfg C T cert row with
      | none => False
      | some z => x = (if z.parentSlot = 0 then data.first else data.last) := by
-- BODY
  classical
  dsimp only
  let shift : GaussianInt := match P3996T1SRowTable q cfg C T cert row with
    | some z => z.oldShift
    | none => match a.label with
      | .A => if a.first = -1 then -cert.u else cert.u
      | .B => if a.first = 1 then cert.u else -cert.u
      | .C => -cert.v
      | .D => cert.v
      | .E | .F => 0
  let oldCoord : Int × Int := routedOldCoordinates row
  have hshift := RoutedBlockGeometry.hshift q cfg C T cert a b row
  have a_coord_ne : (a.first, a.second) ≠ oldCoord := by
    cases row <;> simp [oldCoord, routedOldCoordinates]
  have b_coord_ne : (b.first, b.second) ≠ oldCoord := by
    cases row <;> simp [oldCoord, routedOldCoordinates]
  have root_disjoint (m n r s : Int) (hne : (m, n) ≠ (r, s)) := RoutedBlockGeometry.root_disjoint
      q cfg C T cert m n r s hne
  have old_lattice : LatticeTile (TileTranslation T shift) :=
    (TileDiskAreaCovariance T shift).1.mp hT
  have old_nonempty : (TileTranslation T shift).cells.Nonempty :=
    (LatticeTileGridStructure _ old_lattice).1.1
  have footprint_incident (U : ProtoTile) (hne : U.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices U) := RoutedBlockGeometry.footprint_incident
          U hne z hz
  have incident_footprint (U : ProtoTile) (hne : U.cells.Nonempty)
      (z : GaussianInt) (k : Fin 4)
      (hk : LatticeVertexIncidentCell z k ∈ U.cells) := RoutedBlockGeometry.incident_footprint U
          hne z k hk
  let V := SubtileOccurrenceInterpretation cert.P cert.u cert.v a
  let W := SubtileOccurrenceInterpretation cert.P cert.u cert.v b
  let G₀ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
  let G₁ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
    (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
  have root_cells (o : PeriodicSubtileIndex) (c : LatticeCell)
      (hc : c ∈ (SubtileOccurrenceInterpretation cert.P cert.u cert.v o).cells) :=
          RoutedBlockGeometry.root_cells q cfg C T cert o c hc
  have hVroot := RoutedBlockGeometry.hVroot q cfg C T cert a root_cells
  have hWroot := RoutedBlockGeometry.hWroot q cfg C T cert b root_cells
  have hG₀root := RoutedBlockGeometry.hG₀root q cfg C T cert a b row root_cells
  have hG₁root := RoutedBlockGeometry.hG₁root q cfg C T cert a b row root_cells
  have hVold := RoutedBlockGeometry.hVold q cfg C T cert a b row hshift
      a_coord_ne root_disjoint hVroot
  have hWold := RoutedBlockGeometry.hWold q cfg C T cert a b row hshift
      b_coord_ne root_disjoint hWroot
  have hxedge := RoutedBlockGeometry.hxedge q cfg C T cert a b x edge hx hedge
  have htri := SimpleGridPathPointTrichotomy _ _ data.first data.last x data.path hxedge
  let o₀ := (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
  let o₁ := (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
  have hfirst_criterion := RoutedBlockGeometry.hfirst_criterion q cfg C T cert a b row data x j
      edge hx hedge ha hb hshift root_disjoint old_nonempty
      footprint_incident incident_footprint hG₀root hVold hWold htri
  have hlast_criterion := RoutedBlockGeometry.hlast_criterion q cfg C T cert a b row data x j
      edge hx hedge ha hb hshift root_disjoint old_nonempty
      footprint_incident incident_footprint hG₁root hVold hWold htri hfirst_criterion
  have hcriterion : x ∈ FootprintVertices (TileTranslation T shift) ↔
      (x = data.first ∧ oldCoord = (o₀.first, o₀.second)) ∨
      (x = data.last ∧ oldCoord = (o₁.first, o₁.second)) := RoutedBlockGeometry.hcriterion q cfg
          C T cert a b row data x old_nonempty footprint_incident hVold hWold
          htri hfirst_criterion hlast_criterion
  change (x ∈ FootprintVertices (TileTranslation T shift) ↔ _)
  rw [hcriterion]
  cases row <;>
    simp [oldCoord, routedOldCoordinates, o₀, o₁, P3996T1SRowTable,
      P4418T3EndpointOwnerIndices]

end ApollonianSuperharmonic

end
