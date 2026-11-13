/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.P4590T1PositivePrototileDisk
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.P4616T1ThirdOwnerPathEndpoint

-- [TABLET NODE: P4590T1JunctionRefinement]

/-!
# P4590T1JunctionRefinement

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace JunctionRefinementGeometry

private theorem htransZero :
    (by
      classical
      exact
        GaussianTranslation (0 : GaussianInt) = id ) := by
  classical
  funext z
  exact add_zero z

private abbrev incident :=
  LatticeFootprintIncidence.incidentCell

private theorem hfourCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T.cells) → (x ∈ T.cells ∧ x - 1 ∈ T.cells ∧ x - 1 - ⟨0, 1⟩ ∈ T.cells ∧ x - ⟨0, 1⟩ ∈
            T.cells) ) := by
  classical
  intro T x hmissingT
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [LatticeVertexIncidentCell] using hmissingT 0
  · simpa [LatticeVertexIncidentCell] using hmissingT 1
  · simpa [LatticeVertexIncidentCell] using hmissingT 2
  · simpa [LatticeVertexIncidentCell] using hmissingT 3

private theorem incidentCorner :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (y : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell y j ∈
            W.cells) → (y ∈ FootprintVertices W) ) := by
  classical
  intro W y j hc
  have hne : W.cells.Nonempty := ⟨_, hc⟩
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
  refine ⟨LatticeVertexIncidentCell y j, hc, ?_⟩
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

private theorem singletonCorner :
    (by
      classical
      exact
        ∀ (y : GaussianInt), ∀ (a : GaussianInt), (y = a ∨ y = a + 1 ∨ y = a + ⟨0, 1⟩ ∨
            y = a + 1 + ⟨0, 1⟩) → (y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile)) ) := by
  classical
  intro y a hc
  simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
    Set.mem_ofPred_eq]
  exact ⟨a, Finset.mem_singleton_self a, hc⟩

private theorem incidentSingleton :
    (by
      classical
      exact
        (∀ (y : GaussianInt), ∀ (a : GaussianInt), (y = a ∨ y = a + 1 ∨ y = a + ⟨0, 1⟩ ∨ y = a +
            1 + ⟨0, 1⟩) → (y ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile))) → (∀ (y : GaussianInt),
            ∀ (j : Fin 4), y ∈ FootprintVertices (⟨{LatticeVertexIncidentCell y j},
            LatticeVertexIncidentCell y j⟩ : ProtoTile)) ) := by
  classical
  intro singletonCorner y j
  apply singletonCorner
  fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

private theorem supportedToFootprint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (y : GaussianInt), (y ∈ CellSupportedFootprintVertices cert.O) → (y ∈
            FootprintVertices cert.O) ) := by
  classical
  intro q cfg C T cert y hy
  by_cases hO : cert.O.cells.Nonempty
  · simpa [CellSupportedFootprintVertices, FootprintVertices, hO] using hy
  · have hempty : cert.O.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
    simp [CellSupportedFootprintVertices, hempty] at hy

private theorem precursorIsolationSupported :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → ((∀ (y : GaussianInt), (y ∈
            CellSupportedFootprintVertices cert.O) → (y ∈ FootprintVertices cert.O)) → (∀ y ∈
            CellSupportedFootprintVertices cert.O, ∀ a : GaussianInt, y ∈ FootprintVertices
            (⟨{a}, a⟩ : ProtoTile) → a ∈ (cert.P 0 true).cells ∨ a ∈ (cert.P 0 false).cells)) )
            := by
  classical
  intro q cfg C T cert htransZero supportedToFootprint y hy a hya
  have hyfoot := supportedToFootprint y hy
  have hisolated := cert.precursor_isolated 0 0 y
    (by simpa [TileTranslation, GaussianTranslation, htransZero,
      Finset.image_id] using hyfoot) a hya
  simpa [SubtileOccurrenceInterpretation, TileTranslation,
    GaussianTranslation, htransZero, Finset.image_id] using hisolated

private theorem blockSeparation :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (((∀ (m : ℤ), ∀ (n : ℤ), ∀ (x :
            LatticeCell), x ∈ (TileTranslation T ((↑m : GaussianInt) * cert.u + (↑n :
            GaussianInt) * cert.v)).cells ↔ ∃ (label : SixSubtileLabel), x ∈
            (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u cert.v ⟨label, m,
            n⟩).cells) ∧ ∀ (m : ℤ), ∀ (n : ℤ), ∀ (r : ℤ), ∀ (s : ℤ), (m, n) ≠ (r, s) → Disjoint
            (TileTranslation T ((↑m : GaussianInt) * cert.u + (↑n : GaussianInt) * cert.v)).cells
            (TileTranslation T ((↑r : GaussianInt) * cert.u + (↑s : GaussianInt) *
            cert.v)).cells) → (∀ (m : Int), ∀ (n : Int), ((m, n) ≠ (0, 0)) → (Disjoint T.cells
            (TileTranslation T ((m : GaussianInt) * cert.u + (n : GaussianInt) *
            cert.v)).cells))) ) := by
  classical
  intro q cfg C T cert htransZero hblocks m n hmn
  have h := hblocks.2 0 0 m n hmn.symm
  simpa [TileTranslation, GaussianTranslation, htransZero, Finset.image_id] using h

private theorem tileCellInBlock :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ((∀ (m : ℤ), ∀ (n : ℤ), ∀ (x : LatticeCell), x ∈ (TileTranslation T ((↑m :
            GaussianInt) * cert.u + (↑n : GaussianInt) * cert.v)).cells ↔ ∃ (label :
            SixSubtileLabel), x ∈ (ModifiedSubtileOccurrenceInterpretation cert.P cert.O cert.u
            cert.v ⟨label, m, n⟩).cells) ∧ ∀ (m : ℤ), ∀ (n : ℤ), ∀ (r : ℤ), ∀ (s : ℤ), (m, n) ≠
            (r, s) → Disjoint (TileTranslation T ((↑m : GaussianInt) * cert.u + (↑n :
            GaussianInt) * cert.v)).cells (TileTranslation T ((↑r : GaussianInt) * cert.u + (↑s :
            GaussianInt) * cert.v)).cells) → (∀ (label : SixSubtileLabel), ∀ (m : Int), ∀ (n :
            Int), ∀ (a : GaussianInt), (a ∈ (cert.modified.tile ⟨label, m, n⟩).cells) → (a ∈
            (TileTranslation T ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells))
            ) := by
  classical
  intro q cfg C T cert hblocks label m n a ha
  apply (hblocks.1 m n a).2
  exact ⟨label, by simpa [cert.modified_tile] using ha⟩

private theorem hBtile :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        cert.modified.tile b = cert.P 0 false) ) := by
  classical
  intro q cfg C T cert htransZero b
  rw [cert.modified_tile]
  simp [b, ModifiedSubtileOccurrenceInterpretation, TileTranslation, htransZero]

private theorem hCtile :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        cert.modified.tile c = cert.P 1 true) ) := by
  classical
  intro q cfg C T cert htransZero c
  rw [cert.modified_tile]
  simp [c, ModifiedSubtileOccurrenceInterpretation, TileTranslation, htransZero]

private theorem hthirdABC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (GaussianTranslation (0 : GaussianInt) = id) → ((∀ (W :
            ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty) → ((y ∈ FootprintVertices W) → (∃
            j : Fin 4, LatticeVertexIncidentCell y j ∈ W.cells))) → ((∀ (W : ProtoTile), ∀ (y :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell y j ∈ W.cells) → (y ∈
            FootprintVertices W)) → ((∀ (y : GaussianInt), ∀ (j : Fin 4), y ∈ FootprintVertices
            (⟨{LatticeVertexIncidentCell y j}, LatticeVertexIncidentCell y j⟩ : ProtoTile)) →
            (((cert.P (0 : Fin (3 : ℕ)) true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells =
            cert.O.cells) → ((Disjoint (cert.P 0 false).cells (cert.P 1 true).cells) → ((Disjoint
            (cert.P 0 true).cells (cert.P 1 true).cells) → ((x ∈ FootprintVertices (cert.P 0 true) ∧
          x ∈ FootprintVertices (cert.P 0 false) ∧
          x ∈ FootprintVertices (cert.P 1 true)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
              (cert.P 0 true).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.P 0 false).cells ∧
              LatticeVertexIncidentCell x j ∉ (cert.P 1 true).cells)))))))) ) := by
  classical
  intro q cfg C T cert x htransZero incident incidentCorner incidentSingleton hABO hBCseparate
      hACseparate hABC
  obtain ⟨jA, hjA⟩ := incident (cert.P 0 true) x
    (LatticeTileGridStructure _ (cert.parent_lattice 0 true)).1.1 hABC.1
  have hnotC : LatticeVertexIncidentCell x jA ∉ (cert.P 1 true).cells := by
    intro hC
    exact (Finset.disjoint_left.mp hACseparate hjA hC).elim
  have hnotB : LatticeVertexIncidentCell x jA ∉ (cert.P 0 false).cells := by
    intro hB
    have hO : LatticeVertexIncidentCell x jA ∈ cert.O.cells := by
      rw [← hABO]
      exact Finset.mem_inter.mpr ⟨hjA, hB⟩
    have hxO : x ∈ FootprintVertices cert.O := incidentCorner cert.O x jA hO
    obtain ⟨jC, hjC⟩ := incident (cert.P 1 true) x
      (LatticeTileGridStructure _ (cert.parent_lattice 1 true)).1.1 hABC.2.2
    let a := LatticeVertexIncidentCell x jC
    have hisolated := cert.precursor_isolated 0 0 x
      (by simpa [TileTranslation, GaussianTranslation, htransZero,
        Finset.image_id] using hxO) a
      (incidentSingleton x jC)
    have hab : a ∈ (cert.P 0 true).cells ∨ a ∈ (cert.P 0 false).cells := by
      simpa [a, SubtileOccurrenceInterpretation, TileTranslation,
        GaussianTranslation] using hisolated
    rcases hab with ha | hb
    · exact (Finset.disjoint_left.mp hACseparate ha hjC).elim
    · exact (Finset.disjoint_left.mp hBCseparate hb hjC).elim
  exact ⟨jA, hjA, hnotB, hnotC⟩

private theorem hxBC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        (cert.modified.tile b = cert.P 0 false) → ((cert.modified.tile c = cert.P 1 true) → ((x ∈
            FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∧ x ∈ FootprintVertices (cert.P (0
            : Fin (3 : ℕ)) false) ∧ x ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → (x ∈
            FootprintVertices (cert.modified.tile b) ∩ FootprintVertices (cert.modified.tile
            c)))) ) := by
  classical
  intro q cfg C T cert x b c hBtile hCtile hABC
  simpa [hBtile, hCtile] using ⟨hABC.2.1, hABC.2.2⟩

private theorem hxv :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt),
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        (cert.modified.plane.adjacent b c) → ((PeriodicTileAdjacentContactRegularity
            cert.modified) → ((x ∈ FootprintVertices (cert.modified.tile b) ∩ FootprintVertices
            (cert.modified.tile c)) → (x ∈ CommonFootprintEdgeVertices (cert.modified.tile b)
            (cert.modified.tile c)))) ) := by
  classical
  intro q cfg C T cert x b c hbc hregular hxBC
  rw [← hregular.adjacent_raw_eq_edge_vertices b c hbc]
  exact hxBC

private theorem classifyBCface :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        ∀ (F : cert.modified.plane.Face), ((∃ i, cert.modified.plane.faceVertex F i = b) ∧
            ∃ i, cert.modified.plane.faceVertex F i = c) → (cert.modifiedFaceEquivalence F =
                ⟨.I1, 0,
                0⟩ ∨ cert.modifiedFaceEquivalence F = ⟨.J3, -1, -1⟩) ) := by
  classical
  intro q cfg C T cert b c F hF
  obtain ⟨i, hi⟩ := hF.1
  obtain ⟨j, hj⟩ := hF.2
  rw [cert.modified_face_vertices] at hi hj
  generalize hidx : cert.modifiedFaceEquivalence F = face at hi hj ⊢
  rcases face with ⟨label, m, n⟩
  cases label <;> fin_cases i <;> fin_cases j <;>
    simp [SixSubtileFaceVertices, b, c] at hi hj ⊢ <;> omega

private theorem rhoFace :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (F : cert.modified.plane.Face), ∀ (face : PeriodicSubtileFaceIndex),
            (cert.modifiedFaceEquivalence F = face) → (cert.modified.rho F =
                cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm face)) ) := by
  classical
  intro q cfg C T cert F face hF
  have hEq : F = cert.modifiedFaceEquivalence.symm face := by
    have hh := congrArg cert.modifiedFaceEquivalence.symm hF
    simpa using hh
  rw [hEq, cert.modified_face_points]

private theorem hfpoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f : cert.modified.plane.Face), ((cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f = (⟨SixSubtileFaceLabel.I1, (0
            : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex) ∨ (cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f = (⟨SixSubtileFaceLabel.J3,
            (-1 : ℤ), (-1 : ℤ)⟩ : PeriodicSubtileFaceIndex)) → (
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let pJ := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J3, -1, -1⟩)
        (∀ (F : cert.modified.plane.Face), ∀ (face : PeriodicSubtileFaceIndex),
            (cert.modifiedFaceEquivalence F = face) → (cert.modified.rho F =
                cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm face))) → (cert.modified.rho f = p1 ∨
            cert.modified.rho f = pJ)) ) := by
  classical
  intro q cfg C T cert f hfclass p1 pJ rhoFace
  rcases hfclass with h | h
  · exact Or.inl (by simpa [p1] using rhoFace f _ h)
  · exact Or.inr (by simpa [pJ] using rhoFace f _ h)

private abbrev hgpoint := ApollonianSuperharmonic.JunctionRefinementGeometry.hfpoint

private theorem hx_p1_or_pJ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (f : cert.modified.plane.Face), ∀ (g :
            cert.modified.plane.Face), (x = cert.modified.rho f ∨ x = cert.modified.rho g) → (
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let pJ := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J3, -1, -1⟩)
        (cert.modified.rho f = p1 ∨ cert.modified.rho f = pJ) → ((cert.modified.rho g = p1 ∨
            cert.modified.rho g = pJ) → (x = p1 ∨ x = pJ))) ) := by
  classical
  intro q cfg C T cert x f g hxendpoint p1 pJ hfpoint hgpoint
  rcases hxendpoint with h | h
  · rcases hfpoint with hF | hF
    · exact Or.inl (h.trans hF)
    · exact Or.inr (h.trans hF)
  · rcases hgpoint with hG | hG
    · exact Or.inl (h.trans hG)
    · exact Or.inr (h.trans hG)

private theorem hJvertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let faceJ : PeriodicSubtileFaceIndex := ⟨.J3, -1, -1⟩
        let aJ : PeriodicSubtileIndex := ⟨.A, -1, -1⟩
        cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ) 0 = aJ ) := by
  classical
  intro q cfg C T cert faceJ aJ
  rw [cert.modified_face_vertices]
  simp [faceJ, aJ, SixSubtileFaceVertices]

private theorem hpJa :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let pJ := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J3, -1, -1⟩)
        let faceJ : PeriodicSubtileFaceIndex := ⟨.J3, -1, -1⟩
        let aJ : PeriodicSubtileIndex := ⟨.A, -1, -1⟩
        (cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ) 0 = aJ) → (pJ ∈
            FootprintVertices (cert.modified.tile aJ)) ) := by
  classical
  intro q cfg C T cert pJ faceJ aJ hJvertex
  have h := cert.modified.rho_common (cert.modifiedFaceEquivalence.symm faceJ) 0
  rw [cert.modified_face_points, hJvertex] at h
  simpa [pJ, faceJ] using h

private theorem hblockSep :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (m : Int), ∀ (n : Int), ((m, n) ≠ (0, 0)) → (Disjoint T.cells (TileTranslation
            T ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells)) → (Disjoint
            T.cells (TileTranslation T ((-1 : GaussianInt) * cert.u + (-1 : GaussianInt) *
            cert.v)).cells) ) := by
  classical
  intro q cfg C T cert blockSeparation
  exact blockSeparation (-1) (-1) (by decide)

private theorem htranslatedCell :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (label : SixSubtileLabel), ∀ (m : Int), ∀ (n : Int), ∀ (a : GaussianInt), (a ∈
            (cert.modified.tile ⟨label, m, n⟩).cells) → (a ∈ (TileTranslation T ((m :
            GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells)) → (
        let aJ : PeriodicSubtileIndex := ⟨.A, -1, -1⟩
        ∀ (a : GaussianInt), (a ∈ (cert.modified.tile aJ).cells) → (a ∈ (TileTranslation T ((-1 :
            GaussianInt) * cert.u + (-1 : GaussianInt) * cert.v)).cells)) ) := by
  classical
  intro q cfg C T cert tileCellInBlock aJ a ha
  exact tileCellInBlock .A (-1) (-1) a (by simpa [aJ] using ha)

private theorem hp1C :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        p1 ∈ FootprintVertices (cert.P 1 true)) ) := by
  classical
  intro q cfg C T cert htransZero p1
  let faceI : PeriodicSubtileFaceIndex := ⟨.I1, 0, 0⟩
  let cI : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  have hvertex : cert.modified.plane.faceVertex
      (cert.modifiedFaceEquivalence.symm faceI) 2 = cI := by
    rw [cert.modified_face_vertices]
    simp [faceI, cI, SixSubtileFaceVertices]
  have h := cert.modified.rho_common
    (cert.modifiedFaceEquivalence.symm faceI) 2
  rw [hvertex, cert.modified_tile, cert.modified_face_points] at h
  simpa [p1, faceI, cI, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, GaussianTranslation, htransZero, Finset.image_id] using h

private theorem hAtile :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        cert.modified.tile a0 = TileCellComplement (cert.P 0 true) cert.O) ) := by
  classical
  intro q cfg C T cert htransZero a0
  rw [cert.modified_tile]
  simp [a0, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, htransZero]

private theorem hDtile :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        cert.modified.tile d0 = cert.P 1 false) ) := by
  classical
  intro q cfg C T cert htransZero d0
  rw [cert.modified_tile]
  simp [d0, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, htransZero]

private theorem hOinA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ((cert.P (0 : Fin (3 : ℕ)) true).cells ∩ (cert.P (0 : Fin (3 : ℕ)) false).cells =
            cert.O.cells) → (cert.O.cells ⊆ (cert.P 0 true).cells) ) := by
  classical
  intro q cfg C T cert hABO z hz
  have hz' : z ∈ (cert.P 0 true).cells ∩ (cert.P 0 false).cells := by
    rw [hABO]
    exact hz
  exact (Finset.mem_inter.mp hz').1

private theorem hAcompne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        (cert.modified.tile a0 = TileCellComplement (cert.P 0 true) cert.O) →
            ((TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty) ) := by
  classical
  intro q cfg C T cert a0 hAtile
  rw [← hAtile]
  exact (LatticeTileGridStructure _ (cert.modified.tiles_are_disks a0)).1.1

private theorem hxAD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (x ∈ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∧ x ∈
            FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ∧ x ∈ FootprintVertices (cert.P (1
            : Fin (3 : ℕ)) false)) → (
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (cert.modified.tile a0 = TileCellComplement (cert.P 0 true) cert.O) →
            ((cert.modified.tile d0 = cert.P 1 false) → ((FootprintVertices (TileCellComplement
            (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 1 false) = FootprintVertices
            (cert.P 0 true) ∩ FootprintVertices (cert.P 1 false)) → (x ∈ FootprintVertices
            (cert.modified.tile a0) ∩ FootprintVertices (cert.modified.tile d0))))) ) := by
  classical
  intro q cfg C T cert x hABD a0 d0 hAtile hDtile hADvertices
  rw [hAtile, hDtile]
  exact hADvertices.symm ▸ (show x ∈ FootprintVertices (cert.P 0 true) ∩
    FootprintVertices (cert.P 1 false) from ⟨hABD.1, hABD.2.2⟩)

private theorem had :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        cert.modified.plane.adjacent a0 d0 ) := by
  classical
  intro q cfg C T cert a0 d0
  exact (cert.modified_adjacency a0 d0).mpr
    (AllowedSubtileIncidence.AD 0 0)

private theorem hADdis :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (cert.modified.tile a0 = TileCellComplement (cert.P 0 true) cert.O) →
            ((cert.modified.tile d0 = cert.P 1 false) → ((Disjoint (cert.P 1 false).cells (cert.P
            0 true).cells) → (Disjoint (cert.modified.tile a0).cells (cert.modified.tile
            d0).cells))) ) := by
  classical
  intro q cfg C T cert a0 d0 hAtile hDtile hDA
  rw [hAtile, hDtile]
  apply Finset.disjoint_left.mpr
  intro z hzA hzD
  exact (Finset.disjoint_left.mp hDA hzD (Finset.mem_sdiff.mp hzA).1).elim

private theorem hthirdABD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty)
            → ((y ∈ FootprintVertices W) → (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈
            W.cells))) → (((cert.P (0 : Fin (3 : ℕ)) true).cells ∩ (cert.P (0 : Fin (3 : ℕ))
            false).cells = cert.O.cells) → (
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (cert.modified.tile a0 = TileCellComplement (cert.P 0 true) cert.O) →
            ((cert.modified.tile d0 = cert.P 1 false) → ((Disjoint (cert.P 1 false).cells (cert.P
            0 false).cells) → ((x ∈ FootprintVertices (cert.P 0 true) ∧
          x ∈ FootprintVertices (cert.P 0 false) ∧
          x ∈ FootprintVertices (cert.P 1 false)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
              (cert.P 0 false).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile
              a0).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile d0).cells)))))) )
              := by
  classical
  intro q cfg C T cert x incident hABO a0 d0 hAtile hDtile hDB h
  obtain ⟨jB, hjB⟩ := incident (cert.P 0 false) x
    (LatticeTileGridStructure _ (cert.parent_lattice 0 false)).1.1 h.2.1
  have hjD : LatticeVertexIncidentCell x jB ∉ (cert.P 1 false).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hDB hh hjB).elim
  have hjA : LatticeVertexIncidentCell x jB ∉
      (TileCellComplement (cert.P 0 true) cert.O).cells := by
    intro hh
    have hpair : LatticeVertexIncidentCell x jB ∈
        (cert.P 0 true).cells ∩ (cert.P 0 false).cells :=
      Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hh).1, hjB⟩
    have ho : LatticeVertexIncidentCell x jB ∈ cert.O.cells := by
      rw [← hABO]
      exact hpair
    exact (Finset.mem_sdiff.mp hh).2 ho
  exact ⟨jB, hjB, by simpa [hAtile] using hjA, by simpa [hDtile] using hjD⟩

private theorem hxvAD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (PeriodicTileAdjacentContactRegularity cert.modified) → (
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        (x ∈ FootprintVertices (cert.modified.tile a0) ∩ FootprintVertices (cert.modified.tile
            d0)) → ((cert.modified.plane.adjacent a0 d0) → (x ∈ CommonFootprintEdgeVertices
            (cert.modified.tile a0) (cert.modified.tile d0)))) ) := by
  classical
  intro q cfg C T cert x hregular a0 d0 hxAD had
  rw [← hregular.adjacent_raw_eq_edge_vertices a0 d0 had]
  exact hxAD

private theorem classifyADface :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        ∀ (F : cert.modified.plane.Face), ((∃ i, cert.modified.plane.faceVertex F i = a0) ∧
            ∃ i, cert.modified.plane.faceVertex F i = d0) → (cert.modifiedFaceEquivalence F = ⟨.I2,
                0, 0⟩ ∨ cert.modifiedFaceEquivalence F = ⟨.J4, 0, 0⟩) ) := by
  classical
  intro q cfg C T cert a0 d0 F hF
  obtain ⟨i, hi⟩ := hF.1
  obtain ⟨j, hj⟩ := hF.2
  rw [cert.modified_face_vertices] at hi hj
  generalize hidx : cert.modifiedFaceEquivalence F = face at hi hj ⊢
  rcases face with ⟨label, m, n⟩
  cases label <;> fin_cases i <;> fin_cases j <;>
    simp [SixSubtileFaceVertices, a0, d0] at hi hj ⊢ <;> omega

private abbrev rhoFace2 :=
  ApollonianSuperharmonic.JunctionRefinementGeometry.rhoFace

private theorem hf2point :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f2 : cert.modified.plane.Face), ((cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f2 = (⟨SixSubtileFaceLabel.I2,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex) ∨ (cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f2 = (⟨SixSubtileFaceLabel.J4,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex)) → (
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        let pJ4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J4, 0, 0⟩)
        (∀ (F : cert.modified.plane.Face), ∀ (face : PeriodicSubtileFaceIndex),
            (cert.modifiedFaceEquivalence F = face) → (cert.modified.rho F =
                cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm face))) → (cert.modified.rho f2 = p2 ∨
            cert.modified.rho f2 = pJ4)) ) := by
  classical
  intro q cfg C T cert f2 hf2class p2 pJ4 rhoFace2
  rcases hf2class with h | h
  · exact Or.inl (by simpa [p2] using rhoFace2 f2 _ h)
  · exact Or.inr (by simpa [pJ4] using rhoFace2 f2 _ h)

private abbrev hg2point := ApollonianSuperharmonic.JunctionRefinementGeometry.hf2point

private theorem hx_p2_or_pJ4 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (f2 : cert.modified.plane.Face), ∀ (g2 :
            cert.modified.plane.Face), (x = cert.modified.rho f2 ∨ x = cert.modified.rho g2) → (
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        let pJ4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J4, 0, 0⟩)
        (cert.modified.rho f2 = p2 ∨ cert.modified.rho f2 = pJ4) → ((cert.modified.rho g2 = p2 ∨
            cert.modified.rho g2 = pJ4) → (x = p2 ∨ x = pJ4))) ) := by
  classical
  intro q cfg C T cert x f2 g2 hxendpointAD p2 pJ4 hf2point hg2point
  rcases hxendpointAD with h | h
  · rcases hf2point with hF | hF
    · exact Or.inl (h.trans hF)
    · exact Or.inr (h.trans hF)
  · rcases hg2point with hG | hG
    · exact Or.inl (h.trans hG)
    · exact Or.inr (h.trans hG)

private theorem hJ4vertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let faceJ4 : PeriodicSubtileFaceIndex := ⟨.J4, 0, 0⟩
        let bJ4 : PeriodicSubtileIndex := ⟨.B, 1, 1⟩
        cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ4) 1 = bJ4 ) := by
  classical
  intro q cfg C T cert faceJ4 bJ4
  rw [cert.modified_face_vertices]
  simp [faceJ4, bJ4, SixSubtileFaceVertices]

private theorem hpJ4b :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let pJ4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J4, 0, 0⟩)
        let faceJ4 : PeriodicSubtileFaceIndex := ⟨.J4, 0, 0⟩
        let bJ4 : PeriodicSubtileIndex := ⟨.B, 1, 1⟩
        (cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ4) 1 = bJ4) → (pJ4 ∈
            FootprintVertices (cert.modified.tile bJ4)) ) := by
  classical
  intro q cfg C T cert pJ4 faceJ4 bJ4 hJ4vertex
  have hh := cert.modified.rho_common (cert.modifiedFaceEquivalence.symm faceJ4) 1
  rw [cert.modified_face_points, hJ4vertex] at hh
  simpa [pJ4, faceJ4] using hh

private theorem hp2D :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        p2 ∈ FootprintVertices (cert.P 1 false)) ) := by
  classical
  intro q cfg C T cert htransZero p2
  let faceI2 : PeriodicSubtileFaceIndex := ⟨.I2, 0, 0⟩
  let dI2 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have hvertex : cert.modified.plane.faceVertex
      (cert.modifiedFaceEquivalence.symm faceI2) 2 = dI2 := by
    rw [cert.modified_face_vertices]
    simp [faceI2, dI2, SixSubtileFaceVertices]
  have hh := cert.modified.rho_common
    (cert.modifiedFaceEquivalence.symm faceI2) 2
  rw [hvertex, cert.modified_tile, cert.modified_face_points] at hh
  simpa [p2, faceI2, dI2, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, GaussianTranslation, htransZero, Finset.image_id] using hh

private abbrev hCtile0 := ApollonianSuperharmonic.JunctionRefinementGeometry.hCtile

private theorem hFtile0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        cert.modified.tile f0 = cert.P 2 false) ) := by
  classical
  intro q cfg C T cert htransZero f0
  rw [cert.modified_tile]
  simp [f0, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, htransZero]

private theorem hcd :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        cert.modified.plane.adjacent c0 f0 ) := by
  classical
  intro q cfg C T cert c0 f0
  exact (cert.modified_adjacency c0 f0).mpr
    (AllowedSubtileIncidence.CF 0 0)

private theorem hCFdis :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (cert.modified.tile c0 = cert.P 1 true) → ((cert.modified.tile f0 = cert.P 2 false) →
            ((Disjoint (cert.P 1 true).cells (cert.P 2 false).cells) → (Disjoint
            (cert.modified.tile c0).cells (cert.modified.tile f0).cells))) ) := by
  classical
  intro q cfg C T cert c0 f0 hCtile0 hFtile0 hCFseparate
  rw [hCtile0, hFtile0]
  exact hCFseparate

private theorem hthirdACF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty)
            → ((y ∈ FootprintVertices W) → (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈
            W.cells))) → ((Disjoint (cert.P 0 true).cells (cert.P 1 true).cells) → (
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (cert.modified.tile c0 = cert.P 1 true) → ((cert.modified.tile f0 = cert.P 2 false) →
            ((Disjoint (cert.P 0 true).cells (cert.P 2 false).cells) → ((x ∈ FootprintVertices
            (cert.P 0 true) ∧
          x ∈ FootprintVertices (cert.P 1 true) ∧
          x ∈ FootprintVertices (cert.P 2 false)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
              (cert.P 0 true).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile
              c0).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile f0).cells)))))) )
              := by
  classical
  intro q cfg C T cert x incident hACseparate c0 f0 hCtile0 hFtile0 hAFseparate h
  obtain ⟨jA, hjA⟩ := incident (cert.P 0 true) x
    (LatticeTileGridStructure _ (cert.parent_lattice 0 true)).1.1 h.1
  have hjC : LatticeVertexIncidentCell x jA ∉ (cert.P 1 true).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hACseparate hjA hh).elim
  have hjF : LatticeVertexIncidentCell x jA ∉ (cert.P 2 false).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hAFseparate hjA hh).elim
  exact ⟨jA, hjA, by simpa [hCtile0] using hjC,
    by simpa [hFtile0] using hjF⟩

private theorem hxCF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (x ∈ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∧ x ∈
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∧ x ∈ FootprintVertices (cert.P (2
            : Fin (3 : ℕ)) false)) → (
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (cert.modified.tile c0 = cert.P 1 true) → ((cert.modified.tile f0 = cert.P 2 false) → (x
            ∈ FootprintVertices (cert.modified.tile c0) ∩ FootprintVertices (cert.modified.tile
            f0)))) ) := by
  classical
  intro q cfg C T cert x hACF c0 f0 hCtile0 hFtile0
  simpa [hCtile0, hFtile0] using ⟨hACF.2.1, hACF.2.2⟩

private theorem hxvCF :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (PeriodicTileAdjacentContactRegularity cert.modified) → (
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (cert.modified.plane.adjacent c0 f0) → ((x ∈ FootprintVertices (cert.modified.tile c0) ∩
            FootprintVertices (cert.modified.tile f0)) → (x ∈ CommonFootprintEdgeVertices
            (cert.modified.tile c0) (cert.modified.tile f0)))) ) := by
  classical
  intro q cfg C T cert x hregular c0 f0 hcd hxCF
  rw [← hregular.adjacent_raw_eq_edge_vertices c0 f0 hcd]
  exact hxCF

private theorem classifyCFface :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        ∀ (F : cert.modified.plane.Face), ((∃ i, cert.modified.plane.faceVertex F i = c0) ∧
            ∃ i, cert.modified.plane.faceVertex F i = f0) → (cert.modifiedFaceEquivalence F = ⟨.I3,
                0, 0⟩ ∨ cert.modifiedFaceEquivalence F = ⟨.J8, 0, 0⟩) ) := by
  classical
  intro q cfg C T cert c0 f0 F hF
  obtain ⟨i, hi⟩ := hF.1
  obtain ⟨j, hj⟩ := hF.2
  rw [cert.modified_face_vertices] at hi hj
  generalize hidx : cert.modifiedFaceEquivalence F = face at hi hj ⊢
  rcases face with ⟨label, m, n⟩
  cases label <;> fin_cases i <;> fin_cases j <;>
    simp [SixSubtileFaceVertices, c0, f0] at hi hj ⊢ <;> omega

private abbrev rhoFace3 :=
  ApollonianSuperharmonic.JunctionRefinementGeometry.rhoFace

private theorem hf3point :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f3 : cert.modified.plane.Face), ((cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f3 = (⟨SixSubtileFaceLabel.I3,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex) ∨ (cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f3 = (⟨SixSubtileFaceLabel.J8,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex)) → (
        let p3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        let pJ8 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J8, 0, 0⟩)
        (∀ (F : cert.modified.plane.Face), ∀ (face : PeriodicSubtileFaceIndex),
            (cert.modifiedFaceEquivalence F = face) → (cert.modified.rho F =
                cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm face))) → (cert.modified.rho f3 = p3 ∨
            cert.modified.rho f3 = pJ8)) ) := by
  classical
  intro q cfg C T cert f3 hf3class p3 pJ8 rhoFace3
  rcases hf3class with h | h
  · exact Or.inl (by simpa [p3] using rhoFace3 f3 _ h)
  · exact Or.inr (by simpa [pJ8] using rhoFace3 f3 _ h)

private abbrev hg3point := ApollonianSuperharmonic.JunctionRefinementGeometry.hf3point

private theorem hx_p3_or_pJ8 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), ∀ (f3 : cert.modified.plane.Face), ∀ (g3 :
            cert.modified.plane.Face), (x = cert.modified.rho f3 ∨ x = cert.modified.rho g3) → (
        let p3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        let pJ8 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J8, 0, 0⟩)
        (cert.modified.rho f3 = p3 ∨ cert.modified.rho f3 = pJ8) → ((cert.modified.rho g3 = p3 ∨
            cert.modified.rho g3 = pJ8) → (x = p3 ∨ x = pJ8))) ) := by
  classical
  intro q cfg C T cert x f3 g3 hxendpointCF p3 pJ8 hf3point hg3point
  rcases hxendpointCF with h | h
  · rcases hf3point with hF | hF
    · exact Or.inl (h.trans hF)
    · exact Or.inr (h.trans hF)
  · rcases hg3point with hG | hG
    · exact Or.inl (h.trans hG)
    · exact Or.inr (h.trans hG)

private theorem hJ8vertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let faceJ8 : PeriodicSubtileFaceIndex := ⟨.J8, 0, 0⟩
        let dJ8 : PeriodicSubtileIndex := ⟨.D, -1, 0⟩
        cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ8) 1 = dJ8 ) := by
  classical
  intro q cfg C T cert faceJ8 dJ8
  rw [cert.modified_face_vertices]
  simp [faceJ8, dJ8, SixSubtileFaceVertices]

private theorem hpJ8d :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let pJ8 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J8, 0, 0⟩)
        let faceJ8 : PeriodicSubtileFaceIndex := ⟨.J8, 0, 0⟩
        let dJ8 : PeriodicSubtileIndex := ⟨.D, -1, 0⟩
        (cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ8) 1 = dJ8) → (pJ8 ∈
            FootprintVertices (cert.modified.tile dJ8)) ) := by
  classical
  intro q cfg C T cert pJ8 faceJ8 dJ8 hJ8vertex
  have hh := cert.modified.rho_common (cert.modifiedFaceEquivalence.symm faceJ8) 1
  rw [cert.modified_face_points, hJ8vertex] at hh
  simpa [pJ8, faceJ8] using hh

private theorem hp3F :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let p3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        p3 ∈ FootprintVertices (cert.P 2 false)) ) := by
  classical
  intro q cfg C T cert htransZero p3
  let faceI3 : PeriodicSubtileFaceIndex := ⟨.I3, 0, 0⟩
  let fI3 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  have hvertex : cert.modified.plane.faceVertex
      (cert.modifiedFaceEquivalence.symm faceI3) 2 = fI3 := by
    rw [cert.modified_face_vertices]
    simp [faceI3, fI3, SixSubtileFaceVertices]
  have hh := cert.modified.rho_common
    (cert.modifiedFaceEquivalence.symm faceI3) 2
  rw [hvertex, cert.modified_tile, cert.modified_face_points] at hh
  simpa [p3, faceI3, fI3, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, GaussianTranslation, htransZero, Finset.image_id] using hh

private theorem hEtile0 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (GaussianTranslation (0 : GaussianInt) = id) → (
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        cert.modified.tile e0 = cert.P 2 true) ) := by
  classical
  intro q cfg C T cert htransZero e0
  rw [cert.modified_tile]
  simp [e0, ModifiedSubtileOccurrenceInterpretation,
    TileTranslation, htransZero]

private theorem hde :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        cert.modified.plane.adjacent d0 e0 ) := by
  classical
  intro q cfg C T cert d0 e0
  exact (cert.modified_adjacency d0 e0).mpr
    (AllowedSubtileIncidence.DE 0 0)

private theorem hDEdis :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.tile d0 = cert.P 1 false) → ((cert.modified.tile e0 = cert.P 2 true) →
            ((Disjoint (cert.P 1 false).cells (cert.P 2 true).cells) → (Disjoint
            (cert.modified.tile d0).cells (cert.modified.tile e0).cells))) ) := by
  classical
  intro q cfg C T cert d0 e0 hDtile0 hEtile0 hDEseparate
  rw [hDtile0, hEtile0]
  exact hDEseparate

private theorem hthirdB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty)
            → ((y ∈ FootprintVertices W) → (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈
            W.cells))) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.tile d0 = cert.P 1 false) → ((cert.modified.tile e0 = cert.P 2 true) →
            ((Disjoint (cert.P 0 false).cells (cert.P 1 false).cells) → ((Disjoint (cert.P 0
            false).cells (cert.P 2 true).cells) → ((x ∈ FootprintVertices (cert.P 0 false) ∧
          x ∈ FootprintVertices (cert.P 1 false) ∧
          x ∈ FootprintVertices (cert.P 2 true)) → (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈
              (cert.P 0 false).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile
              d0).cells ∧ LatticeVertexIncidentCell x j ∉ (cert.modified.tile e0).cells)))))) )
              := by
  classical
  intro q cfg C T cert x incident d0 e0 hDtile0 hEtile0 hBDseparate hBEseparate h
  obtain ⟨jB, hjB⟩ := incident (cert.P 0 false) x
    (LatticeTileGridStructure _ (cert.parent_lattice 0 false)).1.1 h.1
  have hjD : LatticeVertexIncidentCell x jB ∉ (cert.P 1 false).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hBDseparate hjB hh).elim
  have hjE : LatticeVertexIncidentCell x jB ∉ (cert.P 2 true).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hBEseparate hjB hh).elim
  exact ⟨jB, hjB, by simpa [hDtile0] using hjD,
    by simpa [hEtile0] using hjE⟩

private theorem hxDE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (x ∈ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ∧ x
            ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) false) ∧ x ∈ FootprintVertices (cert.P
            (2 : Fin (3 : ℕ)) true)) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.tile d0 = cert.P 1 false) → ((cert.modified.tile e0 = cert.P 2 true) → (x
            ∈ FootprintVertices (cert.modified.tile d0) ∩ FootprintVertices (cert.modified.tile
            e0)))) ) := by
  classical
  intro q cfg C T cert x hBDE d0 e0 hDtile0 hEtile0
  simpa [hDtile0, hEtile0] using ⟨hBDE.2.1, hBDE.2.2⟩

private theorem hxvDE :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (x : GaussianInt), (PeriodicTileAdjacentContactRegularity cert.modified) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.plane.adjacent d0 e0) → ((x ∈ FootprintVertices (cert.modified.tile d0) ∩
            FootprintVertices (cert.modified.tile e0)) → (x ∈ CommonFootprintEdgeVertices
            (cert.modified.tile d0) (cert.modified.tile e0)))) ) := by
  classical
  intro q cfg C T cert x hregular d0 e0 hde hxDE
  rw [← hregular.adjacent_raw_eq_edge_vertices d0 e0 hde]
  exact hxDE

private abbrev rhoFace4 :=
  ApollonianSuperharmonic.JunctionRefinementGeometry.rhoFace

private theorem hf4point :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f4 : cert.modified.plane.Face), ((cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f4 = (⟨SixSubtileFaceLabel.I4,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex) ∨ (cert.modifiedFaceEquivalence :
            cert.modified.plane.Face → PeriodicSubtileFaceIndex) f4 = (⟨SixSubtileFaceLabel.J7,
            (1 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileFaceIndex)) → (
        let p4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I4, 0, 0⟩)
        let pJ7 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩)
        (∀ (F : cert.modified.plane.Face), ∀ (face : PeriodicSubtileFaceIndex),
            (cert.modifiedFaceEquivalence F = face) → (cert.modified.rho F =
                cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm face))) → (cert.modified.rho f4 = p4 ∨
            cert.modified.rho f4 = pJ7)) ) := by
  classical
  intro q cfg C T cert f4 hf4class p4 pJ7 rhoFace4
  rcases hf4class with h | h
  · exact Or.inl (by simpa [p4] using rhoFace4 f4 _ h)
  · exact Or.inr (by simpa [pJ7] using rhoFace4 f4 _ h)

private abbrev hg4point := ApollonianSuperharmonic.JunctionRefinementGeometry.hf4point

private theorem endpointAlternative :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (f4 : cert.modified.plane.Face), ∀ (g4 : cert.modified.plane.Face),
        let p4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I4, 0, 0⟩)
        let pJ7 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩)
        (cert.modified.rho f4 = p4 ∨ cert.modified.rho f4 = pJ7) → ((cert.modified.rho g4 = p4 ∨
            cert.modified.rho g4 = pJ7) → (∀ (z : GaussianInt), (z = cert.modified.rho f4 ∨ z =
            cert.modified.rho g4) → (z = p4 ∨ z = pJ7))) ) := by
  classical
  intro q cfg C T cert f4 g4 p4 pJ7 hf4point hg4point z hz
  rcases hz with h | h
  · rcases hf4point with hp | hp
    · exact Or.inl (h.trans hp)
    · exact Or.inr (h.trans hp)
  · rcases hg4point with hp | hp
    · exact Or.inl (h.trans hp)
    · exact Or.inr (h.trans hp)

private theorem hJ7vertex :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let faceJ7 : PeriodicSubtileFaceIndex := ⟨.J7, 1, 0⟩
        let cJ7 : PeriodicSubtileIndex := ⟨.C, 1, 0⟩
        cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ7) 0 = cJ7 ) := by
  classical
  intro q cfg C T cert faceJ7 cJ7
  rw [cert.modified_face_vertices]
  simp [faceJ7, cJ7, SixSubtileFaceVertices]

private theorem hpJ7c :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let pJ7 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩)
        let faceJ7 : PeriodicSubtileFaceIndex := ⟨.J7, 1, 0⟩
        let cJ7 : PeriodicSubtileIndex := ⟨.C, 1, 0⟩
        (cert.modified.plane.faceVertex (cert.modifiedFaceEquivalence.symm faceJ7) 0 = cJ7) → (pJ7 ∈
            FootprintVertices (cert.modified.tile cJ7)) ) := by
  classical
  intro q cfg C T cert pJ7 faceJ7 cJ7 hJ7vertex
  have hh := cert.modified.rho_common (cert.modifiedFaceEquivalence.symm faceJ7) 0
  rw [cert.modified_face_points, hJ7vertex] at hh
  simpa [pJ7, faceJ7] using hh

private theorem hS1disk :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), LatticeTile (cert.S 1 false) ) := by
  classical
  intro q cfg C T cert
  apply P4590T1PositivePrototileDisk _ _
    (cert.minus_occurrence 1 false).1
  change 0 < (cfg.firstPredecessor 2).1
  rw [cfg.firstParentTwo]
  have h := cfg.secondLarge
  omega

private theorem boundaryFootprint :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (z : GaussianInt), (z ∈
            BoundaryFootprintVertices U) → (z ∈ FootprintVertices U)) ) := by
  classical
  intro U hne z hz
  simp only [BoundaryFootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hz
  obtain ⟨e, he, hz⟩ := hz
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq]
  obtain ⟨a, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩ := he
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases ha with ⟨ha, _⟩ | ⟨_, ha⟩
    · refine ⟨a, ha, ?_⟩
      rcases hz with rfl | rfl <;> simp
    · refine ⟨_, ha, ?_⟩
      rcases hz with rfl | rfl <;>
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem nestedCellsInsideT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ z, z ∈ (cert.S 1 false).cells ∨ z ∈ (cert.P 1 false).cells ∨ z ∈ (cert.P 2
            true).cells → z ∈ T.cells ) := by
  classical
  intro q cfg C T cert z hz
  rcases hz with hs | hd | he
  · exact (cert.outer_union z).2 ⟨0, false,
      (cert.minus_union z).2 ⟨1, false, hs⟩⟩
  · exact (cert.outer_union z).2 ⟨1, false, hd⟩
  · exact (cert.outer_union z).2 ⟨2, true, he⟩

private theorem nestedStarInsideT :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (pN : GaussianInt), ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell pN j ∈
            (cert.S (1 : Fin (3 : ℕ)) false).cells ∨ LatticeVertexIncidentCell pN j ∈ (cert.P (1
            : Fin (3 : ℕ)) false).cells ∨ LatticeVertexIncidentCell pN j ∈ (cert.P (2 : Fin (3 :
            ℕ)) true).cells) ∧ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell pN j ∈ (cert.S (1
            : Fin (3 : ℕ)) false).cells) ∧ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell pN j ∈
            (cert.P (1 : Fin (3 : ℕ)) false).cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell pN j ∈ (cert.P (2 : Fin (3 : ℕ)) true).cells) ∧ ((∃ (j :
            Fin (4 : ℕ)), LatticeVertexIncidentCell pN j ∈ (cert.S (1 : Fin (3 : ℕ)) false).cells
            ∧ LatticeVertexIncidentCell pN (j + (2 : Fin (4 : ℕ))) ∈ (cert.P (1 : Fin (3 : ℕ))
            false).cells) ∨ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell pN j ∈ (cert.S (1 :
            Fin (3 : ℕ)) false).cells ∧ LatticeVertexIncidentCell pN (j + (2 : Fin (4 : ℕ))) ∈
            (cert.P (2 : Fin (3 : ℕ)) true).cells) ∨ ∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell pN j ∈ (cert.P (1 : Fin (3 : ℕ)) false).cells ∧
            LatticeVertexIncidentCell pN (j + (2 : Fin (4 : ℕ))) ∈ (cert.P (2 : Fin (3 : ℕ))
            true).cells)) → ((∀ z, z ∈ (cert.S 1 false).cells ∨ z ∈ (cert.P 1 false).cells ∨ z ∈
            (cert.P 2 true).cells → z ∈ T.cells) → (∀ j : Fin 4, LatticeVertexIncidentCell pN j ∈
            T.cells)) ) := by
  classical
  intro q cfg C T cert pN hsectorN nestedCellsInsideT j
  rcases hsectorN.1 j with hs | hd | he
  · exact nestedCellsInsideT _ (Or.inl hs)
  · exact nestedCellsInsideT _ (Or.inr (Or.inl hd))
  · exact nestedCellsInsideT _ (Or.inr (Or.inr he))

private theorem hSNthird :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty) → ((y ∈
            FootprintVertices W) → (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈ W.cells))) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.tile d0 = cert.P 1 false) → ((cert.modified.tile e0 = cert.P 2 true) →
            ((Disjoint (cert.P 0 false).cells (cert.P 1 false).cells) → ((Disjoint (cert.P 0
            false).cells (cert.P 2 true).cells) → (((cert.S 1 false).cells.Nonempty) → (∀ (pN :
            GaussianInt), (pN ∈ FootprintVertices (cert.S 1 false)) → (∃ j : Fin 4,
            LatticeVertexIncidentCell pN j ∈ (cert.S 1 false).cells ∧ LatticeVertexIncidentCell
            pN j ∉ (cert.modified.tile d0).cells ∧ LatticeVertexIncidentCell pN j ∉
            (cert.modified.tile e0).cells))))))) ) := by
  classical
  intro q cfg C T cert incident d0 e0 hDtile0 hEtile0 hBDseparate hBEseparate hS1ne pN hpNS
  obtain ⟨j, hj⟩ := incident (cert.S 1 false) pN hS1ne hpNS
  have hjB : LatticeVertexIncidentCell pN j ∈ (cert.P 0 false).cells :=
    (cert.minus_union _).2 ⟨1, false, hj⟩
  have hjD : LatticeVertexIncidentCell pN j ∉ (cert.P 1 false).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hBDseparate hjB hh).elim
  have hjE : LatticeVertexIncidentCell pN j ∉ (cert.P 2 true).cells := by
    intro hh
    exact (Finset.disjoint_left.mp hBEseparate hjB hh).elim
  exact ⟨j, hj, by simpa [hDtile0] using hjD,
    by simpa [hEtile0] using hjE⟩

private theorem hpNv :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (PeriodicTileAdjacentContactRegularity cert.modified) → (
        let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
        let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
        (cert.modified.tile d0 = cert.P 1 false) → ((cert.modified.tile e0 = cert.P 2 true) →
            ((cert.modified.plane.adjacent d0 e0) → (∀ (pN : GaussianInt), (pN ∈
            FootprintVertices (cert.P 1 false)) → ((pN ∈ FootprintVertices (cert.P 2 true)) → (pN
            ∈ CommonFootprintEdgeVertices (cert.modified.tile d0) (cert.modified.tile e0))))))) )
            := by
  classical
  intro q cfg C T cert hregular d0 e0 hDtile0 hEtile0 hde pN hpND hpNE
  rw [← hregular.adjacent_raw_eq_edge_vertices d0 e0 hde]
  simpa [hDtile0, hEtile0] using ⟨hpND, hpNE⟩

private theorem hpNeTranslated :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), (∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty) → ((y ∈
            FootprintVertices W) → (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈ W.cells))) → (
        let pJ7 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩)
        let cJ7 : PeriodicSubtileIndex := ⟨.C, 1, 0⟩
        (pJ7 ∈ FootprintVertices (cert.modified.tile cJ7)) → ((Disjoint T.cells (TileTranslation
            T ((↑(1 : ℤ) : GaussianInt) * cert.u + (↑(0 : ℤ) : GaussianInt) * cert.v)).cells) →
            ((∀ (z : GaussianInt), (z ∈ (cert.modified.tile cJ7).cells) → (z ∈ (TileTranslation T
            ((1 : GaussianInt) * cert.u + (0 : GaussianInt) * cert.v)).cells)) → (∀ (pN :
            GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell pN j ∈ T.cells) → (pN ≠
            pJ7))))) ) := by
  classical
  intro q cfg C T cert incident pJ7 cJ7 hpJ7c hblockSepDE hblockCellDE pN nestedStarInsideT hEq
  obtain ⟨j, hj⟩ := incident (cert.modified.tile cJ7) pJ7
    (LatticeTileGridStructure _ (cert.modified.tiles_are_disks cJ7)).1.1 hpJ7c
  have hjBlock := hblockCellDE (LatticeVertexIncidentCell pJ7 j) hj
  have hjT : LatticeVertexIncidentCell pJ7 j ∈ T.cells := by
    simpa [hEq] using nestedStarInsideT j
  exact (Finset.disjoint_left.mp hblockSepDE hjT hjBlock).elim

private theorem hpNisP4 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let p4 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I4, 0, 0⟩)
        let pJ7 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩)
        ∀ (pN : GaussianInt), (pN = p4 ∨ pN = pJ7) → ((pN ≠ pJ7) → (pN = p4)) ) := by
  classical
  intro q cfg C T cert p4 pJ7 pN hpNalt hpNeTranslated
  rcases hpNalt with hp | hp
  · exact hp
  · exact (hpNeTranslated hp).elim

private theorem hxJ7neq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    (∀ (W : ProtoTile),
                        ∀ (y : GaussianInt),
                          W.cells.Nonempty →
                            y ∈ FootprintVertices W →
                              ∃ j : Fin 4, LatticeVertexIncidentCell y j ∈ W.cells) →
                      (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) →
                        ∀ (f4 : cert.modified.plane.Face),
                          ∀ (g4 : cert.modified.plane.Face),
                            x = cert.modified.rho f4 ∨ x = cert.modified.rho g4 →
                              let pJ7 :=
                                cert.unmodified.core.rho
                                (cert.unmodified.faceEquiv.symm ⟨.J7, 1, 0⟩);
                              let cJ7 : PeriodicSubtileIndex := ⟨.C, 1, 0⟩;
                              pJ7 ∈ FootprintVertices (cert.modified.tile cJ7) →
                                Disjoint T.cells
                                (TileTranslation T
                                ((↑(1 : ℤ) : GaussianInt) * cert.u +
                                (↑(0 : ℤ) : GaussianInt) * cert.v)).cells →
                                (∀ (z : GaussianInt),
                                z ∈ (cert.modified.tile cJ7).cells →
                                z ∈
                                (TileTranslation T
                                ((1 : GaussianInt) * cert.u +
                                (0 : GaussianInt) * cert.v)).cells) →
                                x ≠ pJ7
    ) := by
  classical
  intro q cfg C T cert x incident hmissingT f4 g4 hxendpointDE pJ7 cJ7 hpJ7c hblockSepDE
      hblockCellDE hEq
  subst x
  obtain ⟨j, hj⟩ := incident (cert.modified.tile cJ7) pJ7
    (LatticeTileGridStructure _ (cert.modified.tiles_are_disks cJ7)).1.1 hpJ7c
  have hjBlock := hblockCellDE (LatticeVertexIncidentCell pJ7 j) hj
  exact (Finset.disjoint_left.mp hblockSepDE (hmissingT j) hjBlock).elim

end JunctionRefinementGeometry

namespace JunctionCases

private theorem firstJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    GaussianTranslation (0 : GaussianInt) = id →
                      (∀ (W : ProtoTile),
                          ∀ (y : GaussianInt),
                            Finset.Nonempty W.cells →
                              y ∈ FootprintVertices W →
                                ∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell y j ∈ W.cells) →
                        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) →
                          (∀ (U : ProtoTile),
                              ∀ (V : ProtoTile),
                                ∀ (W : ProtoTile),
                                ∀ (p : GaussianInt),
                                ∀ (q : GaussianInt),
                                ∀ (vertex : GaussianInt),
                                ∀ (vertices : Set GaussianInt),
                                LatticeTile U →
                                LatticeTile V →
                                Disjoint U.cells V.cells →
                                SimpleGridPathBetween vertices
                                (FootprintEdges U ∩ FootprintEdges V) p q →
                                vertex ∈ vertices →
                                (∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell vertex j ∈ W.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ U.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ V.cells) →
                                vertex = p ∨ vertex = q) →
                            let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
                            let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
                            cert.modified.plane.adjacent b c →
                              PeriodicTileAdjacentContactRegularity cert.modified →
                                ∀ (f : cert.modified.plane.Face),
                                ∀ (g : cert.modified.plane.Face),
                                ((∃ (i : Fin (3 : ℕ)),
                                cert.modified.plane.faceVertex f i = b) ∧
                                ∃ (i : Fin (3 : ℕ)),
                                cert.modified.plane.faceVertex f i = c) →
                                ((∃ (i : Fin (3 : ℕ)),
                                cert.modified.plane.faceVertex g i = b) ∧
                                ∃ (i : Fin (3 : ℕ)),
                                cert.modified.plane.faceVertex g i = c) →
                                SimpleGridPathBetween
                                (CommonFootprintEdgeVertices (cert.modified.tile b)
                                (cert.modified.tile c))
                                (FootprintEdges (cert.modified.tile b) ∩
                                FootprintEdges (cert.modified.tile c))
                                (cert.modified.rho f) (cert.modified.rho g) →
                                (∀ (m : ℤ),
                                ∀ (n : ℤ),
                                (m, n) ≠ ((0 : ℤ), (0 : ℤ)) →
                                Disjoint T.cells
                                (TileTranslation T
                                ((↑m : GaussianInt) * cert.u +
                                (↑n : GaussianInt) * cert.v)).cells) →
                                (∀ (label : SixSubtileLabel),
                                ∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (a : GaussianInt),
                                a ∈ (cert.modified.tile ⟨label, m, n⟩).cells →
                                a ∈
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells) →
                                cert.modified.tile b = cert.P 0 false →
                                cert.modified.tile c = cert.P 1 true →
                                Disjoint (cert.modified.tile b).cells
                                (cert.modified.tile c).cells →
                                (x ∈ FootprintVertices (cert.P 0 true) ∧
                                x ∈ FootprintVertices (cert.P 0 false) ∧
                                x ∈ FootprintVertices (cert.P 1 true) →
                                ∃ j : Fin 4,
                                LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧
                                LatticeVertexIncidentCell x j ∉ (cert.P 0 false).cells ∧
                                LatticeVertexIncidentCell x j ∉ (cert.P 1 true).cells) →
                                x ∈ FootprintVertices (cert.P 0 true) ∧
                                x ∈ FootprintVertices (cert.P 0 false) ∧
                                x ∈ FootprintVertices (cert.P 1 true) →
                                x ∈
                                FootprintVertices (cert.Q 1 true) ∩
                                FootprintVertices (cert.S 2 false) ∩
                                FootprintVertices (cert.P 1 true)
    ) := by
  classical
  intro q cfg C T cert x htransZero incident hmissingT path_endpoint_of_third b c hbc hregular f
      g hf hg hBCpath blockSeparation tileCellInBlock hBtile hCtile hBCdis hthirdABC hABC
  have hxv : x ∈ CommonFootprintEdgeVertices
      (cert.modified.tile b) (cert.modified.tile c) := JunctionRefinementGeometry.hxv q cfg C T
          cert x hbc hregular (JunctionRefinementGeometry.hxBC q cfg C T cert x hBtile hCtile
              hABC)
  have hxendpoint := path_endpoint_of_third
    (cert.modified.tile b) (cert.modified.tile c) (cert.P 0 true)
    (cert.modified.rho f) (cert.modified.rho g) x
    (CommonFootprintEdgeVertices (cert.modified.tile b) (cert.modified.tile c))
    (cert.modified.tiles_are_disks b) (cert.modified.tiles_are_disks c)
    hBCdis hBCpath hxv (by simpa [hBtile, hCtile] using hthirdABC hABC)
  have classifyBCface := JunctionRefinementGeometry.classifyBCface q cfg C T cert
  have hfclass := classifyBCface f hf
  have hgclass := classifyBCface g hg
  let p1 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
  let pJ := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.J3, -1, -1⟩)
  have rhoFace := JunctionRefinementGeometry.rhoFace q cfg C T cert
  have hx_p1_or_pJ := JunctionRefinementGeometry.hx_p1_or_pJ q cfg C T cert x
      f g hxendpoint (JunctionRefinementGeometry.hfpoint q cfg C T cert f hfclass rhoFace)
          (JunctionRefinementGeometry.hgpoint q cfg C T cert g hgclass rhoFace)
  let aJ : PeriodicSubtileIndex := ⟨.A, -1, -1⟩
  have hpJa := JunctionRefinementGeometry.hpJa
      q cfg C T cert (JunctionRefinementGeometry.hJvertex q cfg C T cert)
  have hblockSep := JunctionRefinementGeometry.hblockSep q cfg C T cert blockSeparation
  have htranslatedCell := JunctionRefinementGeometry.htranslatedCell q cfg C T cert
      tileCellInBlock
  rcases hx_p1_or_pJ with hxp1 | hxpj
  · have hp1C := JunctionRefinementGeometry.hp1C q cfg
      C T cert htransZero
    have htarget : p1 ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.S 2 false) ∩
        FootprintVertices (cert.P 1 true) := ⟨cert.inner_first, hp1C⟩
    simpa [hxp1] using htarget
  · subst x
    obtain ⟨j, hj⟩ := incident (cert.modified.tile aJ) pJ
      (LatticeTileGridStructure _ (cert.modified.tiles_are_disks aJ)).1.1 hpJa
    have hjT : LatticeVertexIncidentCell pJ j ∈ T.cells := hmissingT j
    have hjBlock := htranslatedCell (LatticeVertexIncidentCell pJ j) hj
    exact (Finset.disjoint_left.mp hblockSep hjT hjBlock).elim

private theorem secondJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    GaussianTranslation (0 : GaussianInt) = id →
                      (∀ (W : ProtoTile),
                          ∀ (y : GaussianInt),
                            Finset.Nonempty W.cells →
                              y ∈ FootprintVertices W →
                                ∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell y j ∈ W.cells) →
                        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) →
                          (∀ y ∈ CellSupportedFootprintVertices cert.O,
                              ∀ (a : GaussianInt),
                                y ∈ FootprintVertices (⟨{ a }, a⟩ : ProtoTile) →
                                a ∈ (cert.P (0 : Fin (3 : ℕ)) true).cells ∨
                                a ∈ (cert.P (0 : Fin (3 : ℕ)) false).cells) →
                            (∀ (U : ProtoTile),
                                ∀ (V : ProtoTile),
                                ∀ (W : ProtoTile),
                                ∀ (p : GaussianInt),
                                ∀ (q : GaussianInt),
                                ∀ (vertex : GaussianInt),
                                ∀ (vertices : Set GaussianInt),
                                LatticeTile U →
                                LatticeTile V →
                                Disjoint U.cells V.cells →
                                SimpleGridPathBetween vertices
                                (FootprintEdges U ∩ FootprintEdges V) p q →
                                vertex ∈ vertices →
                                (∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell vertex j ∈ W.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ U.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ V.cells) →
                                vertex = p ∨ vertex = q) →
                              (cert.P (0 : Fin (3 : ℕ)) true).cells ∩
                                (cert.P (0 : Fin (3 : ℕ)) false).cells =
                                cert.O.cells →
                                (∀ (i : Fin (3 : ℕ)),
                                ∀ (s : Bool),
                                ∀ (j : Fin (3 : ℕ)),
                                ∀ (t : Bool),
                                (i, s) ≠ (j, t) →
                                ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) →
                                Disjoint (cert.P i s).cells (cert.P j t).cells) →
                                PeriodicTileAdjacentContactRegularity cert.modified →
                                (∀ (m : ℤ),
                                ∀ (n : ℤ),
                                (m, n) ≠ ((0 : ℤ), (0 : ℤ)) →
                                Disjoint T.cells
                                (TileTranslation T
                                ((↑m : GaussianInt) * cert.u +
                                (↑n : GaussianInt) * cert.v)).cells) →
                                (∀ (label : SixSubtileLabel),
                                ∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (a : GaussianInt),
                                a ∈ (cert.modified.tile ⟨label, m, n⟩).cells →
                                a ∈
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells) →
                                x ∈ FootprintVertices (cert.P 0 true) ∧
                                x ∈ FootprintVertices (cert.P 0 false) ∧
                                x ∈ FootprintVertices (cert.P 1 false) →
                                x ∈
                                FootprintVertices (cert.Q 2 true) ∩
                                FootprintVertices (cert.S 1 false) ∩
                                FootprintVertices (cert.P 1 false)
    ) := by
  classical
  intro q cfg C T cert x htransZero incident hmissingT precursorIsolationSupported
      path_endpoint_of_third hABO hseparate hregular blockSeparation tileCellInBlock hABD
  let a0 : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have hAtile : cert.modified.tile a0 =
      TileCellComplement (cert.P 0 true) cert.O := JunctionRefinementGeometry.hAtile q cfg C
          T cert htransZero
  have hDtile : cert.modified.tile d0 = cert.P 1 false := JunctionRefinementGeometry.hDtile q
      cfg C T cert htransZero
  have hDA : Disjoint (cert.P 1 false).cells (cert.P 0 true).cells :=
    hseparate 1 false 0 true (by decide) (by decide)
  have hDB : Disjoint (cert.P 1 false).cells (cert.P 0 false).cells :=
    hseparate 1 false 0 false (by decide) (by decide)
  have hret := FootprintDeletionRetention (cert.P 0 true)
    (cert.P 0 false) cert.O (cert.P 1 false) (JunctionRefinementGeometry.hOinA q cfg C T cert
        hABO)
    precursorIsolationSupported hDA hDB
  have hDne : (cert.P 1 false).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice 1 false)).1.1
  have hADvertices :
      FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
        FootprintVertices (cert.P 1 false) =
      FootprintVertices (cert.P 0 true) ∩
        FootprintVertices (cert.P 1 false) :=
    hret.2.2 (Or.inr ⟨(JunctionRefinementGeometry.hAcompne q cfg C T cert hAtile), hDne⟩)
  have hxAD := JunctionRefinementGeometry.hxAD q cfg C T
          cert x hABD hAtile hDtile hADvertices
  have had := JunctionRefinementGeometry.had q cfg C T cert
  have hadne : a0 ≠ d0 := by decide
  have hADedges := cert.modified.adjacent_has_common_edge a0 d0 had
  obtain ⟨_, f2, g2, hfg2, hf2, hg2, hfaces2, hADpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular a0 d0 hadne).1.mpr hADedges
  have hthirdABD (h : x ∈ FootprintVertices (cert.P 0 true) ∧
      x ∈ FootprintVertices (cert.P 0 false) ∧
      x ∈ FootprintVertices (cert.P 1 false)) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile a0).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile d0).cells :=
            JunctionRefinementGeometry.hthirdABD q cfg C T cert x incident hABO hAtile hDtile
            hDB h
  have hxendpointAD := path_endpoint_of_third
    (cert.modified.tile a0) (cert.modified.tile d0) (cert.P 0 false)
    (cert.modified.rho f2) (cert.modified.rho g2) x
    (CommonFootprintEdgeVertices (cert.modified.tile a0) (cert.modified.tile d0))
    (cert.modified.tiles_are_disks a0) (cert.modified.tiles_are_disks d0)
    (JunctionRefinementGeometry.hADdis q cfg C T cert hAtile hDtile hDA) hADpath
        (JunctionRefinementGeometry.hxvAD q cfg C T cert x hregular hxAD had)
    (by simpa [hAtile, hDtile] using hthirdABD hABD)
  have classifyADface := JunctionRefinementGeometry.classifyADface q cfg C T cert
  have hf2class := classifyADface f2 hf2
  have hg2class := classifyADface g2 hg2
  let p2 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
  let pJ4 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.J4, 0, 0⟩)
  have rhoFace2 := JunctionRefinementGeometry.rhoFace2 q cfg C T cert
  have hx_p2_or_pJ4 := JunctionRefinementGeometry.hx_p2_or_pJ4 q cfg C T
      cert x f2 g2 hxendpointAD (JunctionRefinementGeometry.hf2point q cfg C T cert f2
          hf2class rhoFace2) (JunctionRefinementGeometry.hg2point q cfg C T cert g2 hg2class
          rhoFace2)
  let bJ4 : PeriodicSubtileIndex := ⟨.B, 1, 1⟩
  have hpJ4b := JunctionRefinementGeometry.hpJ4b q cfg C T cert
      (JunctionRefinementGeometry.hJ4vertex q cfg C T cert)
  have hblockSepAD := blockSeparation 1 1 (by decide)
  have hblockCellAD (v : GaussianInt)
      (hv : v ∈ (cert.modified.tile bJ4).cells) :
      v ∈ (TileTranslation T
        ((1 : GaussianInt) * cert.u + (1 : GaussianInt) * cert.v)).cells :=
    tileCellInBlock .B 1 1 v (by simpa [bJ4] using hv)
  rcases hx_p2_or_pJ4 with hxp2 | hxpj4
  · have hp2D := JunctionRefinementGeometry.hp2D q
      cfg C T cert htransZero
    have htarget : p2 ∈ FootprintVertices (cert.Q 2 true) ∩
        FootprintVertices (cert.S 1 false) ∩
        FootprintVertices (cert.P 1 false) := ⟨cert.inner_second, hp2D⟩
    simpa [hxp2] using htarget
  · subst x
    obtain ⟨j, hj⟩ := incident (cert.modified.tile bJ4) pJ4
      (LatticeTileGridStructure _ (cert.modified.tiles_are_disks bJ4)).1.1 hpJ4b
    have hjT : LatticeVertexIncidentCell pJ4 j ∈ T.cells := hmissingT j
    exact (Finset.disjoint_left.mp hblockSepAD hjT
      (hblockCellAD (LatticeVertexIncidentCell pJ4 j) hj)).elim

private theorem thirdJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    GaussianTranslation (0 : GaussianInt) = id →
                      (∀ (W : ProtoTile),
                          ∀ (y : GaussianInt),
                            Finset.Nonempty W.cells →
                              y ∈ FootprintVertices W →
                                ∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell y j ∈ W.cells) →
                        (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) →
                          (∀ (U : ProtoTile),
                              ∀ (V : ProtoTile),
                                ∀ (W : ProtoTile),
                                ∀ (p : GaussianInt),
                                ∀ (q : GaussianInt),
                                ∀ (vertex : GaussianInt),
                                ∀ (vertices : Set GaussianInt),
                                LatticeTile U →
                                LatticeTile V →
                                Disjoint U.cells V.cells →
                                SimpleGridPathBetween vertices
                                (FootprintEdges U ∩ FootprintEdges V) p q →
                                vertex ∈ vertices →
                                (∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell vertex j ∈ W.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ U.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ V.cells) →
                                vertex = p ∨ vertex = q) →
                            (∀ (i : Fin (3 : ℕ)),
                                ∀ (s : Bool),
                                ∀ (j : Fin (3 : ℕ)),
                                ∀ (t : Bool),
                                (i, s) ≠ (j, t) →
                                ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) →
                                Disjoint (cert.P i s).cells (cert.P j t).cells) →
                              Disjoint (cert.P 0 true).cells (cert.P 1 true).cells →
                                PeriodicTileAdjacentContactRegularity cert.modified →
                                (∀ (m : ℤ),
                                ∀ (n : ℤ),
                                (m, n) ≠ ((0 : ℤ), (0 : ℤ)) →
                                Disjoint T.cells
                                (TileTranslation T
                                ((↑m : GaussianInt) * cert.u +
                                (↑n : GaussianInt) * cert.v)).cells) →
                                (∀ (label : SixSubtileLabel),
                                ∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (a : GaussianInt),
                                a ∈ (cert.modified.tile ⟨label, m, n⟩).cells →
                                a ∈
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells) →
                                x ∈ FootprintVertices (cert.P 0 true) ∧
                                x ∈ FootprintVertices (cert.P 1 true) ∧
                                x ∈ FootprintVertices (cert.P 2 false) →
                                x ∈
                                FootprintVertices (cert.Q 1 true) ∩
                                FootprintVertices (cert.P 1 true) ∩
                                FootprintVertices (cert.P 2 false)
    ) := by
  classical
  intro q cfg C T cert x htransZero incident hmissingT path_endpoint_of_third hseparate
      hACseparate hregular blockSeparation tileCellInBlock hACF
  let c0 : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let f0 : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  have hCtile0 : cert.modified.tile c0 = cert.P 1 true :=
      JunctionRefinementGeometry.hCtile0 q cfg C T cert htransZero
  have hFtile0 : cert.modified.tile f0 = cert.P 2 false :=
      JunctionRefinementGeometry.hFtile0 q cfg C T cert htransZero
  have hCFseparate : Disjoint (cert.P 1 true).cells
      (cert.P 2 false).cells := hseparate 1 true 2 false (by decide) (by decide)
  have hAFseparate : Disjoint (cert.P 0 true).cells
      (cert.P 2 false).cells := hseparate 0 true 2 false (by decide) (by decide)
  have hcd := JunctionRefinementGeometry.hcd q cfg C T
      cert
  have hcdne : c0 ≠ f0 := by decide
  have hCFedges := cert.modified.adjacent_has_common_edge c0 f0 hcd
  obtain ⟨_, f3, g3, hfg3, hf3, hg3, hfaces3, hCFpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular c0 f0 hcdne).1.mpr hCFedges
  have hthirdACF (h : x ∈ FootprintVertices (cert.P 0 true) ∧
      x ∈ FootprintVertices (cert.P 1 true) ∧
      x ∈ FootprintVertices (cert.P 2 false)) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile c0).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile f0).cells :=
            JunctionRefinementGeometry.hthirdACF q cfg C T cert x incident hACseparate
            hCtile0 hFtile0 hAFseparate h
  have hxendpointCF := path_endpoint_of_third
    (cert.modified.tile c0) (cert.modified.tile f0) (cert.P 0 true)
    (cert.modified.rho f3) (cert.modified.rho g3) x
    (CommonFootprintEdgeVertices (cert.modified.tile c0) (cert.modified.tile f0))
    (cert.modified.tiles_are_disks c0) (cert.modified.tiles_are_disks f0)
    (JunctionRefinementGeometry.hCFdis q cfg C T cert hCtile0 hFtile0 hCFseparate) hCFpath
        (JunctionRefinementGeometry.hxvCF q cfg C T cert x hregular hcd
        (JunctionRefinementGeometry.hxCF q cfg C T cert x hACF hCtile0 hFtile0))
    (by simpa [hCtile0, hFtile0] using hthirdACF hACF)
  have classifyCFface := JunctionRefinementGeometry.classifyCFface q cfg C T cert
  have hf3class := classifyCFface f3 hf3
  have hg3class := classifyCFface g3 hg3
  let p3 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
  let pJ8 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.J8, 0, 0⟩)
  have rhoFace3 := JunctionRefinementGeometry.rhoFace3 q cfg C T cert
  have hx_p3_or_pJ8 := JunctionRefinementGeometry.hx_p3_or_pJ8 q cfg C T
      cert x f3 g3 hxendpointCF (JunctionRefinementGeometry.hf3point q cfg C T cert f3
          hf3class rhoFace3) (JunctionRefinementGeometry.hg3point q cfg C T cert g3
          hg3class rhoFace3)
  let dJ8 : PeriodicSubtileIndex := ⟨.D, -1, 0⟩
  have hpJ8d := JunctionRefinementGeometry.hpJ8d q cfg C T cert
      (JunctionRefinementGeometry.hJ8vertex q cfg C T cert)
  have hblockSepCF := blockSeparation (-1) 0 (by decide)
  rcases hx_p3_or_pJ8 with hxp3 | hxpj8
  · have hp3F := JunctionRefinementGeometry.hp3F
      q cfg C T cert htransZero
    have htarget : p3 ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.P 1 true) ∩
        FootprintVertices (cert.P 2 false) := ⟨cert.inner_third, hp3F⟩
    simpa [hxp3] using htarget
  · subst x
    obtain ⟨j, hj⟩ := incident (cert.modified.tile dJ8) pJ8
      (LatticeTileGridStructure _ (cert.modified.tiles_are_disks dJ8)).1.1 hpJ8d
    have hjBlock := tileCellInBlock .D (-1) 0
      (LatticeVertexIncidentCell pJ8 j) (by simpa [dJ8] using hj)
    exact (Finset.disjoint_left.mp hblockSepCF (hmissingT j) hjBlock).elim

private theorem fourthJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    x ∈ FootprintVertices T →
                      x ∉ BoundaryFootprintVertices T →
                        GaussianTranslation (0 : GaussianInt) = id →
                          (∀ (W : ProtoTile),
                              ∀ (y : GaussianInt),
                                Finset.Nonempty W.cells →
                                y ∈ FootprintVertices W →
                                ∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell y j ∈ W.cells) →
                            (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells) →
                              x ∈ T.cells ∧
                                x - (1 : GaussianInt) ∈ T.cells ∧
                                x - (1 : GaussianInt) -
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈
                                T.cells ∧
                                x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ T.cells →
                                (∀ (U : ProtoTile),
                                ∀ (V : ProtoTile),
                                ∀ (W : ProtoTile),
                                ∀ (p : GaussianInt),
                                ∀ (q : GaussianInt),
                                ∀ (vertex : GaussianInt),
                                ∀ (vertices : Set GaussianInt),
                                LatticeTile U →
                                LatticeTile V →
                                Disjoint U.cells V.cells →
                                SimpleGridPathBetween vertices
                                (FootprintEdges U ∩ FootprintEdges V) p q →
                                vertex ∈ vertices →
                                (∃ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell vertex j ∈ W.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ U.cells ∧
                                LatticeVertexIncidentCell vertex j ∉ V.cells) →
                                vertex = p ∨ vertex = q) →
                                (∀ (i : Fin (3 : ℕ)),
                                ∀ (s : Bool),
                                ∀ (j : Fin (3 : ℕ)),
                                ∀ (t : Bool),
                                (i, s) ≠ (j, t) →
                                ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) →
                                Disjoint (cert.P i s).cells (cert.P j t).cells) →
                                PeriodicTileAdjacentContactRegularity cert.modified →
                                (∀ (m : ℤ),
                                ∀ (n : ℤ),
                                (m, n) ≠ ((0 : ℤ), (0 : ℤ)) →
                                Disjoint T.cells
                                (TileTranslation T
                                ((↑m : GaussianInt) * cert.u +
                                (↑n : GaussianInt) * cert.v)).cells) →
                                (∀ (label : SixSubtileLabel),
                                ∀ (m : Int),
                                ∀ (n : Int),
                                ∀ (a : GaussianInt),
                                a ∈ (cert.modified.tile ⟨label, m, n⟩).cells →
                                a ∈
                                (TileTranslation T
                                ((m : GaussianInt) * cert.u +
                                (n : GaussianInt) * cert.v)).cells) →
                                (x ∈ FootprintVertices (cert.P 0 true) ∧
                                x ∈ FootprintVertices (cert.P 0 false) ∧
                                x ∈ FootprintVertices (cert.P 1 true) →
                                ∃ j : Fin 4,
                                LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧
                                LatticeVertexIncidentCell x j ∉ (cert.P 0 false).cells ∧
                                LatticeVertexIncidentCell x j ∉ (cert.P 1 true).cells) →
                                x ∈ FootprintVertices (cert.P 0 false) ∧
                                x ∈ FootprintVertices (cert.P 1 false) ∧
                                x ∈ FootprintVertices (cert.P 2 true) →
                                x ∈
                                FootprintVertices (cert.S 1 false) ∩
                                FootprintVertices (cert.P 1 false) ∩
                                FootprintVertices (cert.P 2 true)
    ) := by
  classical
  intro q cfg C T cert x hx hxb htransZero incident hmissingT hfourCells path_endpoint_of_third
      hseparate hregular blockSeparation tileCellInBlock hthirdABC hBDE
  let d0 : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  let e0 : PeriodicSubtileIndex := ⟨.E, 0, 0⟩
  have hDtile0 : cert.modified.tile d0 = cert.P 1 false :=
      JunctionRefinementGeometry.hDtile q cfg C T cert htransZero
  have hEtile0 : cert.modified.tile e0 = cert.P 2 true :=
      JunctionRefinementGeometry.hEtile0 q cfg C T cert htransZero
  have hDEseparate : Disjoint (cert.P 1 false).cells
      (cert.P 2 true).cells := hseparate 1 false 2 true (by decide) (by decide)
  have hBDseparate : Disjoint (cert.P 0 false).cells
      (cert.P 1 false).cells := hseparate 0 false 1 false (by decide) (by decide)
  have hBEseparate : Disjoint (cert.P 0 false).cells
      (cert.P 2 true).cells := hseparate 0 false 2 true (by decide) (by decide)
  have hde := JunctionRefinementGeometry.hde q cfg C T
      cert
  have hdene : d0 ≠ e0 := by decide
  have hDEedges := cert.modified.adjacent_has_common_edge d0 e0 hde
  obtain ⟨_, f4, g4, hfg4, hf4, hg4, hfaces4, hDEpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular d0 e0 hdene).1.mpr hDEedges
  have hDEdis := JunctionRefinementGeometry.hDEdis q cfg C T cert
          hDtile0 hEtile0 hDEseparate
  have hthirdB (h : x ∈ FootprintVertices (cert.P 0 false) ∧
      x ∈ FootprintVertices (cert.P 1 false) ∧
      x ∈ FootprintVertices (cert.P 2 true)) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 false).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile d0).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.modified.tile e0).cells :=
            JunctionRefinementGeometry.hthirdB q cfg C T cert x incident hDtile0 hEtile0
            hBDseparate hBEseparate h
  have hxDE := JunctionRefinementGeometry.hxDE q cfg C
          T cert x hBDE hDtile0 hEtile0
  have hxvDE := JunctionRefinementGeometry.hxvDE q
          cfg C T cert x hregular hde hxDE
  have hxendpointDE := path_endpoint_of_third
    (cert.modified.tile d0) (cert.modified.tile e0) (cert.P 0 false)
    (cert.modified.rho f4) (cert.modified.rho g4) x
    (CommonFootprintEdgeVertices (cert.modified.tile d0) (cert.modified.tile e0))
    (cert.modified.tiles_are_disks d0) (cert.modified.tiles_are_disks e0)
    hDEdis hDEpath hxvDE
    (by simpa [hDtile0, hEtile0] using hthirdB hBDE)
  have classifyDEface (F : cert.modified.plane.Face)
      (hF : (∃ i, cert.modified.plane.faceVertex F i = d0) ∧
        ∃ i, cert.modified.plane.faceVertex F i = e0) :
      cert.modifiedFaceEquivalence F = ⟨.I4, 0, 0⟩ ∨
      cert.modifiedFaceEquivalence F = ⟨.J7, 1, 0⟩ :=
    (by
    obtain ⟨i, hi⟩ := hF.1
    obtain ⟨j, hj⟩ := hF.2
    rw [cert.modified_face_vertices] at hi hj
    generalize hidx : cert.modifiedFaceEquivalence F = face at hi hj ⊢
    rcases face with ⟨label, m, n⟩
    cases label <;> fin_cases i <;> fin_cases j <;>
      simp [SixSubtileFaceVertices, d0, e0] at hi hj ⊢ <;> omega)
  have hf4class := classifyDEface f4 hf4
  have hg4class := classifyDEface g4 hg4
  let p4 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I4, 0, 0⟩)
  have rhoFace4 := JunctionRefinementGeometry.rhoFace4 q cfg C T cert
  have endpointAlternative := JunctionRefinementGeometry.endpointAlternative q cfg C T cert
      f4 g4 (JunctionRefinementGeometry.hf4point q cfg C T cert f4 hf4class rhoFace4)
      (JunctionRefinementGeometry.hg4point q cfg C T cert g4 hg4class rhoFace4)
  let cJ7 : PeriodicSubtileIndex := ⟨.C, 1, 0⟩
  have hpJ7c := JunctionRefinementGeometry.hpJ7c q cfg C T cert
      (JunctionRefinementGeometry.hJ7vertex q cfg C T cert)
  have hblockSepDE := blockSeparation 1 0 (by decide)
  have hblockCellDE (z : GaussianInt)
      (hz : z ∈ (cert.modified.tile cJ7).cells) :
      z ∈ (TileTranslation T
        ((1 : GaussianInt) * cert.u + (0 : GaussianInt) * cert.v)).cells :=
    tileCellInBlock SixSubtileLabel.C 1 0 z
      (by simpa only [cJ7] using hz)
  have hS1disk := JunctionRefinementGeometry.hS1disk q cfg C
      T cert
  have hS1ne : (cert.S 1 false).cells.Nonempty :=
    (LatticeTileGridStructure _ hS1disk).1.1
  have boundaryFootprint := JunctionRefinementGeometry.boundaryFootprint
  obtain ⟨pN, hpN, hpNUnique⟩ := cert.double_fourth.2.2.2
  have hpNS : pN ∈ FootprintVertices (cert.S 1 false) :=
    boundaryFootprint _ hS1ne _ hpN.1
  have hpND : pN ∈ FootprintVertices (cert.P 1 false) :=
    boundaryFootprint _ (LatticeTileGridStructure _
      (cert.parent_lattice 1 false)).1.1 _ hpN.2.1
  have hpNE : pN ∈ FootprintVertices (cert.P 2 true) :=
    boundaryFootprint _ (LatticeTileGridStructure _
      (cert.parent_lattice 2 true)).1.1 _ hpN.2.2
  have hpNendpoint := path_endpoint_of_third
    (cert.modified.tile d0) (cert.modified.tile e0) (cert.S 1 false)
    (cert.modified.rho f4) (cert.modified.rho g4) pN
    (CommonFootprintEdgeVertices (cert.modified.tile d0) (cert.modified.tile e0))
    (cert.modified.tiles_are_disks d0) (cert.modified.tiles_are_disks e0)
    hDEdis hDEpath (JunctionRefinementGeometry.hpNv q cfg C T cert hregular hDtile0 hEtile0
        hde pN hpND hpNE) (JunctionRefinementGeometry.hSNthird q cfg C T cert incident
        hDtile0 hEtile0 hBDseparate hBEseparate hS1ne pN hpNS)
  have hpNalt := endpointAlternative pN hpNendpoint
  have hpNisP4 : pN = p4 := JunctionRefinementGeometry.hpNisP4 q cfg C T cert pN hpNalt
      (JunctionRefinementGeometry.hpNeTranslated q cfg C T cert incident hpJ7c hblockSepDE
          hblockCellDE pN (JunctionRefinementGeometry.nestedStarInsideT q cfg C T cert pN
          (LocalLatticeInterfaceSectors.1 (cert.S 1 false) (cert.P 1 false) (cert.P 2 true)
          pN hS1disk (cert.parent_lattice 1 false) (cert.parent_lattice 2 true)
          cert.double_fourth ⟨⟨hpNS, hpND⟩, hpNE⟩)
          (JunctionRefinementGeometry.nestedCellsInsideT q cfg C T cert)))
  have hxAlt := endpointAlternative x hxendpointDE
  rcases hxAlt with hxP4 | hxJ7
  · subst x
    have htarget : pN ∈ FootprintVertices (cert.S 1 false) ∩
        FootprintVertices (cert.P 1 false) ∩
        FootprintVertices (cert.P 2 true) := ⟨⟨hpNS, hpND⟩, hpNE⟩
    simpa [hpNisP4] using htarget
  · have hxJ7neq := JunctionRefinementGeometry.hxJ7neq q cfg C T cert x
      incident hmissingT f4 g4 hxendpointDE
      hpJ7c hblockSepDE hblockCellDE
    exact (hxJ7neq hxJ7).elim

end JunctionCases

theorem P4590T1JunctionRefinement
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : LatticeTile T) (x : GaussianInt)
    (hx : x ∈ FootprintVertices T) (hxb : x ∉ BoundaryFootprintVertices T) :
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
        x ∈ FootprintVertices (cert.P 0 false) ∧
        x ∈ FootprintVertices (cert.P 1 true)) →
      x ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.S 2 false) ∩ FootprintVertices (cert.P 1 true)) ∧
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
        x ∈ FootprintVertices (cert.P 0 false) ∧
        x ∈ FootprintVertices (cert.P 1 false)) →
      x ∈ FootprintVertices (cert.Q 2 true) ∩
        FootprintVertices (cert.S 1 false) ∩ FootprintVertices (cert.P 1 false)) ∧
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
        x ∈ FootprintVertices (cert.P 1 true) ∧
        x ∈ FootprintVertices (cert.P 2 false)) →
      x ∈ FootprintVertices (cert.Q 1 true) ∩
        FootprintVertices (cert.P 1 true) ∩ FootprintVertices (cert.P 2 false)) ∧
    ((x ∈ FootprintVertices (cert.P 0 false) ∧
        x ∈ FootprintVertices (cert.P 1 false) ∧
        x ∈ FootprintVertices (cert.P 2 true)) →
      x ∈ FootprintVertices (cert.S 1 false) ∩
        FootprintVertices (cert.P 1 false) ∩ FootprintVertices (cert.P 2 true)) := by
-- BODY
  classical
  have hTne : T.cells.Nonempty := (LatticeTileGridStructure T hT).1.1
  have htransZero := JunctionRefinementGeometry.htransZero
  have incident := JunctionRefinementGeometry.incident
  have hmissingT : ∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells :=
    (P4456T2VertexInterior T hTne x hx).2.mp hxb
  have hfourCells := JunctionRefinementGeometry.hfourCells T
          x hmissingT
  have incidentCorner := JunctionRefinementGeometry.incidentCorner
  have incidentSingleton := JunctionRefinementGeometry.incidentSingleton
      (JunctionRefinementGeometry.singletonCorner)
  have precursorIsolationSupported := JunctionRefinementGeometry.precursorIsolationSupported q
      cfg C T cert htransZero
            (JunctionRefinementGeometry.supportedToFootprint q cfg C T cert)
  have path_endpoint_of_third := P4616T1ThirdOwnerPathEndpoint
  obtain ⟨_, _, _, _, _, _, hABO, hseparate⟩ :=
    P4339T1PrecursorSupportGeometry C q cfg T cert
  have hBCseparate : Disjoint (cert.P 0 false).cells
      (cert.P 1 true).cells := hseparate 0 false 1 true (by decide) (by decide)
  have hACseparate : Disjoint (cert.P 0 true).cells
      (cert.P 1 true).cells := hseparate 0 true 1 true (by decide) (by decide)
  let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  have hbc : cert.modified.plane.adjacent b c := by
    exact (cert.modified_adjacency b c).mpr (AllowedSubtileIncidence.BC 0 0)
  have hbcne : b ≠ c := by decide
  have hBCedges := cert.modified.adjacent_has_common_edge b c hbc
  have hregular := (PeriodicTileIntersectionClassification cert.modified).2
  obtain ⟨_, f, g, hfg, hf, hg, hfaces, hBCpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular b c hbcne).1.mpr hBCedges
  have hblocks := BandOrderedGeneralPeriodicBlockCells q cfg C T cert
  have blockSeparation := JunctionRefinementGeometry.blockSeparation q cfg C T cert htransZero
      hblocks
  have tileCellInBlock (label : SixSubtileLabel) (m n : Int) (a : GaussianInt)
      (ha : a ∈ (cert.modified.tile ⟨label, m, n⟩).cells) :
      a ∈ (TileTranslation T
        ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells :=
            JunctionRefinementGeometry.tileCellInBlock q cfg C T cert hblocks label m n a ha
  have hBtile : cert.modified.tile b = cert.P 0 false := JunctionRefinementGeometry.hBtile q cfg
      C T cert htransZero
  have hCtile : cert.modified.tile c = cert.P 1 true := JunctionRefinementGeometry.hCtile q cfg C
      T cert htransZero
  have hBCdis : Disjoint (cert.modified.tile b).cells
      (cert.modified.tile c).cells := by rw [hBtile, hCtile]; exact hBCseparate
  have hthirdABC (hABC : x ∈ FootprintVertices (cert.P 0 true) ∧
      x ∈ FootprintVertices (cert.P 0 false) ∧
      x ∈ FootprintVertices (cert.P 1 true)) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ (cert.P 0 true).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.P 0 false).cells ∧
        LatticeVertexIncidentCell x j ∉ (cert.P 1 true).cells :=
            JunctionRefinementGeometry.hthirdABC q cfg C T cert x htransZero incident
            incidentCorner incidentSingleton hABO hBCseparate hACseparate hABC
  have firstJunction :
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
            x ∈ FootprintVertices (cert.P 0 false) ∧
            x ∈ FootprintVertices (cert.P 1 true)) →
          x ∈ FootprintVertices (cert.Q 1 true) ∩
            FootprintVertices (cert.S 2 false) ∩ FootprintVertices (cert.P 1 true)) :=
                JunctionCases.firstJunction q cfg C T cert x htransZero incident hmissingT
                    path_endpoint_of_third hbc hregular f g hf hg hBCpath blockSeparation
                tileCellInBlock hBtile hCtile hBCdis hthirdABC
  have secondJunction :
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
            x ∈ FootprintVertices (cert.P 0 false) ∧
            x ∈ FootprintVertices (cert.P 1 false)) →
          x ∈ FootprintVertices (cert.Q 2 true) ∩
            FootprintVertices (cert.S 1 false) ∩ FootprintVertices (cert.P 1 false)) :=
                JunctionCases.secondJunction q cfg C T cert x htransZero incident
                hmissingT precursorIsolationSupported path_endpoint_of_third hABO
                hseparate hregular blockSeparation tileCellInBlock
  have thirdJunction :
    ((x ∈ FootprintVertices (cert.P 0 true) ∧
            x ∈ FootprintVertices (cert.P 1 true) ∧
            x ∈ FootprintVertices (cert.P 2 false)) →
          x ∈ FootprintVertices (cert.Q 1 true) ∩
            FootprintVertices (cert.P 1 true) ∩ FootprintVertices (cert.P 2 false)) :=
                JunctionCases.thirdJunction q cfg C T cert x htransZero incident hmissingT
                    path_endpoint_of_third hseparate hACseparate hregular blockSeparation
                tileCellInBlock
  have fourthJunction :
    ((x ∈ FootprintVertices (cert.P 0 false) ∧
            x ∈ FootprintVertices (cert.P 1 false) ∧
            x ∈ FootprintVertices (cert.P 2 true)) →
          x ∈ FootprintVertices (cert.S 1 false) ∩
            FootprintVertices (cert.P 1 false) ∩ FootprintVertices (cert.P 2 true)) :=
                JunctionCases.fourthJunction q cfg C T cert x hx hxb htransZero incident
                hmissingT hfourCells path_endpoint_of_third hseparate hregular blockSeparation
                tileCellInBlock hthirdABC
  exact ⟨firstJunction, secondJunction, thirdJunction, fourthJunction⟩


end ApollonianSuperharmonic

end
