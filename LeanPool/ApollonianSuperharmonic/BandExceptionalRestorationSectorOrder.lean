/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion
public import LeanPool.ApollonianSuperharmonic.TileTouchingDisjoint

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.ExceptionalRestorationSectorData

-- [TABLET NODE: BandExceptionalRestorationSectorOrder]

/-!
# BandExceptionalRestorationSectorOrder

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RestorationSectorGeometry

private theorem tile_from_band :
    (by
      classical
      exact
        ∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U ) := by
  classical
  intro c U hU
  induction hU with
  | line w x hw =>
      intro h
      rcases h with h | h
      · simp at h
      · simp at h
  | unit z x anchor =>
      intro _
      have hgeom := (FordTileGeometry 1 (by norm_num)).1
      have htrans := (TileDiskAreaCovariance (FordTile 1) x).1.mp hgeom
      have hcells : (TileTranslation (FordTile 1) x).cells = ({x} : Finset GaussianInt) := by
        rw [(TileTranslationFormulas (FordTile 1) x).1]
        simp [FordTile, FordCellDomain, GaussianTranslation, Zsqrtd.ext_iff]
      have hcell : (⟨{x}, anchor⟩ : ProtoTile).cells =
          (TileTranslation (FordTile 1) x).cells := by rw [hcells]
      have hobs := ProtoTileObservableExtensionality _ _ hcell (by intro he; simp at he)
      have hre : TileRealization (⟨{x}, anchor⟩ : ProtoTile) =
          TileRealization (TileTranslation (FordTile 1) x) := hobs.2.2.2.1
      change TopologicalDisk (TileRealization (⟨{x}, anchor⟩ : ProtoTile))
      rw [hre]
      exact htrans
  | @decompose r hproper F W hF hcells hfoot hcentroid =>
      intro _
      exact (BandTileSimultaneousInduction r hproper W
        (BandPrototile.decompose hproper hF hcells hfoot hcentroid)).1

private theorem hQ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let Q := cert.Q 1 true
        (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U) → (LatticeTile Q) ) := by
  classical
  intro q cfg C₀ T cert Q tile_from_band
  have hocc := cert.plus_occurrence (1 : Fin 3) true
  have hcurv := (ProperBandCurvatureStructure _ cfg.firstProper).2.1 1
  have hcoord : cfg.firstPredecessor 2 = q 2 := cfg.firstParentTwo
  have hnonzero : (cfg.firstPredecessor 2).1 ≠ 0 := by rw [hcoord]; exact cfg.noLine 2
  have hpos : 0 < (cfg.firstPredecessor 2).1 := lt_of_le_of_ne hcurv (Ne.symm hnonzero)
  exact tile_from_band (cfg.firstPredecessor (1 : Fin 3).succ) Q hocc.1
    (Or.inl (by simpa using hpos))

private theorem hS :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let S := cert.S 2 false
        (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U) → (LatticeTile S) ) := by
  classical
  intro q cfg C₀ T cert S tile_from_band
  have hocc := cert.minus_occurrence (2 : Fin 3) false
  have hcurv := (ProperBandCurvatureStructure _ cfg.firstProper).2.1 2
  have hcoord : cfg.firstPredecessor 3 = q 3 := cfg.firstParentThree
  have hnonzero : (cfg.firstPredecessor 3).1 ≠ 0 := by rw [hcoord]; exact cfg.noLine 3
  have hpos : 0 < (cfg.firstPredecessor 3).1 := lt_of_le_of_ne hcurv (Ne.symm hnonzero)
  exact tile_from_band (cfg.firstPredecessor (2 : Fin 3).succ) S hocc.1
    (Or.inl (by simpa using hpos))

private theorem hR :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let R := cert.Q 2 true
        (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U) → (LatticeTile R) ) := by
  classical
  intro q cfg C₀ T cert R tile_from_band
  have hocc := cert.plus_occurrence (2 : Fin 3) true
  have hcurv := (ProperBandCurvatureStructure _ cfg.firstProper).2.1 2
  have hcoord : cfg.firstPredecessor 3 = q 3 := cfg.firstParentThree
  have hnonzero : (cfg.firstPredecessor 3).1 ≠ 0 := by rw [hcoord]; exact cfg.noLine 3
  have hpos : 0 < (cfg.firstPredecessor 3).1 := lt_of_le_of_ne hcurv (Ne.symm hnonzero)
  exact tile_from_band (cfg.firstPredecessor (2 : Fin 3).succ) R hocc.1
    (Or.inl (by simpa using hpos))

private theorem hV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let V := cert.S 1 false
        (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U) → (LatticeTile V) ) := by
  classical
  intro q cfg C₀ T cert V tile_from_band
  have hocc := cert.minus_occurrence (1 : Fin 3) false
  have hcurv := (ProperBandCurvatureStructure _ cfg.firstProper).2.1 1
  have hcoord : cfg.firstPredecessor 2 = q 2 := cfg.firstParentTwo
  have hnonzero : (cfg.firstPredecessor 2).1 ≠ 0 := by rw [hcoord]; exact cfg.noLine 2
  have hpos : 0 < (cfg.firstPredecessor 2).1 := lt_of_le_of_ne hcurv (Ne.symm hnonzero)
  exact tile_from_band (cfg.firstPredecessor (1 : Fin 3).succ) V hocc.1
    (Or.inl (by simpa using hpos))

private theorem hO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let O := cert.O
        (∀ (c : CircleCoordinates), ∀ (U : ProtoTile), BandPrototile c U → (0 < c.1 ∨
            U.cells.Nonempty) → LatticeTile U) → (O.cells.Nonempty → LatticeTile O) ) := by
  classical
  intro q cfg C₀ T cert O tile_from_band hOne
  have hocc := cert.plus_occurrence (0 : Fin 3) false
  rw [← cert.precursor_eq] at hocc
  exact tile_from_band (cfg.firstPredecessor (0 : Fin 3).succ) O hocc.1 (Or.inr hOne)

private theorem nonempty_cells :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (LatticeTile U) → (U.cells.Nonempty) ) := by
  classical
  intro U hU
  rcases hU with ⟨hhome⟩
  let z : (Metric.closedBall (0 : Real × Real) 1 : Set (Real × Real)) :=
    ⟨0, by simp [Metric.mem_closedBall]⟩
  have hreal : (TileRealization U).Nonempty := ⟨(hhome z).val, (hhome z).property⟩
  by_contra hn
  have he : U.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [TileRealization, he] at hreal


private theorem trzero :
    (by
      classical
      exact
        ∀ (Y : ProtoTile), TileTranslation Y 0 = Y ) := by
  classical
  intro Y
  have hfun : GaussianTranslation 0 = id := by
    funext z
    simp [GaussianTranslation]
  cases Y
  simp [TileTranslation, hfun]

private theorem htileComp :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let O := cert.O
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        let iA : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        cert.modified.tile iA = TileCellComplement A O) ) := by
  classical
  intro q cfg C₀ T cert A O trzero iA
  rw [cert.modified_tile]
  simp [iA, A, O, ModifiedSubtileOccurrenceInterpretation, trzero]

private theorem htileB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let B := cert.P 0 false
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        let iB : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        cert.modified.tile iB = B) ) := by
  classical
  intro q cfg C₀ T cert B trzero iB
  rw [cert.modified_tile]
  simp [iB, B, ModifiedSubtileOccurrenceInterpretation, trzero]

private theorem hcompB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let iA : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let iB : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        (cert.modified.tile iA = TileCellComplement A O) → ((cert.modified.tile iB = B) →
            (Disjoint (TileCellComplement A O).cells B.cells)) ) := by
  classical
  intro q cfg C₀ T cert A B O iA iB htileComp htileB
  apply Finset.disjoint_left.mpr
  intro x hxComp hxB
  have hxA : x ∈ (cert.modified.tile iA).cells := by rw [htileComp]; exact hxComp
  have hxBi : x ∈ (cert.modified.tile iB).cells := by rw [htileB]; exact hxB
  have hxA' : x ∈ (ModifiedSubtileOccurrenceInterpretation cert.P O cert.u cert.v iA).cells := by
    rw [← cert.modified_tile]
    exact hxA
  have hxBi' : x ∈ (ModifiedSubtileOccurrenceInterpretation cert.P O cert.u cert.v iB).cells := by
    rw [← cert.modified_tile]
    exact hxBi
  have hEq := (cert.partition x).unique hxA' hxBi'
  exact (show iA ≠ iB by decide) hEq

private theorem hAC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let C := cert.P 1 true
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        (∀ (i : PeriodicSubtileIndex), ∀ (j : PeriodicSubtileIndex), (i ≠ j) → ((¬ ((i.label = .A
            ∧ j.label = .B ∨ i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second =
            j.second)) → (Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells))) → (Disjoint A.cells
            C.cells)) ) := by
  classical
  intro q cfg C₀ T cert A C trzero indexed_disjoint
  let iA : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let iC : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  have h := indexed_disjoint iA iC (by decide) (by simp [iA, iC])
  simpa [iA, iC, SubtileOccurrenceInterpretation, trzero] using h

private theorem hAD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let D := cert.P 1 false
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        (∀ (i : PeriodicSubtileIndex), ∀ (j : PeriodicSubtileIndex), (i ≠ j) → ((¬ ((i.label = .A
            ∧ j.label = .B ∨ i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second =
            j.second)) → (Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells))) → (Disjoint A.cells
            D.cells)) ) := by
  classical
  intro q cfg C₀ T cert A D trzero indexed_disjoint
  let iA : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let iD : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have h := indexed_disjoint iA iD (by decide) (by simp [iA, iD])
  simpa [iA, iD, SubtileOccurrenceInterpretation, trzero] using h

private theorem hBC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let B := cert.P 0 false
        let C := cert.P 1 true
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        (∀ (i : PeriodicSubtileIndex), ∀ (j : PeriodicSubtileIndex), (i ≠ j) → ((¬ ((i.label = .A
            ∧ j.label = .B ∨ i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second =
            j.second)) → (Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells))) → (Disjoint B.cells
            C.cells)) ) := by
  classical
  intro q cfg C₀ T cert B C trzero indexed_disjoint
  let iB : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let iC : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  have h := indexed_disjoint iB iC (by decide) (by simp [iB, iC])
  simpa [iB, iC, SubtileOccurrenceInterpretation, trzero] using h

private theorem hBD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let B := cert.P 0 false
        let D := cert.P 1 false
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        (∀ (i : PeriodicSubtileIndex), ∀ (j : PeriodicSubtileIndex), (i ≠ j) → ((¬ ((i.label = .A
            ∧ j.label = .B ∨ i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second =
            j.second)) → (Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells))) → (Disjoint B.cells
            D.cells)) ) := by
  classical
  intro q cfg C₀ T cert B D trzero indexed_disjoint
  let iB : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let iD : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have h := indexed_disjoint iB iD (by decide) (by simp [iB, iD])
  simpa [iB, iD, SubtileOccurrenceInterpretation, trzero] using h

private theorem hCD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let C := cert.P 1 true
        let D := cert.P 1 false
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → (
        (∀ (i : PeriodicSubtileIndex), ∀ (j : PeriodicSubtileIndex), (i ≠ j) → ((¬ ((i.label = .A
            ∧ j.label = .B ∨ i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second =
            j.second)) → (Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells))) → (Disjoint C.cells
            D.cells)) ) := by
  classical
  intro q cfg C₀ T cert C D trzero indexed_disjoint
  let iC : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let iD : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have h := indexed_disjoint iC iD (by decide) (by simp [iC, iD])
  simpa [iC, iD, SubtileOccurrenceInterpretation, trzero] using h

private theorem hOC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let C := cert.P 1 true
        let O := cert.O
        (Disjoint A.cells C.cells) → (Disjoint O.cells C.cells) ) := by
  classical
  intro q cfg C₀ T cert A C O hAC
  let seg := cert.exceptionalSegments
  apply Finset.disjoint_left.mpr
  intro x hxO hxC
  exact Finset.disjoint_left.mp hAC (seg.precursor_in_left hxO) hxC

private theorem hOD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let D := cert.P 1 false
        let O := cert.O
        (Disjoint A.cells D.cells) → (Disjoint O.cells D.cells) ) := by
  classical
  intro q cfg C₀ T cert A D O hAD
  let seg := cert.exceptionalSegments
  apply Finset.disjoint_left.mpr
  intro x hxO hxD
  exact Finset.disjoint_left.mp hAD (seg.precursor_in_left hxO) hxD


private abbrev edge_vertex_footprint :=
  BoundaryFootprintInclusion.edgeVertex

private theorem boundary_raw :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
            FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges U) → (∀ (x : GaussianInt), (x ∈ e) → (x ∈ FootprintVertices U))) → (∀
            (U : ProtoTile), (U.cells.Nonempty) → (BoundaryFootprintVertices U ⊆
            FootprintVertices U))) ) := by
  classical
  intro boundary_edge_footprint edge_vertex_footprint U hne x hx
  simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
  obtain ⟨e, he, hxe⟩ := hx
  exact edge_vertex_footprint U e (boundary_edge_footprint U e he) x hxe

private theorem footprint_incident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (∀ (x : GaussianInt), (x ∈ FootprintVertices U) →
            (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells)) ) := by
  classical
  intro U hne x hx
  simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
  rcases hx with ⟨c, hc, h | h | h | h⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h ▸ hc⟩
  · subst x
    exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
  · subst x
    exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
  · refine ⟨2, ?_⟩
    change x - 1 - ⟨0, 1⟩ ∈ U.cells
    rw [h]
    convert hc using 1; ext <;> simp

private theorem boundary_missing_incident :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices U) → (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∉ U.cells) ) := by
  classical
  intro U x hx
  by_cases hne : U.cells.Nonempty
  · simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
    obtain ⟨e, he, hxe⟩ := hx
    rcases he with ⟨z, ⟨rfl, hcross⟩ | ⟨rfl, hcross⟩⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      rcases hcross with ⟨hz, hzi⟩ | ⟨hz, hzi⟩
      · rcases hxe with hxe | hxe
        · subst x
          exact ⟨3, by simpa [LatticeVertexIncidentCell] using hzi⟩
        · subst x
          exact ⟨2, by
            simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using hzi⟩
      · rcases hxe with hxe | hxe
        · subst x
          exact ⟨0, by simpa [LatticeVertexIncidentCell] using hz⟩
        · subst x
          exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      rcases hcross with ⟨hz, hz1⟩ | ⟨hz, hz1⟩
      · rcases hxe with hxe | hxe
        · subst x
          exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz1⟩
        · subst x
          exact ⟨2, by
            simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using hz1⟩
      · rcases hxe with hxe | hxe
        · subst x
          exact ⟨0, by simpa [LatticeVertexIncidentCell] using hz⟩
        · subst x
          exact ⟨3, by
            simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc] using hz⟩
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hne]⟩

private theorem hQO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let O := cert.O
        let Q := cert.Q 1 true
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((TileTouching X Y) → (Disjoint X.cells Y.cells)))) → ((Finset.Nonempty Q.cells) →
            (O.cells.Nonempty → Disjoint Q.cells O.cells)) ) := by
  classical
  intro q cfg C₀ T cert O Q touching_disjoint hQne hOne
  exact (touching_disjoint O Q hOne hQne cert.precursor_first.2.2.1).symm

private theorem hSO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let O := cert.O
        let S := cert.S 2 false
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((TileTouching X Y) → (Disjoint X.cells Y.cells)))) → ((Finset.Nonempty S.cells) →
            (O.cells.Nonempty → Disjoint S.cells O.cells)) ) := by
  classical
  intro q cfg C₀ T cert O S touching_disjoint hSne hOne
  exact touching_disjoint S O hSne hOne cert.precursor_first.2.1

private theorem hRO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let O := cert.O
        let R := cert.Q 2 true
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((TileTouching X Y) → (Disjoint X.cells Y.cells)))) → ((Finset.Nonempty R.cells) →
            (O.cells.Nonempty → Disjoint R.cells O.cells)) ) := by
  classical
  intro q cfg C₀ T cert O R touching_disjoint hRne hOne
  exact (touching_disjoint O R hOne hRne cert.precursor_second.2.2.1).symm

private theorem hVO :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let O := cert.O
        let V := cert.S 1 false
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((TileTouching X Y) → (Disjoint X.cells Y.cells)))) → ((Finset.Nonempty V.cells) →
            (O.cells.Nonempty → Disjoint V.cells O.cells)) ) := by
  classical
  intro q cfg C₀ T cert O V touching_disjoint hVne hOne
  exact touching_disjoint V O hVne hOne cert.precursor_second.2.1

private theorem rho_mem :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (f : PeriodicSubtileFaceIndex), ∀ (k : Fin 3), cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm f) ∈ FootprintVertices
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (SixSubtileFaceVertices f k)) )
            := by
  classical
  intro q cfg C₀ T cert f k
  have h := cert.unmodified.core.rho_common (cert.unmodified.faceEquiv.symm f) k
  rw [cert.unmodified.face_vertices, cert.unmodified.faceEquiv.apply_symm_apply,
    cert.unmodified.tile_eq] at h
  exact h

private theorem hp1C :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let C := cert.P 1 true
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → ((∀ (f : PeriodicSubtileFaceIndex), ∀ (k :
            Fin 3), cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f) ∈
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (SixSubtileFaceVertices f k))) → (
        p1 ∈ FootprintVertices C)) ) := by
  classical
  intro q cfg C₀ T cert C p1 trzero rho_mem
  let f1 : PeriodicSubtileFaceIndex := ⟨.I1, 0, 0⟩
  have h := rho_mem f1 2
  simpa [p1, f1, SixSubtileFaceVertices, SubtileOccurrenceInterpretation, trzero] using h

private theorem hp2D :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let D := cert.P 1 false
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        (∀ (Y : ProtoTile), TileTranslation Y 0 = Y) → ((∀ (f : PeriodicSubtileFaceIndex), ∀ (k :
            Fin 3), cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm f) ∈
            FootprintVertices (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (SixSubtileFaceVertices f k))) → (
        p2 ∈ FootprintVertices D)) ) := by
  classical
  intro q cfg C₀ T cert D p2 trzero rho_mem
  let f2 : PeriodicSubtileFaceIndex := ⟨.I2, 0, 0⟩
  have h := rho_mem f2 2
  simpa [p2, f2, SixSubtileFaceVertices, SubtileOccurrenceInterpretation, trzero] using h

private theorem cutData :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt),
            LatticeTile X → LatticeTile Y → LatticeTile Z → TouchingTriple X Y Z → x ∈
            FootprintVertices X ∩ FootprintVertices Y ∩ FootprintVertices Z → (∀ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈
            Y.cells ∨ LatticeVertexIncidentCell x j ∈ Z.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ Y.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ Z.cells) ∧ ((∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells ∧ LatticeVertexIncidentCell x (j + (2 : Fin
            (4 : ℕ))) ∈ Y.cells) ∨ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ X.cells
            ∧ LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ Z.cells) ∨ ∃ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∈ Y.cells ∧ LatticeVertexIncidentCell x (j + (2 :
            Fin (4 : ℕ))) ∈ Z.cells)) → (
        let O := cert.O
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        let seg := cert.exceptionalSegments
        (LatticeTile Q) → ((LatticeTile S) → ((O.cells.Nonempty → LatticeTile O) →
            ((Finset.Nonempty Q.cells) → ((Finset.Nonempty S.cells) → ((∀ (U : ProtoTile),
            (U.cells.Nonempty) → (BoundaryFootprintVertices U ⊆ FootprintVertices U)) →
            ((O.cells.Nonempty) → ((∀ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∨
            LatticeVertexIncidentCell seg.a j ∈ S.cells ∨ LatticeVertexIncidentCell seg.a j ∈
            O.cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ O.cells) ∧ ((∃ j : Fin
            4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∧ LatticeVertexIncidentCell seg.a (j +
            2) ∈ S.cells) ∨ (∃ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∧
            LatticeVertexIncidentCell seg.a (j + 2) ∈ O.cells) ∨ (∃ j : Fin 4,
            LatticeVertexIncidentCell seg.a j ∈ S.cells ∧ LatticeVertexIncidentCell seg.a (j + 2)
            ∈ O.cells)))))))))) ) := by
  classical
  intro q cfg C₀ T cert three_owner_sectors O Q S seg hQ hS hO hQne hSne boundary_raw hOne
  have hb := (seg.first_cut_unique seg.a).mpr rfl
  have hfQ := boundary_raw Q hQne hb.1
  have hfS := boundary_raw S hSne hb.2.1
  have hfO := boundary_raw O hOne hb.2.2
  have h := three_owner_sectors Q S O seg.a hQ hS (hO hOne)
    cert.precursor_first ⟨⟨hfQ, hfS⟩, hfO⟩
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem cutDataR :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt),
            LatticeTile X → LatticeTile Y → LatticeTile Z → TouchingTriple X Y Z → x ∈
            FootprintVertices X ∩ FootprintVertices Y ∩ FootprintVertices Z → (∀ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈
            Y.cells ∨ LatticeVertexIncidentCell x j ∈ Z.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ Y.cells) ∧ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ Z.cells) ∧ ((∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells ∧ LatticeVertexIncidentCell x (j + (2 : Fin
            (4 : ℕ))) ∈ Y.cells) ∨ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ X.cells
            ∧ LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ Z.cells) ∨ ∃ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∈ Y.cells ∧ LatticeVertexIncidentCell x (j + (2 :
            Fin (4 : ℕ))) ∈ Z.cells)) → (
        let O := cert.O
        let R := cert.Q 2 true
        let V := cert.S 1 false
        let seg := cert.exceptionalSegments
        (LatticeTile R) → ((LatticeTile V) → ((O.cells.Nonempty → LatticeTile O) →
            ((Finset.Nonempty R.cells) → ((Finset.Nonempty V.cells) → ((∀ (U : ProtoTile),
            (U.cells.Nonempty) → (BoundaryFootprintVertices U ⊆ FootprintVertices U)) →
            ((O.cells.Nonempty) → ((∀ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∨
            LatticeVertexIncidentCell seg.b j ∈ V.cells ∨ LatticeVertexIncidentCell seg.b j ∈
            O.cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ O.cells) ∧ ((∃ j : Fin
            4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∧ LatticeVertexIncidentCell seg.b (j +
            2) ∈ V.cells) ∨ (∃ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∧
            LatticeVertexIncidentCell seg.b (j + 2) ∈ O.cells) ∨ (∃ j : Fin 4,
            LatticeVertexIncidentCell seg.b j ∈ V.cells ∧ LatticeVertexIncidentCell seg.b (j + 2)
            ∈ O.cells)))))))))) ) := by
  classical
  intro q cfg C₀ T cert three_owner_sectors O R V seg hR hV hO hRne hVne boundary_raw hOne
  have hb := (seg.second_cut_unique seg.b).mpr rfl
  have hfR := boundary_raw R hRne hb.1
  have hfV := boundary_raw V hVne hb.2.1
  have hfO := boundary_raw O hOne hb.2.2
  have h := three_owner_sectors R V O seg.b hR hV (hO hOne)
    cert.precursor_second ⟨⟨hfR, hfV⟩, hfO⟩
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem cutNoC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let C := cert.P 1 true
        let O := cert.O
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        let seg := cert.exceptionalSegments
        (Disjoint O.cells C.cells) → ((Disjoint Q.cells C.cells) → ((Disjoint S.cells C.cells) →
            (((O.cells.Nonempty) → ((∀ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∨
            LatticeVertexIncidentCell seg.a j ∈ S.cells ∨ LatticeVertexIncidentCell seg.a j ∈
            O.cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ O.cells) ∧ ((∃ j : Fin
            4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∧ LatticeVertexIncidentCell seg.a (j +
            2) ∈ S.cells) ∨ (∃ j : Fin 4, LatticeVertexIncidentCell seg.a j ∈ Q.cells ∧
            LatticeVertexIncidentCell seg.a (j + 2) ∈ O.cells) ∨ (∃ j : Fin 4,
            LatticeVertexIncidentCell seg.a j ∈ S.cells ∧ LatticeVertexIncidentCell seg.a (j + 2)
            ∈ O.cells)))) → ((O.cells.Nonempty) → (∀ (j : Fin 4), LatticeVertexIncidentCell seg.a
            j ∉ C.cells))))) ) := by
  classical
  intro q cfg C₀ T cert C O Q S seg hOC hQC hSC cutData hOne j
  rcases (cutData hOne).1 j with hq | hs | ho
  · exact fun hc => Finset.disjoint_left.mp hQC hq hc
  · exact fun hc => Finset.disjoint_left.mp hSC hs hc
  · exact fun hc => Finset.disjoint_left.mp hOC ho hc

private theorem cutNoD :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let D := cert.P 1 false
        let O := cert.O
        let R := cert.Q 2 true
        let V := cert.S 1 false
        let seg := cert.exceptionalSegments
        (Disjoint O.cells D.cells) → ((Disjoint R.cells D.cells) → ((Disjoint V.cells D.cells) →
            (((O.cells.Nonempty) → ((∀ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∨
            LatticeVertexIncidentCell seg.b j ∈ V.cells ∨ LatticeVertexIncidentCell seg.b j ∈
            O.cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ O.cells) ∧ ((∃ j : Fin
            4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∧ LatticeVertexIncidentCell seg.b (j +
            2) ∈ V.cells) ∨ (∃ j : Fin 4, LatticeVertexIncidentCell seg.b j ∈ R.cells ∧
            LatticeVertexIncidentCell seg.b (j + 2) ∈ O.cells) ∨ (∃ j : Fin 4,
            LatticeVertexIncidentCell seg.b j ∈ V.cells ∧ LatticeVertexIncidentCell seg.b (j + 2)
            ∈ O.cells)))) → ((O.cells.Nonempty) → (∀ (j : Fin 4), LatticeVertexIncidentCell seg.b
            j ∉ D.cells))))) ) := by
  classical
  intro q cfg C₀ T cert D O R V seg hOD hRD hVD cutDataR hOne j
  rcases (cutDataR hOne).1 j with hr | hv | ho
  · exact fun hd => Finset.disjoint_left.mp hRD hr hd
  · exact fun hd => Finset.disjoint_left.mp hVD hv hd
  · exact fun hd => Finset.disjoint_left.mp hOD ho hd

private theorem cuts_ne_marked :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let C := cert.P 1 true
        let D := cert.P 1 false
        let O := cert.O
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        let seg := cert.exceptionalSegments
        (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p1 j ∈ C.cells) → ((∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell p2 j ∈ D.cells) → (((O.cells.Nonempty) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell seg.a j ∉ C.cells)) → (((O.cells.Nonempty) → (∀ (j : Fin
            4), LatticeVertexIncidentCell seg.b j ∉ D.cells)) → ((O.cells.Nonempty) → (seg.a ≠ p1
            ∧ seg.b ≠ p2))))) ) := by
  classical
  intro q cfg C₀ T cert C D O p1 p2 seg hmark1C hmark2D cutNoC cutNoD hOne
  constructor
  · intro heq
    rcases hmark1C with ⟨j, hj⟩
    exact cutNoC hOne j (heq ▸ hj)
  · intro heq
    rcases hmark2D with ⟨j, hj⟩
    exact cutNoD hOne j (heq ▸ hj)


private theorem leftInternal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (x : GaussianInt), LatticeTile X →
            LatticeTile Y → Disjoint X.cells Y.cells → (∃ (e : Finset GaussianInt) (f : Finset
            GaussianInt), e ≠ f ∧ x ∈ e ∧ x ∈ f ∧ e ∈ FootprintEdges X ∩ FootprintEdges Y ∧ f ∈
            FootprintEdges X ∩ FootprintEdges Y) → (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈ Y.cells) ∧
            ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ X.cells ∧
            LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ Y.cells) → (
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let seg := cert.exceptionalSegments
        (LatticeTile Q) → ((LatticeTile S) → ((Disjoint Q.cells S.cells) → ((∀ (l : List
            GaussianInt), ∀ (x : GaussianInt), ∀ (h : GaussianInt), ∀ (t : GaussianInt), l.Nodup
            → l.head? = some h → l.getLast? = some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z post, l
            = pre ++ y :: x :: z :: post) → (∀ (x : GaussianInt), (x ∈ seg.left) → ((x ≠ p1) →
            ((x ≠ seg.a) → ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ Q.cells ∨
            LatticeVertexIncidentCell x j ∈ S.cells) ∧ ∃ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ Q.cells ∧ LatticeVertexIncidentCell x (j + 2) ∈ S.cells)))))))) ) := by
  classical
  intro q cfg C₀ T cert two_owner_sectors Q S p1 seg hQ hS hQSC splitInternal x hx hh ht
  obtain ⟨pre, y, z, post, hlist⟩ :=
    splitInternal seg.left x p1 seg.a seg.left_nodup seg.left_head seg.left_last hx hh ht
  have he₁ := seg.left_edges y x pre (z :: post) hlist
  have he₂ := seg.left_edges x z (pre ++ [y]) post (by
    rw [hlist]
    simp [List.append_assoc])
  have hnod := seg.left_nodup
  rw [hlist] at hnod
  have htail : (y :: x :: z :: post).Nodup := (List.nodup_append.mp hnod).2.1
  have hnot : y ∉ x :: z :: post := (List.nodup_cons.mp htail).1
  have hyx : y ≠ x := by intro h; exact hnot (by simp [h])
  have hyz : y ≠ z := by intro h; exact hnot (by simp [h])
  have hne : ({y, x} : Finset GaussianInt) ≠ {x, z} := by
    intro h
    have hy' : y = x ∨ y = z := by
      have : y ∈ ({x, z} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hy' with h' | h'
    · exact hyx h'
    · exact hyz h'
  have hsectors := two_owner_sectors Q S x hQ hS hQSC
    ⟨{y, x}, {x, z}, hne, by simp, by simp, he₁, he₂⟩
  exact hsectors

private theorem rightInternal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (x : GaussianInt), LatticeTile X →
            LatticeTile Y → Disjoint X.cells Y.cells → (∃ (e : Finset GaussianInt) (f : Finset
            GaussianInt), e ≠ f ∧ x ∈ e ∧ x ∈ f ∧ e ∈ FootprintEdges X ∩ FootprintEdges Y ∧ f ∈
            FootprintEdges X ∩ FootprintEdges Y) → (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈ Y.cells) ∧
            ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ X.cells ∧
            LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ Y.cells) → (
        let R := cert.Q 2 true
        let V := cert.S 1 false
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        let seg := cert.exceptionalSegments
        (LatticeTile R) → ((LatticeTile V) → ((Disjoint R.cells V.cells) → ((∀ (l : List
            GaussianInt), ∀ (x : GaussianInt), ∀ (h : GaussianInt), ∀ (t : GaussianInt), l.Nodup
            → l.head? = some h → l.getLast? = some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z post, l
            = pre ++ y :: x :: z :: post) → (∀ (x : GaussianInt), (x ∈ seg.right) → ((x ≠ seg.b)
            → ((x ≠ p2) → ((∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ R.cells ∨
            LatticeVertexIncidentCell x j ∈ V.cells) ∧ ∃ j : Fin 4, LatticeVertexIncidentCell x j
            ∈ R.cells ∧ LatticeVertexIncidentCell x (j + 2) ∈ V.cells)))))))) ) := by
  classical
  intro q cfg C₀ T cert two_owner_sectors R V p2 seg hR hV hRVD splitInternal x hx hh ht
  obtain ⟨pre, y, z, post, hlist⟩ :=
    splitInternal seg.right x seg.b p2 seg.right_nodup seg.right_head seg.right_last hx hh ht
  have he₁ := seg.right_edges y x pre (z :: post) hlist
  have he₂ := seg.right_edges x z (pre ++ [y]) post (by
    rw [hlist]
    simp [List.append_assoc])
  have hnod := seg.right_nodup
  rw [hlist] at hnod
  have htail : (y :: x :: z :: post).Nodup := (List.nodup_append.mp hnod).2.1
  have hnot : y ∉ x :: z :: post := (List.nodup_cons.mp htail).1
  have hyx : y ≠ x := by intro h; exact hnot (by simp [h])
  have hyz : y ≠ z := by intro h; exact hnot (by simp [h])
  have hne : ({y, x} : Finset GaussianInt) ≠ {x, z} := by
    intro h
    have hy' : y = x ∨ y = z := by
      have : y ∈ ({x, z} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hy' with h' | h'
    · exact hyx h'
    · exact hyz h'
  exact two_owner_sectors R V x hR hV hRVD
    ⟨{y, x}, {x, z}, hne, by simp, by simp, he₁, he₂⟩

private theorem middleInternal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (x : GaussianInt), LatticeTile X →
            LatticeTile Y → Disjoint X.cells Y.cells → (∃ (e : Finset GaussianInt) (f : Finset
            GaussianInt), e ≠ f ∧ x ∈ e ∧ x ∈ f ∧ e ∈ FootprintEdges X ∩ FootprintEdges Y ∧ f ∈
            FootprintEdges X ∩ FootprintEdges Y) → (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈ Y.cells) ∧
            ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ X.cells ∧
            LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ Y.cells) → (
        let A := cert.P 0 true
        let O := cert.O
        let seg := cert.exceptionalSegments
        (O.cells.Nonempty → LatticeTile O) → ((∀ (l : List GaussianInt), ∀ (x : GaussianInt), ∀
            (h : GaussianInt), ∀ (t : GaussianInt), l.Nodup → l.head? = some h → l.getLast? =
            some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z post, l = pre ++ y :: x :: z :: post) → (∀
            (x : GaussianInt), (x ∈ seg.middle) → ((x ≠ seg.a) → ((x ≠ seg.b) → ((∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (TileCellComplement A O).cells ∨
            LatticeVertexIncidentCell x j ∈ O.cells) ∧ O.cells.Nonempty)))))) ) := by
  classical
  intro q cfg C₀ T cert two_owner_sectors A O seg hO splitInternal x hx ha hb
  obtain ⟨pre, y, z, post, hlist⟩ :=
    splitInternal seg.middle x seg.a seg.b seg.middle_nodup
      seg.middle_head seg.middle_last hx ha hb
  have he := seg.middle_edges y x pre (z :: post) hlist
  have he₂ := seg.middle_edges x z (pre ++ [y]) post (by
    rw [hlist]
    simp [List.append_assoc])
  have hnod := seg.middle_nodup
  rw [hlist] at hnod
  have htail : (y :: x :: z :: post).Nodup := (List.nodup_append.mp hnod).2.1
  have hnot : y ∉ x :: z :: post := (List.nodup_cons.mp htail).1
  have hyx : y ≠ x := by intro h; exact hnot (by simp [h])
  have hyz : y ≠ z := by intro h; exact hnot (by simp [h])
  have hne : ({y, x} : Finset GaussianInt) ≠ {x, z} := by
    intro h
    have hy' : y = x ∨ y = z := by
      have : y ∈ ({x, z} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hy' with h' | h'
    · exact hyx h'
    · exact hyz h'
  have hOne : O.cells.Nonempty := by
    by_contra hn
    rcases he.2 with ⟨c, hc, _⟩
    exact hn ⟨c, hc⟩
  have hcomp : Disjoint (TileCellComplement A O).cells O.cells := by
    apply Finset.disjoint_left.mpr
    intro c hc hco
    exact (Finset.mem_sdiff.mp hc).2 hco
  have hsec := two_owner_sectors (TileCellComplement A O) O x
    cert.precursor_complement_lattice.1 (hO hOne) hcomp
    ⟨{y, x}, {x, z}, hne, by simp, by simp, he, he₂⟩
  exact ⟨hsec.1, hOne⟩

private theorem middleRestored :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let O := cert.O
        let seg := cert.exceptionalSegments
        (∀ (x : GaussianInt), (x ∈ seg.middle) → ((x ≠ seg.a) → ((x ≠ seg.b) → ((∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ (TileCellComplement A O).cells ∨
            LatticeVertexIncidentCell x j ∈ O.cells) ∧ O.cells.Nonempty)))) → (∀ (x :
            GaussianInt), (x ∈ seg.middle) → ((x ≠ seg.a) → ((x ≠ seg.b) → (∀ (j : Fin 4),
            LatticeVertexIncidentCell x j ∈ A.cells)))) ) := by
  classical
  intro q cfg C₀ T cert A O seg middleInternal x hx ha hb j
  rcases (middleInternal x hx ha hb).1 j with hcomp | hOcell
  · exact (Finset.mem_sdiff.mp hcomp).1
  · exact seg.precursor_in_left hOcell

private theorem middleWalkEdge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let seg := cert.exceptionalSegments
        (∀ (l : List GaussianInt), ∀ (x : GaussianInt), ∀ (h : GaussianInt), ∀ (t : GaussianInt),
            l.Nodup → l.head? = some h → l.getLast? = some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z
            post, l = pre ++ y :: x :: z :: post) → (∀ (x : GaussianInt), (x ∈ seg.middle) → ((x
            ≠ seg.a) → ((x ≠ seg.b) → (∃ e : Finset GaussianInt, x ∈ e ∧ e ∈ FootprintEdges
            (TileCellComplement A O) ∩ FootprintEdges B ∧ (TileCellComplement A
            O).cells.Nonempty)))) ) := by
  classical
  intro q cfg C₀ T cert A B O seg splitInternal x hx ha hb
  obtain ⟨pre, y, z, post, hlist⟩ :=
    splitInternal seg.middle x seg.a seg.b seg.middle_nodup
      seg.middle_head seg.middle_last hx ha hb
  have heMid := seg.middle_edges y x pre (z :: post) hlist
  have hDne : (TileCellComplement A O).cells.Nonempty := by
    rcases heMid.1 with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  have hwalk : ∃ wl wr, seg.walk = wl ++ y :: x :: wr := by
    cases pre with
    | nil =>
      have hy : y = seg.a := by
        have h := seg.middle_head
        rw [hlist] at h
        simpa using h
      have hleft := (List.getLast?_eq_some_iff.mp seg.left_last)
      rcases hleft with ⟨lp, hleft⟩
      have htail : seg.middle.tail = x :: z :: post := by
        simp [hlist, hy]
      refine ⟨lp, z :: post ++ seg.right.tail, ?_⟩
      rw [seg.walk_order, hleft, htail, hy]
      simp [List.append_assoc]
    | cons d ds =>
      have htail : seg.middle.tail = ds ++ y :: x :: z :: post := by
        simp [hlist]
      refine ⟨seg.left ++ ds, z :: post ++ seg.right.tail, ?_⟩
      rw [seg.walk_order, htail]
      simp [List.append_assoc]
  obtain ⟨wl, wr, hwalk⟩ := hwalk
  have heWalk := seg.walk_edges y x wl wr hwalk
  exact ⟨{y, x}, by simp, heWalk, hDne⟩

end RestorationSectorGeometry

namespace RestorationSectorCertificate

private theorem sectorOrderCertificate :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let C := cert.P 1 true
        let D := cert.P 1 false
        let O := cert.O
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        let R := cert.Q 2 true
        let V := cert.S 1 false
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        (Finset.Nonempty B.cells) → ((Finset.Nonempty Q.cells) → ((Finset.Nonempty S.cells) →
            ((Finset.Nonempty R.cells) → ((Finset.Nonempty V.cells) → ((Disjoint Q.cells S.cells)
            → ((Disjoint R.cells V.cells) → ((Disjoint (TileCellComplement A O).cells B.cells) →
            ((Disjoint Q.cells C.cells) → ((Disjoint S.cells C.cells) → ((Disjoint R.cells
            D.cells) → ((Disjoint V.cells D.cells) → ((∀ (U : ProtoTile), Finset.Nonempty U.cells
            → ∀ x ∈ FootprintVertices U, ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            U.cells) → ((∀ (U : ProtoTile), ∀ x ∈ BoundaryFootprintVertices U, ∃ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell x j ∉ U.cells) → ((Finset.Nonempty cert.O.cells →
            Disjoint (cert.Q (1 : Fin (3 : ℕ)) true).cells cert.O.cells) → ((Finset.Nonempty
            cert.O.cells → Disjoint (cert.Q (2 : Fin (3 : ℕ)) true).cells cert.O.cells) →
            ((Finset.Nonempty cert.O.cells → (∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∨
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.S (2 : Fin (3 : ℕ))
            false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈
            cert.O.cells) ∧ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ cert.O.cells) ∧ ((∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q (1 : Fin (3 : ℕ))
            true).cells ∧ LatticeVertexIncidentCell cert.exceptionalSegments.a (j + (2 : Fin (4
            : ℕ))) ∈ (cert.S (2 : Fin (3 : ℕ)) false).cells) ∨ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.a j ∈ (cert.Q (1 : Fin (3 : ℕ))
            true).cells ∧ LatticeVertexIncidentCell cert.exceptionalSegments.a (j + (2 : Fin (4
            : ℕ))) ∈ cert.O.cells) ∨ ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∈ (cert.S (2 : Fin (3 : ℕ)) false).cells ∧
            LatticeVertexIncidentCell cert.exceptionalSegments.a (j + (2 : Fin (4 : ℕ))) ∈
            cert.O.cells)) → ((Finset.Nonempty cert.O.cells → (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q (2 : Fin (3 : ℕ))
            true).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.S (1 :
            Fin (3 : ℕ)) false).cells ∨ LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈
            cert.O.cells) ∧ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ cert.O.cells) ∧ ((∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q (2 : Fin (3 : ℕ))
            true).cells ∧ LatticeVertexIncidentCell cert.exceptionalSegments.b (j + (2 : Fin (4
            : ℕ))) ∈ (cert.S (1 : Fin (3 : ℕ)) false).cells) ∨ (∃ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell cert.exceptionalSegments.b j ∈ (cert.Q (2 : Fin (3 : ℕ))
            true).cells ∧ LatticeVertexIncidentCell cert.exceptionalSegments.b (j + (2 : Fin (4
            : ℕ))) ∈ cert.O.cells) ∨ ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∈ (cert.S (1 : Fin (3 : ℕ)) false).cells ∧
            LatticeVertexIncidentCell cert.exceptionalSegments.b (j + (2 : Fin (4 : ℕ))) ∈
            cert.O.cells)) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p1 j ∈ Q.cells ∨
            LatticeVertexIncidentCell p1 j ∈ S.cells ∨ LatticeVertexIncidentCell p1 j ∈ C.cells)
            → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p1 j ∈ C.cells) → (((∃ (j : Fin (4
            : ℕ)), LatticeVertexIncidentCell p1 j ∈ Q.cells ∧ LatticeVertexIncidentCell p1 (j +
            (2 : Fin (4 : ℕ))) ∈ S.cells) ∨ (∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p1 j
            ∈ Q.cells ∧ LatticeVertexIncidentCell p1 (j + (2 : Fin (4 : ℕ))) ∈ C.cells) ∨ ∃ (j :
            Fin (4 : ℕ)), LatticeVertexIncidentCell p1 j ∈ S.cells ∧ LatticeVertexIncidentCell p1
            (j + (2 : Fin (4 : ℕ))) ∈ C.cells) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            p2 j ∈ R.cells ∨ LatticeVertexIncidentCell p2 j ∈ V.cells ∨ LatticeVertexIncidentCell
            p2 j ∈ D.cells) → ((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p2 j ∈ D.cells) →
            (((∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p2 j ∈ R.cells ∧
            LatticeVertexIncidentCell p2 (j + (2 : Fin (4 : ℕ))) ∈ V.cells) ∨ (∃ (j : Fin (4 :
            ℕ)), LatticeVertexIncidentCell p2 j ∈ R.cells ∧ LatticeVertexIncidentCell p2 (j + (2
            : Fin (4 : ℕ))) ∈ D.cells) ∨ ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p2 j ∈
            V.cells ∧ LatticeVertexIncidentCell p2 (j + (2 : Fin (4 : ℕ))) ∈ D.cells) →
            ((Finset.Nonempty cert.O.cells → ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.a j ∉ (cert.P (1 : Fin (3 : ℕ)) true).cells) →
            ((Finset.Nonempty cert.O.cells → ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell
            cert.exceptionalSegments.b j ∉ (cert.P (1 : Fin (3 : ℕ)) false).cells) →
            ((Finset.Nonempty cert.O.cells → cert.exceptionalSegments.a ≠
            cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex
            → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex)) ∧ cert.exceptionalSegments.b ≠ cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) → ((∀ x ∈ cert.exceptionalSegments.left, x ≠
            cert.unmodified.core.rho ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex
            → cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex)) → x ≠ cert.exceptionalSegments.a → (∀ (j : Fin (4 : ℕ)),
            LatticeVertexIncidentCell x j ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∨
            LatticeVertexIncidentCell x j ∈ (cert.S (2 : Fin (3 : ℕ)) false).cells) ∧ ∃ (j : Fin
            (4 : ℕ)), LatticeVertexIncidentCell x j ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∧
            LatticeVertexIncidentCell x (j + (2 : Fin (4 : ℕ))) ∈ (cert.S (2 : Fin (3 : ℕ))
            false).cells) → ((∀ x ∈ cert.exceptionalSegments.right, x ≠
            cert.exceptionalSegments.b → x ≠ cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex)) → (∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            (cert.Q (2 : Fin (3 : ℕ)) true).cells ∨ LatticeVertexIncidentCell x j ∈ (cert.S (1 :
            Fin (3 : ℕ)) false).cells) ∧ ∃ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            (cert.Q (2 : Fin (3 : ℕ)) true).cells ∧ LatticeVertexIncidentCell x (j + (2 : Fin (4
            : ℕ))) ∈ (cert.S (1 : Fin (3 : ℕ)) false).cells) → ((∀ x ∈
            cert.exceptionalSegments.middle, x ≠ cert.exceptionalSegments.a → x ≠
            cert.exceptionalSegments.b → ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈
            (cert.P (0 : Fin (3 : ℕ)) true).cells) → ((∀ x ∈ cert.exceptionalSegments.middle, x
            ≠ cert.exceptionalSegments.a → x ≠ cert.exceptionalSegments.b → ∃ (e : Finset
            GaussianInt), x ∈ e ∧ e ∈ FootprintEdges (TileCellComplement (cert.P (0 : Fin (3 :
            ℕ)) true) cert.O) ∩ FootprintEdges (cert.P (0 : Fin (3 : ℕ)) false) ∧ Finset.Nonempty
            (TileCellComplement (cert.P (0 : Fin (3 : ℕ)) true) cert.O).cells) →
            (ExceptionalRestorationSectorData (cert.P 0 true) (cert.P 0 false) cert.O (cert.Q 1
            true) (cert.S 2 false) (cert.Q 2 true) (cert.S 1 false) (cert.P 1 true) (cert.P 1
            false) (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩))
            cert.exceptionalSegments))))))))))))))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert A B C D O Q S R V p1 p2 hBne hQne hSne hRne hVne hQSC hRVD hcompB hQC hSC
      hRD hVD footprint_incident boundary_missing_incident hQO hRO cutData cutDataR hmark1cover
      hmark1C hmark1opp hmark2cover hmark2D hmark2opp cutNoC cutNoD cuts_ne_marked leftInternal
      rightInternal middleRestored middleWalkEdge
  let seg := cert.exceptionalSegments
  refine {
    left_opposite := by
      intro x hx guard hNoC hNoO
      by_cases hp : x = p1
      · subst x
        exact (hNoC hmark1C.choose hmark1C.choose_spec).elim
      by_cases ha : x = seg.a
      · subst x
        rcases guard with hOne | hne
        · exact (hNoO (cutData hOne).2.1.choose
            (cutData hOne).2.1.choose_spec).elim
        · exact (hne rfl).elim
      · exact (leftInternal x hx hp ha).2
    right_opposite := by
      intro x hx guard hNoD hNoO
      by_cases hp : x = p2
      · subst x
        exact (hNoD hmark2D.choose hmark2D.choose_spec).elim
      by_cases hb : x = seg.b
      · subst x
        rcases guard with hOne | hne
        · exact (hNoO (cutDataR hOne).2.1.choose
            (cutDataR hOne).2.1.choose_spec).elim
        · exact (hne rfl).elim
      · exact (rightInternal x hx hb hp).2
    left_owners := by
      intro x hx guard j
      by_cases hp : x = p1
      · subst x
        rcases hmark1cover j with hQcell | hScell | hCcell
        · exact Or.inl hQcell
        · exact Or.inr (Or.inl hScell)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, hCcell⟩))
      by_cases ha : x = seg.a
      · subst x
        rcases guard with hOne | hne
        · rcases (cutData hOne).1 j with hQcell | hScell | hOcell
          · exact Or.inl hQcell
          · exact Or.inr (Or.inl hScell)
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, hOcell⟩))
        · exact (hne rfl).elim
      · rcases (leftInternal x hx hp ha).1 j with hQcell | hScell
        · exact Or.inl hQcell
        · exact Or.inr (Or.inl hScell)
    right_owners := by
      intro x hx guard j
      by_cases hp : x = p2
      · subst x
        rcases hmark2cover j with hRcell | hVcell | hDcell
        · exact Or.inl hRcell
        · exact Or.inr (Or.inl hVcell)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, hDcell⟩))
      by_cases hb : x = seg.b
      · subst x
        rcases guard with hOne | hne
        · rcases (cutDataR hOne).1 j with hRcell | hVcell | hOcell
          · exact Or.inl hRcell
          · exact Or.inr (Or.inl hVcell)
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, hOcell⟩))
        · exact (hne rfl).elim
      · rcases (rightInternal x hx hb hp).1 j with hRcell | hVcell
        · exact Or.inl hRcell
        · exact Or.inr (Or.inl hVcell)
    left_companion := by
      intro x hx guard
      constructor
      · rintro ⟨j, hc⟩
        by_contra hp
        by_cases ha : x = seg.a
        · subst x
          rcases guard with hOne | hne
          · exact cutNoC hOne j hc
          · exact hne rfl
        · rcases (leftInternal x hx hp ha).1 j with hq | hs
          · exact Finset.disjoint_left.mp hQC hq hc
          · exact Finset.disjoint_left.mp hSC hs hc
      · intro hp
        subst x
        exact hmark1C
    right_companion := by
      intro x hx guard
      constructor
      · rintro ⟨j, hd⟩
        by_contra hp
        by_cases hb : x = seg.b
        · subst x
          rcases guard with hOne | hne
          · exact cutNoD hOne j hd
          · exact hne rfl
        · rcases (rightInternal x hx hb hp).1 j with hr | hv
          · exact Finset.disjoint_left.mp hRD hr hd
          · exact Finset.disjoint_left.mp hVD hv hd
      · intro hp
        subst x
        exact hmark2D
    positive_left_precursor := by
      intro hOne x hx
      constructor
      · intro hOinc
        have hQS := seg.left_vertices x hx
        have hQinc := footprint_incident Q hQne x hQS.1
        have hSinc := footprint_incident S hSne x hQS.2
        have hQmissS : ∃ j, LatticeVertexIncidentCell x j ∉ Q.cells :=
          ⟨hSinc.choose, fun hq =>
            Finset.disjoint_left.mp hQSC hq hSinc.choose_spec⟩
        have hSmissQ : ∃ j, LatticeVertexIncidentCell x j ∉ S.cells :=
          ⟨hQinc.choose, fun hs =>
            Finset.disjoint_left.mp hQSC hQinc.choose_spec hs⟩
        have hOmissQ : ∃ j, LatticeVertexIncidentCell x j ∉ Q.cells :=
          ⟨hOinc.choose, fun hq =>
            Finset.disjoint_left.mp (hQO hOne) hq hOinc.choose_spec⟩
        have hbQ := P3161T2IncidentBoundary Q x hQinc hQmissS
        have hbS := P3161T2IncidentBoundary S x hSinc hSmissQ
        have hOmissO : ∃ j, LatticeVertexIncidentCell x j ∉ O.cells :=
          ⟨hQinc.choose, fun ho =>
            Finset.disjoint_left.mp (hQO hOne) hQinc.choose_spec ho⟩
        have hbO := P3161T2IncidentBoundary O x hOinc hOmissO
        exact (seg.first_cut_unique x).mp ⟨hbQ, hbS, hbO⟩
      · intro hxa
        subst x
        exact (cutData hOne).2.1
    positive_right_precursor := by
      intro hOne x hx
      constructor
      · intro hOinc
        have hRV := seg.right_vertices x hx
        have hRinc := footprint_incident R hRne x hRV.1
        have hVinc := footprint_incident V hVne x hRV.2
        have hRmissV : ∃ j, LatticeVertexIncidentCell x j ∉ R.cells :=
          ⟨hVinc.choose, fun hr =>
            Finset.disjoint_left.mp hRVD hr hVinc.choose_spec⟩
        have hVmissR : ∃ j, LatticeVertexIncidentCell x j ∉ V.cells :=
          ⟨hRinc.choose, fun hv =>
            Finset.disjoint_left.mp hRVD hRinc.choose_spec hv⟩
        have hOmissR : ∃ j, LatticeVertexIncidentCell x j ∉ R.cells :=
          ⟨hOinc.choose, fun hr =>
            Finset.disjoint_left.mp (hRO hOne) hr hOinc.choose_spec⟩
        have hbR := P3161T2IncidentBoundary R x hRinc hRmissV
        have hbV := P3161T2IncidentBoundary V x hVinc hVmissR
        have hOmissO : ∃ j, LatticeVertexIncidentCell x j ∉ O.cells :=
          ⟨hRinc.choose, fun ho =>
            Finset.disjoint_left.mp (hRO hOne) hRinc.choose_spec ho⟩
        have hbO := P3161T2IncidentBoundary O x hOinc hOmissO
        exact (seg.second_cut_unique x).mp ⟨hbR, hbV, hbO⟩
      · intro hxb
        subst x
        exact (cutDataR hOne).2.1
    positive_cut_separation := cuts_ne_marked
    positive_first_cut_no_companion := fun h j => cutNoC h j
    positive_second_cut_no_companion := fun h j => cutNoD h j
    first_marked_companion := hmark1C
    second_marked_companion := hmark2D
    first_marked_opposite := hmark1opp
    second_marked_opposite := hmark2opp
    positive_first_cut_precursor := fun h => (cutData h).2.1
    positive_second_cut_precursor := fun h => (cutDataR h).2.1
    positive_first_cut_opposite := fun h => (cutData h).2.2
    positive_second_cut_opposite := fun h => (cutDataR h).2.2
    empty_cut := seg.empty_cut
    proper_middle_modified_boundary := by
      intro x hx ha hb
      obtain ⟨e, hxe, he, hDne⟩ := middleWalkEdge x hx ha hb
      rw [CellDisjointCommonEdgesBoundary (TileCellComplement A O) B hcompB] at he
      have hDne' : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty := by
        simpa [A, O] using hDne
      have hBne' : (cert.P 0 false).cells.Nonempty := by simpa [B] using hBne
      constructor
      · simp only [BoundaryFootprintVertices, ite_eq_left hDne', Set.mem_ofPred_eq]
        exact ⟨e, he.1, hxe⟩
      · simp only [BoundaryFootprintVertices, ite_eq_left hBne', Set.mem_ofPred_eq]
        exact ⟨e, he.2, hxe⟩
    proper_middle_restored_left := by
      intro x hx ha hb j
      exact middleRestored x hx ha hb j
    proper_middle_not_original_common := by
      intro x hx ha hb hxAB
      have hmiss := boundary_missing_incident A x hxAB.1
      exact hmiss.choose_spec (middleRestored x hx ha hb hmiss.choose) }

end RestorationSectorCertificate

theorem BandExceptionalRestorationSectorOrder
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    ExceptionalRestorationSectorData
      (cert.P 0 true) (cert.P 0 false) cert.O
      (cert.Q 1 true) (cert.S 2 false)
      (cert.Q 2 true) (cert.S 1 false)
      (cert.P 1 true) (cert.P 1 false)
      (cert.unmodified.core.rho
        (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
      (cert.unmodified.core.rho
        (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩))
      cert.exceptionalSegments := by
-- BODY
  classical
  obtain ⟨three_owner_sectors, two_owner_sectors⟩ :=
    LocalLatticeInterfaceSectors
  let A := cert.P 0 true
  let B := cert.P 0 false
  let C := cert.P 1 true
  let D := cert.P 1 false
  let O := cert.O
  let Q := cert.Q 1 true
  let S := cert.S 2 false
  let R := cert.Q 2 true
  let V := cert.S 1 false
  let p1 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
  let p2 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
  let seg := cert.exceptionalSegments
  have tile_from_band := RestorationSectorGeometry.tile_from_band
  have hQ := RestorationSectorGeometry.hQ q cfg C₀ T cert tile_from_band
  have hS := RestorationSectorGeometry.hS q cfg C₀ T cert tile_from_band
  have hR := RestorationSectorGeometry.hR q cfg C₀ T cert tile_from_band
  have hV := RestorationSectorGeometry.hV q cfg C₀ T cert tile_from_band
  have hO := RestorationSectorGeometry.hO q cfg C₀ T cert
      tile_from_band
  have nonempty_cells := RestorationSectorGeometry.nonempty_cells
  have touching_disjoint := TileTouchingDisjoint.cells
  have hA : LatticeTile A := cert.parent_lattice 0 true
  have hB : LatticeTile B := cert.parent_lattice 0 false
  have hCparent : LatticeTile C := cert.parent_lattice 1 true
  have hDparent : LatticeTile D := cert.parent_lattice 1 false
  have hAne := nonempty_cells A hA
  have hBne := nonempty_cells B hB
  have hCne := nonempty_cells C hCparent
  have hDne := nonempty_cells D hDparent
  have hQne := nonempty_cells Q hQ
  have hSne := nonempty_cells S hS
  have hRne := nonempty_cells R hR
  have hVne := nonempty_cells V hV
  have hQSC : Disjoint Q.cells S.cells :=
    touching_disjoint Q S hQne hSne cert.double_first.1
  have hRVD : Disjoint R.cells V.cells :=
    touching_disjoint R V hRne hVne cert.double_second.1
  have trzero := RestorationSectorGeometry.trzero
  have hsep := BandOriginalPairSeparation cert.P O cert.u cert.v
    seg.precursor_in_left seg.precursor_in_right cert.partition
  let iA : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let iB : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let iC : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let iD : PeriodicSubtileIndex := ⟨.D, 0, 0⟩
  have hcompB : Disjoint (TileCellComplement A O).cells B.cells :=
      RestorationSectorGeometry.hcompB q cfg C₀ T cert (RestorationSectorGeometry.htileComp q cfg
          C₀ T cert trzero) (RestorationSectorGeometry.htileB q cfg C₀ T cert trzero)
  have indexed_disjoint (i j : PeriodicSubtileIndex) (hij : i ≠ j)
      (hlabels : ¬ ((i.label = .A ∧ j.label = .B ∨
        i.label = .B ∧ j.label = .A) ∧ i.first = j.first ∧ i.second = j.second)) :
      Disjoint (SubtileOccurrenceInterpretation cert.P cert.u cert.v i).cells
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v j).cells := hsep.2 i j hij hlabels
  have hBC := RestorationSectorGeometry.hBC q cfg C₀ T cert trzero
      indexed_disjoint
  have hBD := RestorationSectorGeometry.hBD q cfg C₀ T cert trzero
      indexed_disjoint
  have hCD := RestorationSectorGeometry.hCD q cfg C₀ T cert trzero
      indexed_disjoint
  have hOC := RestorationSectorGeometry.hOC q cfg C₀ T cert (RestorationSectorGeometry.hAC q cfg
      C₀ T cert trzero indexed_disjoint)
  have hOD := RestorationSectorGeometry.hOD q cfg C₀ T cert (RestorationSectorGeometry.hAD q cfg
      C₀ T cert trzero indexed_disjoint)
  have hQC : Disjoint Q.cells C.cells :=
    (touching_disjoint C Q hCne hQne cert.double_first.2.2.1).symm
  have hSC : Disjoint S.cells C.cells :=
    touching_disjoint S C hSne hCne cert.double_first.2.1
  have hRD : Disjoint R.cells D.cells :=
    (touching_disjoint D R hDne hRne cert.double_second.2.2.1).symm
  have hVD : Disjoint V.cells D.cells :=
    touching_disjoint V D hVne hDne cert.double_second.2.1
  have boundary_raw := RestorationSectorGeometry.boundary_raw
      (BoundaryFootprintInclusion.boundaryEdge)
      (RestorationSectorGeometry.edge_vertex_footprint)
  have footprint_incident := RestorationSectorGeometry.footprint_incident
  have boundary_missing_incident := RestorationSectorGeometry.boundary_missing_incident
  have hQO := RestorationSectorGeometry.hQO q cfg
      C₀ T cert touching_disjoint hQne
  have hSO := RestorationSectorGeometry.hSO q cfg
      C₀ T cert touching_disjoint hSne
  have hRO := RestorationSectorGeometry.hRO q cfg
      C₀ T cert touching_disjoint hRne
  have hVO := RestorationSectorGeometry.hVO q cfg
      C₀ T cert touching_disjoint hVne
  have rho_mem := RestorationSectorGeometry.rho_mem q cfg C₀ T cert
  let f1 : PeriodicSubtileFaceIndex := ⟨.I1, 0, 0⟩
  let f2 : PeriodicSubtileFaceIndex := ⟨.I2, 0, 0⟩
  have hp1QS : p1 ∈ FootprintVertices Q ∩ FootprintVertices S := by
    exact cert.inner_first
  have hp2RV : p2 ∈ FootprintVertices R ∩ FootprintVertices V := by
    exact cert.inner_second
  have cutData := RestorationSectorGeometry.cutData q cfg C₀ T cert three_owner_sectors hQ hS hO
      hQne hSne boundary_raw
  have cutDataR := RestorationSectorGeometry.cutDataR q cfg C₀ T cert three_owner_sectors hR hV
      hO hRne hVne boundary_raw
  have hmark1 := three_owner_sectors Q S C p1 hQ hS hCparent
    cert.double_first ⟨hp1QS, (RestorationSectorGeometry.hp1C q cfg C₀ T cert trzero rho_mem)⟩
  have hmark2 := three_owner_sectors R V D p2 hR hV hDparent
    cert.double_second ⟨hp2RV, (RestorationSectorGeometry.hp2D q cfg C₀ T cert trzero rho_mem)⟩
  rcases hmark1 with ⟨hmark1cover, hmark1Q, hmark1S, hmark1C, hmark1opp⟩
  rcases hmark2 with ⟨hmark2cover, hmark2R, hmark2V, hmark2D, hmark2opp⟩
  have cutNoC := RestorationSectorGeometry.cutNoC q cfg C₀ T cert hOC hQC hSC cutData
  have cutNoD := RestorationSectorGeometry.cutNoD q cfg C₀ T cert hOD hRD hVD cutDataR
  have cuts_ne_marked := RestorationSectorGeometry.cuts_ne_marked q cfg C₀ T cert hmark1C hmark2D
      cutNoC cutNoD
  have splitInternal := ListEndpointFacts.internalNeighbors
  have leftInternal := RestorationSectorGeometry.leftInternal q cfg C₀ T cert two_owner_sectors
      hQ hS hQSC splitInternal
  have rightInternal := RestorationSectorGeometry.rightInternal q cfg C₀ T cert two_owner_sectors
      hR hV hRVD splitInternal
  have middleRestored := RestorationSectorGeometry.middleRestored q cfg C₀ T cert
      (RestorationSectorGeometry.middleInternal q cfg C₀ T cert two_owner_sectors hO splitInternal)
  have middleWalkEdge := RestorationSectorGeometry.middleWalkEdge q cfg C₀ T cert splitInternal
  have sectorOrderCertificate :
    ExceptionalRestorationSectorData
      (cert.P 0 true) (cert.P 0 false) cert.O
      (cert.Q 1 true) (cert.S 2 false)
      (cert.Q 2 true) (cert.S 1 false)
      (cert.P 1 true) (cert.P 1 false)
      (cert.unmodified.core.rho
        (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
      (cert.unmodified.core.rho
        (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩))
      cert.exceptionalSegments := RestorationSectorCertificate.sectorOrderCertificate q cfg C₀ T
          cert hBne hQne hSne hRne hVne hQSC hRVD hcompB hQC hSC hRD hVD footprint_incident
          boundary_missing_incident hQO hRO cutData cutDataR hmark1cover hmark1C hmark1opp
          hmark2cover hmark2D hmark2opp cutNoC cutNoD cuts_ne_marked leftInternal rightInternal
          middleRestored middleWalkEdge
  exact sectorOrderCertificate


end ApollonianSuperharmonic

end
