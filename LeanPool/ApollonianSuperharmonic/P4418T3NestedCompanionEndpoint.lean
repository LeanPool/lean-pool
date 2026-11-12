/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4418T3EndpointOwnerIndices
public import LeanPool.ApollonianSuperharmonic.P4418T3SelectedInterfaceData
public import LeanPool.ApollonianSuperharmonic.P3996T1SRowAlignment
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPeriodicBlockCells
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleLatticeTouching
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathEndpointPairUnique
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTriplePermutations

-- [TABLET NODE: P4418T3NestedCompanionEndpoint]

/-!
# P4418T3NestedCompanionEndpoint

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private def nestedOldCoordinates
    {q : Fin 4 → CircleCoordinates} {cfg : BandOrderedGeneralConfiguration q}
    {C : BandCircle} {T : ProtoTile}
    {cert : BandOrderedGeneralLayoutCertificate q cfg C T}
    {a b : PeriodicSubtileIndex}
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b) : Int × Int :=
  match row with
    | .positiveS1 _ => (-1, 0)
    | .positiveS2 _ => (1, 0)
    | .positiveS3 _ => (0, -1)
    | .positiveS4 _ => (0, 1)
    | .positiveS5 _ => (1, 1)
    | .positiveS6 _ => (-1, -1)
    | .reflectedS1 _ => (1, 0)
    | .reflectedS2 _ => (-1, 0)
    | .reflectedS3 _ => (0, 1)
    | .reflectedS4 _ => (0, -1)
    | .reflectedS5 _ => (-1, -1)
    | .reflectedS6 _ => (1, 1)
    | _ => (0, 0)

namespace NestedCompanionGeometry

private theorem hpath :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (z :
            P3996T1SRowParameters), ∀ (E : ExactTileInterfaceTriple
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) (TileTranslation
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) z.rightShift)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.parentIndex)),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) ) := by
  classical
  intro q cfg C T cert a b z E occ V W hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp? [hchild] at hi
    rcases hi with ⟨hc, hp⟩
    simpa [V, W, occ, SubtileOccurrenceInterpretation, hc, hp,
      Set.inter_comm] using E.pathCA
  · have hi := hindices
    simp? [hchild] at hi
    rcases hi with ⟨hc, hp⟩
    simpa [V, W, occ, SubtileOccurrenceInterpretation, hc, hp,
      Set.inter_comm] using E.pathCA

private theorem hdataEndpoints :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), ∀ (E : ExactTileInterfaceTriple
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) (TileTranslation
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) z.rightShift)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.parentIndex)),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → ((SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) →
            (({data.first, data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset
            GaussianInt))) ) := by
  classical
  intro q cfg C T cert a b row data z E occ V W hindices hpath
  have hpath' : SimpleGridPathBetween
      (FootprintVertices (occ a) ∩ FootprintVertices (occ b))
      (FootprintEdges (occ a) ∩ FootprintEdges (occ b)) E.point E.otherCA := by
    cases hchild : z.childIsExterior
    · have hi := hindices
      simp? [hchild] at hi
      rcases hi with ⟨hc, hp⟩
      simpa [V, W, occ, hc, hp, Set.inter_comm] using hpath
    · have hi := hindices
      simp? [hchild] at hi
      rcases hi with ⟨hc, hp⟩
      simpa [V, W, occ, hc, hp, Set.inter_comm] using hpath
  have hp := SimpleGridPathEndpointPairUnique data.path hpath'
  simpa [Finset.pair_comm] using hp

private theorem hpointPair :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), ∀ (E : ExactTileInterfaceTriple
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) (TileTranslation
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) z.rightShift)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.parentIndex)), (({data.first,
            data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset GaussianInt)) →
            (E.point = data.first ∨ E.point = data.last) ) := by
  classical
  intro q cfg C T cert a b row data z E hdataEndpoints
  have hm : E.point ∈ ({data.first, data.last} : Finset GaussianInt) := by
    rw [hdataEndpoints]
    simp
  simpa using hm

private theorem hprecursorInMinus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), cert.O.cells ⊆ (cert.P 0 false).cells ) := by
  classical
  intro q cfg C T cert x hx
  rw [cert.precursor_cells] at hx
  exact (cert.minus_union x).2 ⟨0, true, hx⟩

private theorem originalInBlock :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (cert.O.cells ⊆ (cert.P 0 false).cells) → (∀ (i : PeriodicSubtileIndex), ∀ (x :
            LatticeCell), (x ∈ (occ i).cells) → (x ∈ (TileTranslation T ((i.first : GaussianInt)
            * cert.u + (i.second : GaussianInt) * cert.v)).cells)) ) := by
  classical
  intro q cfg C T cert occ hprecursorInMinus i x hx
  cases i with
  | mk label m n =>
    cases label with
    | A =>
    change x ∈ (TileTranslation (cert.P 0 true)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ (cert.P 0 true).cells := by simpa using hy
    by_cases ho : y ∈ cert.O.cells
    · have hb : y ∈ (cert.P 0 false).cells := hprecursorInMinus ho
      have hbase : y ∈ T.cells := (cert.outer_union y).2 <| by
        exact ⟨0, false, hb⟩
      exact Finset.mem_image.mpr ⟨y, hbase, by rfl⟩
    · have hbase : y ∈ T.cells := (cert.outer_union y).2 <| by
        exact ⟨0, true, hy'
      ⟩
      exact Finset.mem_image.mpr ⟨y, hbase, by rfl⟩
    | B =>
    change x ∈ (TileTranslation (cert.P 0 false)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨0, false, by simpa using hy⟩, rfl⟩
    | C =>
    change x ∈ (TileTranslation (cert.P 1 true)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨1, true, by simpa using hy⟩, rfl⟩
    | D =>
    change x ∈ (TileTranslation (cert.P 1 false)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨1, false, by simpa using hy⟩, rfl⟩
    | E =>
    change x ∈ (TileTranslation (cert.P 2 true)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨2, true, by simpa using hy⟩, rfl⟩
    | F =>
    change x ∈ (TileTranslation (cert.P 2 false)
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells at hx
    rw [(TileTranslationFormulas _ _).1] at hx ⊢
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, (cert.outer_union y).2 ⟨2, false, by simpa using hy⟩, rfl⟩

private theorem hKDisjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (z : P3996T1SRowParameters), ((TileTranslation
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex)
            z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) → (
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let K := TileTranslation V z.rightShift
        (∀ (i : PeriodicSubtileIndex), ∀ (x : LatticeCell), (x ∈ (occ i).cells) → (x ∈
            (TileTranslation T ((i.first : GaussianInt) * cert.u + (i.second : GaussianInt) *
            cert.v)).cells)) → (∀ (i : PeriodicSubtileIndex), ∀ (r : Int), ∀ (s : Int),
            (z.oldShift = (r : GaussianInt) * cert.u + (s : GaussianInt) * cert.v) → (((i.first,
            i.second) ≠ (r, s)) → (Disjoint K.cells (occ i).cells)))) ) := by
  classical
  intro q cfg C T cert z hsub occ V K originalInBlock i r s hshift hneq
  rw [Finset.disjoint_left]
  intro x hxK hxi
  have hbk : x ∈ (TileTranslation T
      ((r : GaussianInt) * cert.u + (s : GaussianInt) * cert.v)).cells := by
    have hx := hsub hxK
    simpa [hshift] using hx
  have hbi := originalInBlock i x hxi
  have hblocks := (BandOrderedGeneralPeriodicBlockCells q cfg C T cert).2
    i.first i.second r s (by simpa [Prod.mk.injEq] using hneq)
  exact (Finset.disjoint_left.mp hblocks) hbi hbk

private theorem hLV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
            (P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)) → (∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (LatticeTile V)) ) := by
  classical
  intro q cfg C T cert a b row data z occ V hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, occ, SubtileOccurrenceInterpretation, hi.1] using data.latticeW
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, occ, SubtileOccurrenceInterpretation, hi.1] using data.latticeV

private theorem hLW :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
            (P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)) → (∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let W := occ z.parentIndex
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (LatticeTile W)) ) := by
  classical
  intro q cfg C T cert a b row data z occ W hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    simpa [W, occ, SubtileOccurrenceInterpretation, hi.2] using data.latticeV
  · have hi := hindices
    simp [hchild] at hi
    simpa [W, occ, SubtileOccurrenceInterpretation, hi.2] using data.latticeW

private theorem holdShift :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg C T cert row = some z) → (∀ (E :
            ExactTileInterfaceTriple (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) (TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) z.rightShift) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.parentIndex)), ((TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v z.childIndex) z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) → (
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let K := TileTranslation V z.rightShift
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → ((SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) →
            ((({data.first, data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset
            GaussianInt)) → ((E.point = data.first ∨ E.point = data.last) → ((∀ (i :
            PeriodicSubtileIndex), ∀ (r : Int), ∀ (s : Int), (z.oldShift = (r : GaussianInt) *
            cert.u + (s : GaussianInt) * cert.v) → (((i.first, i.second) ≠ (r, s)) → (Disjoint
            K.cells (occ i).cells))) → ((LatticeTile V) → ((LatticeTile W) → ((LatticeTile K) → (
        let oldCoords : Int × Int := nestedOldCoordinates row
        z.oldShift = (oldCoords.1 : GaussianInt) * cert.u + (oldCoords.2 : GaussianInt) *
            cert.v)))))))))) ) := by
  classical
  intro q cfg C T cert a b row data z hz E hsub occ V W K hindices hpath hdataEndpoints
      hpointPair hKDisjoint hLV hLW hLK oldCoords
  cases row <;> simp? [P3996T1SRowTable] at hz
  all_goals cases hz
  all_goals simp [oldCoords, nestedOldCoordinates]
  all_goals ring

private theorem hchildBlockNe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg C T cert row = some z) → (∀ (E :
            ExactTileInterfaceTriple (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) (TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) z.rightShift) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.parentIndex)), ((TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v z.childIndex) z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) → (
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let K := TileTranslation V z.rightShift
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → ((SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) →
            ((({data.first, data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset
            GaussianInt)) → ((E.point = data.first ∨ E.point = data.last) → ((∀ (i :
            PeriodicSubtileIndex), ∀ (r : Int), ∀ (s : Int), (z.oldShift = (r : GaussianInt) *
            cert.u + (s : GaussianInt) * cert.v) → (((i.first, i.second) ≠ (r, s)) → (Disjoint
            K.cells (occ i).cells))) → ((LatticeTile V) → ((LatticeTile W) → ((LatticeTile K) → (
        let oldCoords : Int × Int := nestedOldCoordinates row
        (z.oldShift = (oldCoords.1 : GaussianInt) * cert.u + (oldCoords.2 : GaussianInt) *
            cert.v) → ((z.childIndex.first, z.childIndex.second) ≠ oldCoords))))))))))) ) := by
  classical
  intro q cfg C T cert a b row data z hz E hsub occ V W K hindices hpath hdataEndpoints
      hpointPair hKDisjoint hLV hLW hLK oldCoords holdShift
  cases row <;> simp? [P3996T1SRowTable] at hz
  all_goals
    cases hz
    simp [oldCoords, nestedOldCoordinates]

private theorem hparentBlockNe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg C T cert row = some z) → (∀ (E :
            ExactTileInterfaceTriple (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) (TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) z.rightShift) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.parentIndex)), ((TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v z.childIndex) z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) → (
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let K := TileTranslation V z.rightShift
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → ((SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) →
            ((({data.first, data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset
            GaussianInt)) → ((E.point = data.first ∨ E.point = data.last) → ((∀ (i :
            PeriodicSubtileIndex), ∀ (r : Int), ∀ (s : Int), (z.oldShift = (r : GaussianInt) *
            cert.u + (s : GaussianInt) * cert.v) → (((i.first, i.second) ≠ (r, s)) → (Disjoint
            K.cells (occ i).cells))) → ((LatticeTile V) → ((LatticeTile W) → ((LatticeTile K) → (
        let oldCoords : Int × Int := nestedOldCoordinates row
        (z.oldShift = (oldCoords.1 : GaussianInt) * cert.u + (oldCoords.2 : GaussianInt) *
            cert.v) → (((z.childIndex.first, z.childIndex.second) ≠ oldCoords) →
            ((z.parentIndex.first, z.parentIndex.second) ≠ oldCoords)))))))))))) ) := by
  classical
  intro q cfg C T cert a b row data z hz E hsub occ V W K hindices hpath hdataEndpoints
      hpointPair hKDisjoint hLV hLW hLK oldCoords holdShift hchildBlockNe
  cases row <;> simp? [P3996T1SRowTable] at hz
  all_goals
    cases hz
    simp [oldCoords, nestedOldCoordinates]

private theorem hwrongBlockNe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), (P3996T1SRowTable q cfg C T cert row = some z) → (∀ (E :
            ExactTileInterfaceTriple (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) (TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.childIndex) z.rightShift) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            z.parentIndex)), ((TileTranslation (SubtileOccurrenceInterpretation cert.P cert.u
            cert.v z.childIndex) z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) → (
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let K := TileTranslation V z.rightShift
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → ((SimpleGridPathBetween (FootprintVertices V ∩
            FootprintVertices W) (FootprintEdges V ∩ FootprintEdges W) E.point E.otherCA) →
            ((({data.first, data.last} : Finset GaussianInt) = ({E.point, E.otherCA} : Finset
            GaussianInt)) → ((E.point = data.first ∨ E.point = data.last) → ((∀ (i :
            PeriodicSubtileIndex), ∀ (r : Int), ∀ (s : Int), (z.oldShift = (r : GaussianInt) *
            cert.u + (s : GaussianInt) * cert.v) → (((i.first, i.second) ≠ (r, s)) → (Disjoint
            K.cells (occ i).cells))) → ((LatticeTile V) → ((LatticeTile W) → ((LatticeTile K) → (
        let oldCoords : Int × Int := nestedOldCoordinates row
        (z.oldShift = (oldCoords.1 : GaussianInt) * cert.u + (oldCoords.2 : GaussianInt) *
            cert.v) → (((z.childIndex.first, z.childIndex.second) ≠ oldCoords) →
            (((z.parentIndex.first, z.parentIndex.second) ≠ oldCoords) → (
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
        let wrongOwner := if z.parentSlot = 0 then owners.2 else owners.1
        (wrongOwner.first, wrongOwner.second) ≠ oldCoords))))))))))))) ) := by
  classical
  intro q cfg C T cert a b row data z hz E hsub occ V W K hindices hpath hdataEndpoints
      hpointPair hKDisjoint hLV hLW hLK oldCoords holdShift hchildBlockNe hparentBlockNe owners
      wrongOwner
  cases row <;> simp? [P3996T1SRowTable] at hz
  all_goals
    cases hz
    simp [wrongOwner, owners, oldCoords,
      P4418T3EndpointOwnerIndices, nestedOldCoordinates]

private theorem hTVW :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
            (P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)) → (∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let G₀ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (TouchingTriple V W G₀)) ) := by
  classical
  intro q cfg C T cert a b row data z occ V W G₀ hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    have hrev :=
      (TouchingTriplePermutations (occ a) (occ b) G₀).mp data.touching₀ |>.2.1
    simpa [V, W, G₀, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2] using hrev
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₀, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2] using data.touching₀

private theorem hTVW' :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
            (P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)) → (∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let G₁ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (TouchingTriple V W G₁)) ) := by
  classical
  intro q cfg C T cert a b row data z occ V W G₁ hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    have hrev :=
      (TouchingTriplePermutations (occ a) (occ b) G₁).mp data.touching₁ |>.2.1
    simpa [V, W, G₁, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2] using hrev
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₁, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2] using data.touching₁

private theorem hcommon₀ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let G₀ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (data.first ∈ FootprintVertices V ∩ FootprintVertices W ∩
            FootprintVertices G₀) ) := by
  classical
  intro q cfg C T cert a b row data z occ V W G₀ hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₀, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using data.common₀
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₀, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using data.common₀

private theorem hcommon₁ :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let G₁ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (data.last ∈ FootprintVertices V ∩ FootprintVertices W ∩
            FootprintVertices G₁) ) := by
  classical
  intro q cfg C T cert a b row data z occ V W G₁ hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₁, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using data.common₁
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, G₁, occ, SubtileOccurrenceInterpretation,
      hi.1, hi.2, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using data.common₁

private theorem hVW :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b),
            (P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)) → (∀ (z :
            P3996T1SRowParameters),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        (if z.childIsExterior = true then z.childIndex = a ∧ z.parentIndex = b else z.childIndex
            = b ∧ z.parentIndex = a) → (Disjoint V.cells W.cells)) ) := by
  classical
  intro q cfg C T cert a b row data z occ V W hindices
  cases hchild : z.childIsExterior
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, occ, SubtileOccurrenceInterpretation, hi.1, hi.2] using
      data.disjointVW.symm
  · have hi := hindices
    simp [hchild] at hi
    simpa [V, W, occ, SubtileOccurrenceInterpretation, hi.1, hi.2] using
      data.disjointVW

private theorem hNoWrong :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C
            T), ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (row :
            BandOrderedGeneralSelectedContactRow q cfg C T cert a b), ∀ (data :
            P4418T3SelectedInterfaceData (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            a) (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4418T3EndpointOwnerIndices
            q cfg C T cert a b row).1) (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2)), ∀ (z :
            P3996T1SRowParameters), ∀ (E : ExactTileInterfaceTriple
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) (TileTranslation
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex) z.rightShift)
            (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.parentIndex)),
        let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
        let V := occ z.childIndex
        let W := occ z.parentIndex
        let K := TileTranslation V z.rightShift
        let G₀ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
        let G₁ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
        (LatticeTile V) → ((LatticeTile W) → ((LatticeTile K) → (
        let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
        let wrongOwner := if z.parentSlot = 0 then owners.2 else owners.1
        (Disjoint K.cells V.cells) → ((Disjoint K.cells W.cells) → ((Disjoint K.cells (occ
            wrongOwner).cells) → ((TouchingTriple V W G₀) → ((TouchingTriple V W G₁) →
            ((data.first ∈ FootprintVertices V ∩ FootprintVertices W ∩ FootprintVertices G₀) →
            ((data.last ∈ FootprintVertices V ∩ FootprintVertices W ∩ FootprintVertices G₁) →
            ((TouchingTriple V K W) → (E.point ≠ if z.parentSlot = 0 then data.last else
            data.first))))))))))) ) := by
  classical
  intro q cfg C T cert a b row data z E occ V W K G₀ G₁ hLV hLW hLK owners wrongOwner hKV hKW
      hKGwrong hTVW hTVW' hcommon₀ hcommon₁ hET
  by_cases hslot : z.parentSlot = 0
  · intro heq
    have hG : Disjoint K.cells G₁.cells := by
      simpa [wrongOwner, owners, hslot, G₁] using hKGwrong
    have hsectorData := LocalLatticeInterfaceSectors.1 V W G₁ data.last
      hLV hLW data.latticeG₁ hTVW' hcommon₁
    have hpointE := (E.unique_common E.point).2 rfl
    have hsectorE := LocalLatticeInterfaceSectors.1 V K W E.point
      hLV hLK hLW hET hpointE
    obtain ⟨j, hjK⟩ := hsectorE.2.2.1
    have hjData := hsectorData.1 j
    simp? [hslot] at heq
    rw [← heq] at hjData
    rcases hjData with hjV | hjW | hjG
    · exact (Finset.disjoint_left.mp hKV) hjK hjV
    · exact (Finset.disjoint_left.mp hKW) hjK hjW
    · exact (Finset.disjoint_left.mp hG) hjK hjG
  · intro heq
    have hG : Disjoint K.cells G₀.cells := by
      simpa [wrongOwner, owners, hslot, G₀] using hKGwrong
    have hsectorData := LocalLatticeInterfaceSectors.1 V W G₀ data.first
      hLV hLW data.latticeG₀ hTVW hcommon₀
    have hpointE := (E.unique_common E.point).2 rfl
    have hsectorE := LocalLatticeInterfaceSectors.1 V K W E.point
      hLV hLK hLW hET hpointE
    obtain ⟨j, hjK⟩ := hsectorE.2.2.1
    have hjData := hsectorData.1 j
    simp? [hslot] at heq
    rw [← heq] at hjData
    rcases hjData with hjV | hjW | hjG
    · exact (Finset.disjoint_left.mp hKV) hjK hjV
    · exact (Finset.disjoint_left.mp hKW) hjK hjW
    · exact (Finset.disjoint_left.mp hG) hjK hjG

end NestedCompanionGeometry

theorem P4418T3NestedCompanionEndpoint
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (a b : PeriodicSubtileIndex)
    (row : BandOrderedGeneralSelectedContactRow q cfg C T cert a b)
    (data : P4418T3SelectedInterfaceData
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v a)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v b)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v
        (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2))
    (z : P3996T1SRowParameters)
    (hz : P3996T1SRowTable q cfg C T cert row = some z)
    (E : ExactTileInterfaceTriple
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex)
      (TileTranslation
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex)
        z.rightShift)
      (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.parentIndex))
    (hsub : (TileTranslation
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v z.childIndex)
        z.rightShift).cells ⊆ (TileTranslation T z.oldShift).cells) :
    E.point = (if z.parentSlot = 0 then data.first else data.last) := by
-- BODY
  classical
  let occ := SubtileOccurrenceInterpretation cert.P cert.u cert.v
  let V := occ z.childIndex
  let W := occ z.parentIndex
  let K := TileTranslation V z.rightShift
  let G₀ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).1
  let G₁ := occ (P4418T3EndpointOwnerIndices q cfg C T cert a b row).2
  obtain ⟨_, _, _, _, _, _, hindices, _, _⟩ :=
    P3996T1SRowAlignment q cfg C T cert a b row z hz
  have hpath := NestedCompanionGeometry.hpath q cfg C T cert a b z E hindices
  have hdataEndpoints := NestedCompanionGeometry.hdataEndpoints q cfg C T cert a b row data z E
      hindices hpath
  have hpointPair := NestedCompanionGeometry.hpointPair q cfg C T cert a b row data z E
      hdataEndpoints
  have hprecursorInMinus := NestedCompanionGeometry.hprecursorInMinus q cfg C T cert
  have originalInBlock (i : PeriodicSubtileIndex) (x : LatticeCell)
      (hx : x ∈ (occ i).cells) := NestedCompanionGeometry.originalInBlock q cfg C T cert
          hprecursorInMinus i x hx
  have hKDisjoint (i : PeriodicSubtileIndex) (r s : Int)
      (hshift : z.oldShift = (r : GaussianInt) * cert.u + (s : GaussianInt) * cert.v)
      (hneq : (i.first, i.second) ≠ (r, s)) := NestedCompanionGeometry.hKDisjoint q cfg C T cert
          z hsub originalInBlock i r s hshift hneq
  have hLV := NestedCompanionGeometry.hLV q cfg C T cert a b row data z hindices
  have hLW := NestedCompanionGeometry.hLW q cfg C T cert a b row data z hindices
  have hLK : LatticeTile K :=
    (TileDiskAreaCovariance V z.rightShift).1.mp hLV
  let oldCoords : Int × Int := nestedOldCoordinates row
  have holdShift := NestedCompanionGeometry.holdShift q cfg C T cert a b row data z hz E hsub
      hindices hpath hdataEndpoints hpointPair hKDisjoint hLV hLW hLK
  have hchildBlockNe := NestedCompanionGeometry.hchildBlockNe q cfg C T cert a b row data z hz E
      hsub hindices hpath hdataEndpoints hpointPair hKDisjoint hLV hLW hLK holdShift
  have hparentBlockNe := NestedCompanionGeometry.hparentBlockNe q cfg C T cert a b row data z hz
      E hsub hindices hpath hdataEndpoints hpointPair hKDisjoint hLV hLW hLK holdShift hchildBlockNe
  let owners := P4418T3EndpointOwnerIndices q cfg C T cert a b row
  let wrongOwner := if z.parentSlot = 0 then owners.2 else owners.1
  have hwrongBlockNe := NestedCompanionGeometry.hwrongBlockNe q cfg C T cert a b row data z hz E
      hsub hindices hpath hdataEndpoints hpointPair hKDisjoint hLV hLW hLK holdShift
      hchildBlockNe hparentBlockNe
  have hKV : Disjoint K.cells V.cells :=
    hKDisjoint z.childIndex oldCoords.1 oldCoords.2 holdShift hchildBlockNe
  have hKW : Disjoint K.cells W.cells :=
    hKDisjoint z.parentIndex oldCoords.1 oldCoords.2 holdShift hparentBlockNe
  have hKGwrong : Disjoint K.cells (occ wrongOwner).cells :=
    hKDisjoint wrongOwner oldCoords.1 oldCoords.2 holdShift hwrongBlockNe
  have hTVW := NestedCompanionGeometry.hTVW q cfg C T cert a b row data z hindices
  have hTVW' := NestedCompanionGeometry.hTVW' q cfg C T cert a b row data z hindices
  have hcommon₀ := NestedCompanionGeometry.hcommon₀ q cfg C T cert a b row data z hindices
  have hcommon₁ := NestedCompanionGeometry.hcommon₁ q cfg C T cert a b row data z hindices
  have hVW := NestedCompanionGeometry.hVW q cfg C T cert a b row data z hindices
  have hET : TouchingTriple V K W :=
    ExactTileInterfaceTripleLatticeTouching V K W E hLV hLK hLW
      hKV.symm hKW hVW.symm
  have hNoWrong := NestedCompanionGeometry.hNoWrong q cfg C T cert a b row data z E hLV hLW hLK
      hKV hKW hKGwrong hTVW hTVW' hcommon₀ hcommon₁ hET
  by_cases hslot : z.parentSlot = 0
  · have hn := hNoWrong
    simp? [hslot] at hn
    rcases hpointPair with hp | hp
    · simpa [hslot] using hp
    · exact False.elim (hn hp)
  · have hn := hNoWrong
    simp? [hslot] at hn
    rcases hpointPair with hp | hp
    · exact False.elim (hn hp)
    · simpa [hslot] using hp

end ApollonianSuperharmonic

end
