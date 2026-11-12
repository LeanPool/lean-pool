/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeVertexSectorFacts

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTripleLatticeTouching
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex

-- [TABLET NODE: P5635T1EndpointDiagonalOwnership]

/-!
# P5635T1EndpointDiagonalOwnership

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EndpointDiagonalGeometry

private theorem triple_label_pattern :
    (by
      classical
      exact
        ∀ (label : Fin 4 → Fin 3), ∀ (a : Fin 4), ∀ (b : Fin 4), ∀ (c : Fin 4), a ≠ b → b ≠ c → c
            ≠ a → ({label a, label (a + 1)} : Finset (Fin 3)) = {0, 1} → ({label b,
            label (b + 1)} : Finset (Fin 3)) = {1, 2} → ({label c, label (c + 1)} : Finset (Fin
            3)) = {2, 0} → (label (a + 2) = 2 ∧ label (a + 3) = label a) ∨ (label (a + 3) = 2 ∧
            label (a + 2) = label (a + 1)) ∨ (label (a + 2) = 2 ∧ label (a + 3) = 2) ∨ (label (a
            + 3) = 2 ∧ label a = 2) ) := by
  classical
  exact ((((by decide +kernel))))

private theorem neighbor_injective :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (x : GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (neighbor x j = neighbor x k) → (j =
            k) ) := by
  classical
  intro neighbor x j k h
  fin_cases j <;> fin_cases k <;>
    simp [neighbor, Zsqrtd.ext_iff] at h ⊢ <;> omega




private theorem edge_of_sector_pair :
    (by
      classical
      exact
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        ∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈
            R.cells) → ((LatticeVertexIncidentCell x (j + 1) ∈ R.cells) → (edgeAt x j ∈
            FootprintEdges R)) ) := by
  classical
  intro edgeAt R x j h0 h1
  fin_cases j
  · simpa [edgeAt] using
      (show {x, x + ⟨0, 1⟩} ∈ FootprintEdges R from
        ⟨x, by simpa [LatticeVertexIncidentCell] using h0,
          Or.inr (Or.inl rfl)⟩)
  · simpa [edgeAt] using
      (show {x - 1, x} ∈ FootprintEdges R from
        ⟨x - 1, by simpa [LatticeVertexIncidentCell] using h0,
          Or.inl (by simp)⟩)
  · simpa [edgeAt] using
      (show {x - ⟨0, 1⟩, x} ∈ FootprintEdges R from
        ⟨x - ⟨0, 1⟩, by simpa [LatticeVertexIncidentCell] using h1,
          Or.inr (Or.inl (by simp))⟩)
  · simpa [edgeAt] using
      (show {x, x + 1} ∈ FootprintEdges R from
        ⟨x, by simpa [LatticeVertexIncidentCell] using h1,
          Or.inl rfl⟩)

private theorem edge_foreign_impossible :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (j : Fin 4), x ∈ edgeAt x j ∧ neighbor x j ∈ edgeAt x j) → ((∀ (x
            : GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (edgeAt x j = edgeAt x k) → (j = k)) →
            ((∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x
            j ∈ R.cells) → ((LatticeVertexIncidentCell x (j + 1) ∈ R.cells) → (edgeAt x j ∈
            FootprintEdges R))) → (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (x : GaussianInt), ∀
            (j : Fin 4), (Disjoint A.cells B.cells) → ((LatticeVertexIncidentCell x j ∈ A.cells)
            → ((LatticeVertexIncidentCell x (j + 1) ∈ A.cells) → ((edgeAt x j ∈ FootprintEdges B)
            → (False))))))) ) := by
  classical
  intro neighbor edgeAt edgeAt_mem edgeAt_injective edge_of_sector_pair A B x j hdisAB h0 h1 hBedge
  have hAedge := edge_of_sector_pair A x j h0 h1
  obtain ⟨k, hk, htransition⟩ := P3102T2CommonEdgeSectorTransition
    A B x (edgeAt x j) hdisAB (edgeAt_mem x j).1 ⟨hAedge, hBedge⟩
  have hkj : k = j := edgeAt_injective x hk.symm
  rcases htransition with htransition | htransition
  · have hcB : LatticeVertexIncidentCell x (j + 1) ∈ B.cells := by
      simpa [hkj] using htransition.2
    exact (Finset.disjoint_left.mp hdisAB) h1 hcB
  · have hcB : LatticeVertexIncidentCell x j ∈ B.cells := by
      simpa [hkj] using htransition.1
    exact (Finset.disjoint_left.mp hdisAB) h0 hcB

private theorem neighbor_in_star :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (x : GaussianInt), ∀ (j : Fin 4), neighbor x j = x ∨ neighbor x j = x + 1 ∨ neighbor x
            j = x - 1 ∨ neighbor x j = x + ⟨0, 1⟩ ∨ neighbor x j = x - ⟨0, 1⟩ ) := by
  classical
  intro neighbor x j
  fin_cases j <;> simp [neighbor, sub_eq_add_neg,
    ]

private theorem neighbor_four_adjacent :
    (by
      classical
      exact
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        ∀ (x : GaussianInt), ∀ (j : Fin 4), FourNeighborAdjacent x (neighbor x j) ) := by
  classical
  intro neighbor x j
  fin_cases j <;> simp [FourNeighborAdjacent, neighbor,
    sub_eq_add_neg]

private theorem star_induced_edge :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (∀ x ∈ FootprintVertices T0, ∀ y ∈
            FootprintVertices T0, FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0) → ((∀ x
            ∈ FootprintVertices T0', ∀ y ∈ FootprintVertices T0', FourNeighborAdjacent x y → {x,
            y} ∈ FootprintEdges T0') → (
        let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
          ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ (j : Fin 4), edgeAt x j = {x, neighbor x j}) → ((∀ (x :
            GaussianInt), ∀ (j : Fin 4), neighbor x j = x ∨ neighbor x j = x + 1 ∨ neighbor x j =
            x - 1 ∨ neighbor x j = x + ⟨0, 1⟩ ∨ neighbor x j = x - ⟨0, 1⟩) → ((∀ (x :
            GaussianInt), ∀ (j : Fin 4), FourNeighborAdjacent x (neighbor x j)) → (∀ (x :
            GaussianInt), (x ∈ FootprintVertices T0) → ((x ∈ FootprintVertices T0') → ((∀ y, y =
            x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
            y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') → (∀ (j : Fin 4), edgeAt x j ∈
                FootprintEdges T0 ∨ edgeAt x j ∈ FootprintEdges T0')))))))) ) := by
  classical
  intro T0 T0' hreg hreg' neighbor edgeAt edgeAt_eq_pair neighbor_in_star neighbor_four_adjacent
      x hx0 hx1 hstar j
  have hy := hstar (neighbor x j) (neighbor_in_star x j)
  rcases hy with hy | hy
  · have he := hreg x hx0 (neighbor x j) hy (neighbor_four_adjacent x j)
    rw [← edgeAt_eq_pair x j] at he
    exact Or.inl he
  · have he := hreg' x hx1 (neighbor x j) hy (neighbor_four_adjacent x j)
    rw [← edgeAt_eq_pair x j] at he
    exact Or.inr he

private theorem endpoint_repeat_impossible :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (Disjoint
            A.cells B.cells) → ((LatticeVertexIncidentCell x j ∈ A.cells) →
            ((LatticeVertexIncidentCell x (j + 1) ∈ A.cells) → ((edgeAt x j ∈ FootprintEdges B) →
            (False))))) → ((∀ (x : GaussianInt), (x ∈ FootprintVertices T0) → ((x ∈
            FootprintVertices T0') → ((∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y =
            x - ⟨0, 1⟩ → y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') → (∀ (j : Fin 4),
            edgeAt x j ∈ FootprintEdges T0 ∨ edgeAt x j ∈ FootprintEdges T0')))) → (∀ (E :
            ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (x ∈ FootprintVertices T0) → ((x ∈
            FootprintVertices T0') → ((∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
            y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
            y ∈ FootprintVertices T0 ∨ y ∈ FootprintVertices T0') → ((Disjoint E.cells T0.cells)
                → ((Disjoint E.cells T0'.cells) → ((LatticeVertexIncidentCell x j ∈ E.cells) →
                ((LatticeVertexIncidentCell x (j + 1) ∈ E.cells) → (False))))))))) ) := by
  classical
  intro T0 T0' edgeAt edge_foreign_impossible star_induced_edge E x j hx0 hx1 hstar hEdis0 hEdis1
      hE0 hE1
  rcases star_induced_edge x hx0 hx1 hstar j with houter | houter
  · exact edge_foreign_impossible E T0 x j hEdis0 hE0 hE1 houter
  · exact edge_foreign_impossible E T0' x j hEdis1 hE0 hE1 houter

private theorem exact_point_boundary :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (point : GaussianInt), ∀ (other : GaussianInt),
            (SimpleGridPathBetween
            (FootprintVertices A ∩ FootprintVertices B)
            (FootprintEdges A ∩ FootprintEdges B) point other) → ((LatticeTile A) → ((LatticeTile
                B) → ((Disjoint A.cells B.cells) → (point ∈ BoundaryFootprintVertices A ∩
                BoundaryFootprintVertices B)))) ) := by
  classical
  intro A B point other pathAB hA hB hdisAB
  rcases pathAB with ⟨p, hnd, hlen, hhead, hlast, hvertices, hsteps, hedges⟩
  have hsimple : SimpleGridPath
      (FootprintVertices A ∩ FootprintVertices B)
      (FootprintEdges A ∩ FootprintEdges B) :=
    ⟨p, hnd, hlen, hvertices, hsteps, hedges⟩
  have hpoint : point ∈ (p.toFinset : Set GaussianInt) := by
    cases p with
    | nil => simp at hlen
    | cons a p =>
      change point ∈ (a :: p).toFinset
      simp only [List.toFinset_cons, Finset.mem_insert]
      simp only [List.head?, Option.some.injEq] at hhead
      exact Or.inl hhead.symm
  have hpointVertices :
      point ∈ FootprintVertices A ∩ FootprintVertices B := by
    rw [hvertices]
    exact hpoint
  obtain ⟨e, hpe, he⟩ := SimpleGridPathVertexIncidentEdge
    _ _ hsimple point hpointVertices
  have heBoundary : e ∈ BoundaryFootprintEdges A ∩
      BoundaryFootprintEdges B := by
    rw [CellDisjointCommonEdgesBoundary A B hdisAB] at he
    exact he
  have hAne : A.cells.Nonempty := (LatticeTileGridStructure A hA).1.1
  have hBne : B.cells.Nonempty := (LatticeTileGridStructure B hB).1.1
  constructor
  · unfold BoundaryFootprintVertices
    rw [ite_eq_left hAne]
    exact ⟨e, heBoundary.1, hpe⟩
  · unfold BoundaryFootprintVertices
    rw [ite_eq_left hBne]
    exact ⟨e, heBoundary.2, hpe⟩

private theorem touching_path :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), (LatticeTile A) → ((LatticeTile B) → ((TileTouching
            A B) → (SimpleGridPath (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
            (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B)))) ) := by
  classical
  intro A B hA hB htouch
  rcases htouch with h | h | h
  · exact h.2.2.2
  · have hne := (LatticeTileGridStructure A hA).1.1
    rw [h.1] at hne
    simp at hne
  · have hne := (LatticeTileGridStructure B hB).1.1
    rw [h.1] at hne
    simp at hne

private theorem transition_indices_ne :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin
            4), ∀ (k : Fin 4), ((LatticeVertexIncidentCell x j ∈ A.cells ∧
              LatticeVertexIncidentCell x (j + 1) ∈ B.cells) ∨
            (LatticeVertexIncidentCell x j ∈ B.cells ∧
              LatticeVertexIncidentCell x (j + 1) ∈ A.cells)) → (((LatticeVertexIncidentCell x k
                  ∈ B.cells ∧
              LatticeVertexIncidentCell x (k + 1) ∈ C.cells) ∨
            (LatticeVertexIncidentCell x k ∈ C.cells ∧
              LatticeVertexIncidentCell x (k + 1) ∈ B.cells)) → ((Disjoint A.cells B.cells) →
                  ((Disjoint B.cells C.cells) → ((Disjoint A.cells C.cells) → (j ≠ k))))) ) := by
  classical
  intro A B C x j k hAB hBC hABdis hBCdis hACdis hEq
  subst k
  rcases hAB with hAB | hAB <;> rcases hBC with hBC | hBC
  · exact (Finset.disjoint_left.mp hABdis) hAB.1 hBC.1
  · exact (Finset.disjoint_left.mp hACdis) hAB.1 hBC.1
  · exact (Finset.disjoint_left.mp hACdis) hAB.2 hBC.2
  · exact (Finset.disjoint_left.mp hBCdis) hAB.1 hBC.1

private theorem triple_transitions :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (LatticeTile T0) → ((LatticeTile T0') →
            ((Disjoint T0.cells T0'.cells) → (
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (point : GaussianInt), ∀ (other : GaussianInt),
            (SimpleGridPathBetween (FootprintVertices A ∩ FootprintVertices B) (FootprintEdges A
            ∩ FootprintEdges B) point other) → ((LatticeTile A) → ((LatticeTile B) → ((Disjoint
            A.cells B.cells) → (point ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices
            B))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), (LatticeTile A) → ((LatticeTile B) →
            ((TileTouching A B) → (SimpleGridPath (BoundaryFootprintVertices A ∩
            BoundaryFootprintVertices B) (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges
            B))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (x :
            GaussianInt), ∀ (j : Fin 4), ∀ (k : Fin 4), ((LatticeVertexIncidentCell x j ∈ A.cells
            ∧ LatticeVertexIncidentCell x (j + 1) ∈ B.cells) ∨ (LatticeVertexIncidentCell x j ∈
            B.cells ∧ LatticeVertexIncidentCell x (j + 1) ∈ A.cells)) →
            (((LatticeVertexIncidentCell x k ∈ B.cells ∧ LatticeVertexIncidentCell x (k + 1) ∈
            C.cells) ∨ (LatticeVertexIncidentCell x k ∈ C.cells ∧ LatticeVertexIncidentCell x (k
            + 1) ∈ B.cells)) → ((Disjoint A.cells B.cells) → ((Disjoint B.cells C.cells) →
            ((Disjoint A.cells C.cells) → (j ≠ k)))))) → (∀ (R : ProtoTile), ∀ (E :
            ExactTileInterfaceTriple T0 T0' R), (LatticeTile R) → ((Disjoint T0.cells R.cells) →
            ((Disjoint T0'.cells R.cells) → ((TouchingTriple T0 T0' R) → (∃ eAB eBR eRA : Finset
            GaussianInt, ∃ jAB jBR jRA : Fin 4, E.point ∈ eAB ∧ eAB ∈ FootprintEdges T0 ∩
            FootprintEdges T0' ∧ eAB = edgeAt E.point jAB ∧ E.point ∈ eBR ∧ eBR ∈ FootprintEdges
            T0' ∩ FootprintEdges R ∧ eBR = edgeAt E.point jBR ∧ E.point ∈ eRA ∧ eRA ∈
            FootprintEdges R ∩ FootprintEdges T0 ∧ eRA = edgeAt E.point jRA ∧
            ((LatticeVertexIncidentCell E.point jAB ∈ T0.cells ∧ LatticeVertexIncidentCell
            E.point (jAB + 1) ∈ T0'.cells) ∨ (LatticeVertexIncidentCell E.point jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell E.point (jAB + 1) ∈ T0.cells)) ∧
            ((LatticeVertexIncidentCell E.point jBR ∈ T0'.cells ∧ LatticeVertexIncidentCell
            E.point (jBR + 1) ∈ R.cells) ∨ (LatticeVertexIncidentCell E.point jBR ∈ R.cells ∧
            LatticeVertexIncidentCell E.point (jBR + 1) ∈ T0'.cells)) ∧
            ((LatticeVertexIncidentCell E.point jRA ∈ R.cells ∧ LatticeVertexIncidentCell E.point
            (jRA + 1) ∈ T0.cells) ∨ (LatticeVertexIncidentCell E.point jRA ∈ T0.cells ∧
            LatticeVertexIncidentCell E.point (jRA + 1) ∈ R.cells)) ∧ jAB ≠ jBR ∧ jBR ≠ jRA ∧ jRA
            ≠ jAB)))))))))) ) := by
  classical
  intro T0 T0' hT hT' hdis edgeAt exact_point_boundary touching_path transition_indices_ne R E hR
      hAR hBR hTouch
  rcases hTouch with ⟨hABtouch, hBRtouch, hRAtouch, _⟩
  have hABvertex := exact_point_boundary T0 T0' E.point E.otherAB
    E.pathAB hT hT' hdis
  have hBRvertex := exact_point_boundary T0' R E.point E.otherBC
    E.pathBC hT' hR hBR
  have hRAvertex := exact_point_boundary R T0 E.point E.otherCA
    E.pathCA hR hT hAR.symm
  have hABpath := touching_path T0 T0' hT hT' hABtouch
  have hBRpath := touching_path T0' R hT' hR hBRtouch
  have hRApath := touching_path R T0 hR hT hRAtouch
  obtain ⟨eAB, hxeAB, heAB⟩ := SimpleGridPathVertexIncidentEdge
    _ _ hABpath E.point hABvertex
  obtain ⟨eBR, hxeBR, heBR⟩ := SimpleGridPathVertexIncidentEdge
    _ _ hBRpath E.point hBRvertex
  obtain ⟨eRA, hxeRA, heRA⟩ := SimpleGridPathVertexIncidentEdge
    _ _ hRApath E.point hRAvertex
  have heABraw : eAB ∈ FootprintEdges T0 ∩ FootprintEdges T0' := by
    rw [CellDisjointCommonEdgesBoundary T0 T0' hdis]
    exact heAB
  have heBRraw : eBR ∈ FootprintEdges T0' ∩ FootprintEdges R := by
    rw [CellDisjointCommonEdgesBoundary T0' R hBR]
    exact heBR
  have heRAraw : eRA ∈ FootprintEdges R ∩ FootprintEdges T0 := by
    rw [CellDisjointCommonEdgesBoundary R T0 hAR.symm]
    exact heRA
  obtain ⟨jAB, heABat, htransAB⟩ :=
    P3102T2CommonEdgeSectorTransition T0 T0' E.point eAB hdis hxeAB heABraw
  obtain ⟨jBR, heBRat, htransBR⟩ :=
    P3102T2CommonEdgeSectorTransition T0' R E.point eBR hBR hxeBR heBRraw
  obtain ⟨jRA, heRAat, htransRA⟩ :=
    P3102T2CommonEdgeSectorTransition R T0 E.point eRA hAR.symm hxeRA heRAraw
  have hABBR := transition_indices_ne T0 T0' R E.point jAB jBR
    htransAB htransBR hdis hBR hAR
  have hBRRA := transition_indices_ne T0' R T0 E.point jBR jRA
    htransBR htransRA hBR hAR.symm hdis.symm
  have hRAAB := transition_indices_ne R T0 T0' E.point jRA jAB
    htransRA htransAB hAR.symm hdis hBR.symm
  exact ⟨eAB, eBR, eRA, jAB, jBR, jRA, hxeAB, heABraw, heABat,
    hxeBR, heBRraw, heBRat, hxeRA, heRAraw, heRAat,
    htransAB, htransBR, htransRA, hABBR, hBRRA, hRAAB⟩

private theorem triple_sector_cover :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), (LatticeTile T0) → ((LatticeTile T0') → (∀ (R :
            ProtoTile), (LatticeTile R) → ((TouchingTriple T0 T0' R) → (∀ (x : GaussianInt), (x ∈
            FootprintVertices T0 ∩ FootprintVertices T0' ∩
            FootprintVertices R) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈ T0.cells ∨
                LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j ∈
                R.cells))))) ) := by
  classical
  intro T0 T0' hT hT' R hR htriple x hx
  exact (LocalLatticeInterfaceSectors.1 T0 T0' R x hT hT' hR
    htriple hx).1



private theorem label_R :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4), (Disjoint T0.cells R.cells) →
            ((Disjoint T0'.cells R.cells) → ((LatticeVertexIncidentCell x j ∈ R.cells) →
            (outerLabel x j = 2))) ) := by
  classical
  intro T0 T0' outerLabel R x j hR0 hR1 hc
  have hn0 : LatticeVertexIncidentCell x j ∉ T0.cells :=
    Finset.disjoint_left.mp hR0.symm hc
  have hn1 : LatticeVertexIncidentCell x j ∉ T0'.cells :=
    Finset.disjoint_left.mp hR1.symm hc
  simp [outerLabel, hn0, hn1]

private theorem label_mem :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (∀ (R :
            ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨
              LatticeVertexIncidentCell x j ∈ T0'.cells ∨
              LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧
                  LatticeVertexIncidentCell x j ∈ T0.cells) ∨ (outerLabel x j = 1 ∧
                  LatticeVertexIncidentCell x j ∈ T0'.cells) ∨ (outerLabel x j = 2 ∧
                  LatticeVertexIncidentCell x j ∈ R.cells)))) ) := by
  classical
  intro T0 T0' outerLabel label_T0 label_T0' R x hexhaust j
  by_cases h0 : LatticeVertexIncidentCell x j ∈ T0.cells
  · exact Or.inl ⟨label_T0 x j h0, h0⟩
  · by_cases h1 : LatticeVertexIncidentCell x j ∈ T0'.cells
    · exact Or.inr (Or.inl ⟨label_T0' x j h1, h1⟩)
    · rcases hexhaust j with h0' | h1' | hR
      · exact (h0 h0').elim
      · exact (h1 h1').elim
      · exact Or.inr (Or.inr ⟨by simp [outerLabel, h0, h1], hR⟩)

private theorem label_eq_two_mem :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧ LatticeVertexIncidentCell x j ∈
            T0.cells) ∨ (outerLabel x j = 1 ∧ LatticeVertexIncidentCell x j ∈ T0'.cells) ∨
            (outerLabel x j = 2 ∧ LatticeVertexIncidentCell x j ∈ R.cells))) → (∀ (R :
            ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨
              LatticeVertexIncidentCell x j ∈ T0'.cells ∨
              LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 2) →
                  (LatticeVertexIncidentCell x j ∈ R.cells))) ) := by
  classical
  intro T0 T0' outerLabel label_mem R x hexhaust j h
  rcases label_mem R x hexhaust j with h0 | h1 | h2
  · rw [h0.1] at h
    exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
  · rw [h1.1] at h
    exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h)
  · exact h2.2

private theorem label_eq_zero_mem :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧ LatticeVertexIncidentCell x j ∈
            T0.cells) ∨ (outerLabel x j = 1 ∧ LatticeVertexIncidentCell x j ∈ T0'.cells) ∨
            (outerLabel x j = 2 ∧ LatticeVertexIncidentCell x j ∈ R.cells))) → (∀ (R :
            ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨
              LatticeVertexIncidentCell x j ∈ T0'.cells ∨
              LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0) →
                  (LatticeVertexIncidentCell x j ∈ T0.cells))) ) := by
  classical
  intro T0 T0' outerLabel label_mem R x hexhaust j h
  rcases label_mem R x hexhaust j with h0 | h1 | h2
  · exact h0.2
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 0)
      (h1.1.symm.trans h))
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 0)
      (h2.1.symm.trans h))

private theorem label_eq_one_mem :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧ LatticeVertexIncidentCell x j ∈
            T0.cells) ∨ (outerLabel x j = 1 ∧ LatticeVertexIncidentCell x j ∈ T0'.cells) ∨
            (outerLabel x j = 2 ∧ LatticeVertexIncidentCell x j ∈ R.cells))) → (∀ (R :
            ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨
              LatticeVertexIncidentCell x j ∈ T0'.cells ∨
              LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 1) →
                  (LatticeVertexIncidentCell x j ∈ T0'.cells))) ) := by
  classical
  intro T0 T0' outerLabel label_mem R x hexhaust j h
  rcases label_mem R x hexhaust j with h0 | h1 | h2
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1)
      (h0.1.symm.trans h))
  · exact h1.2
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 1)
      (h2.1.symm.trans h))

private theorem label_side_mem :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∧ LatticeVertexIncidentCell x j ∈
            T0.cells) ∨ (outerLabel x j = 1 ∧ LatticeVertexIncidentCell x j ∈ T0'.cells) ∨
            (outerLabel x j = 2 ∧ LatticeVertexIncidentCell x j ∈ R.cells))) → (∀ (R :
            ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨
              LatticeVertexIncidentCell x j ∈ T0'.cells ∨
              LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∨
                  outerLabel x j = 1) → (LatticeVertexIncidentCell x j ∈ T0.cells ∨
                  LatticeVertexIncidentCell x j ∈ T0'.cells))) ) := by
  classical
  intro T0 T0' outerLabel label_mem R x hexhaust j h
  rcases label_mem R x hexhaust j with h0 | h1 | h2
  · exact Or.inl h0.2
  · exact Or.inr h1.2
  · rcases h with h | h
    · exact False.elim ((by decide : (0 : Fin 3) ≠ 2)
        (h.symm.trans h2.1))
    · exact False.elim ((by decide : (1 : Fin 3) ≠ 2)
        (h.symm.trans h2.1))

private theorem owner_eq_endpoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), ∀ (R :
            ProtoTile), ∀ (endpointIndex : ι), (P.tile endpointIndex = R) → ((∀ (c :
            GaussianInt), ∀ (a : ι), (c ∈ (P.tile a).cells) → (owner c = a)) → (∀ (x :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ R.cells) → (owner
            (LatticeVertexIncidentCell x j) = endpointIndex))) ) := by
  classical
  intro ι P owner R endpointIndex hRidx owner_unique x j hc
  apply owner_unique
  simpa [hRidx] using hc

private theorem owner_repeat_at :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), (∀ (x : GaussianInt), owner
            (LatticeVertexIncidentCell x (0 : Fin (4 : ℕ))) = owner (LatticeVertexIncidentCell x
            (1 : Fin (4 : ℕ))) ∨ owner (LatticeVertexIncidentCell x (0 : Fin (4 : ℕ))) = owner
            (LatticeVertexIncidentCell x (2 : Fin (4 : ℕ))) ∨ owner (LatticeVertexIncidentCell x
            (0 : Fin (4 : ℕ))) = owner (LatticeVertexIncidentCell x (3 : Fin (4 : ℕ))) ∨ owner
            (LatticeVertexIncidentCell x (1 : Fin (4 : ℕ))) = owner (LatticeVertexIncidentCell x
            (2 : Fin (4 : ℕ))) ∨ owner (LatticeVertexIncidentCell x (1 : Fin (4 : ℕ))) = owner
            (LatticeVertexIncidentCell x (3 : Fin (4 : ℕ))) ∨ owner (LatticeVertexIncidentCell x
            (2 : Fin (4 : ℕ))) = owner (LatticeVertexIncidentCell x (3 : Fin (4 : ℕ)))) → (∀ (x :
            GaussianInt), ∀ (j : Fin 4), owner (LatticeVertexIncidentCell x j) = owner
            (LatticeVertexIncidentCell x (j + 1)) ∨ owner (LatticeVertexIncidentCell x j) = owner
            (LatticeVertexIncidentCell x (j + 2)) ∨ owner (LatticeVertexIncidentCell x j) = owner
            (LatticeVertexIncidentCell x (j + 3)) ∨ owner (LatticeVertexIncidentCell x (j + 1)) =
            owner (LatticeVertexIncidentCell x (j + 2)) ∨ owner (LatticeVertexIncidentCell x (j +
            1)) = owner (LatticeVertexIncidentCell x (j + 3)) ∨ owner (LatticeVertexIncidentCell
            x (j + 2)) = owner (LatticeVertexIncidentCell x (j + 3))) ) := by
  classical
  intro ι owner owner_no_fourfold x j
  let occ : Fin 4 → ι := fun i =>
    owner (LatticeVertexIncidentCell x i)
  have h := owner_no_fourfold x
  change occ 0 = occ 1 ∨ occ 0 = occ 2 ∨ occ 0 = occ 3 ∨
    occ 1 = occ 2 ∨ occ 1 = occ 3 ∨ occ 2 = occ 3 at h
  fin_cases j
  · exact h
  · rcases h with h01 | h02 | h03 | h12 | h13 | h23
    · exact Or.inr (Or.inr (Or.inl h01.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h02.symm))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h03.symm))))
    · exact Or.inl h12
    · exact Or.inr (Or.inl h13)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h23)))
  · rcases h with h01 | h02 | h03 | h12 | h13 | h23
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h01))))
    · exact Or.inr (Or.inl h02.symm)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h03.symm)))
    · exact Or.inr (Or.inr (Or.inl h12.symm))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h13.symm))))
    · exact Or.inl h23
  · rcases h with h01 | h02 | h03 | h12 | h13 | h23
    · exact Or.inr (Or.inr (Or.inr (Or.inl h01)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h02))))
    · exact Or.inl h03.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h12))))
    · exact Or.inr (Or.inl h13.symm)
    · exact Or.inr (Or.inr (Or.inl h23.symm))

private theorem owner_ne_T0_index :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), (Disjoint T0.cells T0'.cells) → (∀ (c : GaussianInt), ∀ (a : ι),
            ((P.tile a).cells ⊆ T0.cells) → ((c ∈ T0'.cells) → (owner c ≠ a)))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' hdis c a hsub hc heq
  have hcP := (owner_mem_iff c a).2 heq
  exact (Finset.disjoint_left.mp hdis) (hsub hcP) hc

private theorem owner_ne_T0'_index :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), (Disjoint T0.cells T0'.cells) → (∀ (c : GaussianInt), ∀ (a : ι),
            ((P.tile a).cells ⊆ T0'.cells) → ((c ∈ T0.cells) → (owner c ≠ a)))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' hdis c a hsub hc heq
  have hcP := (owner_mem_iff c a).2 heq
  exact (Finset.disjoint_left.mp hdis.symm) (hsub hcP) hc

private theorem owner_ne_endpoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), ∀ (R : ProtoTile), (Disjoint T0.cells R.cells) → ((Disjoint
            T0'.cells R.cells) → (∀ (endpointIndex : ι), (P.tile endpointIndex = R) → (∀ (x :
            GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠
                endpointIndex))))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' R hTm hT'm endpointIndex hRidx x j hside heq
  have hcP := (owner_mem_iff (LatticeVertexIncidentCell x j) endpointIndex).2 heq
  have hcR : LatticeVertexIncidentCell x j ∈ R.cells := by
    simpa [hRidx] using hcP
  rcases hside with hside | hside
  · exact (Finset.disjoint_left.mp hTm) hside hcR
  · exact (Finset.disjoint_left.mp hT'm) hside hcR

private theorem hdisUV :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (Disjoint
            T0.cells T0'.cells) → ((U.cells ⊆ T0.cells) → ((V.cells ⊆ T0'.cells) → (Disjoint
            U.cells V.cells))) ) := by
  classical
  intro T0 T0' U V hdis hUsub hVsub
  apply Finset.disjoint_left.mpr
  intro c hcU hcV
  exact (Finset.disjoint_left.mp hdis) (hUsub hcU) (hVsub hcV)

private theorem hsectorEdge :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (ia
            : ι), ∀ (ib : ι), (P.tile ia = U) → ((P.tile ib = V) → (∀ (x : GaussianInt), ∀ (jEdge
            : Fin (4 : ℕ)), (LatticeVertexIncidentCell x jEdge ∈ U.cells ∧
            LatticeVertexIncidentCell x (jEdge + (1 : Fin (4 : ℕ))) ∈ V.cells ∨
            LatticeVertexIncidentCell x jEdge ∈ V.cells ∧ LatticeVertexIncidentCell x (jEdge + (1
            : Fin (4 : ℕ))) ∈ U.cells) → ((LatticeVertexIncidentCell x jEdge ∈ (P.tile ia).cells
            ∧ LatticeVertexIncidentCell x (jEdge + 1) ∈ (P.tile ib).cells) ∨
            (LatticeVertexIncidentCell x jEdge ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x
            (jEdge + 1) ∈ (P.tile ia).cells)))) ) := by
  classical
  intro ι P U V ia ib hUidx hVidx x jEdge htransition
  simpa [hUidx, hVidx] using htransition

private theorem hjABEdge :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (y : GaussianInt),
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + ⟨0, 1⟩}, {x - 1, x},
            {x - ⟨0, 1⟩, x}, {x, x + 1}]
        (∀ (x : GaussianInt), ∀ {j : Fin 4}, ∀ {k : Fin 4}, (edgeAt x j = edgeAt x k) → (j = k))
            → (∀ (jEdge : Fin (4 : ℕ)), ∀ (eAB : Finset GaussianInt), ∀ (jAB : Fin (4 : ℕ)), (eAB
            = {x, y}) → ((eAB = edgeAt x jAB) → ((({x, y} : Finset GaussianInt) = edgeAt x jEdge)
            → (jAB = jEdge)))) ) := by
  classical
  intro x y edgeAt edgeAt_injective jEdge eAB jAB hABedge_eq hABatx hedgeAtx
  apply edgeAt_injective x
  calc
    edgeAt x jAB = eAB := hABatx.symm
    _ = {x, y} := hABedge_eq
    _ = edgeAt x jEdge := hedgeAtx

private theorem hlabelAB :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (∀ (jAB : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jAB ∈ T0.cells ∧ LatticeVertexIncidentCell x
            (jAB + (1 : Fin (4 : ℕ))) ∈ T0'.cells ∨ LatticeVertexIncidentCell x jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell x (jAB + (1 : Fin (4 : ℕ))) ∈ T0.cells) →
            (({outerLabel x jAB, outerLabel x (jAB + 1)} : Finset (Fin 3)) = {0, 1}))) ) := by
  classical
  intro T0 T0' x outerLabel label_T0 label_T0' jAB htransABx
  rcases htransABx with h | h
  · rw [label_T0 x jAB h.1,
      label_T0' x (jAB + 1) h.2]
  · rw [label_T0' x jAB h.1,
      label_T0 x (jAB + 1) h.2]
    try simp [Finset.pair_comm]

private theorem hlabelBR :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (R : ProtoTile), (Disjoint T0.cells R.cells) →
            ((Disjoint T0'.cells R.cells) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0'.cells) →
            (outerLabel x j = 1)) → ((∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4),
            (Disjoint T0.cells R.cells) → ((Disjoint T0'.cells R.cells) →
            ((LatticeVertexIncidentCell x j ∈ R.cells) → (outerLabel x j = 2)))) → (∀ (jBR : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jBR ∈ T0'.cells ∧ LatticeVertexIncidentCell x
            (jBR + (1 : Fin (4 : ℕ))) ∈ R.cells ∨ LatticeVertexIncidentCell x jBR ∈ R.cells ∧
            LatticeVertexIncidentCell x (jBR + (1 : Fin (4 : ℕ))) ∈ T0'.cells) →
            (({outerLabel x jBR, outerLabel x (jBR + 1)} : Finset (Fin 3)) = {1, 2}))))) ) := by
  classical
  intro T0 T0' R hTm hT'm x outerLabel label_T0' label_R jBR htransBRx
  rcases htransBRx with h | h
  · rw [label_T0' x jBR h.1,
      label_R R x (jBR + 1) hTm hT'm h.2]
  · rw [label_R R x jBR hTm hT'm h.1,
      label_T0' x (jBR + 1) h.2]
    try simp [Finset.pair_comm]

private theorem hlabelRA :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (R : ProtoTile), (Disjoint T0.cells R.cells) →
            ((Disjoint T0'.cells R.cells) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (R : ProtoTile), ∀ (x : GaussianInt), ∀ (j : Fin 4),
            (Disjoint T0.cells R.cells) → ((Disjoint T0'.cells R.cells) →
            ((LatticeVertexIncidentCell x j ∈ R.cells) → (outerLabel x j = 2)))) → (∀ (jRA : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jRA ∈ R.cells ∧ LatticeVertexIncidentCell x
            (jRA + (1 : Fin (4 : ℕ))) ∈ T0.cells ∨ LatticeVertexIncidentCell x jRA ∈ T0.cells ∧
            LatticeVertexIncidentCell x (jRA + (1 : Fin (4 : ℕ))) ∈ R.cells) →
            (({outerLabel x jRA, outerLabel x (jRA + 1)} : Finset (Fin 3)) = {2, 0}))))) ) := by
  classical
  intro T0 T0' R hTm hT'm x outerLabel label_T0 label_R jRA htransRAx
  rcases htransRAx with h | h
  · rw [label_R R x jRA hTm hT'm h.1,
      label_T0 x (jRA + 1) h.2]
  · rw [label_T0 x jRA h.1,
      label_R R x (jRA + 1) hTm hT'm h.2]
    try simp [Finset.pair_comm]

private theorem hlabelGood :
    (by
      classical
        exact
        ∀ (T0 : ProtoTile),
          ∀ (T0' : ProtoTile),
            ∀ (R : ProtoTile),
              (Disjoint T0.cells R.cells) →
                ((Disjoint T0'.cells R.cells) →
                  (∀ (x : GaussianInt),
                    (∀ (z : GaussianInt),
                        z = x ∨
                            z = x + (1 : GaussianInt) ∨
                              z = x - (1 : GaussianInt) ∨
                                z = x + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                  z = x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                          z ∈ FootprintVertices T0 ∨ z ∈ FootprintVertices T0') →
                      ((∀ (E : ProtoTile),
                          ∀ (x : GaussianInt),
                            ∀ (j : Fin 4),
                              (x ∈ FootprintVertices T0) →
                                ((x ∈ FootprintVertices T0') →
                                  ((∀ y,
                                      y = x ∨
                                          y = x + 1 ∨
                                            y = x - 1 ∨
                                              y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                        y ∈ FootprintVertices T0 ∨
                                          y ∈ FootprintVertices T0') →
                                    ((Disjoint E.cells T0.cells) →
                                      ((Disjoint E.cells T0'.cells) →
                                        ((LatticeVertexIncidentCell x j ∈ E.cells) →
                                          ((LatticeVertexIncidentCell x (j + 1) ∈
                                              E.cells) →
                                            (False)))))))) →
                        (let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
                          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
                          else
                            if LatticeVertexIncidentCell x j ∈ T0'.cells then 1
                            else 2;
                        (∀ (R : ProtoTile),
                            ∀ (x : GaussianInt),
                              (∀ j : Fin 4,
                                  LatticeVertexIncidentCell x j ∈ T0.cells ∨
                                    LatticeVertexIncidentCell x j ∈ T0'.cells ∨
                                      LatticeVertexIncidentCell x j ∈ R.cells) →
                                (∀ (j : Fin 4),
                                  (outerLabel x j = 2) →
                                    (LatticeVertexIncidentCell x j ∈ R.cells))) →
                          ((x ∈
                              FootprintVertices T0 ∩ FootprintVertices T0' ∩
                                FootprintVertices R) →
                            ((∀ (j : Fin (4 : ℕ)),
                                LatticeVertexIncidentCell x j ∈ T0.cells ∨
                                  LatticeVertexIncidentCell x j ∈ T0'.cells ∨
                                    LatticeVertexIncidentCell x j ∈ R.cells) →
                              (∀ (jAB : Fin (4 : ℕ)),
                                ((outerLabel x (jAB + (2 : Fin (4 : ℕ))) =
                                        (2 : Fin (3 : ℕ)) ∧
                                      outerLabel x (jAB + (3 : Fin (4 : ℕ))) =
                                        outerLabel x jAB ∨
                                    outerLabel x (jAB + (3 : Fin (4 : ℕ))) =
                                          (2 : Fin (3 : ℕ)) ∧
                                        outerLabel x (jAB + (2 : Fin (4 : ℕ))) =
                                          outerLabel x (jAB + (1 : Fin (4 : ℕ))) ∨
                                      outerLabel x (jAB + (2 : Fin (4 : ℕ))) =
                                            (2 : Fin (3 : ℕ)) ∧
                                          outerLabel x (jAB + (3 : Fin (4 : ℕ))) =
                                            (2 : Fin (3 : ℕ)) ∨
                                        outerLabel x (jAB + (3 : Fin (4 : ℕ))) =
                                            (2 : Fin (3 : ℕ)) ∧
                                          outerLabel x jAB = (2 : Fin (3 : ℕ))) →
                                  ((outerLabel x (jAB + 2) = 2 ∧
                                      outerLabel x (jAB + 3) = outerLabel x jAB) ∨
                                    (outerLabel x (jAB + 3) = 2 ∧
                                      outerLabel x (jAB + 2) =
                                        outerLabel x (jAB + 1)))))))))))) := by
  classical
  intro T0 T0' R hTm hT'm x hstar endpoint_repeat_impossible outerLabel label_eq_two_mem
      hxTriple hsectorCover jAB hlabelPattern
  rcases hlabelPattern with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hfalse := endpoint_repeat_impossible R x (jAB + 2)
      hxTriple.1.1 hxTriple.1.2 hstar hTm.symm hT'm.symm
      (label_eq_two_mem R x hsectorCover (jAB + 2) h.1)
      (by
        have heq : jAB + 2 + 1 = jAB + 3 := by omega
        simpa [heq] using
          label_eq_two_mem R x hsectorCover (jAB + 3) h.2)
    exact False.elim hfalse
  · have hfalse := endpoint_repeat_impossible R x (jAB + 3)
      hxTriple.1.1 hxTriple.1.2 hstar hTm.symm hT'm.symm
      (label_eq_two_mem R x hsectorCover (jAB + 3) h.1)
      (by
        have heq : jAB + 3 + 1 = jAB := by
          fin_cases jAB <;> decide
        simpa [heq] using label_eq_two_mem R x hsectorCover jAB h.2)
    exact False.elim hfalse

private theorem hsectorAB :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (ia : ι), ∀ (ib : ι), ∀ (x : GaussianInt),
            ∀ (jEdge : Fin (4 : ℕ)), ((LatticeVertexIncidentCell x jEdge ∈ (P.tile ia).cells ∧
            LatticeVertexIncidentCell x (jEdge + 1) ∈ (P.tile ib).cells) ∨
            (LatticeVertexIncidentCell x jEdge ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x
            (jEdge + 1) ∈ (P.tile ia).cells)) → (∀ (jAB : Fin (4 : ℕ)), (jAB = jEdge) →
            ((LatticeVertexIncidentCell x jAB ∈ (P.tile ia).cells ∧ LatticeVertexIncidentCell x
            (jAB + 1) ∈ (P.tile ib).cells) ∨ (LatticeVertexIncidentCell x jAB ∈ (P.tile ib).cells
            ∧ LatticeVertexIncidentCell x (jAB + 1) ∈ (P.tile ia).cells))) ) := by
  classical
  intro ι P ia ib x jEdge hsectorEdge jAB hjABEdge
  simpa [hjABEdge] using hsectorEdge

private theorem hownerAB :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ∀ (ia : ι), ∀ (ib : ι), (P.tile ia = U) → ((P.tile ib
            = V) → (∀ (x : GaussianInt), (∀ (c : GaussianInt), ∀ (a : ι), (c ∈ (P.tile a).cells)
            → (owner c = a)) → (∀ (jAB : Fin (4 : ℕ)), ((LatticeVertexIncidentCell x jAB ∈
            (P.tile ia).cells ∧ LatticeVertexIncidentCell x (jAB + 1) ∈ (P.tile ib).cells) ∨
            (LatticeVertexIncidentCell x jAB ∈ (P.tile ib).cells ∧ LatticeVertexIncidentCell x
            (jAB + 1) ∈ (P.tile ia).cells)) → ((owner (LatticeVertexIncidentCell x jAB) = ia ∧
            owner (LatticeVertexIncidentCell x (jAB + 1)) = ib) ∨ (owner
            (LatticeVertexIncidentCell x jAB) = ib ∧ owner (LatticeVertexIncidentCell x (jAB +
            1)) = ia))))) ) := by
  classical
  intro ι P owner U V ia ib hUidx hVidx x owner_unique jAB hsectorAB
  rcases hsectorAB with h | h
  · exact Or.inl ⟨owner_unique _ _ (by simpa [hUidx] using h.1),
      owner_unique _ _ (by simpa [hVidx] using h.2)⟩
  · exact Or.inr ⟨owner_unique _ _ (by simpa [hVidx] using h.1),
      owner_unique _ _ (by simpa [hUidx] using h.2)⟩

private theorem hownerAligned :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (Disjoint T0.cells
            T0'.cells) → (∀ (ia : ι), ∀ (ib : ι), (P.tile ia = U) → ((P.tile ib = V) → ((U.cells
            ⊆ T0.cells) → ((V.cells ⊆ T0'.cells) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (∀ (jAB : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jAB ∈ T0.cells ∧ LatticeVertexIncidentCell x
            (jAB + (1 : Fin (4 : ℕ))) ∈ T0'.cells ∨ LatticeVertexIncidentCell x jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell x (jAB + (1 : Fin (4 : ℕ))) ∈ T0.cells) → (((owner
            (LatticeVertexIncidentCell x jAB) = ia ∧ owner (LatticeVertexIncidentCell x (jAB +
            1)) = ib) ∨ (owner (LatticeVertexIncidentCell x jAB) = ib ∧ owner
            (LatticeVertexIncidentCell x (jAB + 1)) = ia)) → ((outerLabel x jAB = 0 ∧ owner
            (LatticeVertexIncidentCell x jAB) = ia ∧ owner (LatticeVertexIncidentCell x (jAB +
            1)) = ib) ∨ (outerLabel x jAB = 1 ∧ owner (LatticeVertexIncidentCell x jAB) = ib ∧
            owner (LatticeVertexIncidentCell x (jAB + 1)) = ia))))))))))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' U V hdis ia ib hUidx hVidx hUsub hVsub x outerLabel
      label_T0 label_T0' jAB htransABx hownerAB
  rcases htransABx with h | h
  · left
    refine ⟨label_T0 x jAB h.1, ?_⟩
    rcases hownerAB with hab | hba
    · exact hab
    · have hc := (owner_mem_iff (LatticeVertexIncidentCell x jAB) ib).2 hba.1
      have hc' : LatticeVertexIncidentCell x jAB ∈ T0'.cells := by
        rw [hVidx] at hc
        exact hVsub hc
      exact False.elim ((Finset.disjoint_left.mp hdis) h.1 hc')
  · right
    refine ⟨label_T0' x jAB h.1, ?_⟩
    rcases hownerAB with hab | hba
    · have hc := (owner_mem_iff (LatticeVertexIncidentCell x jAB) ia).2 hab.1
      have hc' : LatticeVertexIncidentCell x jAB ∈ T0.cells := by
        rw [hUidx] at hc
        exact hUsub hc
      exact False.elim ((Finset.disjoint_left.mp hdis.symm) h.1 hc')
    · exact hba

private theorem hlabelsAB :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (x : GaussianInt), ∀ (j : Fin 4), (LatticeVertexIncidentCell x j ∈ T0.cells) →
            (outerLabel x j = 0)) → ((∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0'.cells) → (outerLabel x j = 1)) → (∀ (jAB : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jAB ∈ T0.cells ∧ LatticeVertexIncidentCell x
            (jAB + (1 : Fin (4 : ℕ))) ∈ T0'.cells ∨ LatticeVertexIncidentCell x jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell x (jAB + (1 : Fin (4 : ℕ))) ∈ T0.cells) → ((outerLabel x
            jAB = 0 ∧ outerLabel x (jAB + 1) = 1) ∨ (outerLabel x jAB = 1 ∧ outerLabel x (jAB +
            1) = 0)))) ) := by
  classical
  intro T0 T0' x outerLabel label_T0 label_T0' jAB htransABx
  rcases htransABx with h | h
  · exact Or.inl ⟨label_T0 x jAB h.1,
      label_T0' x (jAB + 1) h.2⟩
  · exact Or.inr ⟨label_T0' x jAB h.1,
      label_T0 x (jAB + 1) h.2⟩

private theorem hownerAligned' :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (ia
            : ι), ∀ (ib : ι), ∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (jAB : Fin (4 : ℕ)), ((outerLabel x jAB = 0 ∧ owner (LatticeVertexIncidentCell x jAB) =
            ia ∧ owner (LatticeVertexIncidentCell x (jAB + 1)) = ib) ∨ (outerLabel x jAB = 1 ∧
            owner (LatticeVertexIncidentCell x jAB) = ib ∧ owner (LatticeVertexIncidentCell x
            (jAB + 1)) = ia)) → (
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        (outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            ) := by
  classical
  intro ι owner T0 T0' ia ib x outerLabel jAB hownerAligned o0 o1
  simpa [o0, o1] using hownerAligned

private theorem hownerRepeat :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀
            (j : Fin 4), owner (LatticeVertexIncidentCell x j) = owner (LatticeVertexIncidentCell
            x (j + 1)) ∨ owner (LatticeVertexIncidentCell x j) = owner (LatticeVertexIncidentCell
            x (j + 2)) ∨ owner (LatticeVertexIncidentCell x j) = owner (LatticeVertexIncidentCell
            x (j + 3)) ∨ owner (LatticeVertexIncidentCell x (j + 1)) = owner
            (LatticeVertexIncidentCell x (j + 2)) ∨ owner (LatticeVertexIncidentCell x (j + 1)) =
            owner (LatticeVertexIncidentCell x (j + 3)) ∨ owner (LatticeVertexIncidentCell x (j +
            2)) = owner (LatticeVertexIncidentCell x (j + 3))) → (∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        o0 = o1 ∨ o0 = o2 ∨ o0 = o3 ∨ o1 = o2 ∨ o1 = o3 ∨ o2 = o3) ) := by
  classical
  intro ι owner x owner_repeat_at jAB o0 o1 o2 o3
  simpa [o0, o1, o2, o3] using owner_repeat_at x jAB

private theorem hcell3side :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (R
            : ProtoTile), ∀ (ia : ι), ∀ (ib : ι), ∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∨ outerLabel x j = 1) →
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells))) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j ∈ R.cells)
            → (∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((outerLabel x (jAB + (2 : Fin (4 : ℕ))) = (2 : Fin (3 : ℕ)) ∧ outerLabel x (jAB +
            (3 : Fin (4 : ℕ))) = outerLabel x jAB) → (LatticeVertexIncidentCell x (jAB + 3) ∈
            T0.cells ∨ LatticeVertexIncidentCell x (jAB + 3) ∈ T0'.cells)))) ) := by
  classical
  intro ι owner T0 T0' R ia ib x outerLabel label_side_mem hsectorCover jAB o0 o1 hownerAligned'
      hGood
  rcases hownerAligned' with hA | hA
  · apply label_side_mem R x hsectorCover (jAB + 3)
    exact Or.inl (hGood.2.trans hA.1)
  · apply label_side_mem R x hsectorCover (jAB + 3)
    exact Or.inr (hGood.2.trans hA.1)

private theorem hside0At763 :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (x : GaussianInt), ∀ (jAB : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jAB ∈ T0.cells ∧ LatticeVertexIncidentCell x (jAB + (1 :
            Fin (4 : ℕ))) ∈ T0'.cells ∨ LatticeVertexIncidentCell x jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell x (jAB + (1 : Fin (4 : ℕ))) ∈ T0.cells) →
            (LatticeVertexIncidentCell x jAB ∈ T0.cells ∨ LatticeVertexIncidentCell x jAB ∈
            T0'.cells) ) := by
  classical
  intro T0 T0' x jAB htransABx
  rcases htransABx with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem hside1At768 :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (x : GaussianInt), ∀ (jAB : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jAB ∈ T0.cells ∧ LatticeVertexIncidentCell x (jAB + (1 :
            Fin (4 : ℕ))) ∈ T0'.cells ∨ LatticeVertexIncidentCell x jAB ∈ T0'.cells ∧
            LatticeVertexIncidentCell x (jAB + (1 : Fin (4 : ℕ))) ∈ T0.cells) →
            (LatticeVertexIncidentCell x (jAB + 1) ∈ T0.cells ∨ LatticeVertexIncidentCell x (jAB
            + 1) ∈ T0'.cells) ) := by
  classical
  intro T0 T0' x jAB htransABx
  rcases htransABx with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

private theorem ho01neAt773 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (ia
            : ι), ∀ (ib : ι), (ia ≠ ib) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → (o0 ≠ o1)) ) := by
  classical
  intro ι owner T0 T0' ia ib hidxne x outerLabel jAB o0 o1 hownerAligned' heq
  rcases hownerAligned' with hA | hA
  · exact hidxne (hA.2.1.symm.trans (heq.trans hA.2.2))
  · exact hidxne (hA.2.1.symm.trans (heq.trans hA.2.2)).symm

private theorem ho02neAt778 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        (o2 = endpointIndex) → ((LatticeVertexIncidentCell x jAB ∈ T0.cells ∨
            LatticeVertexIncidentCell x jAB ∈ T0'.cells) → (o0 ≠ o2))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o0 o2 ho2 hside0 heq
  exact owner_ne_endpoint x jAB hside0 (heq.trans ho2)

private theorem ho12ne :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        (o2 = endpointIndex) → ((LatticeVertexIncidentCell x (jAB + 1) ∈ T0.cells ∨
            LatticeVertexIncidentCell x (jAB + 1) ∈ T0'.cells) → (o1 ≠ o2))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o1 o2 ho2 hside1 heq
  exact owner_ne_endpoint x (jAB + 1) hside1 (heq.trans ho2)

private theorem ho13neAt784 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), ∀ (T0 :
            ProtoTile), ∀ (T0' : ProtoTile), ∀ (R : ProtoTile), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (ia : ι), ∀ (ib : ι), (P.tile ia = U) → ((P.tile ib = V) → ((U.cells ⊆
            T0.cells) → ((V.cells ⊆ T0'.cells) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0) → (LatticeVertexIncidentCell x j ∈
            T0.cells))) → ((∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells
            ∨ LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 1) →
            (LatticeVertexIncidentCell x j ∈ T0'.cells))) → ((∀ (c : GaussianInt), ∀ (a : ι),
            ((P.tile a).cells ⊆ T0.cells) → ((c ∈ T0'.cells) → (owner c ≠ a))) → ((∀ (c :
            GaussianInt), ∀ (a : ι), ((P.tile a).cells ⊆ T0'.cells) → ((c ∈ T0.cells) → (owner c
            ≠ a))) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j ∈ R.cells)
            → (∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((outerLabel x (jAB + (2 : Fin (4 : ℕ))) = (2 : Fin (3 : ℕ)) ∧ outerLabel x (jAB +
            (3 : Fin (4 : ℕ))) = outerLabel x jAB) → (o1 ≠ o3))))))))))) ) := by
  classical
  intro ι P owner T0 T0' R U V ia ib hUidx hVidx hUsub hVsub x outerLabel label_eq_zero_mem
      label_eq_one_mem owner_ne_T0_index owner_ne_T0'_index hsectorCover jAB o0 o1 o3
      hownerAligned' hGood heq
  rcases hownerAligned' with hA | hA
  · have h3 := label_eq_zero_mem R x hsectorCover
      (jAB + 3) (hGood.2.trans hA.1)
    have hVsubidx : (P.tile ib).cells ⊆ T0'.cells := by
      rw [hVidx]
      exact hVsub
    exact owner_ne_T0'_index (LatticeVertexIncidentCell x (jAB + 3))
      ib hVsubidx h3 (heq.symm.trans hA.2.2)
  · have h3 := label_eq_one_mem R x hsectorCover
      (jAB + 3) (hGood.2.trans hA.1)
    have hUsubidx : (P.tile ia).cells ⊆ T0.cells := by
      rw [hUidx]
      exact hUsub
    exact owner_ne_T0_index (LatticeVertexIncidentCell x (jAB + 3))
      ia hUsubidx h3 (heq.symm.trans hA.2.2)

private theorem ho23neAt801 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o2 = endpointIndex) → ((LatticeVertexIncidentCell x (jAB + 3) ∈ T0.cells ∨
            LatticeVertexIncidentCell x (jAB + 3) ∈ T0'.cells) → (o2 ≠ o3))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o2 o3 ho2 hcell3side heq
  exact owner_ne_endpoint x (jAB + 3) hcell3side
    (heq.symm.trans ho2)

private theorem ho03 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (x : GaussianInt), ∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o0 = o1 ∨ o0 = o2 ∨ o0 = o3 ∨ o1 = o2 ∨ o1 = o3 ∨ o2 = o3) → ((o0 ≠ o1) → ((o0 ≠ o2) →
            ((o1 ≠ o2) → ((o1 ≠ o3) → ((o2 ≠ o3) → (o0 = o3)))))) ) := by
  classical
  intro ι owner x jAB o0 o1 o2 o3 hownerRepeat ho01ne ho02ne ho12ne ho13ne ho23ne
  rcases hownerRepeat with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (ho01ne h01)
  · exact False.elim (ho02ne h02)
  · exact h03
  · exact False.elim (ho12ne h12)
  · exact False.elim (ho13ne h13)
  · exact False.elim (ho23ne h23)

private theorem hdiagAt813 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (ia : ι), ∀ (ib : ι),
            (P.tile ia = U) → ((P.tile ib = V) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((o0 = o3) → ((LatticeVertexIncidentCell x (jAB + 1) ∈ U.cells ∧
            LatticeVertexIncidentCell x (jAB + 3) ∈ V.cells) ∨ (LatticeVertexIncidentCell x (jAB
            + 1) ∈ V.cells ∧ LatticeVertexIncidentCell x (jAB + 3) ∈ U.cells)))))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' U V ia ib hUidx hVidx x outerLabel jAB o0 o1 o3
      hownerAligned' ho03
  rcases hownerAligned' with hA | hA
  · right
    constructor
    · have hc := (owner_mem_iff _ ib).2 hA.2.2
      simpa [hVidx] using hc
    · have heq : o3 = ia := ho03.symm.trans hA.2.1
      have hc := (owner_mem_iff _ ia).2 heq
      simpa [hUidx] using hc
  · left
    constructor
    · have hc := (owner_mem_iff _ ia).2 hA.2.2
      simpa [hUidx] using hc
    · have heq : o3 = ib := ho03.symm.trans hA.2.1
      have hc := (owner_mem_iff _ ib).2 heq
      simpa [hVidx] using hc

private theorem hfinalCellsAt833 :
    (by
      classical
        exact
        ∀ (U : ProtoTile),
          ∀ (V : ProtoTile),
            ∀ (x : GaussianInt),
              ∀ (jAB : Fin (4 : ℕ)),
                (((LatticeVertexIncidentCell x (jAB + 1) ∈ U.cells ∧
                      LatticeVertexIncidentCell x (jAB + 3) ∈ V.cells) ∨
                    (LatticeVertexIncidentCell x (jAB + 1) ∈ V.cells ∧
                      LatticeVertexIncidentCell x (jAB + 3) ∈ U.cells)) →
                  ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
                    (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨
                      (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
                        (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells)))) := by
  classical
  intro U V x jAB hdiag
  rcases hdiag with hdiag | hdiag
  · fin_cases jAB
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using hdiag)))
    · exact Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩))
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)))
    · exact Or.inl
        (by simpa [LatticeVertexIncidentCell] using hdiag)
  · fin_cases jAB
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using hdiag)))
    · exact Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)))
    · exact Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using hdiag))

private theorem hcell2side :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (R
            : ProtoTile), ∀ (ia : ι), ∀ (ib : ι), ∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0 ∨ outerLabel x j = 1) →
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells))) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j ∈ R.cells)
            → (∀ (jAB : Fin (4 : ℕ)), ((outerLabel x jAB = 0 ∧ outerLabel x (jAB + 1) = 1) ∨
            (outerLabel x jAB = 1 ∧ outerLabel x (jAB + 1) = 0)) → (
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((outerLabel x (jAB + (3 : Fin (4 : ℕ))) = (2 : Fin (3 : ℕ)) ∧ outerLabel x (jAB +
            (2 : Fin (4 : ℕ))) = outerLabel x (jAB + (1 : Fin (4 : ℕ)))) →
            (LatticeVertexIncidentCell x (jAB + 2) ∈ T0.cells ∨ LatticeVertexIncidentCell x (jAB
            + 2) ∈ T0'.cells))))) ) := by
  classical
  intro ι owner T0 T0' R ia ib x outerLabel label_side_mem hsectorCover jAB hlabelsAB o0 o1
      hownerAligned' hGood
  rcases hownerAligned' with hA | hA
  · apply label_side_mem R x hsectorCover (jAB + 2)
    rcases hlabelsAB with h | h
    · exact Or.inr (hGood.2.trans h.2)
    · exact False.elim ((by decide : (1 : Fin 3) ≠ 0)
        (h.1.symm.trans hA.1))
  · apply label_side_mem R x hsectorCover (jAB + 2)
    rcases hlabelsAB with h | h
    · exact False.elim ((by decide : (0 : Fin 3) ≠ 1)
        (h.1.symm.trans hA.1))
    · exact Or.inl (hGood.2.trans h.2)

private theorem ho02neAt895 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), ∀ (T0 :
            ProtoTile), ∀ (T0' : ProtoTile), ∀ (R : ProtoTile), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ∀ (ia : ι), ∀ (ib : ι), (P.tile ia = U) → ((P.tile ib = V) → ((U.cells ⊆
            T0.cells) → ((V.cells ⊆ T0'.cells) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        (∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4, LatticeVertexIncidentCell x j ∈
            T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j
            ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 0) → (LatticeVertexIncidentCell x j ∈
            T0.cells))) → ((∀ (R : ProtoTile), ∀ (x : GaussianInt), (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈ T0'.cells
            ∨ LatticeVertexIncidentCell x j ∈ R.cells) → (∀ (j : Fin 4), (outerLabel x j = 1) →
            (LatticeVertexIncidentCell x j ∈ T0'.cells))) → ((∀ (c : GaussianInt), ∀ (a : ι),
            ((P.tile a).cells ⊆ T0.cells) → ((c ∈ T0'.cells) → (owner c ≠ a))) → ((∀ (c :
            GaussianInt), ∀ (a : ι), ((P.tile a).cells ⊆ T0'.cells) → ((c ∈ T0.cells) → (owner c
            ≠ a))) → ((∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ T0.cells ∨
            LatticeVertexIncidentCell x j ∈ T0'.cells ∨ LatticeVertexIncidentCell x j ∈ R.cells)
            → (∀ (jAB : Fin (4 : ℕ)), ((outerLabel x jAB = 0 ∧ outerLabel x (jAB + 1) = 1) ∨
            (outerLabel x jAB = 1 ∧ outerLabel x (jAB + 1) = 0)) → (
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((outerLabel x (jAB + (3 : Fin (4 : ℕ))) = (2 : Fin (3 : ℕ)) ∧ outerLabel x (jAB +
            (2 : Fin (4 : ℕ))) = outerLabel x (jAB + (1 : Fin (4 : ℕ)))) → (o0 ≠ o2)))))))))))) )
            := by
  classical
  intro ι P owner T0 T0' R U V ia ib hUidx hVidx hUsub hVsub x outerLabel label_eq_zero_mem
      label_eq_one_mem owner_ne_T0_index owner_ne_T0'_index hsectorCover jAB hlabelsAB o0 o1 o2
      hownerAligned' hGood heq
  rcases hownerAligned' with hA | hA
  · have hUsubidx : (P.tile ia).cells ⊆ T0.cells := by
      rw [hUidx]
      exact hUsub
    have hc2 : LatticeVertexIncidentCell x (jAB + 2) ∈ T0'.cells := by
      rcases hlabelsAB with h | h
      · exact label_eq_one_mem R x hsectorCover
          (jAB + 2) (hGood.2.trans h.2)
      · exact False.elim ((by decide : (1 : Fin 3) ≠ 0)
          (h.1.symm.trans hA.1))
    exact owner_ne_T0_index (LatticeVertexIncidentCell x (jAB + 2))
      ia hUsubidx hc2 (heq.symm.trans hA.2.1)
  · have hVsubidx : (P.tile ib).cells ⊆ T0'.cells := by
      rw [hVidx]
      exact hVsub
    have hc2 : LatticeVertexIncidentCell x (jAB + 2) ∈ T0.cells := by
      rcases hlabelsAB with h | h
      · exact False.elim ((by decide : (0 : Fin 3) ≠ 1)
          (h.1.symm.trans hA.1))
      · exact label_eq_zero_mem R x hsectorCover
          (jAB + 2) (hGood.2.trans h.2)
    exact owner_ne_T0'_index (LatticeVertexIncidentCell x (jAB + 2))
      ib hVsubidx hc2 (heq.symm.trans hA.2.1)

private theorem ho03ne :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o3 = endpointIndex) → ((LatticeVertexIncidentCell x jAB ∈ T0.cells ∨
            LatticeVertexIncidentCell x jAB ∈ T0'.cells) → (o0 ≠ o3))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o0 o3 ho3 hside0 heq
  exact owner_ne_endpoint x jAB hside0 (heq.trans ho3)

private theorem ho13neAt923 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o3 = endpointIndex) → ((LatticeVertexIncidentCell x (jAB + 1) ∈ T0.cells ∨
            LatticeVertexIncidentCell x (jAB + 1) ∈ T0'.cells) → (o1 ≠ o3))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o1 o3 ho3 hside1 heq
  exact owner_ne_endpoint x (jAB + 1) hside1 (heq.trans ho3)

private theorem ho23neAt926 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀
            (endpointIndex : ι), ∀ (x : GaussianInt), (∀ (x : GaussianInt), ∀ (j : Fin 4),
            (LatticeVertexIncidentCell x j ∈ T0.cells ∨ LatticeVertexIncidentCell x j ∈
            T0'.cells) → (owner (LatticeVertexIncidentCell x j) ≠ endpointIndex)) → (∀ (jAB : Fin
            (4 : ℕ)),
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o3 = endpointIndex) → ((LatticeVertexIncidentCell x (jAB + 2) ∈ T0.cells ∨
            LatticeVertexIncidentCell x (jAB + 2) ∈ T0'.cells) → (o2 ≠ o3))) ) := by
  classical
  intro ι owner T0 T0' endpointIndex x owner_ne_endpoint jAB o2 o3 ho3 hcell2side heq
  exact owner_ne_endpoint x (jAB + 2) hcell2side
    (heq.trans ho3)

private theorem ho12 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (owner : GaussianInt → ι), ∀ (x : GaussianInt), ∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
        (o0 = o1 ∨ o0 = o2 ∨ o0 = o3 ∨ o1 = o2 ∨ o1 = o3 ∨ o2 = o3) → ((o0 ≠ o1) → ((o0 ≠ o2) →
            ((o0 ≠ o3) → ((o1 ≠ o3) → ((o2 ≠ o3) → (o1 = o2)))))) ) := by
  classical
  intro ι owner x jAB o0 o1 o2 o3 hownerRepeat ho01ne ho02ne ho03ne ho13ne ho23ne
  rcases hownerRepeat with h01 | h02 | h03 | h12 | h13 | h23
  · exact False.elim (ho01ne h01)
  · exact False.elim (ho02ne h02)
  · exact False.elim (ho03ne h03)
  · exact h12
  · exact False.elim (ho13ne h13)
  · exact False.elim (ho23ne h23)

private theorem hdiagAt938 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (owner : GaussianInt → ι), (∀ (c :
            GaussianInt), ∀ (a : ι), c ∈ (P.tile a).cells ↔ owner c = a) → (∀ (T0 : ProtoTile), ∀
            (T0' : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (ia : ι), ∀ (ib : ι),
            (P.tile ia = U) → ((P.tile ib = V) → (∀ (x : GaussianInt),
        let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
          if LatticeVertexIncidentCell x j ∈ T0.cells then 0
          else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
        ∀ (jAB : Fin (4 : ℕ)),
        let o0 := owner (LatticeVertexIncidentCell x jAB)
        let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
        let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
        ((outerLabel x jAB = 0 ∧ o0 = ia ∧ o1 = ib) ∨ (outerLabel x jAB = 1 ∧ o0 = ib ∧ o1 = ia))
            → ((o1 = o2) → ((LatticeVertexIncidentCell x jAB ∈ U.cells ∧
            LatticeVertexIncidentCell x (jAB + 2) ∈ V.cells) ∨ (LatticeVertexIncidentCell x jAB ∈
            V.cells ∧ LatticeVertexIncidentCell x (jAB + 2) ∈ U.cells)))))) ) := by
  classical
  intro ι P owner owner_mem_iff T0 T0' U V ia ib hUidx hVidx x outerLabel jAB o0 o1 o2
      hownerAligned' ho12
  rcases hownerAligned' with hA | hA
  · left
    constructor
    · have hc := (owner_mem_iff _ ia).2 hA.2.1
      simpa [hUidx] using hc
    · have heq : o2 = ib := ho12.symm.trans hA.2.2
      have hc := (owner_mem_iff _ ib).2 heq
      simpa [hVidx] using hc
  · right
    constructor
    · have hc := (owner_mem_iff _ ib).2 hA.2.1
      simpa [hVidx] using hc
    · have heq : o2 = ia := ho12.symm.trans hA.2.2
      have hc := (owner_mem_iff _ ia).2 heq
      simpa [hUidx] using hc

private theorem hfinalCellsAt958 :
    (by
      classical
        exact
        ∀ (U : ProtoTile),
          ∀ (V : ProtoTile),
            ∀ (x : GaussianInt),
              ∀ (jAB : Fin (4 : ℕ)),
                (((LatticeVertexIncidentCell x jAB ∈ U.cells ∧
                      LatticeVertexIncidentCell x (jAB + 2) ∈ V.cells) ∨
                    (LatticeVertexIncidentCell x jAB ∈ V.cells ∧
                      LatticeVertexIncidentCell x (jAB + 2) ∈ U.cells)) →
                  ((x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
                    (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨
                      (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
                        (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells)))) := by
  classical
  intro U V x jAB hdiag
  rcases hdiag with hdiag | hdiag
  · fin_cases jAB
    · exact Or.inl (by simpa [LatticeVertexIncidentCell] using hdiag)
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using hdiag)))
    · exact Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩))
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)))
  · fin_cases jAB
    · exact Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using hdiag))
    · exact Or.inr (Or.inr (Or.inr
        (by simpa [LatticeVertexIncidentCell] using hdiag)))
    · exact Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)
    · exact Or.inr (Or.inr (Or.inl
        (by simpa [LatticeVertexIncidentCell] using
          ⟨hdiag.2, hdiag.1⟩)))

end EndpointDiagonalGeometry

theorem P5635T1EndpointDiagonalOwnership {ι : Type}
    (P : PeriodicTileComplex ι) (owner : GaussianInt → ι)
    (owner_mem_iff : ∀ (c : GaussianInt) (a : ι),
      c ∈ (P.tile a).cells ↔ owner c = a)
    (owner_no_fourfold : ∀ x : GaussianInt,
      owner (LatticeVertexIncidentCell x 0) =
          owner (LatticeVertexIncidentCell x 1) ∨
        owner (LatticeVertexIncidentCell x 0) =
          owner (LatticeVertexIncidentCell x 2) ∨
        owner (LatticeVertexIncidentCell x 0) =
          owner (LatticeVertexIncidentCell x 3) ∨
        owner (LatticeVertexIncidentCell x 1) =
          owner (LatticeVertexIncidentCell x 2) ∨
        owner (LatticeVertexIncidentCell x 1) =
          owner (LatticeVertexIncidentCell x 3) ∨
        owner (LatticeVertexIncidentCell x 2) =
          owner (LatticeVertexIncidentCell x 3))
    (T0 T0' R U V : ProtoTile)
    (E : ExactTileInterfaceTriple T0 T0' R)
    (hT : LatticeTile T0) (hT' : LatticeTile T0') (hR : LatticeTile R)
    (hdis : Disjoint T0.cells T0'.cells)
    (hTm : Disjoint T0.cells R.cells) (hT'm : Disjoint T0'.cells R.cells)
    (hreg : ∀ x, x ∈ FootprintVertices T0 → ∀ y, y ∈ FootprintVertices T0 →
      FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0)
    (hreg' : ∀ x, x ∈ FootprintVertices T0' → ∀ y, y ∈ FootprintVertices T0' →
      FourNeighborAdjacent x y → {x, y} ∈ FootprintEdges T0')
    (endpointIndex ia ib : ι)
    (hRidx : P.tile endpointIndex = R)
    (hUidx : P.tile ia = U) (hVidx : P.tile ib = V)
    (hidxne : ia ≠ ib)
    (hUsub : U.cells ⊆ T0.cells) (hVsub : V.cells ⊆ T0'.cells)
    (x y : GaussianInt) (hstart : x = E.point)
    (hstar : ∀ z, z = x ∨ z = x + 1 ∨ z = x - 1 ∨
      z = x + ⟨0, 1⟩ ∨ z = x - ⟨0, 1⟩ →
      z ∈ FootprintVertices T0 ∨ z ∈ FootprintVertices T0')
    (hedgeUV : {x, y} ∈ FootprintEdges U ∩ FootprintEdges V)
    (hEndpointEdge : ∀ e, x ∈ e →
      e ∈ FootprintEdges T0 ∩ FootprintEdges T0' → e = {x, y}) :
    (x ∈ U.cells ∧ x - 1 - ⟨0, 1⟩ ∈ V.cells) ∨
      (x ∈ V.cells ∧ x - 1 - ⟨0, 1⟩ ∈ U.cells) ∨
      (x - 1 ∈ U.cells ∧ x - ⟨0, 1⟩ ∈ V.cells) ∨
      (x - 1 ∈ V.cells ∧ x - ⟨0, 1⟩ ∈ U.cells) := by
-- BODY
  classical
  have triple_label_pattern := EndpointDiagonalGeometry.triple_label_pattern
  let neighbor (x : GaussianInt) : Fin 4 → GaussianInt :=
    ![x + ⟨0, 1⟩, x - 1, x - ⟨0, 1⟩, x + 1]
  let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
    ![{x, x + ⟨0, 1⟩}, {x - 1, x},
      {x - ⟨0, 1⟩, x}, {x, x + 1}]
  have edgeAt_mem := LatticeVertexSectorFacts.edgeMembership
  have edgeAt_injective (x : GaussianInt) {j k : Fin 4}
      (h : edgeAt x j = edgeAt x k) := LatticeVertexSectorFacts.edgeInjective
          (LatticeVertexSectorFacts.neighborDistinct)
          (EndpointDiagonalGeometry.neighbor_injective) edgeAt_mem x (j := j) (k := k) h
  have endpoint_repeat_impossible := EndpointDiagonalGeometry.endpoint_repeat_impossible T0 T0'
      (EndpointDiagonalGeometry.edge_foreign_impossible edgeAt_mem edgeAt_injective
      (EndpointDiagonalGeometry.edge_of_sector_pair)) (EndpointDiagonalGeometry.star_induced_edge
      T0 T0' hreg hreg' (LatticeVertexSectorFacts.edgePair)
      (EndpointDiagonalGeometry.neighbor_in_star) (EndpointDiagonalGeometry.neighbor_four_adjacent))
  have triple_transitions := EndpointDiagonalGeometry.triple_transitions T0 T0' hT hT' hdis
      (EndpointDiagonalGeometry.exact_point_boundary) (EndpointDiagonalGeometry.touching_path)
      (EndpointDiagonalGeometry.transition_indices_ne)
  let outerLabel : GaussianInt → Fin 4 → Fin 3 := fun x j =>
    if LatticeVertexIncidentCell x j ∈ T0.cells then 0
    else if LatticeVertexIncidentCell x j ∈ T0'.cells then 1 else 2
  have label_T0 := LatticeVertexSectorFacts.firstTileLabel T0 T0'
  have label_T0' := LatticeVertexSectorFacts.secondTileLabel T0 T0' hdis
  have label_R := EndpointDiagonalGeometry.label_R T0 T0'
  have label_mem := EndpointDiagonalGeometry.label_mem T0 T0' label_T0 label_T0'
  have label_eq_two_mem := EndpointDiagonalGeometry.label_eq_two_mem T0 T0' label_mem
  have label_eq_zero_mem := EndpointDiagonalGeometry.label_eq_zero_mem T0 T0' label_mem
  have label_eq_one_mem := EndpointDiagonalGeometry.label_eq_one_mem T0 T0' label_mem
  have label_side_mem := EndpointDiagonalGeometry.label_side_mem T0 T0' label_mem
  have htriple := ExactTileInterfaceTripleLatticeTouching
    T0 T0' R E hT hT' hR hdis hT'm hTm.symm
  have owner_unique (c : GaussianInt) (a : ι)
      (hc : c ∈ (P.tile a).cells) : owner c = a :=
    (owner_mem_iff c a).mp hc
  have owner_eq_endpoint (x : GaussianInt) (j : Fin 4)
      (hc : LatticeVertexIncidentCell x j ∈ R.cells) :
      owner (LatticeVertexIncidentCell x j) = endpointIndex :=
          EndpointDiagonalGeometry.owner_eq_endpoint ι P owner R endpointIndex hRidx owner_unique
          x j hc
  have owner_repeat_at := EndpointDiagonalGeometry.owner_repeat_at ι owner owner_no_fourfold
  have owner_ne_T0_index := EndpointDiagonalGeometry.owner_ne_T0_index ι P owner owner_mem_iff T0
      T0' hdis
  have owner_ne_T0'_index := EndpointDiagonalGeometry.owner_ne_T0'_index ι P owner owner_mem_iff
      T0 T0' hdis
  have owner_ne_endpoint := EndpointDiagonalGeometry.owner_ne_endpoint ι P owner owner_mem_iff T0
      T0' R hTm hT'm endpointIndex hRidx
  have hxTriple : x ∈ FootprintVertices T0 ∩ FootprintVertices T0' ∩
      FootprintVertices R := (E.unique_common x).2 hstart
  have hsectorCover := (EndpointDiagonalGeometry.triple_sector_cover T0 T0' hT hT') R hR htriple
      x hxTriple
  have hdisUV : Disjoint U.cells V.cells := EndpointDiagonalGeometry.hdisUV T0 T0' U V hdis hUsub
      hVsub
  obtain ⟨jEdge, hedgeAt, htransition⟩ := P3102T2CommonEdgeSectorTransition
    U V x {x, y} hdisUV (by simp) hedgeUV
  have hsectorEdge := EndpointDiagonalGeometry.hsectorEdge ι P U V ia ib hUidx hVidx x jEdge
      htransition
  rcases triple_transitions R E hR hTm hT'm htriple with
    ⟨eAB, eBR, eRA, jAB, jBR, jRA, hxeAB, heAB, hABat,
      hxeBR, heBR, hBRat, hxeRA, heRA, hRAat,
      htransAB, htransBR, htransRA, hjABBR, hjBRRA, hjRAAB⟩
  have hxeABx : x ∈ eAB := by simpa [hstart] using hxeAB
  have hABedge_eq : eAB = {x, y} := hEndpointEdge eAB hxeABx heAB
  have hABatx : eAB = edgeAt x jAB := by
    simpa [hstart] using hABat
  have htransABx := htransAB
  rw [← hstart] at htransABx
  have htransBRx := htransBR
  rw [← hstart] at htransBRx
  have htransRAx := htransRA
  rw [← hstart] at htransRAx
  have hedgeAtx : ({x, y} : Finset GaussianInt) = edgeAt x jEdge := by
    simpa [edgeAt] using hedgeAt
  have hjABEdge := EndpointDiagonalGeometry.hjABEdge x y edgeAt_injective jEdge eAB jAB
      hABedge_eq hABatx hedgeAtx
  have hlabelAB := EndpointDiagonalGeometry.hlabelAB T0 T0' x label_T0 label_T0' jAB htransABx
  have hlabelPattern := triple_label_pattern (fun j => outerLabel x j)
    jAB jBR jRA
    hjABBR hjBRRA hjRAAB hlabelAB (EndpointDiagonalGeometry.hlabelBR T0 T0' R hTm hT'm x
        label_T0' label_R jBR htransBRx) (EndpointDiagonalGeometry.hlabelRA T0 T0' R hTm hT'm x
        label_T0 label_R jRA htransRAx)
  have hlabelGood := EndpointDiagonalGeometry.hlabelGood T0 T0' R hTm hT'm x hstar
      endpoint_repeat_impossible label_eq_two_mem hxTriple hsectorCover jAB hlabelPattern
  have hsectorAB := EndpointDiagonalGeometry.hsectorAB ι P ia ib x jEdge hsectorEdge jAB hjABEdge
  have hownerAB := EndpointDiagonalGeometry.hownerAB ι P owner U V ia ib hUidx hVidx x
      owner_unique jAB hsectorAB
  have hownerAligned := EndpointDiagonalGeometry.hownerAligned ι P owner owner_mem_iff T0 T0' U V
      hdis ia ib hUidx hVidx hUsub hVsub x label_T0 label_T0' jAB htransABx hownerAB
  have hlabelsAB := EndpointDiagonalGeometry.hlabelsAB T0 T0' x label_T0 label_T0' jAB htransABx
  let o0 := owner (LatticeVertexIncidentCell x jAB)
  let o1 := owner (LatticeVertexIncidentCell x (jAB + 1))
  let o2 := owner (LatticeVertexIncidentCell x (jAB + 2))
  let o3 := owner (LatticeVertexIncidentCell x (jAB + 3))
  have hownerAligned' := EndpointDiagonalGeometry.hownerAligned' ι owner T0 T0' ia ib x jAB
      hownerAligned
  have hownerRepeat := EndpointDiagonalGeometry.hownerRepeat ι owner x owner_repeat_at jAB
  rcases hlabelGood with hGood | hGood
  · have hcell2 : LatticeVertexIncidentCell x (jAB + 2) ∈ R.cells :=
      label_eq_two_mem R x hsectorCover (jAB + 2) hGood.1
    have ho2 : o2 = endpointIndex := by
      simpa [o2] using owner_eq_endpoint x (jAB + 2) hcell2
    have hcell3side := EndpointDiagonalGeometry.hcell3side ι owner T0 T0' R ia ib x
        label_side_mem hsectorCover jAB hownerAligned' hGood
    have hside0 := EndpointDiagonalGeometry.hside0At763 T0 T0' x jAB htransABx
    have hside1 := EndpointDiagonalGeometry.hside1At768 T0 T0' x jAB htransABx
    have ho01ne := EndpointDiagonalGeometry.ho01neAt773 ι owner T0 T0' ia ib hidxne x jAB
        hownerAligned'
    have ho02ne := EndpointDiagonalGeometry.ho02neAt778 ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho2 hside0
    have ho12ne := EndpointDiagonalGeometry.ho12ne ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho2 hside1
    have ho13ne := EndpointDiagonalGeometry.ho13neAt784 ι P owner T0 T0' R U V ia ib hUidx hVidx
        hUsub hVsub x label_eq_zero_mem label_eq_one_mem owner_ne_T0_index owner_ne_T0'_index
        hsectorCover jAB hownerAligned' hGood
    have ho23ne := EndpointDiagonalGeometry.ho23neAt801 ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho2 hcell3side
    have ho03 := EndpointDiagonalGeometry.ho03 ι owner x jAB hownerRepeat ho01ne ho02ne ho12ne
        ho13ne ho23ne
    have hdiag := EndpointDiagonalGeometry.hdiagAt813 ι P owner owner_mem_iff T0 T0' U V ia ib
        hUidx hVidx x jAB hownerAligned' ho03
    have hfinalCells := EndpointDiagonalGeometry.hfinalCellsAt833 U V x jAB hdiag
    exact hfinalCells
  · have hcell3 : LatticeVertexIncidentCell x (jAB + 3) ∈ R.cells :=
      label_eq_two_mem R x hsectorCover (jAB + 3) hGood.1
    have ho3 : o3 = endpointIndex := by
      simpa [o3] using owner_eq_endpoint x (jAB + 3) hcell3
    have hcell2side := EndpointDiagonalGeometry.hcell2side ι owner T0 T0' R ia ib x
        label_side_mem hsectorCover jAB hlabelsAB hownerAligned' hGood
    have hside0 := EndpointDiagonalGeometry.hside0At763 T0 T0' x jAB htransABx
    have hside1 := EndpointDiagonalGeometry.hside1At768 T0 T0' x jAB htransABx
    have ho01ne := EndpointDiagonalGeometry.ho01neAt773 ι owner T0 T0' ia ib hidxne x jAB
        hownerAligned'
    have ho02ne := EndpointDiagonalGeometry.ho02neAt895 ι P owner T0 T0' R U V ia ib hUidx hVidx
        hUsub hVsub x label_eq_zero_mem label_eq_one_mem owner_ne_T0_index owner_ne_T0'_index
        hsectorCover jAB hlabelsAB hownerAligned' hGood
    have ho03ne := EndpointDiagonalGeometry.ho03ne ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho3 hside0
    have ho13ne := EndpointDiagonalGeometry.ho13neAt923 ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho3 hside1
    have ho23ne := EndpointDiagonalGeometry.ho23neAt926 ι owner T0 T0' endpointIndex x
        owner_ne_endpoint jAB ho3 hcell2side
    have ho12 := EndpointDiagonalGeometry.ho12 ι owner x jAB hownerRepeat ho01ne ho02ne ho03ne
        ho13ne ho23ne
    have hdiag := EndpointDiagonalGeometry.hdiagAt938 ι P owner owner_mem_iff T0 T0' U V ia ib
        hUidx hVidx x jAB hownerAligned' ho12
    have hfinalCells := EndpointDiagonalGeometry.hfinalCellsAt958 U V x jAB hdiag
    exact hfinalCells

end ApollonianSuperharmonic

end
