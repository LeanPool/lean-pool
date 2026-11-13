/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence

public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import LeanPool.ApollonianSuperharmonic.P3102T2CommonEdgeSectorTransition
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: LocalLatticeInterfaceSectors]

/-!
# LocalLatticeInterfaceSectors

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace InterfaceSectorGeometry

private abbrev raw_incident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private theorem nonempty_touching :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), Finset.Nonempty U.cells → Finset.Nonempty V.cells →
            TileTouching U V → Disjoint U.cells V.cells ∧ SimpleGridPath
            (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V) (BoundaryFootprintEdges U
            ∩ BoundaryFootprintEdges V) ) := by
  classical
  intro U V hUne hVne ht
  rcases ht with ht | ht | ht
  · exact ⟨ht.2.2.1, ht.2.2.2⟩
  · rw [ht.1] at hUne
    simp at hUne
  · rw [ht.1] at hVne
    simp at hVne

private abbrev incident_boundary := ApollonianSuperharmonic.P3161T2IncidentBoundary

private theorem common_edge_transition :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + I}, {x - 1, x}, {x - I, x}, {x, x + 1}]
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt), ∀ (e : Finset GaussianInt),
            Disjoint U.cells V.cells → x ∈ e → e ∈ BoundaryFootprintEdges U ∩
            BoundaryFootprintEdges V → ∃ (j : Fin (4 : ℕ)), e = edgeAt x j ∧
            (LatticeVertexIncidentCell x j ∈ U.cells ∧ LatticeVertexIncidentCell x (j + (1 : Fin
            (4 : ℕ))) ∈ V.cells ∨ LatticeVertexIncidentCell x j ∈ V.cells ∧
            LatticeVertexIncidentCell x (j + (1 : Fin (4 : ℕ))) ∈ U.cells) ) := by
  classical
  intro I edgeAt U V x e hdisjoint hxe he
  rw [← CellDisjointCommonEdgesBoundary U V hdisjoint] at he
  simpa only [edgeAt, I] using
    P3102T2CommonEdgeSectorTransition U V x e hdisjoint hxe he

private theorem two_transition_sectors :
    (by
      classical
      exact
        ∀ (P : Fin (4 : ℕ) → Prop), ∀ (Q : Fin (4 : ℕ) → Prop), (∀ (j : Fin (4 : ℕ)), ¬(P j ∧ Q
            j)) → ¬(P (0 : Fin (4 : ℕ)) ∧ P (2 : Fin (4 : ℕ)) ∧ ¬P (1 : Fin (4 : ℕ)) ∧ ¬P (3 :
            Fin (4 : ℕ)) ∨ P (1 : Fin (4 : ℕ)) ∧ P (3 : Fin (4 : ℕ)) ∧ ¬P (0 : Fin (4 : ℕ)) ∧ ¬P
            (2 : Fin (4 : ℕ))) → ¬(Q (0 : Fin (4 : ℕ)) ∧ Q (2 : Fin (4 : ℕ)) ∧ ¬Q (1 : Fin (4 :
            ℕ)) ∧ ¬Q (3 : Fin (4 : ℕ)) ∨ Q (1 : Fin (4 : ℕ)) ∧ Q (3 : Fin (4 : ℕ)) ∧ ¬Q (0 : Fin
            (4 : ℕ)) ∧ ¬Q (2 : Fin (4 : ℕ))) → ∀ (a : Fin (4 : ℕ)), ∀ (b : Fin (4 : ℕ)), a ≠ b →
            P a ∧ Q (a + (1 : Fin (4 : ℕ))) ∨ Q a ∧ P (a + (1 : Fin (4 : ℕ))) → P b ∧ Q (b + (1 :
            Fin (4 : ℕ))) ∨ Q b ∧ P (b + (1 : Fin (4 : ℕ))) → (∀ (j : Fin (4 : ℕ)), P j ∨ Q j) ∧
            ∃ (j : Fin (4 : ℕ)), P j ∧ Q (j + (2 : Fin (4 : ℕ))) ) := by
  classical
  intro P Q hd hP hQ a b hab ha hb
  have cover4 (r j : Fin 4) :
      j = r ∨ j = r + 1 ∨ j = r + 2 ∨ j = r + 3 := by
    fin_cases r <;> fin_cases j <;> simp
  have add_three_two (r : Fin 4) : r + 3 + 2 = r + 1 := by
    fin_cases r <;> rfl
  have add_one_one (r : Fin 4) : r + 1 + 1 = r + 2 := by
    fin_cases r <;> rfl
  have add_two_one (r : Fin 4) : r + 2 + 1 = r + 3 := by
    fin_cases r <;> rfl
  have add_one_two (r : Fin 4) : r + 1 + 2 = r + 3 := by
    fin_cases r <;> rfl
  have fillP (r : Fin 4) (hr : P r) (hr2 : P (r + 2))
      (hq1 : Q (r + 1)) : P (r + 3) := by
    by_contra hmissing
    apply hP
    fin_cases r
    · exact Or.inl ⟨hr, hr2, fun hp => hd 1 ⟨hp, hq1⟩, hmissing⟩
    · exact Or.inr ⟨hr, hr2, hmissing, fun hp => hd 2 ⟨hp, hq1⟩⟩
    · exact Or.inl ⟨hr2, hr, hmissing, fun hp => hd 3 ⟨hp, hq1⟩⟩
    · exact Or.inr ⟨hr2, hr, fun hp => hd 0 ⟨hp, hq1⟩, hmissing⟩
  have fillQ (r : Fin 4) (hr : Q r) (hr2 : Q (r + 2))
      (hp1 : P (r + 1)) : Q (r + 3) := by
    by_contra hmissing
    apply hQ
    fin_cases r
    · exact Or.inl ⟨hr, hr2, fun hq => hd 1 ⟨hp1, hq⟩, hmissing⟩
    · exact Or.inr ⟨hr, hr2, hmissing, fun hq => hd 2 ⟨hp1, hq⟩⟩
    · exact Or.inl ⟨hr2, hr, hmissing, fun hq => hd 3 ⟨hp1, hq⟩⟩
    · exact Or.inr ⟨hr2, hr, fun hq => hd 0 ⟨hp1, hq⟩, hmissing⟩
  have adjacent (r : Fin 4)
      (hr : (P r ∧ Q (r + 1)) ∨ (Q r ∧ P (r + 1)))
      (hs : (P (r + 1) ∧ Q (r + 2)) ∨
        (Q (r + 1) ∧ P (r + 2))) :
      (∀ j, P j ∨ Q j) ∧ ∃ j, P j ∧ Q (j + 2) := by
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact (hd (r + 1) ⟨hs.1, hr.2⟩).elim
    · have hp3 := fillP r hr.1 hs.2 hr.2
      constructor
      · intro j
        rcases cover4 r j with rfl | rfl | rfl | rfl
        · exact Or.inl hr.1
        · exact Or.inr hr.2
        · exact Or.inl hs.2
        · exact Or.inl hp3
      · refine ⟨r + 3, hp3, ?_⟩
        rw [add_three_two]
        exact hr.2
    · have hq3 := fillQ r hr.1 hs.2 hr.2
      constructor
      · intro j
        rcases cover4 r j with rfl | rfl | rfl | rfl
        · exact Or.inr hr.1
        · exact Or.inl hr.2
        · exact Or.inr hs.2
        · exact Or.inr hq3
      · refine ⟨r + 1, hr.2, ?_⟩
        rw [add_one_two]
        exact hq3
    · exact (hd (r + 1) ⟨hr.2, hs.1⟩).elim
  have opposite (r : Fin 4)
      (hr : (P r ∧ Q (r + 1)) ∨ (Q r ∧ P (r + 1)))
      (hs : (P (r + 2) ∧ Q (r + 3)) ∨
        (Q (r + 2) ∧ P (r + 3))) :
      (∀ j, P j ∨ Q j) ∧ ∃ j, P j ∧ Q (j + 2) := by
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact (hd (r + 3) ⟨fillP r hr.1 hs.1 hr.2, hs.2⟩).elim
    · constructor
      · intro j
        rcases cover4 r j with rfl | rfl | rfl | rfl
        · exact Or.inl hr.1
        · exact Or.inr hr.2
        · exact Or.inr hs.1
        · exact Or.inl hs.2
      · exact ⟨r, hr.1, hs.1⟩
    · constructor
      · intro j
        rcases cover4 r j with rfl | rfl | rfl | rfl
        · exact Or.inr hr.1
        · exact Or.inl hr.2
        · exact Or.inl hs.1
        · exact Or.inr hs.2
      · refine ⟨r + 1, hr.2, ?_⟩
        rw [add_one_two]
        exact hs.2
    · exact (hd (r + 3) ⟨hs.2, fillQ r hr.1 hs.1 hr.2⟩).elim
  have hpos : b = a + 1 ∨ b = a + 2 ∨ a = b + 1 := by
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
  rcases hpos with h | h | h
  · subst b
    apply adjacent a ha
    simpa only [add_one_one] using hb
  · subst b
    apply opposite a ha
    simpa only [add_two_one] using hb
  · subst a
    apply adjacent b hb
    simpa only [add_one_one] using ha

private theorem hxBoundary :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), (T.cells.Nonempty) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ T.cells) → ((∃ j : Fin 4, LatticeVertexIncidentCell x
            j ∉ T.cells) → (x ∈ BoundaryFootprintVertices T)))) → (∀ (X : ProtoTile), ∀ (Y :
            ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Z.cells.Nonempty) → ((Disjoint X.cells Y.cells) → ((Disjoint
            Y.cells Z.cells) → ((Disjoint Z.cells X.cells) → (∀ (jX : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jX ∈ X.cells) → (∀ (jY : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jY ∈ Y.cells) → (∀ (jZ : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jZ ∈ Z.cells) → (x ∈ BoundaryFootprintVertices X ∩
            BoundaryFootprintVertices Y ∧ x ∈ BoundaryFootprintVertices Y ∩
            BoundaryFootprintVertices Z ∧ x ∈ BoundaryFootprintVertices Z ∩
            BoundaryFootprintVertices X)))))))))) ) := by
  classical
  intro incident_boundary X Y Z x hXne hYne hZne hXYdisjoint hYZdisjoint hZXdisjoint jX hjX jY
      hjY jZ hjZ
  have hXY := Finset.disjoint_left.mp hXYdisjoint
  have hYZ := Finset.disjoint_left.mp hYZdisjoint
  have hZX := Finset.disjoint_left.mp hZXdisjoint
  have hxXB : x ∈ BoundaryFootprintVertices X :=
    incident_boundary X x hXne ⟨jX, hjX⟩ ⟨jY, fun h => hXY h hjY⟩
  have hxYB : x ∈ BoundaryFootprintVertices Y :=
    incident_boundary Y x hYne ⟨jY, hjY⟩ ⟨jX, fun h => hXY hjX h⟩
  have hxZB : x ∈ BoundaryFootprintVertices Z :=
    incident_boundary Z x hZne ⟨jZ, hjZ⟩ ⟨jY, fun h => hYZ hjY h⟩
  exact ⟨⟨hxXB, hxYB⟩, ⟨⟨hxYB, hxZB⟩, ⟨hxZB, hxXB⟩⟩⟩

private theorem hXY_YZ :
    (by
      classical
      exact
        ∀ (X : ProtoTile),
          ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile),
              ∀ (x : GaussianInt),
                Finset GaussianInt →
                  ∀ (jXY : Fin (4 : ℕ)),
                    LatticeVertexIncidentCell x jXY ∈ X.cells ∧
                          LatticeVertexIncidentCell x (jXY + (1 : Fin (4 : ℕ))) ∈
                            Y.cells ∨
                        LatticeVertexIncidentCell x jXY ∈ Y.cells ∧
                          LatticeVertexIncidentCell x (jXY + (1 : Fin (4 : ℕ))) ∈
                            X.cells →
                      ∀ (jYZ : Fin (4 : ℕ)),
                        LatticeVertexIncidentCell x jYZ ∈ Y.cells ∧
                              LatticeVertexIncidentCell x (jYZ + (1 : Fin (4 : ℕ))) ∈
                                Z.cells ∨
                            LatticeVertexIncidentCell x jYZ ∈ Z.cells ∧
                              LatticeVertexIncidentCell x (jYZ + (1 : Fin (4 : ℕ))) ∈
                                Y.cells →
                          (∀ ⦃a : LatticeCell⦄, a ∈ Y.cells → a ∉ Z.cells) →
                            (∀ ⦃a : LatticeCell⦄, a ∈ Z.cells → a ∉ X.cells) → jXY ≠ jYZ
    ) := by
  classical
  intro X Y Z x eYZ jXY htXY jYZ htYZ hYZd hZXd h
  subst jYZ
  rcases htXY with htXY | htXY <;> rcases htYZ with htYZ | htYZ
  · exact hYZd htXY.2 htYZ.2
  · exact hZXd htYZ.1 htXY.1
  · exact hZXd htYZ.2 htXY.2
  · exact hYZd htXY.1 htYZ.1

private theorem hYZ_ZX :
    (by
      classical
      exact
        ∀ (X : ProtoTile),
          ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile),
              ∀ (x : GaussianInt),
                Finset GaussianInt →
                  ∀ (jYZ : Fin (4 : ℕ)),
                    LatticeVertexIncidentCell x jYZ ∈ Y.cells ∧
                          LatticeVertexIncidentCell x (jYZ + (1 : Fin (4 : ℕ))) ∈
                            Z.cells ∨
                        LatticeVertexIncidentCell x jYZ ∈ Z.cells ∧
                          LatticeVertexIncidentCell x (jYZ + (1 : Fin (4 : ℕ))) ∈
                            Y.cells →
                      ∀ (jZX : Fin (4 : ℕ)),
                        LatticeVertexIncidentCell x jZX ∈ Z.cells ∧
                              LatticeVertexIncidentCell x (jZX + (1 : Fin (4 : ℕ))) ∈
                                X.cells ∨
                            LatticeVertexIncidentCell x jZX ∈ X.cells ∧
                              LatticeVertexIncidentCell x (jZX + (1 : Fin (4 : ℕ))) ∈
                                Z.cells →
                          (∀ ⦃a : LatticeCell⦄, a ∈ X.cells → a ∉ Y.cells) →
                            (∀ ⦃a : LatticeCell⦄, a ∈ Y.cells → a ∉ Z.cells) →
                              (∀ ⦃a : LatticeCell⦄, a ∈ Z.cells → a ∉ X.cells) → jYZ ≠ jZX
    ) := by
  classical
  intro X Y Z x eZX jYZ htYZ jZX htZX hXYd hYZd hZXd h
  subst jZX
  rcases htYZ with htYZ | htYZ <;> rcases htZX with htZX | htZX
  · exact hYZd htYZ.1 htZX.1
  · exact hXYd htZX.1 htYZ.1
  · exact hXYd htZX.2 htYZ.2
  · exact hZXd htYZ.1 htZX.1

private theorem hZX_XY :
    (by
      classical
      exact
        ∀ (X : ProtoTile),
          ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile),
              ∀ (x : GaussianInt),
                Finset GaussianInt →
                  ∀ (jXY : Fin (4 : ℕ)),
                    LatticeVertexIncidentCell x jXY ∈ X.cells ∧
                          LatticeVertexIncidentCell x (jXY + (1 : Fin (4 : ℕ))) ∈
                            Y.cells ∨
                        LatticeVertexIncidentCell x jXY ∈ Y.cells ∧
                          LatticeVertexIncidentCell x (jXY + (1 : Fin (4 : ℕ))) ∈
                            X.cells →
                      ∀ (jYZ : Fin (4 : ℕ)),
                        ∀ (jZX : Fin (4 : ℕ)),
                          LatticeVertexIncidentCell x jZX ∈ Z.cells ∧
                                LatticeVertexIncidentCell x (jZX + (1 : Fin (4 : ℕ))) ∈
                                X.cells ∨
                              LatticeVertexIncidentCell x jZX ∈ X.cells ∧
                                LatticeVertexIncidentCell x (jZX + (1 : Fin (4 : ℕ))) ∈
                                Z.cells →
                            (∀ ⦃a : LatticeCell⦄, a ∈ X.cells → a ∉ Y.cells) →
                              (∀ ⦃a : LatticeCell⦄, a ∈ Y.cells → a ∉ Z.cells) →
                                (∀ ⦃a : LatticeCell⦄, a ∈ Z.cells → a ∉ X.cells) →
                                jXY ≠ jYZ → jZX ≠ jXY
    ) := by
  classical
  intro X Y Z x eXY jXY htXY jYZ jZX htZX hXYd hYZd hZXd hXY_YZ h
  subst jXY
  rcases htZX with htZX | htZX <;> rcases htXY with htXY | htXY
  · exact hZXd htZX.1 htXY.1
  · exact hYZd htXY.1 htZX.1
  · exact hYZd htXY.2 htZX.2
  · exact hXYd htZX.1 htXY.1

private theorem hexhaust :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt), (Finset
            GaussianInt) →
                                 (Finset GaussianInt) →
                                                               (Finset GaussianInt) →
                                                                                             ∀
            (jXY : Fin (4 : ℕ)),
                                                        ((LatticeVertexIncidentCell x jXY ∈
            X.cells ∧ LatticeVertexIncidentCell x (jXY + (1 : Fin (4 : ℕ))) ∈ Y.cells ∨
            LatticeVertexIncidentCell x jXY ∈ Y.cells ∧ LatticeVertexIncidentCell x (jXY + (1 :
            Fin (4 : ℕ))) ∈ X.cells) → (∀ (jYZ : Fin (4 : ℕ)),
            ((LatticeVertexIncidentCell x jYZ ∈ Y.cells ∧ LatticeVertexIncidentCell x (jYZ + (1 :
            Fin (4 : ℕ))) ∈ Z.cells ∨ LatticeVertexIncidentCell x jYZ ∈ Z.cells ∧
            LatticeVertexIncidentCell x (jYZ + (1 : Fin (4 : ℕ))) ∈ Y.cells) → (∀ (jZX : Fin (4 :
            ℕ)),
                                        ((LatticeVertexIncidentCell x jZX ∈ Z.cells ∧
            LatticeVertexIncidentCell x (jZX + (1 : Fin (4 : ℕ))) ∈ X.cells ∨
            LatticeVertexIncidentCell x jZX ∈ X.cells ∧ LatticeVertexIncidentCell x (jZX + (1 :
            Fin (4 : ℕ))) ∈ Z.cells) → ((jXY ≠ jYZ) → ((jYZ ≠ jZX) → ((jZX ≠ jXY) → (forall j :
            Fin 4, LatticeVertexIncidentCell x j ∈ X.cells ∨ LatticeVertexIncidentCell x j ∈
            Y.cells ∨ LatticeVertexIncidentCell x j ∈ Z.cells))))))))) ) := by
  classical
  intro X Y Z x eXY eYZ eZX jXY htXY jYZ htYZ jZX htZX hXY_YZ hYZ_ZX hZX_XY j
  have hendpoint :
      (j = jXY ∨ j = jXY + 1) ∨
      (j = jYZ ∨ j = jYZ + 1) ∨
      (j = jZX ∨ j = jZX + 1) := by
    fin_cases j <;> fin_cases jXY <;> fin_cases jYZ <;> fin_cases jZX <;>
      simp at hXY_YZ hYZ_ZX hZX_XY ⊢
  rcases hendpoint with h | h | h
  · rcases h with rfl | rfl
    · rcases htXY with htXY | htXY
      · exact Or.inl htXY.1
      · exact Or.inr (Or.inl htXY.1)
    · rcases htXY with htXY | htXY
      · exact Or.inr (Or.inl htXY.2)
      · exact Or.inl htXY.2
  · rcases h with rfl | rfl
    · rcases htYZ with htYZ | htYZ
      · exact Or.inr (Or.inl htYZ.1)
      · exact Or.inr (Or.inr htYZ.1)
    · rcases htYZ with htYZ | htYZ
      · exact Or.inr (Or.inr htYZ.2)
      · exact Or.inr (Or.inl htYZ.2)
  · rcases h with rfl | rfl
    · rcases htZX with htZX | htZX
      · exact Or.inr (Or.inr htZX.1)
      · exact Or.inl htZX.1
    · rcases htZX with htZX | htZX
      · exact Or.inl htZX.2
      · exact Or.inr (Or.inr htZX.2)

private theorem hopposite :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), ∀ (x : GaussianInt), ∀ (jX : Fin
            (4 : ℕ)), (LatticeVertexIncidentCell x jX ∈ X.cells) → (∀ (jY : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jY ∈ Y.cells) → (∀ (jZ : Fin (4 : ℕ)),
            (LatticeVertexIncidentCell x jZ ∈ Z.cells) → ((∀ ⦃a : LatticeCell⦄, a ∈ X.cells → a ∉
            Y.cells) → ((∀ ⦃a : LatticeCell⦄, a ∈ Y.cells → a ∉ Z.cells) → ((∀ ⦃a : LatticeCell⦄,
            a ∈ Z.cells → a ∉ X.cells) → (((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ X.cells
            ∧ LatticeVertexIncidentCell x (j + 2) ∈ Y.cells) ∨ (∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ X.cells ∧ LatticeVertexIncidentCell x (j + 2) ∈
            Z.cells) ∨ (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Y.cells ∧
            LatticeVertexIncidentCell x (j + 2) ∈ Z.cells)))))))) ) := by
  classical
  intro X Y Z x jX hjX jY hjY jZ hjZ hXYd hYZd hZXd
  have hX_Y : jX ≠ jY := by
    intro h
    subst jY
    exact hXYd hjX hjY
  have hY_Z : jY ≠ jZ := by
    intro h
    subst jZ
    exact hYZd hjY hjZ
  have hZ_X : jZ ≠ jX := by
    intro h
    subst jX
    exact hZXd hjZ hjX
  have hindices :
      jY = jX + 2 ∨ jX = jY + 2 ∨
      jZ = jX + 2 ∨ jX = jZ + 2 ∨
      jZ = jY + 2 ∨ jY = jZ + 2 := by
    fin_cases jX <;> fin_cases jY <;> fin_cases jZ <;>
      simp at hX_Y hY_Z hZ_X ⊢
  have add_two_twice (j : Fin 4) : j + 2 + 2 = j := by
    fin_cases j <;> rfl
  rcases hindices with h | h | h | h | h | h
  · exact Or.inl ⟨jX, hjX, by simpa [h, add_two_twice] using hjY⟩
  · exact Or.inl ⟨jX, hjX, by simpa [h, add_two_twice] using hjY⟩
  · exact Or.inr (Or.inl ⟨jX, hjX, by simpa [h, add_two_twice] using hjZ⟩)
  · exact Or.inr (Or.inl ⟨jX, hjX, by simpa [h, add_two_twice] using hjZ⟩)
  · exact Or.inr (Or.inr ⟨jY, hjY, by simpa [h, add_two_twice] using hjZ⟩)
  · exact Or.inr (Or.inr ⟨jY, hjY, by simpa [h, add_two_twice] using hjZ⟩)

private theorem he' :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (FootprintEdges X ∩ FootprintEdges Y =
            BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y) → (∀ (e : Finset GaussianInt),
            (e ∈ FootprintEdges X ∩ FootprintEdges Y) → (e ∈ BoundaryFootprintEdges X ∩
            BoundaryFootprintEdges Y)) ) := by
  classical
  intro X Y hboundary e he
  rw [← hboundary]
  exact he

private abbrev hf' := ApollonianSuperharmonic.InterfaceSectorGeometry.he'

private theorem hjne :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩;
        let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
          ![{x, x + I}, {x - 1, x}, {x - I, x}, {x, x + 1}];
        ∀ (x : GaussianInt),
          ∀ (e : Finset GaussianInt),
            ∀ (f : Finset GaussianInt),
              e ≠ f →
                ∀ (je : Fin (4 : ℕ)),
                  e = edgeAt x je → ∀ (jf : Fin (4 : ℕ)), f = edgeAt x jf → je ≠ jf
    ) := by
  classical
  intro I edgeAt x e f hef je heAt jf hfAt h
  subst jf
  exact hef (heAt.trans hfAt.symm)

private theorem hdPQ :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (x : GaussianInt), (∀ ⦃a : LatticeCell⦄, a ∈
            X.cells → a ∉ Y.cells) → (
        let P : Fin 4 → Prop := fun j => LatticeVertexIncidentCell x j ∈ X.cells
        let Q : Fin 4 → Prop := fun j => LatticeVertexIncidentCell x j ∈ Y.cells
        ∀ j, ¬ (P j ∧ Q j)) ) := by
  classical
  intro X Y x hd P Q j h
  exact hd h.1 h.2

private theorem hcheckP :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (x : GaussianInt), (¬(x ∈ (↑X.cells : Set LatticeCell) ∧ x - (1 :
            GaussianInt) - ⟨(0 : ℤ), (1 : ℤ)⟩ ∈ (↑X.cells : Set LatticeCell) ∧ x - (1 :
            GaussianInt) ∉ (↑X.cells : Set LatticeCell) ∧ x - ⟨(0 : ℤ), (1 : ℤ)⟩ ∉ (↑X.cells :
            Set LatticeCell) ∨ x - (1 : GaussianInt) ∈ (↑X.cells : Set LatticeCell) ∧ x - ⟨(0 :
            ℤ), (1 : ℤ)⟩ ∈ (↑X.cells : Set LatticeCell) ∧ x ∉ (↑X.cells : Set LatticeCell) ∧ x -
            (1 : GaussianInt) - ⟨(0 : ℤ), (1 : ℤ)⟩ ∉ (↑X.cells : Set LatticeCell))) → (
        let P : Fin 4 → Prop := fun j => LatticeVertexIncidentCell x j ∈ X.cells
        ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨ (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2))) ) := by
  classical
  intro X x hcheckX P
  simpa [P, LatticeVertexIncidentCell] using hcheckX

private abbrev hcheckQ := ApollonianSuperharmonic.InterfaceSectorGeometry.hcheckP

end InterfaceSectorGeometry

theorem LocalLatticeInterfaceSectors :
    (forall (X Y Z : ProtoTile) (x : GaussianInt),
      LatticeTile X -> LatticeTile Y -> LatticeTile Z ->
      TouchingTriple X Y Z ->
      x ∈ FootprintVertices X ∩ FootprintVertices Y ∩ FootprintVertices Z ->
      (forall j : Fin 4,
        LatticeVertexIncidentCell x j ∈ X.cells ∨
          LatticeVertexIncidentCell x j ∈ Y.cells ∨
          LatticeVertexIncidentCell x j ∈ Z.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ X.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Y.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Z.cells) ∧
      ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ X.cells ∧
          LatticeVertexIncidentCell x (j + 2) ∈ Y.cells) ∨
       (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ X.cells ∧
          LatticeVertexIncidentCell x (j + 2) ∈ Z.cells) ∨
       (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ Y.cells ∧
          LatticeVertexIncidentCell x (j + 2) ∈ Z.cells))) ∧
    (forall (X Y : ProtoTile) (x : GaussianInt),
      LatticeTile X -> LatticeTile Y -> Disjoint X.cells Y.cells ->
      (∃ e f : Finset GaussianInt,
        e ≠ f ∧ x ∈ e ∧ x ∈ f ∧
          e ∈ FootprintEdges X ∩ FootprintEdges Y ∧
          f ∈ FootprintEdges X ∩ FootprintEdges Y) ->
      (forall j : Fin 4,
        LatticeVertexIncidentCell x j ∈ X.cells ∨
          LatticeVertexIncidentCell x j ∈ Y.cells) ∧
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ X.cells ∧
        LatticeVertexIncidentCell x (j + 2) ∈ Y.cells) := by
-- BODY
  classical
  have raw_incident (T : ProtoTile) (x : GaussianInt)
      (hne : T.cells.Nonempty) (hx : x ∈ FootprintVertices T) :=
          InterfaceSectorGeometry.raw_incident T x hne hx
  have nonempty_touching (U V : ProtoTile)
      (hUne : U.cells.Nonempty) (hVne : V.cells.Nonempty)
      (ht : TileTouching U V) := InterfaceSectorGeometry.nonempty_touching U V hUne hVne ht
  have incident_boundary (T : ProtoTile) (x : GaussianInt)
      (hne : T.cells.Nonempty)
      (hsome : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ T.cells)
      (hmissing : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ T.cells) :=
          InterfaceSectorGeometry.incident_boundary T x hsome hmissing
  let I : GaussianInt := ⟨0, 1⟩
  let edgeAt (x : GaussianInt) : Fin 4 → Finset GaussianInt :=
    ![{x, x + I}, {x - 1, x}, {x - I, x}, {x, x + 1}]
  have common_edge_transition (U V : ProtoTile) (x : GaussianInt)
      (e : Finset GaussianInt) (hdisjoint : Disjoint U.cells V.cells)
      (hxe : x ∈ e)
      (he : e ∈ BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) :=
          InterfaceSectorGeometry.common_edge_transition U V x e hdisjoint hxe he
  have two_transition_sectors (P Q : Fin 4 → Prop)
      (hd : ∀ j, ¬ (P j ∧ Q j))
      (hP : ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
        (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2)))
      (hQ : ¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨
        (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2)))
      (a b : Fin 4) (hab : a ≠ b)
      (ha : (P a ∧ Q (a + 1)) ∨ (Q a ∧ P (a + 1)))
      (hb : (P b ∧ Q (b + 1)) ∨ (Q b ∧ P (b + 1))) :
      (∀ j, P j ∨ Q j) ∧ ∃ j, P j ∧ Q (j + 2) := InterfaceSectorGeometry.two_transition_sectors P
          Q hd hP hQ a b hab ha hb
  constructor
  · intro X Y Z x hX hY hZ htriple hx
    have hXne : X.cells.Nonempty := (LatticeTileGridStructure X hX).1.1
    have hYne : Y.cells.Nonempty := (LatticeTileGridStructure Y hY).1.1
    have hZne : Z.cells.Nonempty := (LatticeTileGridStructure Z hZ).1.1
    rcases htriple with ⟨hXYtouch, hYZtouch, hZXtouch, hunique⟩
    obtain ⟨hXYdisjoint, hXYpath⟩ :=
      nonempty_touching X Y hXne hYne hXYtouch
    obtain ⟨hYZdisjoint, hYZpath⟩ :=
      nonempty_touching Y Z hYne hZne hYZtouch
    obtain ⟨hZXdisjoint, hZXpath⟩ :=
      nonempty_touching Z X hZne hXne hZXtouch
    have hxX : x ∈ FootprintVertices X := hx.1.1
    have hxY : x ∈ FootprintVertices Y := hx.1.2
    have hxZ : x ∈ FootprintVertices Z := hx.2
    obtain ⟨jX, hjX⟩ := raw_incident X x hXne hxX
    obtain ⟨jY, hjY⟩ := raw_incident Y x hYne hxY
    obtain ⟨jZ, hjZ⟩ := raw_incident Z x hZne hxZ
    have hxBoundary := InterfaceSectorGeometry.hxBoundary incident_boundary X Y Z x hXne hYne
        hZne hXYdisjoint hYZdisjoint hZXdisjoint jX hjX jY hjY jZ hjZ
    obtain ⟨eXY, hxeXY, heXY⟩ :=
      SimpleGridPathVertexIncidentEdge _ _ hXYpath x hxBoundary.1
    obtain ⟨eYZ, hxeYZ, heYZ⟩ :=
      SimpleGridPathVertexIncidentEdge _ _ hYZpath x hxBoundary.2.1
    obtain ⟨eZX, hxeZX, heZX⟩ :=
      SimpleGridPathVertexIncidentEdge _ _ hZXpath x hxBoundary.2.2
    obtain ⟨jXY, heXYat, htXY⟩ :=
      common_edge_transition X Y x eXY hXYdisjoint hxeXY heXY
    obtain ⟨jYZ, heYZat, htYZ⟩ :=
      common_edge_transition Y Z x eYZ hYZdisjoint hxeYZ heYZ
    obtain ⟨jZX, heZXat, htZX⟩ :=
      common_edge_transition Z X x eZX hZXdisjoint hxeZX heZX
    have hXYd := Finset.disjoint_left.mp hXYdisjoint
    have hYZd := Finset.disjoint_left.mp hYZdisjoint
    have hZXd := Finset.disjoint_left.mp hZXdisjoint
    have hXY_YZ := InterfaceSectorGeometry.hXY_YZ X Y Z x eYZ jXY htXY jYZ htYZ hYZd hZXd
    have hYZ_ZX := InterfaceSectorGeometry.hYZ_ZX X Y Z x eZX jYZ htYZ jZX htZX hXYd hYZd
        hZXd
    have hZX_XY := InterfaceSectorGeometry.hZX_XY X Y Z x eXY jXY htXY jYZ jZX htZX hXYd
        hYZd hZXd hXY_YZ
    have hexhaust := InterfaceSectorGeometry.hexhaust X Y Z x eXY eYZ eZX jXY htXY jYZ htYZ jZX
        htZX hXY_YZ hYZ_ZX hZX_XY
    have hopposite := InterfaceSectorGeometry.hopposite X Y Z x jX hjX jY hjY jZ hjZ hXYd hYZd hZXd
    exact ⟨hexhaust, ⟨jX, hjX⟩, ⟨jY, hjY⟩, ⟨jZ, hjZ⟩, hopposite⟩
  · intro X Y x hX hY hdisjoint hedges
    have hboundary := CellDisjointCommonEdgesBoundary X Y hdisjoint
    rcases hedges with ⟨e, f, hef, hxe, hxf, he, hf⟩
    have he' := InterfaceSectorGeometry.he' X Y hboundary e he
    have hf' := InterfaceSectorGeometry.hf' X Y hboundary f hf
    obtain ⟨je, heAt, hte⟩ :=
      common_edge_transition X Y x e hdisjoint hxe he'
    obtain ⟨jf, hfAt, htf⟩ :=
      common_edge_transition X Y x f hdisjoint hxf hf'
    have hjne : je ≠ jf := InterfaceSectorGeometry.hjne x e f hef je heAt jf hfAt
    have hd := Finset.disjoint_left.mp hdisjoint
    have hcheckX := (LatticeTileGridStructure X hX).2.1 x
    have hcheckY := (LatticeTileGridStructure Y hY).2.1 x
    let P : Fin 4 → Prop := fun j => LatticeVertexIncidentCell x j ∈ X.cells
    let Q : Fin 4 → Prop := fun j => LatticeVertexIncidentCell x j ∈ Y.cells
    have hdPQ : ∀ j, ¬ (P j ∧ Q j) := InterfaceSectorGeometry.hdPQ X Y x hd
    have hcheckP : ¬ ((P 0 ∧ P 2 ∧ ¬ P 1 ∧ ¬ P 3) ∨
        (P 1 ∧ P 3 ∧ ¬ P 0 ∧ ¬ P 2)) := InterfaceSectorGeometry.hcheckP X x hcheckX
    have hcheckQ : ¬ ((Q 0 ∧ Q 2 ∧ ¬ Q 1 ∧ ¬ Q 3) ∨
        (Q 1 ∧ Q 3 ∧ ¬ Q 0 ∧ ¬ Q 2)) := InterfaceSectorGeometry.hcheckQ Y x hcheckY
    simpa [P, Q] using
      two_transition_sectors P Q hdPQ hcheckP hcheckQ je jf hjne hte htf

end ApollonianSuperharmonic

end
