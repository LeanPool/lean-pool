/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandExceptionalRestorationSectorOrder
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.P4590T1PositivePrototileDisk
public import LeanPool.ApollonianSuperharmonic.P4590T1OppositeCellsStar

-- [TABLET NODE: P4590T1RestoredBoundaryGeometry]

/-!
# P4590T1RestoredBoundaryGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RestoredBoundaryGeometry

private theorem hempty_anchor :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let O := cert.O
        let seg := cert.exceptionalSegments
        (TileCentroid O = TileCentroid T) → (O.cells = ∅ → GaussianRealPoint seg.a = TileCentroid
            T) ) := by
  classical
  intro q cfg C T cert O seg hOcent hOempty
  have hcut := seg.empty_cut hOempty
  have ha : seg.a = O.anchor := hcut.2
  have hanc : GaussianRealPoint O.anchor = TileCentroid T := by
    rw [← hOcent]
    simp [GaussianRealPoint, TileCentroid, hOempty]
  simpa [ha] using hanc

private theorem hnonemptyO :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (GaussianRealPoint x ≠ TileCentroid T) → (
        let O := cert.O
        let seg := cert.exceptionalSegments
        (O.cells = ∅ → GaussianRealPoint seg.a = TileCentroid T) → (O.cells.Nonempty ∨ x ≠
            seg.a)) ) := by
  classical
  intro q cfg C T cert x hnoncentral O seg hempty_anchor
  by_cases hO : O.cells.Nonempty
  · exact Or.inl hO
  · right
    intro hxa
    have hOempty : O.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
    exact hnoncentral (hxa ▸ hempty_anchor hOempty)

private theorem rawBoundary :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    Nat.card
                          { is : Fin (3 : ℕ) × Bool //
                            x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                        (2 : ℕ) →
                      GaussianRealPoint x ≠ TileCentroid T →
                        ∀ (U : ProtoTile),
                          U.cells.Nonempty →
                            x ∈ BoundaryFootprintVertices U → x ∈ FootprintVertices U
    ) := by
  classical
  intro q cfg C T cert x hk hnoncentral U hUne hb
  simp only [BoundaryFootprintVertices, hUne, ite_true, Set.mem_ofPred_eq] at hb
  obtain ⟨e, he, hz⟩ := hb
  simp only [FootprintVertices, hUne, ite_true, Set.mem_ofPred_eq]
  obtain ⟨a, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩ := he
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases ha with ⟨ha, _⟩ | ⟨_, ha⟩
    · refine ⟨a, ha, ?_⟩
      rcases hz with rfl | rfl <;> simp
    · refine ⟨_, ha, ?_⟩
      rcases hz with rfl | rfl <;>
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem boundary_sectors :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    Nat.card
                          { is : Fin (3 : ℕ) × Bool //
                            x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                        (2 : ℕ) →
                      GaussianRealPoint x ≠ TileCentroid T →
                        (∀ (U : ProtoTile),
                            U.cells.Nonempty →
                              x ∈ BoundaryFootprintVertices U → x ∈ FootprintVertices U) →
                          ∀ (U : ProtoTile),
                            U.cells.Nonempty →
                              x ∈ BoundaryFootprintVertices U →
                                (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) ∧
                                ∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ U.cells
    ) := by
  classical
  intro q cfg C T cert x hk hnoncentral rawBoundary U hne hb
  have hraw := rawBoundary U hne hb
  refine ⟨?_, ?_⟩
  · simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hraw
    rcases hraw with ⟨a, ha, rfl | rfl | rfl | rfl⟩
    · exact ⟨0, by simpa [LatticeVertexIncidentCell] using ha⟩
    · exact ⟨1, by simpa [LatticeVertexIncidentCell] using ha⟩
    · exact ⟨3, by simpa [LatticeVertexIncidentCell] using ha⟩
    · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_sub] using ha⟩
  · by_contra! hall
    exact ((P4456T2VertexInterior U hne x hraw).2.mpr hall) hb

private theorem noThird :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (Nat.card
            { is : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } = (2
            : ℕ)) → ((x ∈ BoundaryFootprintVertices (cert.P (0 : Fin (3 : ℕ)) true)) → ((x ∈
            BoundaryFootprintVertices (cert.P (0 : Fin (3 : ℕ)) false)) → (∀ (i : Fin 3), ∀ (s :
            Bool), ((i, s) ≠ ((0 : Fin 3), true)) → (((i, s) ≠ ((0 : Fin 3), false)) → ((x ∈
            BoundaryFootprintVertices (cert.P i s)) → (False)))))) ) := by
  classical
  intro q cfg C T cert x hk hA hB i s hiA hiB hother
  let Sub := {is : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
  let u : Sub := ⟨(0, true), by simpa using hA⟩
  let v : Sub := ⟨(0, false), by simpa using hB⟩
  let w : Sub := ⟨(i, s), hother⟩
  have huv : u ≠ v := by
    intro h
    have := congrArg Subtype.val h
    cases this
  have huw : u ≠ w := by
    intro h
    exact hiA (congrArg Subtype.val h).symm
  have hvw : v ≠ w := by
    intro h
    exact hiB (congrArg Subtype.val h).symm
  have htriple : ({u, v, w} : Finset Sub).card = 3 := by
    simp [huv, huw, hvw]
  have hk' : Fintype.card Sub = 2 := by
    simpa [Sub, Nat.card_eq_fintype_card] using hk
  have hle : 3 ≤ Fintype.card Sub := by
    calc
      3 = ({u, v, w} : Finset Sub).card := htriple.symm
      _ ≤ Finset.univ.card := Finset.card_le_univ _
      _ = Fintype.card Sub := by simp
  omega

private theorem hnotO :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (GaussianRealPoint x ≠ TileCentroid T) → (
        let O := cert.O
        (TileCentroid O = TileCentroid T) → (x ∉ FootprintVertices O ∨ O.cells.Nonempty)) ) := by
  classical
  intro q cfg C T cert x hnoncentral O hOcent
  by_cases hO : O.cells.Nonempty
  · exact Or.inr hO
  · left
    intro hxO
    have ha : x = O.anchor := by simpa [FootprintVertices, hO] using hxO
    have hcen : GaussianRealPoint O.anchor = TileCentroid T := by
      rw [← hOcent]
      simp [GaussianRealPoint, TileCentroid, Finset.not_nonempty_iff_eq_empty.mp hO]
    exact hnoncentral (by simpa [ha] using hcen)

private theorem hmodifiedCommon :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        (A.cells.Nonempty) → ((x ∈ FootprintVertices A) → ((x ∈ FootprintVertices B) →
            (((TileCellComplement A O).cells.Nonempty) → (x ∉ FootprintVertices O → x ∈
            FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B)))) ) := by
  classical
  intro q cfg C T cert x A B O hAne hxA' hxB' hdeletedNe hxO
  refine ⟨?_, hxB'⟩
  obtain ⟨z, hz, hcorner⟩ := by
    simpa only [FootprintVertices, hAne, ite_true, Set.mem_ofPred_eq] using hxA'
  have hzO : z ∉ O.cells := by
    intro hzO
    apply hxO
    simp only [FootprintVertices, show O.cells.Nonempty from ⟨z, hzO⟩,
      ite_true, Set.mem_ofPred_eq]
    exact ⟨z, hzO, hcorner⟩
  simp only [FootprintVertices, hdeletedNe, ite_true, Set.mem_ofPred_eq]
  exact ⟨z, Finset.mem_sdiff.mpr ⟨hz, hzO⟩, hcorner⟩


private theorem htileA :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let A := cert.P 0 true
        let O := cert.O
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile ia =
            TileCellComplement A O) ) := by
  classical
  intro q cfg C T cert A O ia translation_zero
  rw [cert.modified_tile]
  simp [ia, A, O, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem htileB :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let B := cert.P 0 false
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile ib = B) ) := by
  classical
  intro q cfg C T cert B ib translation_zero
  rw [cert.modified_tile]
  simp [ib, B, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem hadj :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        cert.modified.plane.adjacent ia ib ) := by
  classical
  intro q cfg C T cert ia ib
  rw [cert.modified_adjacency]
  exact .AB 0 0

private theorem hf1 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = ia) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = ib) → h = f ∨ h =
            g) → (f1 = f ∨ f1 = g) ) := by
  classical
  intro q cfg C T cert ia ib f1 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f1, ia, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨1, by simp [f1, ib, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

private theorem hf2 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), (∀ (h :
            cert.modified.plane.Face), ((∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i
            = ia) ∧ ∃ (i : Fin (3 : ℕ)), cert.modified.plane.faceVertex h i = ib) → h = f ∨ h =
            g) → (f2 = f ∨ f2 = g) ) := by
  classical
  intro q cfg C T cert ia ib f2 f g hfaces
  apply hfaces
  constructor
  · exact ⟨0, by simp [f2, ia, cert.modified_face_vertices, SixSubtileFaceVertices]⟩
  · exact ⟨1, by simp [f2, ib, cert.modified_face_vertices, SixSubtileFaceVertices]⟩

private theorem hf12 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        f1 ≠ f2 ) := by
  classical
  intro q cfg C T cert f1 f2 h
  have := congrArg cert.modifiedFaceEquivalence h
  simp [f1, f2] at this

private theorem hexhaust :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let seg := cert.exceptionalSegments
        let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
        (cert.modified.tile ia = TileCellComplement A O) → ((cert.modified.tile ib = B) →
            ((FootprintVertices (cert.modified.tile ia) ∩ FootprintVertices (cert.modified.tile
            ib) = CommonFootprintEdgeVertices (cert.modified.tile ia) (cert.modified.tile ib)) →
            (∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices (cert.modified.tile ia)
            (cert.modified.tile ib)) (FootprintEdges (cert.modified.tile ia) ∩ FootprintEdges
            (cert.modified.tile ib)) (cert.modified.rho f) (cert.modified.rho g)) → ((f1 = f ∨ f1
            = g) → ((f2 = f ∨ f2 = g) → ((f1 ≠ f2) → ((cert.modified.rho f1 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) →
            ((cert.modified.rho f2 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm
            ⟨.I2, 0, 0⟩)) → (∀ z ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices
            B, z ∈ seg.connector))))))))) ) := by
  classical
  intro q cfg C T cert A B O seg ia ib f1 f2 htileA htileB hraw f g hpath hf1 hf2 hf12 hrho1 hrho2
  rcases hf1 with hf1 | hf1 <;> rcases hf2 with hf2 | hf2
  · exact False.elim (hf12 (hf1.trans hf2.symm))
  · rw [← hraw, ← hf1, ← hf2, hrho1, hrho2, htileA, htileB] at hpath
    simpa [htileA, htileB] using
      P3161T2PathExhaustion hpath seg.connector seg.connector_head
        seg.connector_last seg.connector_edges
  · rw [← hraw, ← hf2, ← hf1, hrho2, hrho1, htileA, htileB] at hpath
    have hrevEdges : ∀ x y : GaussianInt, ∀ l r : List GaussianInt,
        seg.connector.reverse = l ++ x :: y :: r →
        {x, y} ∈ FootprintEdges (TileCellComplement A O) ∩ FootprintEdges B := by
      intro x y l r h
      have h' := congrArg List.reverse h
      simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc] at h'
      have he := seg.connector_edges y x r.reverse l.reverse (by simpa using h')
      simpa [Finset.pair_comm] using he
    have hex := P3161T2PathExhaustion hpath seg.connector.reverse
      (by simpa using seg.connector_last) (by simpa using seg.connector_head) hrevEdges
    intro z hz
    apply List.mem_reverse.mp
    apply hex
    simpa [htileA, htileB] using hz
  · exact False.elim (hf12 (hf1.trans hf2.symm))

private theorem hsegMembership :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let seg := cert.exceptionalSegments
        (x ∉ FootprintVertices O → x ∈ FootprintVertices (TileCellComplement A O) ∩
            FootprintVertices B) → ((∀ z ∈ FootprintVertices (TileCellComplement A O) ∩
            FootprintVertices B, z ∈ seg.connector) → ((seg.connector.Sublist seg.walk) → (x ∉
            FootprintVertices O → x ∈ seg.left ∨ x ∈ seg.middle ∨ x ∈ seg.right))) ) := by
  classical
  intro q cfg C T cert x A B O seg hmodifiedCommon hexhaust hconnectorWalk hxO
  have hxwalk : x ∈ seg.walk :=
    hconnectorWalk.subset (hexhaust x (hmodifiedCommon hxO))
  rw [seg.walk_order] at hxwalk
  rcases List.mem_append.mp hxwalk with h | hr
  · rcases List.mem_append.mp h with hl | hm
    · exact Or.inl hl
    · exact Or.inr (Or.inl (List.mem_of_mem_tail hm))
  · exact Or.inr (Or.inr (List.mem_of_mem_tail hr))

private theorem incidentRaw :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    Nat.card
                          { is : Fin (3 : ℕ) × Bool //
                            x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                        (2 : ℕ) →
                      GaussianRealPoint x ≠ TileCentroid T →
                        (∀ (i : Fin 3),
                            ∀ (s : Bool),
                              (i, s) ≠ ((0 : Fin 3), true) →
                                (i, s) ≠ ((0 : Fin 3), false) →
                                x ∈ BoundaryFootprintVertices (cert.P i s) → False) →
                          ∀ (U : ProtoTile),
                            U.cells.Nonempty →
                              x ∈ FootprintVertices U →
                                ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells
    ) := by
  classical
  intro q cfg C T cert x hk hnoncentral noThird U hUne hu
  simp only [FootprintVertices, hUne, ite_true, Set.mem_ofPred_eq] at hu
  rcases hu with ⟨z, hz, hcorner⟩
  rcases hcorner with h | h | h | h
  · refine ⟨0, ?_⟩
    simpa [LatticeVertexIncidentCell] using h ▸ hz
  · refine ⟨1, ?_⟩
    subst x
    simpa [LatticeVertexIncidentCell] using hz
  · refine ⟨3, ?_⟩
    subst x
    simpa [LatticeVertexIncidentCell] using hz
  · refine ⟨2, ?_⟩
    subst x
    change (z + 1 + ⟨0, 1⟩) - 1 - ⟨0, 1⟩ ∈ U.cells
    convert hz using 1; ext <;> simp

private theorem hOpositive :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (GaussianRealPoint x ≠ TileCentroid T) → (
        let O := cert.O
        (TileCentroid O = TileCentroid T) → (x ∈ FootprintVertices O → O.cells.Nonempty)) ) := by
  classical
  intro q cfg C T cert x hnoncentral O hOcent hxO
  by_contra hempty
  have hanchor : x = O.anchor := by
    simpa [FootprintVertices, hempty] using hxO
  have hcent : GaussianRealPoint O.anchor = TileCentroid T := by
    rw [← hOcent]
    simp [GaussianRealPoint, TileCentroid, hempty]
  exact hnoncentral (by simpa [hanchor] using hcent)

private theorem hOcuts :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let seg := cert.exceptionalSegments
        (TileCentroid cert.O = TileCentroid T ∧ (cert.O.cells = ∅ ↔ (cfg.firstPredecessor (1 :
            Fin (4 : ℕ))).1 = (0 : ℤ)) ∧ BandPrototile (cfg.firstPredecessor (1 : Fin (4 : ℕ)))
            cert.O ∧ (Finset.Nonempty cert.O.cells → LatticeTile cert.O) ∧ Finset.Nonempty
            (cert.Q (1 : Fin (3 : ℕ)) true).cells ∧ Finset.Nonempty (cert.S (2 : Fin (3 : ℕ))
            false).cells ∧ (cert.P (0 : Fin (3 : ℕ)) true).cells ∩ (cert.P (0 : Fin (3 : ℕ))
            false).cells = cert.O.cells ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ (j : Fin (3 : ℕ)),
            ∀ (t : Bool), (i, s) ≠ (j, t) → ¬(i = (0 : Fin (3 : ℕ)) ∧ j = (0 : Fin (3 : ℕ))) →
            Disjoint (cert.P i s).cells (cert.P j t).cells) → (((∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ A.cells) ∧ (∃ j : Fin 4, LatticeVertexIncidentCell x
            j ∉ A.cells)) → (((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ B.cells) ∧ (∃ j : Fin
            4, LatticeVertexIncidentCell x j ∉ B.cells)) → ((∀ (U : ProtoTile), TileTranslation U
            0 = U) → ((∀ (U : ProtoTile), (U.cells.Nonempty) → ((x ∈ FootprintVertices U) → (∃ j
            : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → ((x ∈ FootprintVertices O →
            O.cells.Nonempty) → (x ∈ FootprintVertices O → x = seg.a ∨ x = seg.b)))))) ) := by
  classical
  intro q cfg C T cert x A B O seg hpre hIncidentA hIncidentB translation_zero incidentRaw
      hOpositive hxO
  have hOne := hOpositive hxO
  have hOlat : LatticeTile O := hpre.2.2.2.1 hOne
  have hOneCell := incidentRaw O hOne hxO
  have isolated (j : Fin 4) :
      LatticeVertexIncidentCell x j ∈ A.cells ∨
        LatticeVertexIncidentCell x j ∈ B.cells := by
    let z := LatticeVertexIncidentCell x j
    have hsingle : x ∈ FootprintVertices (⟨{z}, z⟩ : ProtoTile) := by
      simp only [FootprintVertices, Finset.singleton_nonempty, ite_true,
        Set.mem_ofPred_eq]
      refine ⟨z, Finset.mem_singleton_self z, ?_⟩
      fin_cases j <;> simp [z, LatticeVertexIncidentCell, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc]
    have hi := cert.precursor_isolated 0 0 x
      (by simpa [O, zero_mul, add_zero, translation_zero] using hxO) z hsingle
    simpa [z, SubtileOccurrenceInterpretation, TileTranslation,
      GaussianTranslation] using hi
  obtain ⟨jA, hjA⟩ := hIncidentA.2
  have hjAB : LatticeVertexIncidentCell x jA ∈ B.cells := by
    rcases isolated jA with h | h
    · exact (hjA h).elim
    · exact h
  have hjAO : LatticeVertexIncidentCell x jA ∉ O.cells := by
    intro hz
    exact hjA (seg.precursor_in_left hz)
  obtain ⟨jB, hjB⟩ := hIncidentB.2
  have hjBA : LatticeVertexIncidentCell x jB ∈ A.cells := by
    rcases isolated jB with h | h
    · exact h
    · exact (hjB h).elim
  have hjBO : LatticeVertexIncidentCell x jB ∉ O.cells := by
    intro hz
    exact hjB (seg.precursor_in_right hz)
  have hDminusIn : LatticeVertexIncidentCell x jA ∈
      (TileCellComplement B O).cells := by
    change LatticeVertexIncidentCell x jA ∈ B.cells \ O.cells
    exact Finset.mem_sdiff.mpr ⟨hjAB, hjAO⟩
  have hDplusIn : LatticeVertexIncidentCell x jB ∈
      (TileCellComplement A O).cells := by
    change LatticeVertexIncidentCell x jB ∈ A.cells \ O.cells
    exact Finset.mem_sdiff.mpr ⟨hjBA, hjBO⟩
  have hOoutsidePlus : LatticeVertexIncidentCell x jA ∉
      (TileCellComplement A O).cells := by
    change LatticeVertexIncidentCell x jA ∉ A.cells \ O.cells
    intro h
    exact hjA (Finset.mem_sdiff.mp h).1
  have hOoutsideMinus : LatticeVertexIncidentCell x jB ∉
      (TileCellComplement B O).cells := by
    change LatticeVertexIncidentCell x jB ∉ B.cells \ O.cells
    intro h
    exact hjB (Finset.mem_sdiff.mp h).1
  have hDplusNe : (TileCellComplement A O).cells.Nonempty :=
    ⟨LatticeVertexIncidentCell x jB, hDplusIn⟩
  have hDminusNe : (TileCellComplement B O).cells.Nonempty :=
    ⟨LatticeVertexIncidentCell x jA, hDminusIn⟩
  have hOB : x ∈ BoundaryFootprintVertices O := by
    exact P3161T2IncidentBoundary O x hOneCell ⟨jA, hjAO⟩
  have hDplusB : x ∈ BoundaryFootprintVertices (TileCellComplement A O) := by
    exact P3161T2IncidentBoundary _ x ⟨jB, hDplusIn⟩ ⟨jA, hOoutsidePlus⟩
  have hDminusB : x ∈ BoundaryFootprintVertices (TileCellComplement B O) := by
    exact P3161T2IncidentBoundary _ x ⟨jA, hDminusIn⟩ ⟨jB, hOoutsideMinus⟩
  rcases cert.precursorBoundary.branch with hbranch | hempty
  · rcases hbranch with ⟨_, plusArc, minusArc, _, _, _, _, _, _, hplusSet,
      hminusSet, _, _, _, hinter, _, _⟩
    have hplus : x ∈ (plusArc.toFinset : Set GaussianInt) := by
      rw [hplusSet]
      exact ⟨hDplusB, hOB⟩
    have hminus : x ∈ (minusArc.toFinset : Set GaussianInt) := by
      rw [hminusSet]
      exact ⟨hDminusB, hOB⟩
    have haa : cert.precursorBoundary.a = seg.a := by
      apply (seg.first_cut_unique cert.precursorBoundary.a).mp
      exact (cert.precursorBoundary.first_transition cert.precursorBoundary.a).mpr rfl
    have hbb : cert.precursorBoundary.b = seg.b := by
      apply (seg.second_cut_unique cert.precursorBoundary.b).mp
      exact (cert.precursorBoundary.second_transition cert.precursorBoundary.b).mpr rfl
    have hpair : x ∈ ({cert.precursorBoundary.a,
        cert.precursorBoundary.b} : Set GaussianInt) := by
      rw [← hinter]
      exact ⟨hplus, hminus⟩
    rw [haa, hbb] at hpair
    simpa using hpair
  · rcases hempty with ⟨he, _, _, _, _, _⟩
    rw [he] at hOne
    simp at hOne

private theorem hsupport :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let A := cert.P 0 true
        let B := cert.P 0 false
        let O := cert.O
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        let R := cert.Q 2 true
        let V := cert.S 1 false
        (FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (1 : Fin
            (3 : ℕ)) true) ⊆ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩
            FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∧ FootprintVertices (cert.P (0 :
            Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ⊆
            FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (2 :
            Fin (3 : ℕ)) false) ∪ FootprintVertices (cert.Q (0 : Fin (3 : ℕ)) false) ∪
            FootprintVertices (cert.Q (2 : Fin (3 : ℕ)) true) ∩ FootprintVertices (cert.S (1 :
            Fin (3 : ℕ)) false)) → ((x ∈ FootprintVertices A) → ((x ∈ FootprintVertices B) → (x ∈
            (FootprintVertices Q ∩ FootprintVertices S) ∪ FootprintVertices O ∪
            (FootprintVertices R ∩ FootprintVertices V)))) ) := by
  classical
  intro q cfg C T cert x A B O Q S R V hrawAB hxA' hxB'
  have hs := hrawAB.2 ⟨hxA', hxB'⟩
  simpa [Q, S, O, R, V, ← cert.precursor_eq] using hs

private theorem hVnonzero :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
            (cfg.firstPredecessor 2 = q 2) → ((cfg.firstPredecessor 2).1 ≠ 0) ) := by
  classical
  intro q cfg hVcoord
  rw [hVcoord]
  exact cfg.noLine 2

private theorem hRnonzero :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
            (cfg.firstPredecessor 3 = q 3) → ((cfg.firstPredecessor 3).1 ≠ 0) ) := by
  classical
  intro q cfg hRcoord
  rw [hRcoord]
  exact cfg.noLine 3

private theorem hp1_not :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let Ctile := cert.P 1 true
        let Q := cert.Q 1 true
        let S := cert.S 2 false
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((∀ (i : Fin 3), ∀ (s :
            Bool), ((i, s) ≠ ((0 : Fin 3), true)) → (((i, s) ≠ ((0 : Fin 3), false)) → ((x ∈
            BoundaryFootprintVertices (cert.P i s)) → (False)))) → (
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (Disjoint S.cells Ctile.cells) → ((Disjoint Q.cells Ctile.cells) → (x ≠ p1)))) ) := by
  classical
  intro q cfg C T cert x Ctile Q S sec noThird p1 hSCdisj hQCd hxp
  have hboundC : p1 ∈ BoundaryFootprintVertices Ctile := by
    apply P3161T2IncidentBoundary Ctile p1
    · obtain ⟨jc, hjc⟩ := sec.first_marked_companion
      exact ⟨jc, hjc⟩
    · rcases sec.first_marked_opposite with hQS | hQC | hSC
      · obtain ⟨j, hq, _⟩ := hQS
        exact ⟨j, fun hc => Finset.disjoint_left.mp hQCd hq hc⟩
      · obtain ⟨j, hq, _⟩ := hQC
        exact ⟨j, fun hc => Finset.disjoint_left.mp hQCd hq hc⟩
      · obtain ⟨j, hs, _⟩ := hSC
        exact ⟨j, fun hc => Finset.disjoint_left.mp hSCdisj hs hc⟩
  exact noThird 1 true (by decide) (by decide)
    (by simpa [hxp] using hboundC)

private theorem hp2_not :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let Dtile := cert.P 1 false
        let R := cert.Q 2 true
        let V := cert.S 1 false
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((∀ (i : Fin 3), ∀ (s :
            Bool), ((i, s) ≠ ((0 : Fin 3), true)) → (((i, s) ≠ ((0 : Fin 3), false)) → ((x ∈
            BoundaryFootprintVertices (cert.P i s)) → (False)))) → (
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        (Disjoint V.cells Dtile.cells) → ((Disjoint R.cells Dtile.cells) → (x ≠ p2)))) ) := by
  classical
  intro q cfg C T cert x Dtile R V sec noThird p2 hVRdisj hRDdisj hxp
  have hboundD : p2 ∈ BoundaryFootprintVertices Dtile := by
    apply P3161T2IncidentBoundary Dtile p2
    · obtain ⟨jd, hjd⟩ := sec.second_marked_companion
      exact ⟨jd, hjd⟩
    · rcases sec.second_marked_opposite with hRS | hRD | hSD
      · obtain ⟨j, hr, _⟩ := hRS
        exact ⟨j, fun hd => Finset.disjoint_left.mp hRDdisj hr hd⟩
      · obtain ⟨j, hr, _⟩ := hRD
        exact ⟨j, fun hd => Finset.disjoint_left.mp hRDdisj hr hd⟩
      · obtain ⟨j, hs, _⟩ := hSD
        exact ⟨j, fun hd => Finset.disjoint_left.mp hVRdisj hs hd⟩
  exact noThird 1 false (by decide) (by decide)
    (by simpa [hxp] using hboundD)

private theorem hcutApositive :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let O := cert.O
        let seg := cert.exceptionalSegments
        (O.cells.Nonempty ∨ x ≠ seg.a) → (x = seg.a → O.cells.Nonempty) ) := by
  classical
  intro q cfg C T cert x O seg hnonemptyO hxa
  rcases hnonemptyO with h | h
  · exact h
  · exact (h hxa).elim

private theorem hcutBpositive :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (GaussianRealPoint x ≠ TileCentroid T) → (
        let O := cert.O
        let seg := cert.exceptionalSegments
        (O.cells = ∅ → GaussianRealPoint seg.a = TileCentroid T) → (x = seg.b →
            O.cells.Nonempty)) ) := by
  classical
  intro q cfg C T cert x hnoncentral O seg hempty_anchor hxb
  by_contra hO
  have hOempty : O.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
  have hcut := seg.empty_cut hOempty
  have hxa : x = seg.a := hxb.trans hcut.1.symm
  have hcen : GaussianRealPoint x = TileCentroid T := by
    rw [hxa]
    exact hempty_anchor hOempty
  exact hnoncentral hcen

private theorem hCnone :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let Ctile := cert.P 1 true
        let O := cert.O
        let seg := cert.exceptionalSegments
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((O.cells.Nonempty ∨ x ≠
            seg.a) → (
        let p1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (x ≠ p1) → ((x ∈ seg.left) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉
            Ctile.cells)))) ) := by
  classical
  intro q cfg C T cert x Ctile O seg sec hnonemptyO p1 hp1_not hleft j hj
  have hc : ∃ k : Fin 4, LatticeVertexIncidentCell x k ∈ Ctile.cells := ⟨j, hj⟩
  have hxP := (sec.left_companion x hleft hnonemptyO).mp hc
  exact hp1_not (by
    have hendpoint : x = p1 := hxP
    simpa [p1] using hendpoint)

private theorem hOnoneAt589 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let O := cert.O
        let seg := cert.exceptionalSegments
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((x ∈ seg.left) → ((¬x =
            seg.a) → (∀ j : Fin 4, LatticeVertexIncidentCell x j ∉ O.cells))) ) := by
  classical
  intro q cfg C T cert x O seg sec hleft hxa j hj
  by_cases hO : O.cells.Nonempty
  · have hxcut := (sec.positive_left_precursor hO x hleft).mp ⟨j, hj⟩
    exact hxa hxcut
  · exact hO ⟨LatticeVertexIncidentCell x j, hj⟩

private theorem hguardR :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let seg := cert.exceptionalSegments
        (¬x = seg.b) → (
        let O := cert.O
        O.cells.Nonempty ∨ x ≠ seg.b) ) := by
  classical
  intro q cfg C T cert x seg hxb O
  by_cases hO : O.cells.Nonempty
  · exact Or.inl hO
  · exact Or.inr hxb

private theorem hDnone :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let Dtile := cert.P 1 false
        let O := cert.O
        let seg := cert.exceptionalSegments
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → (
        let p2 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
        (x ≠ p2) → ((x ∈ seg.right) → ((O.cells.Nonempty ∨ x ≠ seg.b) → (∀ j : Fin 4,
            LatticeVertexIncidentCell x j ∉ Dtile.cells)))) ) := by
  classical
  intro q cfg C T cert x Dtile O seg sec p2 hp2_not hright hguardR j hj
  have hd : ∃ k : Fin 4, LatticeVertexIncidentCell x k ∈ Dtile.cells := ⟨j, hj⟩
  have hxP := (sec.right_companion x hright hguardR).mp hd
  exact hp2_not (by simpa [p2] using hxP)

private theorem hOnoneAt624 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt),
        let seg := cert.exceptionalSegments
        (¬x = seg.b) → (
        let O := cert.O
        (ExceptionalRestorationSectorData (cert.P (0 : Fin (3 : ℕ)) true) (cert.P (0 : Fin (3 :
            ℕ)) false) cert.O (cert.Q (1 : Fin (3 : ℕ)) true) (cert.S (2 : Fin (3 : ℕ)) false)
            (cert.Q (2 : Fin (3 : ℕ)) true) (cert.S (1 : Fin (3 : ℕ)) false) (cert.P (1 : Fin (3
            : ℕ)) true) (cert.P (1 : Fin (3 : ℕ)) false) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I1, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) (cert.unmodified.core.rho
            ((cert.unmodified.faceEquiv.symm : PeriodicSubtileFaceIndex →
            cert.unmodified.core.plane.Face) (⟨SixSubtileFaceLabel.I2, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileFaceIndex))) cert.exceptionalSegments) → ((x ∈ seg.right) → (∀ j :
            Fin 4, LatticeVertexIncidentCell x j ∉ O.cells))) ) := by
  classical
  intro q cfg C T cert x seg hxb O sec hright j hj
  by_cases hO : O.cells.Nonempty
  · have hxcut := (sec.positive_right_precursor hO x hright).mp ⟨j, hj⟩
    exact hxb hxcut
  · exact hO ⟨LatticeVertexIncidentCell x j, hj⟩

end RestoredBoundaryGeometry

theorem P4590T1RestoredBoundaryGeometry :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
        BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
        (LatticeTile T) → (∀ (x : GaussianInt), (x ∈ FootprintVertices T) → ((x ∉
        BoundaryFootprintVertices T) → ((Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) → ((GaussianRealPoint x ≠
          TileCentroid T) → ((x ∈ BoundaryFootprintVertices (cert.P 0 true)) → ((x ∈
          BoundaryFootprintVertices (cert.P 0 false)) → ((x ∈ FootprintVertices (cert.Q 1 true) ∧
          x ∈ FootprintVertices (cert.S 2 false) ∧
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 1 true) ∨ y ∈ FootprintVertices (cert.S 2 false)) ∧
      x ∉ FootprintVertices (cert.P 1 true)) ∨
    (x ∈ FootprintVertices (cert.Q 2 true) ∧ x ∈ FootprintVertices (cert.S 1 false) ∧
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 2 true) ∨ y ∈ FootprintVertices (cert.S 1 false)) ∧
      x ∉ FootprintVertices (cert.P 1 false)) ∨
    (x = cert.exceptionalSegments.a ∧ cert.O.cells.Nonempty) ∨
    (x = cert.exceptionalSegments.b ∧ cert.O.cells.Nonempty)))))))) := by
  intro q cfg C T cert hT x hx hxb hk hnoncentral hA hB
-- BODY
  classical
  let A := cert.P 0 true
  let B := cert.P 0 false
  let Ctile := cert.P 1 true
  let Dtile := cert.P 1 false
  let O := cert.O
  let Q := cert.Q 1 true
  let S := cert.S 2 false
  let R := cert.Q 2 true
  let V := cert.S 1 false
  let seg := cert.exceptionalSegments
  let sec := BandExceptionalRestorationSectorOrder q cfg C T cert
  have hsec := sec
  have hpre := P4339T1PrecursorSupportGeometry C q cfg T cert
  have hABcells : A.cells ∩ B.cells = O.cells := by
    simpa [A, B, O] using hpre.2.2.2.2.2.2.1
  have hsep := hpre.2.2.2.2.2.2.2
  have hABdisj : Disjoint A.cells Ctile.cells := by
    simpa [A, Ctile] using hsep 0 true 1 true (by decide) (by decide)
  have hBDdisj : Disjoint B.cells Dtile.cells := by
    simpa [B, Dtile] using hsep 0 false 1 false (by decide) (by decide)
  have hAne : A.cells.Nonempty :=
    (LatticeTileGridStructure A (cert.parent_lattice 0 true)).1.1
  have hBne : B.cells.Nonempty :=
    (LatticeTileGridStructure B (cert.parent_lattice 0 false)).1.1
  have hOcent : TileCentroid O = TileCentroid T := hpre.1
  have hempty_anchor := RestoredBoundaryGeometry.hempty_anchor q cfg C T cert hOcent
  have hnonemptyO := RestoredBoundaryGeometry.hnonemptyO q cfg C T cert x hnoncentral hempty_anchor
  have rawBoundary (U : ProtoTile) (hUne : U.cells.Nonempty)
      (hb : x ∈ BoundaryFootprintVertices U) : x ∈ FootprintVertices U :=
          RestoredBoundaryGeometry.rawBoundary q cfg C T cert x hk hnoncentral U hUne hb
  have boundary_sectors (U : ProtoTile) (hne : U.cells.Nonempty)
      (hb : x ∈ BoundaryFootprintVertices U) :
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ U.cells) :=
          RestoredBoundaryGeometry.boundary_sectors q cfg C T cert x hk hnoncentral rawBoundary U
              hne hb
  have hIncidentA : (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ A.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ A.cells) :=
    boundary_sectors A hAne (by simpa [A] using hA)
  have hIncidentB : (∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ B.cells) ∧
      (∃ j : Fin 4, LatticeVertexIncidentCell x j ∉ B.cells) :=
    boundary_sectors B hBne (by simpa [B] using hB)
  have noThird := RestoredBoundaryGeometry.noThird q cfg C T cert x hk hA hB
  have hnotO := RestoredBoundaryGeometry.hnotO q cfg C T cert x hnoncentral hOcent
  have hrawAB := BandOrderedGeneralRawSupport q cfg C T cert
  have hxA' := rawBoundary A hAne (by simpa [A] using hA)
  have hxB' := rawBoundary B hBne (by simpa [B] using hB)
  have hdeletedNe : (TileCellComplement A O).cells.Nonempty :=
    (LatticeTileGridStructure _ cert.precursor_complement_lattice.1).1.1
  have hmodifiedCommon := RestoredBoundaryGeometry.hmodifiedCommon q cfg C T cert x hAne hxA'
      hxB' hdeletedNe
  let ia : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let ib : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
  let f2 := cert.modifiedFaceEquivalence.symm ⟨.I2, 0, 0⟩
  have translation_zero := TileTranslationProperties.zero
  have htileA := RestoredBoundaryGeometry.htileA q cfg C T cert translation_zero
  have htileB := RestoredBoundaryGeometry.htileB q cfg C T cert translation_zero
  have hab : ia ≠ ib := by decide
  have habedge := cert.modified.adjacent_has_common_edge ia ib (RestoredBoundaryGeometry.hadj q
      cfg C T cert)
  obtain ⟨hclassification, hregular⟩ := PeriodicTileIntersectionClassification cert.modified
  have hraw := ((hclassification ia ib hab).2.1 habedge).2
  obtain ⟨_, f, g, hfg, hf, hg, hfaces, hpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular ia ib hab).1.mpr habedge
  have hrho1 : cert.modified.rho f1 =
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩) :=
    cert.modified_face_points _
  have hrho2 : cert.modified.rho f2 =
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩) :=
    cert.modified_face_points _
  have hconnectorWalk : seg.connector.Sublist seg.walk := seg.connector_from_walk
  have hsegMembership := RestoredBoundaryGeometry.hsegMembership q cfg C T cert x hmodifiedCommon
      (RestoredBoundaryGeometry.hexhaust q cfg C T cert htileA htileB hraw f g hpath
      (RestoredBoundaryGeometry.hf1 q cfg C T cert f g hfaces) (RestoredBoundaryGeometry.hf2 q
      cfg C T cert f g hfaces) (RestoredBoundaryGeometry.hf12 q cfg C T cert) hrho1 hrho2)
      hconnectorWalk
  have incidentRaw := RestoredBoundaryGeometry.incidentRaw q cfg C T cert x hk hnoncentral noThird
  have hOpositive := RestoredBoundaryGeometry.hOpositive q cfg C T cert x hnoncentral hOcent
  have hOcuts := RestoredBoundaryGeometry.hOcuts q cfg C T cert x hpre hIncidentA hIncidentB
      translation_zero incidentRaw hOpositive
  have hsupport := RestoredBoundaryGeometry.hsupport q cfg C T cert x hrawAB hxA' hxB'
  let p1 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
  let p2 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I2, 0, 0⟩)
  have hQne : Q.cells.Nonempty := hpre.2.2.2.2.1
  have hSne : S.cells.Nonempty := hpre.2.2.2.2.2.1
  have hCparent : LatticeTile Ctile := cert.parent_lattice 1 true
  have hDparent : LatticeTile Dtile := cert.parent_lattice 1 false
  have hCne : Ctile.cells.Nonempty := (LatticeTileGridStructure _ hCparent).1.1
  have hDne : Dtile.cells.Nonempty := (LatticeTileGridStructure _ hDparent).1.1
  have hVcurv :=
    (ProperBandCurvatureStructure cfg.firstPredecessor cfg.firstProper).2.1 1
  have hVcoord : cfg.firstPredecessor 2 = q 2 := cfg.firstParentTwo
  have hVpos : 0 < (cfg.firstPredecessor 2).1 :=
    lt_of_le_of_ne hVcurv (Ne.symm (RestoredBoundaryGeometry.hVnonzero q cfg hVcoord))
  have hVlat : LatticeTile V :=
    P4590T1PositivePrototileDisk (cfg.firstPredecessor 2) V
      (cert.minus_occurrence 1 false).1 hVpos
  have hVne : V.cells.Nonempty := (LatticeTileGridStructure _ hVlat).1.1
  have hRcurv :=
    (ProperBandCurvatureStructure cfg.firstPredecessor cfg.firstProper).2.1 2
  have hRcoord : cfg.firstPredecessor 3 = q 3 := cfg.firstParentThree
  have hRpos : 0 < (cfg.firstPredecessor 3).1 :=
    lt_of_le_of_ne hRcurv (Ne.symm (RestoredBoundaryGeometry.hRnonzero q cfg hRcoord))
  have hRlat : LatticeTile R :=
    P4590T1PositivePrototileDisk (cfg.firstPredecessor 3) R
      (cert.plus_occurrence 2 true).1 hRpos
  have hRne : R.cells.Nonempty := (LatticeTileGridStructure _ hRlat).1.1
  have touchingDisjoint := TileTouchingDisjoint.cells
  have hSCdisj : Disjoint S.cells Ctile.cells :=
    touchingDisjoint S Ctile hSne hCne cert.double_first.2.1
  have hCQdisj : Disjoint Ctile.cells Q.cells :=
    touchingDisjoint Ctile Q hCne hQne cert.double_first.2.2.1
  have hQCd : Disjoint Q.cells Ctile.cells := hCQdisj.symm
  have hVRdisj : Disjoint V.cells Dtile.cells := by
    exact touchingDisjoint V Dtile hVne hDne cert.double_second.2.1
  have hDRdisj : Disjoint Dtile.cells R.cells :=
    touchingDisjoint Dtile R hDne hRne cert.double_second.2.2.1
  have hRDdisj : Disjoint R.cells Dtile.cells := hDRdisj.symm
  have hp1_not := RestoredBoundaryGeometry.hp1_not q cfg C T cert x sec noThird hSCdisj hQCd
  have hp2_not := RestoredBoundaryGeometry.hp2_not q cfg C T cert x sec noThird hVRdisj hRDdisj
  have hcutApositive := RestoredBoundaryGeometry.hcutApositive q cfg C T cert x hnonemptyO
  have hcutBpositive := RestoredBoundaryGeometry.hcutBpositive q cfg C T cert x hnoncentral
      hempty_anchor
  by_cases hxO : x ∈ FootprintVertices O
  · rcases hOcuts hxO with hxA | hxB
    · exact Or.inr (Or.inr (Or.inl ⟨hxA, hOpositive hxO⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hxB, hOpositive hxO⟩))
  · rcases hsegMembership hxO with hleft | hmiddle | hright
    · by_cases hxa : x = seg.a
      · exact Or.inr (Or.inr (Or.inl ⟨hxa, hcutApositive hxa⟩))
      · by_cases hxb : x = seg.b
        · exact Or.inr (Or.inr (Or.inr ⟨hxb, hcutBpositive hxb⟩))
        · have hCnone := RestoredBoundaryGeometry.hCnone q cfg C T cert x sec hnonemptyO hp1_not
            hleft
          have hOnone := RestoredBoundaryGeometry.hOnoneAt589 q cfg C T cert x sec hleft hxa
          have hopp := sec.left_opposite x hleft hnonemptyO hCnone hOnone
          have hvertices := seg.left_vertices x hleft
          exact Or.inl ⟨hvertices.1, hvertices.2,
            P4590T1OppositeCellsStar Q S x hopp, by
              intro hxC
              obtain ⟨j, hj⟩ := incidentRaw Ctile hCne hxC
              exact hCnone j hj⟩
    · by_cases hxa : x = seg.a
      · exact Or.inr (Or.inr (Or.inl ⟨hxa, hcutApositive hxa⟩))
      · by_cases hxb : x = seg.b
        · exact Or.inr (Or.inr (Or.inr ⟨hxb, hcutBpositive hxb⟩))
        · have hcommon : x ∈ BoundaryFootprintVertices A ∩
              BoundaryFootprintVertices B := ⟨by simpa [A] using hA, by simpa [B] using hB⟩
          have hnotcommon := sec.proper_middle_not_original_common x hmiddle hxa hxb
          exact False.elim (hnotcommon hcommon)
    · by_cases hxa : x = seg.a
      · exact Or.inr (Or.inr (Or.inl ⟨hxa, hcutApositive hxa⟩))
      · by_cases hxb : x = seg.b
        · exact Or.inr (Or.inr (Or.inr ⟨hxb, hcutBpositive hxb⟩))
        · have hguardR := RestoredBoundaryGeometry.hguardR q cfg C T cert x hxb
          have hDnone := RestoredBoundaryGeometry.hDnone q cfg C T cert x sec hp2_not hright hguardR
          have hOnone := RestoredBoundaryGeometry.hOnoneAt624 q cfg C T cert x hxb sec hright
          have hopp := sec.right_opposite x hright hguardR hDnone hOnone
          have hvertices := seg.right_vertices x hright
          exact Or.inr (Or.inl ⟨hvertices.1, hvertices.2,
            P4590T1OppositeCellsStar R V x hopp, by
              intro hxD
              obtain ⟨j, hj⟩ := incidentRaw Dtile hDne hxD
              exact hDnone j hj⟩)

end ApollonianSuperharmonic

end
