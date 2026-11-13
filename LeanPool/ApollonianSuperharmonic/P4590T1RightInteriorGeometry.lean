/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion
public import LeanPool.ApollonianSuperharmonic.LatticeFootprintIncidence
public import LeanPool.ApollonianSuperharmonic.PairAssignmentFacts
public import LeanPool.ApollonianSuperharmonic.BandLayoutCentroidCoordinates
public import LeanPool.ApollonianSuperharmonic.BandLayoutFaceSupport

public import LeanPool.ApollonianSuperharmonic.P4590T1PositivePrototileDisk
public import LeanPool.ApollonianSuperharmonic.P4590T1OppositeCellsStar
public import LeanPool.ApollonianSuperharmonic.LatticeEdgeRegularity
public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas

-- [TABLET NODE: P4590T1RightInteriorGeometry]

/-!
# P4590T1RightInteriorGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RightInteriorGeometry

private abbrev ht :=
  BandLayoutCentroidCoordinates.doubledCenter

private theorem hHcells :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        ∀ (U : ProtoTile), (H U).cells = U.cells.image tau ) := by
  classical
  intro q u w t H tau U
  simp only [H, TileTranslation, TileHalfTurn, Finset.image_image]
  apply Finset.image_congr
  intro z hz
  apply Zsqrtd.ext <;>
    simp [GaussianTranslation, tau] <;> ring

private theorem halfTurnRealization :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        ((t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) → (
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        ∀ (U : ProtoTile), TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid
            T).1 - p.1, 2 * (TileCentroid T).2 - p.2)) '' TileRealization U) ) := by
  classical
  intro q T u w t ht H U
  change TileRealization (TileTranslation (TileHalfTurn U) t) = _
  rw [(TileTranslationFormulas (TileHalfTurn U) t).2.2.2.1,
    (TileHalfTurnFormulas U).2.2.2.2.2.1, Set.image_image]
  congr 1
  funext p
  apply Prod.ext <;> simp [ht.1, ht.2] <;> ring

private theorem halfTurnFootprint :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        ∀ (U : ProtoTile), FootprintVertices (H U) = (fun z : GaussianInt => t - z) ''
            FootprintVertices U ) := by
  classical
  intro q u w t H U
  change FootprintVertices (TileTranslation (TileHalfTurn U) t) = _
  rw [(TileTranslationFormulas (TileHalfTurn U) t).2.2.2.2.2.1,
    (TileHalfTurnFormulas U).2.2.2.2.2.2.1, Set.image_image]
  congr 1
  funext z
  apply Zsqrtd.ext <;> simp [GaussianTranslation] <;> ring

private theorem halfTurnBoundary :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        ∀ (U : ProtoTile), (U.cells.Nonempty) → (BoundaryFootprintVertices (H U) = (fun z :
            GaussianInt => t - z) '' BoundaryFootprintVertices U) ) := by
  classical
  intro q u w t H U hne
  have hcells : (TileHalfTurn U).cells =
      (TileQuarterTurn (TileQuarterTurn U)).cells :=
    (TileHalfTurnFormulas U).2.2.2.2.1
  have hhalfne : (TileHalfTurn U).cells.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hne.ne_empty ((TileHalfTurnFormulas U).2.2.1.mp he)
  have hhalfBound : BoundaryFootprintVertices (TileHalfTurn U) =
      BoundaryFootprintVertices (TileQuarterTurn (TileQuarterTurn U)) := by
    have hempty : (TileHalfTurn U).cells = ∅ →
        (TileHalfTurn U).anchor =
          (TileQuarterTurn (TileQuarterTurn U)).anchor := by
      intro h
      exact False.elim (hhalfne.ne_empty h)
    exact (ProtoTileObservableExtensionality _ _ hcells hempty).2.1
  have hquarterBound :
      BoundaryFootprintVertices (TileQuarterTurn (TileQuarterTurn U)) =
        (fun z : GaussianInt => -z) '' BoundaryFootprintVertices U := by
    rw [(TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.2.2.2.2.1,
      (TileQuarterTurnFormulas U).2.2.2.2.2.2.2.1, Set.image_image]
    congr 1
  change BoundaryFootprintVertices (TileTranslation (TileHalfTurn U) t) = _
  rw [(TileTranslationFormulas (TileHalfTurn U) t).2.2.2.2.2.2.2.1,
    hhalfBound, hquarterBound, Set.image_image]
  congr 1
  funext z
  apply Zsqrtd.ext <;> simp [GaussianTranslation] <;> ring

private theorem cells_of_realization :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), (TileRealization U = TileRealization V) → (U.cells
            = V.cells) ) := by
  classical
  intro U V hreal
  ext a
  rw [← P3776T1CellCenterMembership U a,
    ← P3776T1CellCenterMembership V a, hreal]

private theorem outerRealization :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (U : ProtoTile), TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid
            T).1 - p.1, 2 * (TileCentroid T).2 - p.2)) '' TileRealization U) → ((∀ (i : Fin (3 :
            ℕ)),
        let w := BandVectors.1 (q (i + (2 : Fin (3 : ℕ))).succ) (q (i + (1 : Fin (3 : ℕ))).succ);
        let u := GaussianQuarterTurn w - w; (TileTranslation (cert.P i true) u).cells = (cert.P i
            false).cells ∧ ((cert.P i true).cells = ∅ → (TileTranslation (cert.P i true)
            u).anchor = (cert.P i false).anchor) ∧ FootprintVertices (TileTranslation (cert.P i
            true) u) = FootprintVertices (cert.P i false) ∧ TileCentroid (TileTranslation (cert.P
            i true) u) = TileCentroid (cert.P i false) ∧ TileArea (cert.P i true) = TileArea
            (cert.P i false) ∧ CentrallyReflectedAt (TileCentroid T) (cert.P i true) (cert.P i
            false)) → (∀ (i : Fin 3), TileRealization (H (cert.P i true)) = TileRealization
            (cert.P i false))) ) := by
  classical
  intro q cfg C T cert u w t H halfTurnRealization signedOuter i
  rw [halfTurnRealization]
  have houter := (signedOuter i).2.2.2.2.2
  simpa using houter.symm

private theorem outerFootprint :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (i : Fin 3), (H (cert.P i true)).cells = (cert.P i false).cells) → ((∀ (i : Fin 3), ∀
            (s : Bool), (cert.P i s).cells.Nonempty) → (∀ (i : Fin 3), FootprintVertices (H
            (cert.P i true)) = FootprintVertices (cert.P i false))) ) := by
  classical
  intro q cfg C T cert u w t H outerCells outerNonempty i
  have hempty : (H (cert.P i true)).cells = ∅ →
      (H (cert.P i true)).anchor = (cert.P i false).anchor := by
    intro hh
    have : (cert.P i false).cells = ∅ := by rw [← outerCells i]; exact hh
    exact False.elim ((outerNonempty i false).ne_empty this)
  exact (ProtoTileObservableExtensionality (H (cert.P i true))
    (cert.P i false) (outerCells i) hempty).1

private theorem outerBoundary :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (i : Fin 3), (H (cert.P i true)).cells = (cert.P i false).cells) → ((∀ (i : Fin 3), ∀
            (s : Bool), (cert.P i s).cells.Nonempty) → (∀ (i : Fin 3), BoundaryFootprintVertices
            (H (cert.P i true)) = BoundaryFootprintVertices (cert.P i false))) ) := by
  classical
  intro q cfg C T cert u w t H outerCells outerNonempty i
  have hempty : (H (cert.P i true)).cells = ∅ →
      (H (cert.P i true)).anchor = (cert.P i false).anchor := by
    intro hh
    have : (cert.P i false).cells = ∅ := by rw [← outerCells i]; exact hh
    exact False.elim ((outerNonempty i false).ne_empty this)
  exact (ProtoTileObservableExtensionality (H (cert.P i true))
    (cert.P i false) (outerCells i) hempty).2.1


private theorem twoPathEdges :
    (by
      classical
      exact
        (∀ (l : List GaussianInt), ∀ (x : GaussianInt), ∀ (h : GaussianInt), ∀ (t : GaussianInt),
            l.Nodup → l.head? = some h → l.getLast? = some t → x ∈ l → x ≠ h → x ≠ t → ∃ pre y z
            post, l = pre ++ y :: x :: z :: post) → (∀ (v : GaussianInt), ∀ (V : Set
            GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (SimpleGridPathBetween V E a b) → ((v ∈ V) → ((v ≠ a) → ((v ≠ b) → (∃ y
            z : GaussianInt, ∃ e f : Finset GaussianInt, e ≠ f ∧ v ∈ e ∧ v ∈ f ∧ e ∈ E ∧ f ∈ E ∧
            e = {y, v} ∧ f = {v, z} ∧ FourNeighborAdjacent y v ∧ FourNeighborAdjacent v z))))) )
            := by
  classical
  intro splitInternal v V E a b hpath hxV hxa hxb
  rcases hpath with ⟨p, hp, hlen, hhead, hlast, hV, hstep, hE⟩
  have hxp : v ∈ p := by
    rw [hV] at hxV
    simpa using hxV
  obtain ⟨pre, y, z, post, hlist⟩ :=
    splitInternal p v a b hp hhead hlast hxp hxa hxb
  have he₁ : {y, v} ∈ E :=
    (hE {y, v}).2 ⟨y, v, pre, z :: post, hlist, rfl⟩
  have he₂ : {v, z} ∈ E :=
    (hE {v, z}).2 ⟨v, z, pre ++ [y], post, by
      rw [hlist]
      simp [List.append_assoc], rfl⟩
  have hstep₁ := hstep y v pre (z :: post) hlist
  have hstep₂ := hstep v z (pre ++ [y]) post (by
    rw [hlist]
    simp [List.append_assoc])
  have hnod := hp
  rw [hlist] at hnod
  have htail : (y :: v :: z :: post).Nodup :=
    (List.nodup_append.mp hnod).2.1
  have hnot : y ∉ v :: z :: post := (List.nodup_cons.mp htail).1
  have hyx : y ≠ v := by intro h; exact hnot (by simp [h])
  have hyz : y ≠ z := by intro h; exact hnot (by simp [h])
  have hne : ({y, v} : Finset GaussianInt) ≠ {v, z} := by
    intro h
    have hy' : y = v ∨ y = z := by
      have : y ∈ ({v, z} : Finset GaussianInt) := by rw [← h]; simp
      simpa using this
    rcases hy' with hy' | hy'
    · exact hyx (by simpa using hy')
    · exact hyz hy'
  refine ⟨y, z, {y, v}, {v, z}, hne, by simp, by simp, he₁, he₂, rfl, rfl,
    ?_, ?_⟩
  · simpa [FourNeighborAdjacent] using hstep₁
  · simpa [FourNeighborAdjacent] using hstep₂

private theorem touching_disjoint :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), (U.cells.Nonempty) →
            ((V.cells.Nonempty) → ((TouchingTriple U V W) → (Disjoint U.cells V.cells))) ) := by
  classical
  intro U V W hUne hVne ht
  rcases ht with ht | ht | ht
  · exact ht.2.2.1
  · rw [ht.1] at hUne
    simp at hUne
  · rw [ht.1] at hVne
    simp at hVne

private abbrev rawIncident := ApollonianSuperharmonic.LatticeFootprintIncidence.incidentCell

private abbrev edgeEndpoint := ApollonianSuperharmonic.BoundaryFootprintInclusion.edgeVertex

private theorem threeBoundaries :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (z : GaussianInt), (U.cells.Nonempty) → ((z ∈ FootprintVertices U)
            → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ U.cells))) → (∀ (z : GaussianInt), ∀
            (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), (LatticeTile U) →
            ((LatticeTile V) → ((LatticeTile W) → ((Disjoint U.cells W.cells) → ((Disjoint
            V.cells W.cells) → ((z ∈ FootprintVertices U) → ((z ∈ FootprintVertices V) → ((z ∈
            FootprintVertices W) → (z ∈ BoundaryFootprintVertices U ∧ z ∈
            BoundaryFootprintVertices V ∧ z ∈ BoundaryFootprintVertices W))))))))) ) := by
  classical
  intro rawIncident z U V W hU hV hW hUW hVW hzU hzV hzW
  have hUne := (LatticeTileGridStructure U hU).1.1
  have hVne := (LatticeTileGridStructure V hV).1.1
  have hWne := (LatticeTileGridStructure W hW).1.1
  obtain ⟨jU, hjU⟩ := rawIncident U z hUne hzU
  obtain ⟨jV, hjV⟩ := rawIncident V z hVne hzV
  obtain ⟨jW, hjW⟩ := rawIncident W z hWne hzW
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact P3161T2IncidentBoundary U z ⟨jU, hjU⟩
      ⟨jW, fun h => Finset.disjoint_left.mp hUW h hjW⟩
  · exact P3161T2IncidentBoundary V z ⟨jV, hjV⟩
      ⟨jW, fun h => Finset.disjoint_left.mp hVW h hjW⟩
  · exact P3161T2IncidentBoundary W z ⟨jW, hjW⟩
      ⟨jU, fun h => Finset.disjoint_left.mp hUW hjU h⟩

private theorem threeOwnersContradict :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (v : GaussianInt),
                    ∀ (z : GaussianInt),
                      Nat.card
                            { is : Fin 3 × Bool //
                              v ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                          2 →
                        z = v →
                          z ∈ BoundaryFootprintVertices (cert.P 0 true) →
                            z ∈ BoundaryFootprintVertices (cert.P 0 false) →
                              z ∈ BoundaryFootprintVertices (cert.P 1 true) → False
    ) := by
  classical
  intro q cfg C T cert v z hcount hzx hA hB hC
  subst z
  let S := {is : Fin 3 × Bool //
    v ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
  let f : Fin 3 → S := ![
    ⟨(0, true), hA⟩,
    ⟨(0, false), hB⟩,
    ⟨(1, true), hC⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hval ⊢
  have hcard := Fintype.card_le_of_injective f hf
  have hk' : Fintype.card S = 2 := by
    simpa [S, Nat.card_eq_fintype_card] using hcount
  have hcard' : 3 ≤ Fintype.card S := by simpa using hcard
  omega

private theorem threeOwnersAFContradict :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (v : GaussianInt),
                    ∀ (z : GaussianInt),
                      Nat.card
                            { is : Fin 3 × Bool //
                              v ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                          2 →
                        z = v →
                          z ∈ BoundaryFootprintVertices (cert.P 0 true) →
                            z ∈ BoundaryFootprintVertices (cert.P 1 true) →
                              z ∈ BoundaryFootprintVertices (cert.P 2 false) → False
    ) := by
  classical
  intro q cfg C T cert v z hcount hzx hA hC hF
  subst z
  let S := {is : Fin 3 × Bool //
    v ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
  let f : Fin 3 → S := ![
    ⟨(0, true), hA⟩,
    ⟨(1, true), hC⟩,
    ⟨(2, false), hF⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hval ⊢
  have hcard := Fintype.card_le_of_injective f hf
  have hk' : Fintype.card S = 2 := by
    simpa [S, Nat.card_eq_fintype_card] using hcount
  have hcard' : 3 ≤ Fintype.card S := by simpa using hcard
  omega

private theorem interfaceConclusion :
    (by
      classical
      exact
        ∀ (v : GaussianInt),
          ∀ (U : ProtoTile),
            ∀ (V : ProtoTile),
              LatticeTile U →
                LatticeTile V →
                  Disjoint U.cells V.cells →
                    (∃ e f : Finset GaussianInt,
                        e ≠ f ∧
                          v ∈ e ∧
                            v ∈ f ∧
                              e ∈ FootprintEdges U ∩ FootprintEdges V ∧
                                f ∈ FootprintEdges U ∩ FootprintEdges V) →
                      (∀ y,
                          y = v ∨
                              y = v + 1 ∨ y = v - 1 ∨ y = v + ⟨0, 1⟩ ∨ y = v - ⟨0, 1⟩ →
                            y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) ∧
                        ∀ z,
                          z = v ∨ z = v - 1 ∨ z = v - ⟨0, 1⟩ ∨ z = v - 1 - ⟨0, 1⟩ →
                            z ∈ U.cells ∨ z ∈ V.cells
    ) := by
  classical
  intro v U V hU hV hdis hedges
  have sec := (LocalLatticeInterfaceSectors.2 U V v hU hV hdis hedges)
  refine ⟨P4590T1OppositeCellsStar U V v sec.2, ?_⟩
  intro z hz
  have hzindex : ∃ j : Fin 4, z = LatticeVertexIncidentCell v j := by
    rcases hz with hz | hz | hz | hz
    · subst z
      exact ⟨0, by simp [LatticeVertexIncidentCell]⟩
    · subst z
      exact ⟨1, by simp [LatticeVertexIncidentCell]⟩
    · subst z
      exact ⟨3, by simp [LatticeVertexIncidentCell]⟩
    · subst z
      exact ⟨2, by simp [LatticeVertexIncidentCell]⟩
  obtain ⟨j, rfl⟩ := hzindex
  rcases sec.1 j with hUcell | hVcell
  · exact Or.inl hUcell
  · exact Or.inr hVcell


private theorem htileA :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile a = TileCellComplement
            (cert.P 0 true) cert.O) ) := by
  classical
  intro q cfg C T cert a translation_zero
  rw [cert.modified_tile]
  simp [a, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem htileC :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → (cert.modified.tile c = cert.P 1 true) )
            := by
  classical
  intro q cfg C T cert c translation_zero
  rw [cert.modified_tile]
  simp [c, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem hOA :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), cert.O.cells ⊆ (cert.P 0 true).cells ) := by
  classical
  intro q cfg C T cert cell hc
  apply (cert.plus_union cell).mpr
  rw [cert.precursor_eq] at hc
  exact ⟨0, false, hc⟩

private theorem hOB :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), cert.O.cells ⊆ (cert.P 0 false).cells ) := by
  classical
  intro q cfg C T cert cell hc
  apply (cert.minus_union cell).mpr
  rw [cert.precursor_cells] at hc
  exact ⟨0, true, hc⟩

private theorem hCA :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (Disjoint (cert.P 1 true).cells (cert.P 0 true).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  simpa [c, a, SubtileOccurrenceInterpretation, translation_zero] using
    hsep c a (by decide) (by simp [c, a])

private theorem hCB :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (Disjoint (cert.P 1 true).cells (cert.P 0 false).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  simpa [c, b, SubtileOccurrenceInterpretation, translation_zero] using
    hsep c b (by decide) (by simp [c, b])

private theorem hisolated :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (∀ (U : ProtoTile), TileTranslation U 0 = U) → (∀ z ∈
            CellSupportedFootprintVertices cert.O, ∀ cell : GaussianInt, z ∈ FootprintVertices
            (⟨{cell}, cell⟩ : ProtoTile) → cell ∈ (cert.P 0 true).cells ∨ cell ∈ (cert.P 0
            false).cells) ) := by
  classical
  intro q cfg C T cert translation_zero z hz cell hc
  have hzraw : z ∈ FootprintVertices cert.O := by
    rcases hz with ⟨a0, ha0, hcorner⟩
    simpa only [FootprintVertices,
      ite_eq_left (show cert.O.cells.Nonempty from ⟨a0, ha0⟩), Set.mem_ofPred_eq] using
      (show ∃ a0 ∈ cert.O.cells,
        z = a0 ∨ z = a0 + 1 ∨ z = a0 + ⟨0, 1⟩ ∨
          z = a0 + 1 + ⟨0, 1⟩ from ⟨a0, ha0, hcorner⟩)
  simpa [SubtileOccurrenceInterpretation, translation_zero] using
    cert.precursor_isolated 0 0 z
      (by simpa [translation_zero] using hzraw) cell hc

private abbrev hf1 :=
  BandLayoutFaceSupport.firstFace

private abbrev hf3 :=
  BandLayoutFaceSupport.thirdFace

private theorem hf13 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        f1 ≠ f3 ) := by
  classical
  intro q cfg C T cert f1 f3 h
  have hh := congrArg cert.modifiedFaceEquivalence h
  simp [f1, f3] at hh

private theorem hend :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile c)) (FootprintEdges (cert.modified.tile a) ∩ FootprintEdges
            (cert.modified.tile c)) (cert.modified.rho f) (cert.modified.rho g)) →
            (cert.modified.rho f ≠ cert.modified.rho g) ) := by
  classical
  intro q cfg C T cert a c f g hpath heq
  rcases hpath with ⟨p, hnd, hlen, hh, ht, _, _, _⟩
  have hpne : p ≠ [] := by
    intro hp
    simp [hp] at hlen
  have hh' : p.head hpne = cert.modified.rho f := by
    simpa [List.head?_eq_some_head hpne] using hh
  have ht' : p.getLast hpne = cert.modified.rho g := by
    simpa [List.getLast?_eq_some_getLast hpne] using ht
  obtain ⟨z, hz⟩ := (List.Nodup.head_eq_getLast_iff hpne hnd).mp
    (hh'.trans (heq.trans ht'.symm))
  simp [hz] at hlen

private theorem hz13 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        ∀ (f : cert.modified.plane.Face), ∀ (g : cert.modified.plane.Face), ((f1 = f ∧ f3 = g) ∨
            (f1 = g ∧ f3 = f)) → ((cert.modified.rho f1 = cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) → ((cert.modified.rho f3 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) →
            ((cert.modified.rho f ≠ cert.modified.rho g) → (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩) ≠ cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩))))) ) := by
  classical
  intro q cfg C T cert f1 f3 f g hpair hrho1 hrho3 hend
  rw [← hrho1, ← hrho3]
  rcases hpair with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · simpa [h1, h3] using hend
  · simpa [h1, h3] using hend.symm

private theorem hcomplete :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.tile
            c = cert.P 1 true) → ((FootprintVertices (cert.modified.tile a) ∩ FootprintVertices
            (cert.modified.tile c) = CommonFootprintEdgeVertices (cert.modified.tile a)
            (cert.modified.tile c)) → (∀ (f : cert.modified.plane.Face), ∀ (g :
            cert.modified.plane.Face), (SimpleGridPathBetween (CommonFootprintEdgeVertices
            (cert.modified.tile a) (cert.modified.tile c)) (FootprintEdges (cert.modified.tile a)
            ∩ FootprintEdges (cert.modified.tile c)) (cert.modified.rho f) (cert.modified.rho g))
            → (((f1 = f ∧ f3 = g) ∨ (f1 = g ∧ f3 = f)) → ((cert.modified.rho f1 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) →
            ((cert.modified.rho f3 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm
            ⟨.I3, 0, 0⟩)) → (SimpleGridPathBetween (FootprintVertices (TileCellComplement (cert.P
            0 true) cert.O) ∩ FootprintVertices (cert.P 1 true)) (FootprintEdges
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintEdges (cert.P 1 true))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) ∨
            SimpleGridPathBetween (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)
            ∩ FootprintVertices (cert.P 1 true)) (FootprintEdges (TileCellComplement (cert.P 0
            true) cert.O) ∩ FootprintEdges (cert.P 1 true)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))))))))) ) := by
  classical
  intro q cfg C T cert a c f1 f3 htileA htileC hraw f g hpath hpair hrho1 hrho3
  rw [← hraw, htileA, htileC] at hpath
  rcases hpair with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · left
    simpa [← h1, ← h3, hrho1, hrho3] using hpath
  · right
    simpa [← h3, ← h1, hrho1, hrho3] using hpath

private theorem hcompleteOriginal :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintEdges (cert.P 1 true) = FootprintEdges (cert.P 0 true) ∩ FootprintEdges
            (cert.P 1 true)) → ((FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true) = FootprintVertices (cert.P 0 true) ∩
            FootprintVertices (cert.P 1 true)) → ((SimpleGridPathBetween (FootprintVertices
            (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintVertices (cert.P 1 true))
            (FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩ FootprintEdges (cert.P
            1 true)) (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) ∨
            SimpleGridPathBetween (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)
            ∩ FootprintVertices (cert.P 1 true)) (FootprintEdges (TileCellComplement (cert.P 0
            true) cert.O) ∩ FootprintEdges (cert.P 1 true)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))) → (SimpleGridPathBetween
            (FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P 1 true))
            (FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) ∨
            SimpleGridPathBetween (FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P
            1 true)) (FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))))) ) := by
  classical
  intro q cfg C T cert hretainEdges hretainVertices hcomplete
  rcases hcomplete with h | h
  · exact Or.inl (by simpa [hretainVertices, hretainEdges] using h)
  · exact Or.inr (by simpa [hretainVertices, hretainEdges] using h)

private theorem htileB :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (∀ (U : ProtoTile), TileTranslation U 0 = U) → (
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        cert.modified.tile b = cert.P 0 false) ) := by
  classical
  intro q cfg C T cert translation_zero b
  rw [cert.modified_tile]
  simp [b, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem htileF :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (∀ (U : ProtoTile), TileTranslation U 0 = U) → (
        let fidx : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        cert.modified.tile fidx = cert.P 2 false) ) := by
  classical
  intro q cfg C T cert translation_zero fidx
  rw [cert.modified_tile]
  simp [fidx, ModifiedSubtileOccurrenceInterpretation, translation_zero]

private theorem hz1Amod :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.rho
            f1 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) →
            ((cert.modified.plane.faceVertex f1 0 = a) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        z1 ∈ FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)))) ) := by
  classical
  intro q cfg C T cert a f1 htileA hrho1 hfa10 z1
  have hh := cert.modified.rho_common f1 0
  rw [hfa10, htileA, hrho1] at hh
  simpa [z1] using hh

private theorem hz1B :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        (cert.modified.rho f1 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0,
            0⟩)) → (
        let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
        (cert.modified.tile b = cert.P 0 false) → ((cert.modified.plane.faceVertex f1 1 = b) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        z1 ∈ FootprintVertices (cert.P 0 false)))) ) := by
  classical
  intro q cfg C T cert f1 hrho1 b htileB hfa11 z1
  have hh := cert.modified.rho_common f1 1
  rw [hfa11, htileB, hrho1] at hh
  simpa [z1] using hh

private theorem hz1C :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
        (cert.modified.tile c = cert.P 1 true) → ((cert.modified.rho f1 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) →
            ((cert.modified.plane.faceVertex f1 2 = c) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        z1 ∈ FootprintVertices (cert.P 1 true)))) ) := by
  classical
  intro q cfg C T cert c f1 htileC hrho1 hfa12 z1
  have hh := cert.modified.rho_common f1 2
  rw [hfa12, htileC, hrho1] at hh
  simpa [z1] using hh

private theorem hz1AC :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true) = FootprintVertices (cert.P 0 true) ∩
            FootprintVertices (cert.P 1 true)) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (z1 ∈ FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)) → ((z1 ∈
            FootprintVertices (cert.P 1 true)) → (z1 ∈ FootprintVertices (cert.P 0 true) ∩
            FootprintVertices (cert.P 1 true)))) ) := by
  classical
  intro q cfg C T cert hretainVertices z1 hz1Amod hz1C
  rw [← hretainVertices]
  exact ⟨hz1Amod, hz1C⟩

private theorem hz3Amod :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        (cert.modified.tile a = TileCellComplement (cert.P 0 true) cert.O) → ((cert.modified.rho
            f3 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) →
            ((cert.modified.plane.faceVertex f3 0 = a) → (
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        z3 ∈ FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)))) ) := by
  classical
  intro q cfg C T cert a f3 htileA hrho3 hfa30 z3
  have hh := cert.modified.rho_common f3 0
  rw [hfa30, htileA, hrho3] at hh
  simpa [z3] using hh

private theorem hz3C :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        (cert.modified.tile c = cert.P 1 true) → ((cert.modified.rho f3 =
            cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) →
            ((cert.modified.plane.faceVertex f3 1 = c) → (
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        z3 ∈ FootprintVertices (cert.P 1 true)))) ) := by
  classical
  intro q cfg C T cert c f3 htileC hrho3 hfa31 z3
  have hh := cert.modified.rho_common f3 1
  rw [hfa31, htileC, hrho3] at hh
  simpa [z3] using hh

private theorem hz3F :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
        (cert.modified.rho f3 = cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0,
            0⟩)) → (
        let fidx : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
        (cert.modified.tile fidx = cert.P 2 false) → ((cert.modified.plane.faceVertex f3 2 =
            fidx) → (
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        z3 ∈ FootprintVertices (cert.P 2 false)))) ) := by
  classical
  intro q cfg C T cert f3 hrho3 fidx htileF hfa32 z3
  have hh := cert.modified.rho_common f3 2
  rw [hfa32, htileF, hrho3] at hh
  simpa [z3] using hh

private theorem hz3AC :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
            FootprintVertices (cert.P 1 true) = FootprintVertices (cert.P 0 true) ∩
            FootprintVertices (cert.P 1 true)) → (
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (z3 ∈ FootprintVertices (TileCellComplement (cert.P 0 true) cert.O)) → ((z3 ∈
            FootprintVertices (cert.P 1 true)) → (z3 ∈ FootprintVertices (cert.P 0 true) ∩
            FootprintVertices (cert.P 1 true)))) ) := by
  classical
  intro q cfg C T cert hretainVertices z3 hz3Amod hz3C
  rw [← hretainVertices]
  exact ⟨hz3Amod, hz3C⟩

private theorem hACdis :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (Disjoint (cert.P 0 true).cells (cert.P 1 true).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  simpa [a, c, SubtileOccurrenceInterpretation, translation_zero] using
    hsep a c (by decide) (by simp [a, c])

private theorem hBCdis :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (
        Disjoint (cert.P 0 false).cells (cert.P 1 true).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  simpa [b, c, SubtileOccurrenceInterpretation, translation_zero] using
    hsep b c (by decide) (by simp [b, c])

private theorem hAFdis :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (
        Disjoint (cert.P 0 true).cells (cert.P 2 false).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let fidx : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  simpa [a, fidx, SubtileOccurrenceInterpretation, translation_zero] using
    hsep a fidx (by decide) (by simp [a, fidx])

private theorem hCFdis :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        (∀ (U : ProtoTile), TileTranslation U 0 = U) → ((∀ (a : PeriodicSubtileIndex), ∀ (b :
            PeriodicSubtileIndex), a ≠ b → ¬((a.label = SixSubtileLabel.A ∧ b.label =
            SixSubtileLabel.B ∨ a.label = SixSubtileLabel.B ∧ b.label = SixSubtileLabel.A) ∧
            a.first = b.first ∧ a.second = b.second) → Disjoint (SubtileOccurrenceInterpretation
            cert.P cert.u cert.v a).cells (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            b).cells) → (
        Disjoint (cert.P 1 true).cells (cert.P 2 false).cells)) ) := by
  classical
  intro q cfg C T cert translation_zero hsep
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let fidx : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  simpa [c, fidx, SubtileOccurrenceInterpretation, translation_zero] using
    hsep c fidx (by decide) (by simp [c, fidx])

private theorem hz1ne :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (Nat.card
            { is : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } = (2
            : ℕ)) → ((∀ (v : GaussianInt), ∀ (z : GaussianInt), (Nat.card
            {is : Fin 3 × Bool // v ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) → ((z =
            v) → ((z ∈ BoundaryFootprintVertices (cert.P 0 true)) → ((z ∈
            BoundaryFootprintVertices (cert.P 0 false)) → ((z ∈ BoundaryFootprintVertices (cert.P
            1 true)) → (False)))))) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        (z1 ∈ BoundaryFootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∧ z1 ∈
            BoundaryFootprintVertices (cert.P (0 : Fin (3 : ℕ)) false) ∧ z1 ∈
            BoundaryFootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) → (z1 ≠ x))) ) := by
  classical
  intro q cfg C T cert x hk threeOwnersContradict z1 hz1boundary heq
  exact threeOwnersContradict x z1 hk heq hz1boundary.1 hz1boundary.2.1
    hz1boundary.2.2

private theorem hz3ne :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (Nat.card
            { is : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } = (2
            : ℕ)) → ((∀ (v : GaussianInt), ∀ (z : GaussianInt), (Nat.card
            {is : Fin 3 × Bool // v ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) → ((z =
            v) → ((z ∈ BoundaryFootprintVertices (cert.P 0 true)) → ((z ∈
            BoundaryFootprintVertices (cert.P 1 true)) → ((z ∈ BoundaryFootprintVertices (cert.P
            2 false)) → (False)))))) → (
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (z3 ∈ BoundaryFootprintVertices (cert.P (0 : Fin (3 : ℕ)) true) ∧ z3 ∈
            BoundaryFootprintVertices (cert.P (1 : Fin (3 : ℕ)) true) ∧ z3 ∈
            BoundaryFootprintVertices (cert.P (2 : Fin (3 : ℕ)) false)) → (z3 ≠ x))) ) := by
  classical
  intro q cfg C T cert x hk threeOwnersAFContradict z3 hz3boundary heq
  exact threeOwnersAFContradict x z3 hk heq hz3boundary.1 hz3boundary.2.1
    hz3boundary.2.2

private theorem hpathEndpoints :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (∀ (v : GaussianInt), ∀ (V : Set GaussianInt), ∀ (E :
            Set (Finset GaussianInt)), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (SimpleGridPathBetween V E a b) → ((v ∈ V) → ((v ≠ a) → ((v ≠ b) → (∃ y z :
            GaussianInt, ∃ e f : Finset GaussianInt, e ≠ f ∧ v ∈ e ∧ v ∈ f ∧ e ∈ E ∧ f ∈ E ∧ e =
            {y, v} ∧ f = {v, z} ∧ FourNeighborAdjacent y v ∧ FourNeighborAdjacent v z))))) → ((x
            ∈ FootprintVertices (cert.P (0 : Fin (3 : ℕ)) true)) → ((x ∈ FootprintVertices
            (cert.P (1 : Fin (3 : ℕ)) true)) → ((SimpleGridPathBetween (FootprintVertices (cert.P
            0 true) ∩ FootprintVertices (cert.P 1 true)) (FootprintEdges (cert.P 0 true) ∩
            FootprintEdges (cert.P 1 true)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)) (cert.unmodified.core.rho
            (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)) ∨ SimpleGridPathBetween
            (FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P 1 true))
            (FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩))
            (cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩))) → (
        let z1 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
        let z3 := cert.unmodified.core.rho
          (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
        (z1 ≠ x) → ((z3 ≠ x) → (∃ y z : GaussianInt, ∃ e f : Finset GaussianInt, e ≠ f ∧ x ∈ e ∧
            x ∈ f ∧ e ∈ FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true) ∧ f ∈
            FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true) ∧ e = {y, x} ∧ f =
            {x, z} ∧ FourNeighborAdjacent y x ∧ FourNeighborAdjacent x z)))))) ) := by
  classical
  intro q cfg C T cert x twoPathEdges hA hC hcompleteOriginal z1 z3 hz1ne hz3ne
  rcases hcompleteOriginal with hp | hp
  · exact twoPathEdges x _ _ z1 z3 hp ⟨hA, hC⟩ hz1ne.symm hz3ne.symm
  · exact twoPathEdges x _ _ z3 z1 hp ⟨hA, hC⟩ hz3ne.symm hz1ne.symm

private theorem hprepos :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), 0 <
            (cfg.firstPredecessor 2).1 ) := by
  classical
  intro q cfg
  rw [cfg.firstParentTwo]
  have hn := (ProperBandCurvatureStructure q cfg.proper).2.1 (1 : Fin 3)
  have hnonneg : 0 ≤ (q 2).1 := by simpa using hn
  exact lt_of_le_of_ne hnonneg (Ne.symm (cfg.noLine 2))

private theorem hprotoC :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (hprepos : 0 < (cfg.firstPredecessor 2).1),
        let C2 : BandCircle := ⟨⟨cfg.firstPredecessor 2,
          ⟨Or.inl hprepos, cfg.firstPredecessor, cfg.firstProper.1, 2, rfl⟩⟩, hprepos⟩
        BandPrototile C2.1.1 (cert.P 1 true) ) := by
  classical
  intro q cfg C T cert hprepos C2
  change BandPrototile (cfg.firstPredecessor 2) (cert.P 1 true)
  rw [cfg.firstParentTwo]
  exact (cert.outer_occurrence 1 true).1

private theorem hEdgesQC :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  ∀ (x : GaussianInt),
                    (∀ (U : ProtoTile),
                        ∀ (e : Finset GaussianInt),
                          e ∈ FootprintEdges U →
                            ∀ (z : GaussianInt), z ∈ e → z ∈ FootprintVertices U) →
                      FootprintVertices (cert.P 0 true) ∩
                            FootprintVertices (cert.P 1 true) ⊆
                          FootprintVertices (cert.Q 1 true) ∩
                            FootprintVertices (cert.P 1 true) →
                        (∃ y z : GaussianInt,
                            ∃ e f : Finset GaussianInt,
                              e ≠ f ∧
                                x ∈ e ∧
                                x ∈ f ∧
                                e ∈
                                FootprintEdges (cert.P 0 true) ∩
                                FootprintEdges (cert.P 1 true) ∧
                                f ∈
                                FootprintEdges (cert.P 0 true) ∩
                                FootprintEdges (cert.P 1 true) ∧
                                e = { y, x } ∧
                                f = { x, z } ∧
                                FourNeighborAdjacent y x ∧ FourNeighborAdjacent x z) →
                          (∀ x ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true),
                              ∀ y ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true),
                                FourNeighborAdjacent x y →
                                { x, y } ∈
                                FootprintEdges (cert.Q (1 : Fin (3 : ℕ)) true)) →
                            (∀ x ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true),
                                ∀ y ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true),
                                FourNeighborAdjacent x y →
                                { x, y } ∈
                                FootprintEdges (cert.P (1 : Fin (3 : ℕ)) true)) →
                              ∃ e f : Finset GaussianInt,
                                e ≠ f ∧
                                x ∈ e ∧
                                x ∈ f ∧
                                e ∈
                                FootprintEdges (cert.Q 1 true) ∩
                                FootprintEdges (cert.P 1 true) ∧
                                f ∈
                                FootprintEdges (cert.Q 1 true) ∩
                                FootprintEdges (cert.P 1 true)
    ) := by
  classical
  intro q cfg C T cert x edgeEndpoint raw_support hpathEndpoints regQ regC
  obtain ⟨y, z, e, f, hef, hxe, hxf, he, hf, rfl, rfl, hyx, hxz⟩ :=
    hpathEndpoints
  have hyA := edgeEndpoint (cert.P 0 true)
    {y, x} he.1 y (by simp)
  have hxA := edgeEndpoint (cert.P 0 true)
    {y, x} he.1 x (by simp)
  have hyC := edgeEndpoint (cert.P 1 true) {y, x} he.2 y (by simp)
  have hxC := edgeEndpoint (cert.P 1 true) {y, x} he.2 x (by simp)
  have hzA := edgeEndpoint (cert.P 0 true)
    {x, z} hf.1 z (by simp)
  have hxC' := edgeEndpoint (cert.P 1 true) {x, z} hf.2 x (by simp)
  have hzC := edgeEndpoint (cert.P 1 true) {x, z} hf.2 z (by simp)
  have hyQ := (raw_support ⟨hyA, hyC⟩).1
  have hxQ := (raw_support ⟨hxA, hxC⟩).1
  have hzQ := (raw_support ⟨hzA, hzC⟩).1
  refine ⟨{y, x}, {x, z}, hef, by simp, by simp, ?_, ?_⟩
  · exact ⟨regQ y hyQ x hxQ hyx, regC y hyC x hxC hyx⟩
  · exact ⟨regQ x hxQ z hzQ hxz, regC x hxC' z hzC hxz⟩

private theorem hFinj :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        (∀ (z : GaussianInt), F (F z) = z) → (Function.Injective F) ) := by
  classical
  intro q u w t F hFinvol a b hab
  have := congrArg F hab
  simpa [hFinvol] using this

private theorem image_mem :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        (Function.Injective F) → (∀ (A : Set GaussianInt), ∀ (B : Set GaussianInt), (F '' A = B)
            → (∀ (z : GaussianInt), z ∈ A ↔ F z ∈ B)) ) := by
  classical
  intro q u w t F hFinj A B hAB z
  rw [← hAB]
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, hEq⟩
    have : y = z := hFinj hEq
    simpa [this] using hy

private theorem parentFootprint :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (U : ProtoTile), FootprintVertices (H U) = (fun z : GaussianInt => t - z) ''
            FootprintVertices U) → ((∀ (i : Fin 3), FootprintVertices (H (cert.P i true)) =
            FootprintVertices (cert.P i false)) → (
        let F : GaussianInt → GaussianInt := fun z => t - z
        ∀ (i : Fin 3), F '' FootprintVertices (cert.P i true) = FootprintVertices (cert.P i
            false))) ) := by
  classical
  intro q cfg C T cert u w t H halfTurnFootprint outerFootprint F i
  calc
    _ = FootprintVertices (H (cert.P i true)) :=
      (halfTurnFootprint (cert.P i true)).symm
    _ = _ := outerFootprint i

private theorem parentBoundary :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (U : ProtoTile), (U.cells.Nonempty) → (BoundaryFootprintVertices (H U) = (fun z :
            GaussianInt => t - z) '' BoundaryFootprintVertices U)) → ((∀ (i : Fin 3), ∀ (s :
            Bool), (cert.P i s).cells.Nonempty) → ((∀ (i : Fin 3), BoundaryFootprintVertices (H
            (cert.P i true)) = BoundaryFootprintVertices (cert.P i false)) → (
        let F : GaussianInt → GaussianInt := fun z => t - z
        ∀ (i : Fin 3), F '' BoundaryFootprintVertices (cert.P i true) = BoundaryFootprintVertices
            (cert.P i false)))) ) := by
  classical
  intro q cfg C T cert u w t H halfTurnBoundary outerNonempty outerBoundary F i
  calc
    _ = BoundaryFootprintVertices (H (cert.P i true)) :=
      (halfTurnBoundary (cert.P i true) (outerNonempty i true)).symm
    _ = _ := outerBoundary i

private theorem parentBoundaryReverse :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        (∀ (z : GaussianInt), F (F z) = z) → ((∀ (i : Fin 3), F '' BoundaryFootprintVertices
            (cert.P i true) = BoundaryFootprintVertices (cert.P i false)) → (∀ (i : Fin 3), F ''
            BoundaryFootprintVertices (cert.P i false) = BoundaryFootprintVertices (cert.P i
            true))) ) := by
  classical
  intro q cfg C T cert u w t F hFinvol parentBoundary i
  calc
    _ = F '' (F '' BoundaryFootprintVertices (cert.P i true)) := by
      rw [parentBoundary]
    _ = _ := by
      rw [Set.image_image]
      ext z
      simp [hFinvol]

private theorem hboundaryFlip :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        let v : GaussianInt := F x
        (∀ (z : GaussianInt), F (F z) = z) → ((∀ (A : Set GaussianInt), ∀ (B : Set GaussianInt),
            (F '' A = B) → (∀ (z : GaussianInt), z ∈ A ↔ F z ∈ B)) → ((∀ (i : Fin 3), F ''
            BoundaryFootprintVertices (cert.P i true) = BoundaryFootprintVertices (cert.P i
            false)) → ((∀ (i : Fin 3), F '' BoundaryFootprintVertices (cert.P i false) =
            BoundaryFootprintVertices (cert.P i true)) → (∀ (i : Fin 3), ∀ (s : Bool), v ∈
            BoundaryFootprintVertices (cert.P i s) ↔ x ∈ BoundaryFootprintVertices (cert.P i
            (!s)))))) ) := by
  classical
  intro q cfg C T cert x u w t F v hFinvol image_mem parentBoundary parentBoundaryReverse i s
  cases s
  · have h := image_mem _ _ (parentBoundaryReverse i) v
    simpa [v, hFinvol] using h
  · have h := image_mem _ _ (parentBoundary i) v
    simpa [v, hFinvol] using h

private theorem hvk :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), (Nat.card
            { is : Fin (3 : ℕ) × Bool // x ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } = (2
            : ℕ)) → (∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        let v : GaussianInt := F x
        (∀ (i : Fin 3), ∀ (s : Bool), v ∈ BoundaryFootprintVertices (cert.P i
            s) ↔ x ∈ BoundaryFootprintVertices (cert.P i (!s))) → (
        let A := {is : Fin 3 × Bool //
          v ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
        Nat.card A = 2))) := by
  classical
  intro q cfg C T cert x hk u w t F v hboundaryFlip A
  let B := {is : Fin 3 × Bool //
    x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)}
  let e : A ≃ B :=
    { toFun := fun a => ⟨(a.val.1, !a.val.2), hboundaryFlip a.val.1 a.val.2 |>.mp a.property⟩
      invFun := fun b => ⟨(b.val.1, !b.val.2), by
        have hb : x ∈ BoundaryFootprintVertices
            (cert.P b.val.1 (!(!b.val.2))) := by simpa using b.property
        exact (hboundaryFlip b.val.1 (!b.val.2)).mpr hb⟩
      left_inv := by intro a; apply Subtype.ext; simp
      right_inv := by intro b; apply Subtype.ext; simp }
  calc
    Nat.card A = Nat.card B := Nat.card_congr e
    _ = 2 := hk

private theorem hcentQS :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), (TileCentroid (cert.P (0 : Fin (3 : ℕ)) true) - TileCentroid T = (1 : ℝ) •
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin ((1
            : ℕ) + (2 : ℕ) + (1 : ℕ))))) - (-(GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 :
            ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).2, (GaussianRealPoint
            (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 :
            ℕ)))))).1))) → ((TileCentroid (cert.P (0 : Fin (3 : ℕ)) false) - TileCentroid T = (-1
            : ℝ) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 :
            Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ))))) - (-(GaussianRealPoint (BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).2, (GaussianRealPoint
            (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 :
            ℕ)))))).1))) → ((TileCentroid (cert.Q (1 : Fin (3 : ℕ)) true) - TileCentroid (cert.P
            (0 : Fin (3 : ℕ)) true) = (1 : ℝ) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ)))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ)))) - (-(GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 :
            Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).2,
            (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) +
            (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).1))) → ((TileCentroid (cert.S
            (1 : Fin (3 : ℕ)) false) - TileCentroid (cert.P (0 : Fin (3 : ℕ)) false) = (-1 : ℝ) •
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 :
            ℕ) + (1 : ℕ) + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))) -
            (-(GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ)
            + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ))))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).1))) → (TileCentroid (cert.Q 1 true) +
            TileCentroid (cert.S 1 false) = (2 : Real) • TileCentroid T)))) ) := by
  classical
  intro q cfg C T cert houterPlus houterMinus hchildPlus hchildMinus
  apply Prod.ext
  · have h1 := congrArg Prod.fst houterPlus
    have h2 := congrArg Prod.fst houterMinus
    have h3 := congrArg Prod.fst hchildPlus
    have h4 := congrArg Prod.fst hchildMinus
    dsimp at h1 h2 h3 h4 ⊢
    linarith
  · have h1 := congrArg Prod.snd houterPlus
    have h2 := congrArg Prod.snd houterMinus
    have h3 := congrArg Prod.snd hchildPlus
    have h4 := congrArg Prod.snd hchildMinus
    dsimp at h1 h2 h3 h4 ⊢
    linarith

private theorem hquarterOffset :
    (by
      classical
      exact
        ∀ (w : GaussianInt), GaussianRealPoint (GaussianQuarterTurn w - w) = (-(GaussianRealPoint
            w).1 - (GaussianRealPoint w).2, (GaussianRealPoint w).1 - (GaussianRealPoint w).2) )
            := by
  classical
  intro w
  apply Prod.ext <;> simp [GaussianRealPoint, GaussianQuarterTurn]; ring

private theorem hdeltaRaw :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q),
        let wo := BandVectors.1 (q 3) (q 2)
        let wc := BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)
        let delta : GaussianInt :=
          (GaussianQuarterTurn wo - wo) + (GaussianQuarterTurn wc - wc)
        GaussianRealPoint delta = GaussianRealPoint (GaussianQuarterTurn wo - wo) +
            GaussianRealPoint (GaussianQuarterTurn wc - wc) ) := by
  classical
  intro q cfg wo wc delta
  apply Prod.ext <;> simp [delta, GaussianRealPoint, GaussianQuarterTurn]

private theorem hdelta :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let wo := BandVectors.1 (q 3) (q 2)
        let wc := BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)
        let delta : GaussianInt :=
          (GaussianQuarterTurn wo - wo) + (GaussianQuarterTurn wc - wc)
        (TileCentroid (cert.P (0 : Fin (3 : ℕ)) true) - TileCentroid T = (1 : ℝ) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 :
            ℕ) + (1 : ℕ))))) - (-(GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 :
            Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).2, (GaussianRealPoint (BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).1))) → ((TileCentroid
            (cert.P (0 : Fin (3 : ℕ)) false) - TileCentroid T = (-1 : ℝ) • (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 :
            ℕ) + (1 : ℕ))))) - (-(GaussianRealPoint (BandVectors.1 (q (3 : Fin (4 : ℕ))) (q (2 :
            Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).2, (GaussianRealPoint (BandVectors.1 (q (3 :
            Fin (4 : ℕ))) (q (2 : Fin ((1 : ℕ) + (2 : ℕ) + (1 : ℕ)))))).1))) → ((TileCentroid
            (cert.Q (1 : Fin (3 : ℕ)) true) - TileCentroid (cert.P (0 : Fin (3 : ℕ)) true) = (1 :
            ℝ) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin
            ((2 : ℕ) + (1 : ℕ) + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))) -
            (-(GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ)
            + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).2, (GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ))))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).1))) → ((TileCentroid (cert.S (1 : Fin (3
            : ℕ)) false) - TileCentroid (cert.P (0 : Fin (3 : ℕ)) false) = (-1 : ℝ) • (1 / 2 : ℝ)
            • (GaussianRealPoint (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ)
            + (1 : ℕ)))) (cfg.firstPredecessor (3 : Fin (4 : ℕ)))) - (-(GaussianRealPoint
            (BandVectors.1 (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ))))
            (cfg.firstPredecessor (3 : Fin (4 : ℕ))))).2, (GaussianRealPoint (BandVectors.1
            (cfg.firstPredecessor (1 : Fin ((2 : ℕ) + (1 : ℕ) + (1 : ℕ)))) (cfg.firstPredecessor
            (3 : Fin (4 : ℕ))))).1))) → ((∀ (w : GaussianInt), GaussianRealPoint
            (GaussianQuarterTurn w - w) = (-(GaussianRealPoint w).1 - (GaussianRealPoint w).2,
            (GaussianRealPoint w).1 - (GaussianRealPoint w).2)) → ((GaussianRealPoint delta =
            GaussianRealPoint (GaussianQuarterTurn wo - wo) + GaussianRealPoint
            (GaussianQuarterTurn wc - wc)) → (GaussianRealPoint delta = TileCentroid (cert.S 1
            false) - TileCentroid (cert.Q 1 true))))))) ) := by
  classical
  intro q cfg C T cert wo wc delta houterPlus houterMinus hchildPlus hchildMinus hquarterOffset
      hdeltaRaw
  apply Prod.ext
  · have h1 := congrArg Prod.fst houterPlus
    have h2 := congrArg Prod.fst houterMinus
    have h3 := congrArg Prod.fst hchildPlus
    have h4 := congrArg Prod.fst hchildMinus
    have ho := congrArg Prod.fst (hquarterOffset wo)
    have hc := congrArg Prod.fst (hquarterOffset wc)
    rw [hdeltaRaw, hquarterOffset wo, hquarterOffset wc]
    dsimp [wo, wc] at h1 h2 h3 h4 ⊢
    dsimp at ho hc
    linarith
  · have h1 := congrArg Prod.snd houterPlus
    have h2 := congrArg Prod.snd houterMinus
    have h3 := congrArg Prod.snd hchildPlus
    have h4 := congrArg Prod.snd hchildMinus
    have ho := congrArg Prod.snd (hquarterOffset wo)
    have hc := congrArg Prod.snd (hquarterOffset wc)
    rw [hdeltaRaw, hquarterOffset wo, hquarterOffset wc]
    dsimp [wo, wc] at h1 h2 h3 h4 ⊢
    dsimp at ho hc
    linarith

private theorem hQtransCentroid :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T),
        let wo := BandVectors.1 (q 3) (q 2)
        let wc := BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)
        let delta : GaussianInt :=
          (GaussianQuarterTurn wo - wo) + (GaussianQuarterTurn wc - wc)
        (GaussianRealPoint delta = TileCentroid (cert.S 1 false) - TileCentroid (cert.Q 1 true))
            → (TileCentroid (TileTranslation (cert.Q 1 true) delta) = TileCentroid (cert.S 1
            false)) ) := by
  classical
  intro q cfg C T cert wo wc delta hdelta
  rw [(TileTranslationFormulas (cert.Q 1 true) delta).2.2.2.2.1]
  change TileCentroid (cert.Q 1 true) + GaussianRealPoint delta = _
  rw [hdelta]
  ext <;> simp [Prod.add_def, sub_eq_add_neg]

private theorem hrealHQ :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (U : ProtoTile), TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid
            T).1 - p.1, 2 * (TileCentroid T).2 - p.2)) '' TileRealization U) → (
        let wo := BandVectors.1 (q 3) (q 2)
        let wc := BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)
        let delta : GaussianInt :=
          (GaussianQuarterTurn wo - wo) + (GaussianQuarterTurn wc - wc)
        (TileCentroid (cert.Q 1 true) + TileCentroid (cert.S 1 false) = (2 : Real) • TileCentroid
            T) → ((GaussianRealPoint delta = TileCentroid (cert.S 1 false) - TileCentroid (cert.Q
            1 true)) → ((CentrallyReflectedAt (TileCentroid (cert.Q (1 : Fin (3 : ℕ)) true))
            (cert.Q (1 : Fin (3 : ℕ)) true) (cert.Q (1 : Fin (3 : ℕ)) true)) → (TileRealization
            (H (cert.Q 1 true)) = TileRealization (TileTranslation (cert.Q 1 true) delta))))) )
            := by
  classical
  intro q cfg C T cert u w t H halfTurnRealization wo wc delta hcentQS hdelta hrealQcentral
  rw [halfTurnRealization]
  change TileRealization (cert.Q 1 true) = _ at hrealQcentral
  rw [hrealQcentral, Set.image_image]
  have hmaps :
      (fun p : Real × Real =>
        (2 * (TileCentroid T).1 - (2 * (TileCentroid (cert.Q 1 true)).1 - p.1),
          2 * (TileCentroid T).2 - (2 * (TileCentroid (cert.Q 1 true)).2 - p.2))) =
      (fun p : Real × Real => (p.1 + (delta.re : Real), p.2 + (delta.im : Real))) := by
    funext p
    apply Prod.ext
    · have hs := congrArg Prod.fst hcentQS
      have hd := congrArg Prod.fst hdelta
      dsimp at hs hd ⊢
      change (delta.re : Real) = _ at hd
      linarith
    · have hs := congrArg Prod.snd hcentQS
      have hd := congrArg Prod.snd hdelta
      dsimp at hs hd ⊢
      change (delta.im : Real) = _ at hd
      linarith
  rw [hmaps]
  exact (TileTranslationFormulas (cert.Q 1 true) delta).2.2.2.1.symm

private theorem hHQne :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        ((H (cert.Q 1 true)).cells = (cert.S 1 false).cells) → ((LatticeTile (cert.S 1 false)) →
            ((H (cert.Q 1 true)).cells.Nonempty)) ) := by
  classical
  intro q cfg C T cert u w t H hHQcells hSLat
  rw [hHQcells]
  exact (LatticeTileGridStructure _ hSLat).1.1

private theorem hHQfoot :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        ((H (cert.Q 1 true)).cells = (cert.S 1 false).cells) → (((H (cert.Q 1
            true)).cells.Nonempty) → (FootprintVertices (H (cert.Q 1 true)) = FootprintVertices
            (cert.S 1 false))) ) := by
  classical
  intro q cfg C T cert u w t H hHQcells hHQne
  have hempty : (H (cert.Q 1 true)).cells = ∅ →
      (H (cert.Q 1 true)).anchor = (cert.S 1 false).anchor := by
    intro he
    exact False.elim (hHQne.ne_empty he)
  exact (ProtoTileObservableExtensionality _ _ hHQcells hempty).1

private theorem childFoot :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        (∀ (U : ProtoTile), FootprintVertices (H U) = (fun z : GaussianInt => t - z) ''
            FootprintVertices U) → (
        let F : GaussianInt → GaussianInt := fun z => t - z
        (FootprintVertices (H (cert.Q 1 true)) = FootprintVertices (cert.S 1 false)) → (F ''
            FootprintVertices (cert.Q 1 true) = FootprintVertices (cert.S 1 false))) ) := by
  classical
  intro q cfg C T cert u w t H halfTurnFootprint F hHQfoot
  calc
    _ = FootprintVertices (H (cert.Q 1 true)) :=
      (halfTurnFootprint (cert.Q 1 true)).symm
    _ = _ := hHQfoot

private theorem moveFoot :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        (∀ (z : GaussianInt), F (F z) = z) → ((∀ (A : Set GaussianInt), ∀ (B : Set GaussianInt),
            (F '' A = B) → (∀ (z : GaussianInt), z ∈ A ↔ F z ∈ B)) → (∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (F '' FootprintVertices U = FootprintVertices V) → (∀ (z : GaussianInt),
            (F z ∈ FootprintVertices U) → (z ∈ FootprintVertices V)))) ) := by
  classical
  intro q u w t F hFinvol image_mem U V hUV z hz
  have h := (image_mem _ _ hUV (F z)).mp hz
  simpa [hFinvol] using h

private theorem moveCell :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        (∀ (U : ProtoTile), (H U).cells = U.cells.image tau) → (∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ((H U).cells = V.cells) → (∀ (z : GaussianInt), (z ∈ U.cells) → (tau z ∈
            V.cells))) ) := by
  classical
  intro q u w t H tau hHcells U V hUV z hz
  have hz' : tau z ∈ (H U).cells := by
    rw [hHcells]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  rw [hUV] at hz'
  exact hz'

private theorem hstar :
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
                      ∀ (u : GaussianInt),
                        let w := BandVectors.1 (q 3) (q 2);
                        let t : GaussianInt :=
                          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩;
                        let F : GaussianInt → GaussianInt := fun z => t - z;
                        let v : GaussianInt := F x;
                        (∀ (i : Fin 3),
                            F '' FootprintVertices (cert.P i true) =
                              FootprintVertices (cert.P i false)) →
                          let A :=
                            { is : Fin 3 × Bool //
                              v ∈ BoundaryFootprintVertices (cert.P is.1 is.2) }
                          Nat.card A = 2 →
                            (v ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∧
                                (∀ (y : GaussianInt),
                                y = v ∨
                                y = v + (1 : GaussianInt) ∨
                                y = v - (1 : GaussianInt) ∨
                                y = v + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                y = v - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                                y ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∨
                                y ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ)) true)) ∧
                                ∀ (z : GaussianInt),
                                z = v ∨
                                z = v - (1 : GaussianInt) ∨
                                z = v - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                z =
                                v - (1 : GaussianInt) -
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                                z ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∨
                                z ∈ (cert.P (1 : Fin (3 : ℕ)) true).cells) →
                              F '' FootprintVertices (cert.Q 1 true) =
                                FootprintVertices (cert.S 1 false) →
                                (∀ (U : ProtoTile),
                                ∀ (V : ProtoTile),
                                F '' FootprintVertices U = FootprintVertices V →
                                ∀ (z : GaussianInt),
                                F z ∈ FootprintVertices U → z ∈ FootprintVertices V) →
                                ∀ (y : GaussianInt),
                                y = x ∨
                                y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
                                y ∈ FootprintVertices (cert.S 1 false) ∨
                                y ∈ FootprintVertices (cert.P 1 false)
    ) := by
  classical
  intro q cfg C T cert x hk u w t F v parentFootprint A hvk hpositive childFoot moveFoot y hy
  have hFinvol (z : GaussianInt) : F (F z) = z := by
    dsimp [F]
    abel
  have hFy : F y = v ∨ F y = v + 1 ∨ F y = v - 1 ∨
      F y = v + ⟨0, 1⟩ ∨ F y = v - ⟨0, 1⟩ := by
    rcases hy with rfl | hy | hy | hy | hy
    · exact Or.inl rfl
    · subst y
      right; right; left
      simp [F, v]; ring
    · subst y
      right; left
      simp [F, v]; ring
    · subst y
      right; right; right; right
      simp [F, v]; ring
    · subst y
      right; right; right; left
      simp [F, v]; ring
  rcases (hpositive.2.1 (F y) hFy) with hq | hp
  · exact Or.inl (moveFoot _ _ childFoot y (by simpa [hFinvol] using hq))
  · exact Or.inr (moveFoot _ _ (parentFootprint 1) y
      (by simpa [hFinvol] using hp))

private theorem hcellLift :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (x : GaussianInt), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        let F : GaussianInt → GaussianInt := fun z => t - z
        let v : GaussianInt := F x
        ∀ (z : GaussianInt), (z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
            z = x - 1 - ⟨0, 1⟩) → (∃ c : GaussianInt, (c = v ∨ c = v - 1 ∨ c = v - ⟨0, 1⟩ ∨ c = v
                - 1 - ⟨0, 1⟩) ∧ tau c = z) ) := by
  classical
  intro q x u w t tau F v z hz
  rcases hz with hz | hz | hz | hz
  · subst z
    refine ⟨v - 1 - ⟨0, 1⟩, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
    apply Zsqrtd.ext <;> simp [tau, v, F] <;> ring
  · subst z
    refine ⟨v - ⟨0, 1⟩, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    apply Zsqrtd.ext <;> simp [tau, v, F]; ring
  · subst z
    refine ⟨v - 1, Or.inr (Or.inl rfl), ?_⟩
    apply Zsqrtd.ext <;> simp [tau, v, F]; ring
  · subst z
    refine ⟨v, Or.inl rfl, ?_⟩
    apply Zsqrtd.ext <;> simp [tau, v, F]

private theorem hcellsAt1062 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀
            (C : BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q
            cfg C T), ∀ (x : GaussianInt), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileHalfTurn U) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        (∀ (i : Fin 3), (H (cert.P i true)).cells = (cert.P i false).cells) → (
        let F : GaussianInt → GaussianInt := fun z => t - z
        let v : GaussianInt := F x
        (v ∈ FootprintVertices (cert.Q (1 : Fin (3 : ℕ)) true) ∧ (∀ (y : GaussianInt), y = v ∨ y
            = v + (1 : GaussianInt) ∨ y = v - (1 : GaussianInt) ∨ y = v + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∨ y = v - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) → y ∈ FootprintVertices
            (cert.Q (1 : Fin (3 : ℕ)) true) ∨ y ∈ FootprintVertices (cert.P (1 : Fin (3 : ℕ))
            true)) ∧ ∀ (z : GaussianInt), z = v ∨ z = v - (1 : GaussianInt) ∨ z = v - (⟨(0 : ℤ),
            (1 : ℤ)⟩ : GaussianInt) ∨ z = v - (1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) → z ∈ (cert.Q (1 : Fin (3 : ℕ)) true).cells ∨ z ∈ (cert.P (1 : Fin (3 :
            ℕ)) true).cells) → (((H (cert.Q 1 true)).cells = (cert.S 1 false).cells) → ((∀ (U :
            ProtoTile), ∀ (V : ProtoTile), ((H U).cells = V.cells) → (∀ (z : GaussianInt), (z ∈
            U.cells) → (tau z ∈ V.cells))) → ((∀ (z : GaussianInt), (z = x ∨ z = x - 1 ∨ z = x -
            ⟨0, 1⟩ ∨ z = x - 1 - ⟨0, 1⟩) → (∃ c : GaussianInt, (c = v ∨ c = v - 1 ∨ c = v - ⟨0,
            1⟩ ∨ c = v - 1 - ⟨0, 1⟩) ∧ tau c = z)) → (∀ (z : GaussianInt), (z = x ∨ z = x - 1 ∨ z
            = x - ⟨0, 1⟩ ∨
            z = x - 1 - ⟨0, 1⟩) → (z ∈ (cert.S 1 false).cells ∨ z ∈ (cert.P 1 false).cells))))))
                ) := by
  classical
  intro q cfg C T cert x u w t H tau outerCells F v hpositive hHQcells moveCell hcellLift z hz
  obtain ⟨c, hc, htc⟩ := hcellLift z hz
  have hsquare := hpositive.2.2 c hc
  rcases hsquare with hq | hp
  · have hh := moveCell _ _ hHQcells c hq
    rw [htc] at hh
    exact Or.inl hh
  · have hh := moveCell _ _ (outerCells 1) c hp
    rw [htc] at hh
    exact Or.inr hh

end RightInteriorGeometry

namespace RightInteriorConclusion

private theorem positiveCase :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ∀ (cfg : BandOrderedGeneralConfiguration q),
            ∀ (C : BandCircle),
              ∀ (T : ProtoTile),
                ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
                  (∀ (v : GaussianInt),
                      ∀ (V : Set GaussianInt),
                        ∀ (E : Set (Finset GaussianInt)),
                          ∀ (a : GaussianInt),
                            ∀ (b : GaussianInt),
                              SimpleGridPathBetween V E a b →
                                v ∈ V →
                                v ≠ a →
                                v ≠ b →
                                ∃ (y : GaussianInt) (z : GaussianInt) (e :
                                Finset GaussianInt) (f : Finset GaussianInt),
                                e ≠ f ∧
                                v ∈ e ∧
                                v ∈ f ∧
                                e ∈ E ∧
                                f ∈ E ∧
                                e = { y, v } ∧
                                f = { v, z } ∧
                                FourNeighborAdjacent y v ∧ FourNeighborAdjacent v z) →
                    (∀ (U : ProtoTile),
                        ∀ (V : ProtoTile),
                          ∀ (W : ProtoTile),
                            Finset.Nonempty U.cells →
                              Finset.Nonempty V.cells →
                                TouchingTriple U V W → Disjoint U.cells V.cells) →
                      (∀ (U : ProtoTile),
                          ∀ e ∈ FootprintEdges U, ∀ z ∈ e, z ∈ FootprintVertices U) →
                        (∀ (z : GaussianInt),
                            ∀ (U : ProtoTile),
                              ∀ (V : ProtoTile),
                                ∀ (W : ProtoTile),
                                LatticeTile U →
                                LatticeTile V →
                                LatticeTile W →
                                Disjoint U.cells W.cells →
                                Disjoint V.cells W.cells →
                                z ∈ FootprintVertices U →
                                z ∈ FootprintVertices V →
                                z ∈ FootprintVertices W →
                                z ∈ BoundaryFootprintVertices U ∧
                                z ∈ BoundaryFootprintVertices V ∧
                                z ∈ BoundaryFootprintVertices W) →
                          (∀ (v : GaussianInt),
                              ∀ (z : GaussianInt),
                                Nat.card
                                { is : Fin (3 : ℕ) × Bool //
                                v ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                                (2 : ℕ) →
                                z = v →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (0 : Fin (3 : ℕ)) true) →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (0 : Fin (3 : ℕ)) false) →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (1 : Fin (3 : ℕ)) true) →
                                False) →
                            (∀ (v : GaussianInt),
                                ∀ (z : GaussianInt),
                                Nat.card
                                { is : Fin (3 : ℕ) × Bool //
                                v ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                                (2 : ℕ) →
                                z = v →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (0 : Fin (3 : ℕ)) true) →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (1 : Fin (3 : ℕ)) true) →
                                z ∈
                                BoundaryFootprintVertices
                                (cert.P (2 : Fin (3 : ℕ)) false) →
                                False) →
                              (∀ (v : GaussianInt),
                                ∀ (U : ProtoTile),
                                ∀ (V : ProtoTile),
                                LatticeTile U →
                                LatticeTile V →
                                Disjoint U.cells V.cells →
                                (∃ (e : Finset GaussianInt) (f : Finset GaussianInt),
                                e ≠ f ∧
                                v ∈ e ∧
                                v ∈ f ∧
                                e ∈ FootprintEdges U ∩ FootprintEdges V ∧
                                f ∈ FootprintEdges U ∩ FootprintEdges V) →
                                (∀ (y : GaussianInt),
                                y = v ∨
                                y = v + (1 : GaussianInt) ∨
                                y = v - (1 : GaussianInt) ∨
                                y = v + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                y = v - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                                y ∈ FootprintVertices U ∨ y ∈ FootprintVertices V) ∧
                                ∀ (z : GaussianInt),
                                z = v ∨
                                z = v - (1 : GaussianInt) ∨
                                z = v - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨
                                z =
                                v - (1 : GaussianInt) -
                                (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) →
                                z ∈ U.cells ∨ z ∈ V.cells) →
                                FootprintVertices (cert.P 0 true) ∩
                                FootprintVertices (cert.P 1 true) ⊆
                                FootprintVertices (cert.Q 1 true) ∩
                                FootprintVertices (cert.P 1 true) →
                                ∀ (point : GaussianInt),
                                Nat.card
                                { is : Fin 3 × Bool //
                                point ∈ BoundaryFootprintVertices (cert.P is.1 is.2) } =
                                2 →
                                point ∈ FootprintVertices (cert.P 0 true) →
                                point ∈ FootprintVertices (cert.P 1 true) →
                                point ∈ FootprintVertices (cert.Q 1 true) ∧
                                (∀ y,
                                y = point ∨
                                y = point + 1 ∨
                                y = point - 1 ∨ y = point + ⟨0, 1⟩ ∨ y = point - ⟨0, 1⟩ →
                                y ∈ FootprintVertices (cert.Q 1 true) ∨
                                y ∈ FootprintVertices (cert.P 1 true)) ∧
                                ∀ z,
                                z = point ∨
                                z = point - 1 ∨
                                z = point - ⟨0, 1⟩ ∨ z = point - 1 - ⟨0, 1⟩ →
                                z ∈ (cert.Q 1 true).cells ∨ z ∈ (cert.P 1 true).cells
    ) := by
  classical
  intro q cfg C T cert twoPathEdges touching_disjoint edgeEndpoint threeBoundaries
      threeOwnersContradict threeOwnersAFContradict interfaceConclusion raw_support point hk hA
      hC
  have hQC := raw_support ⟨hA, hC⟩
  have hQ : LatticeTile (cert.Q 1 true) :=
    P4590T1PositivePrototileDisk _ _ (cert.plus_occurrence 1 true).1 (by
      change 0 < (cfg.firstPredecessor 2).1
      rw [cfg.firstParentTwo]
      have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 (1 : Fin 3)
      have hn := cfg.noLine 2
      change 0 ≤ (q 2).1 at hnonneg
      omega)
  have hCtile : LatticeTile (cert.P 1 true) := cert.parent_lattice 1 true
  have hQne : (cert.Q 1 true).cells.Nonempty :=
    (LatticeTileGridStructure _ hQ).1.1
  have hCne : (cert.P 1 true).cells.Nonempty :=
    (LatticeTileGridStructure _ hCtile).1.1
  let a : PeriodicSubtileIndex := ⟨.A, 0, 0⟩
  let c : PeriodicSubtileIndex := ⟨.C, 0, 0⟩
  let f1 := cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩
  let f3 := cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩
  have translation_zero := TileTranslationProperties.zero
  have htileA := RightInteriorGeometry.htileA q cfg C T cert translation_zero
  have htileC := RightInteriorGeometry.htileC q cfg C T cert translation_zero
  have hOA := RightInteriorGeometry.hOA q cfg C T cert
  have hsep := (BandOriginalPairSeparation cert.P cert.O cert.u cert.v
    hOA (RightInteriorGeometry.hOB q cfg C T cert) cert.partition).2
  have hdeletedNe : (TileCellComplement (cert.P 0 true) cert.O).cells.Nonempty :=
    (LatticeTileGridStructure _ cert.precursor_complement_lattice.1).1.1
  have hretainData := FootprintDeletionRetention (cert.P 0 true)
    (cert.P 0 false) cert.O (cert.P 1 true) hOA (RightInteriorGeometry.hisolated q cfg C T cert
        translation_zero) (RightInteriorGeometry.hCA q cfg C T cert translation_zero hsep)
        (RightInteriorGeometry.hCB q cfg C T cert translation_zero hsep)
  have hretainEdges :
      FootprintEdges (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintEdges (cert.P 1 true) =
        FootprintEdges (cert.P 0 true) ∩ FootprintEdges (cert.P 1 true) :=
    hretainData.2.1
  have hretainVertices :
      FootprintVertices (TileCellComplement (cert.P 0 true) cert.O) ∩
          FootprintVertices (cert.P 1 true) =
        FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P 1 true) :=
    hretainData.2.2 (Or.inr ⟨hdeletedNe, hCne⟩)
  have hac : a ≠ c := by decide
  have hadj : cert.modified.plane.adjacent a c :=
    (cert.modified_adjacency a c).mpr (.AC 0 0)
  have hcommon := cert.modified.adjacent_has_common_edge a c hadj
  obtain ⟨hclass, hregular⟩ := PeriodicTileIntersectionClassification cert.modified
  have hraw := ((hclass a c hac).2.1 hcommon).2
  obtain ⟨_, f, g, hfg, hf, hg, hfaces, hpath⟩ :=
    (PeriodicTileIntersectionPaths cert.modified hregular a c hac).1.mpr hcommon
  have hpair := PairAssignmentFacts.assignment (cert.modifiedFaceEquivalence.symm ⟨.I1, 0, 0⟩)
      (cert.modifiedFaceEquivalence.symm ⟨.I3, 0, 0⟩) f g (RightInteriorGeometry.hf1 q cfg
      C T cert f g hfaces) (RightInteriorGeometry.hf3 q cfg C T cert f g hfaces)
          (RightInteriorGeometry.hf13 q cfg C T cert)
  have hrho1 : cert.modified.rho f1 =
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩) :=
    cert.modified_face_points _
  have hrho3 : cert.modified.rho f3 =
      cert.unmodified.core.rho (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩) :=
    cert.modified_face_points _
  let b : PeriodicSubtileIndex := ⟨.B, 0, 0⟩
  let fidx : PeriodicSubtileIndex := ⟨.F, 0, 0⟩
  have hfa10 : cert.modified.plane.faceVertex f1 0 = a := by
    simp [f1, a, cert.modified_face_vertices, SixSubtileFaceVertices]
  have hfa11 : cert.modified.plane.faceVertex f1 1 = b := by
    simp [f1, b, cert.modified_face_vertices, SixSubtileFaceVertices]
  have hfa12 : cert.modified.plane.faceVertex f1 2 = c := by
    simp [f1, c, cert.modified_face_vertices, SixSubtileFaceVertices]
  have hfa30 : cert.modified.plane.faceVertex f3 0 = a := by
    simp [f3, a, cert.modified_face_vertices, SixSubtileFaceVertices]
  have hfa31 : cert.modified.plane.faceVertex f3 1 = c := by
    simp [f3, c, cert.modified_face_vertices, SixSubtileFaceVertices]
  have hfa32 : cert.modified.plane.faceVertex f3 2 = fidx := by
    simp [f3, fidx, cert.modified_face_vertices, SixSubtileFaceVertices]
  let z1 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I1, 0, 0⟩)
  let z3 := cert.unmodified.core.rho
    (cert.unmodified.faceEquiv.symm ⟨.I3, 0, 0⟩)
  have hz1AC := RightInteriorGeometry.hz1AC q cfg C T cert hretainVertices
      (RightInteriorGeometry.hz1Amod q cfg C T cert htileA hrho1 hfa10)
      (RightInteriorGeometry.hz1C q cfg C T cert htileC hrho1 hfa12)
  have hz3C := RightInteriorGeometry.hz3C q cfg C T cert htileC hrho3 hfa31
  have hz1boundary := threeBoundaries z1 (cert.P 0 true)
    (cert.P 0 false) (cert.P 1 true) (cert.parent_lattice 0 true)
    (cert.parent_lattice 0 false) hCtile (RightInteriorGeometry.hACdis q cfg C T cert
        translation_zero hsep) (RightInteriorGeometry.hBCdis q cfg C T cert translation_zero hsep)
    hz1AC.1 (RightInteriorGeometry.hz1B q cfg C T cert hrho1 (RightInteriorGeometry.htileB q
        cfg C T cert translation_zero) hfa11) hz1AC.2
  have hz3boundary := threeBoundaries z3 (cert.P 0 true)
    (cert.P 1 true) (cert.P 2 false) (cert.parent_lattice 0 true)
    hCtile (cert.parent_lattice 2 false) (RightInteriorGeometry.hAFdis q cfg C T cert
        translation_zero hsep) (RightInteriorGeometry.hCFdis q cfg C T cert translation_zero
        hsep) (RightInteriorGeometry.hz3AC q cfg C T cert hretainVertices
        (RightInteriorGeometry.hz3Amod q cfg C T cert htileA hrho3 hfa30) hz3C).1 hz3C
        (RightInteriorGeometry.hz3F q cfg C T cert hrho3 (RightInteriorGeometry.htileF q cfg C
        T cert translation_zero) hfa32)
  have hprepos := RightInteriorGeometry.hprepos q cfg
  let C2 : BandCircle := ⟨⟨cfg.firstPredecessor 2,
    ⟨Or.inl hprepos, cfg.firstPredecessor, cfg.firstProper.1, 2, rfl⟩⟩, hprepos⟩
  have hprotoQ : BandPrototile C2.1.1 (cert.Q 1 true) :=
    (cert.plus_occurrence 1 true).1
  have regQ := (LatticeEdgeRegularity C2 (cert.Q 1 true) hprotoQ hQ).2.1
  have regC := (LatticeEdgeRegularity C2 (cert.P 1 true) (RightInteriorGeometry.hprotoC q cfg C
      T cert hprepos) hCtile).2.1
  have hdis : Disjoint (cert.Q 1 true).cells (cert.P 1 true).cells :=
    touching_disjoint _ _ _ hQne hCne cert.double_third
  have hresult := interfaceConclusion point (cert.Q 1 true) (cert.P 1 true) hQ hCtile hdis
      (RightInteriorGeometry.hEdgesQC q cfg C T cert point
        edgeEndpoint raw_support (RightInteriorGeometry.hpathEndpoints q cfg C T cert point
        twoPathEdges hA hC (RightInteriorGeometry.hcompleteOriginal q cfg C T cert hretainEdges
        hretainVertices (RightInteriorGeometry.hcomplete q cfg C T cert htileA htileC hraw f g
        hpath hpair hrho1 hrho3)) (RightInteriorGeometry.hz1ne q cfg C T cert point hk
        threeOwnersContradict hz1boundary) (RightInteriorGeometry.hz3ne q cfg C T cert point hk
        threeOwnersAFContradict hz3boundary)) regQ regC)
  exact ⟨hQC.1, hresult.1, hresult.2⟩

end RightInteriorConclusion

theorem P4590T1RightInteriorGeometry :
    ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
        BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg C T),
        (LatticeTile T) → (∀ (x : GaussianInt), (x ∈ FootprintVertices T) → ((x ∉
        BoundaryFootprintVertices T) → ((Nat.card {is : Fin 3 × Bool //
      x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2) → ((x ∈ FootprintVertices (cert.P 0
          true) → x ∈ FootprintVertices (cert.P 1 true) →
      x ∈ FootprintVertices (cert.Q 1 true) ∧
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 1 true) ∨ y ∈ FootprintVertices (cert.P 1 true)) ∧
      (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ →
        z ∈ (cert.Q 1 true).cells ∨ z ∈ (cert.P 1 true).cells)) ∧
    (x ∈ FootprintVertices (cert.P 0 false) → x ∈ FootprintVertices (cert.P 1 false) →
      x ∈ FootprintVertices (cert.S 1 false) ∧
      (∀ y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.S 1 false) ∨ y ∈ FootprintVertices (cert.P 1 false)) ∧
      (∀ z, z = x ∨ z = x - 1 ∨ z = x - ⟨0, 1⟩ ∨
          z = x - 1 - ⟨0, 1⟩ →
        z ∈ (cert.S 1 false).cells ∨ z ∈ (cert.P 1 false).cells)))))) := by
  intro q cfg C T cert hT x hx hxb hk
-- BODY
  classical
  obtain ⟨u, hu, _⟩ := QuarterTurnSymmetricCenteredTransport
    (cert.P 0 false) (cert.parent_quarter_turn 0 false)
  let w := BandVectors.1 (q 3) (q 2)
  let t : GaussianInt :=
    ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
  let H : ProtoTile → ProtoTile := fun U =>
    TileTranslation (TileHalfTurn U) t
  have hHcells := RightInteriorGeometry.hHcells q u
  have halfTurnRealization := RightInteriorGeometry.halfTurnRealization q T u
      (RightInteriorGeometry.ht q cfg C T cert u hu)
  have halfTurnFootprint := RightInteriorGeometry.halfTurnFootprint q u
  have halfTurnBoundary := RightInteriorGeometry.halfTurnBoundary q u
  have cells_of_realization (U V : ProtoTile)
      (hreal : TileRealization U = TileRealization V) : U.cells = V.cells :=
          RightInteriorGeometry.cells_of_realization U V hreal
  have signedOuter := BandSignedOccurrenceHalfTurn q (TileCentroid T) cert.P
    (fun i s => (cert.outer_occurrence i s).1)
    (fun i s => (cert.outer_occurrence i s).2.2)
  have outerCells (i : Fin 3) :
      (H (cert.P i true)).cells = (cert.P i false).cells :=
    cells_of_realization _ _ ((RightInteriorGeometry.outerRealization q cfg C T cert u
        halfTurnRealization signedOuter) i)
  have outerNonempty (i : Fin 3) (s : Bool) :
      (cert.P i s).cells.Nonempty :=
    (LatticeTileGridStructure _ (cert.parent_lattice i s)).1.1
  have outerFootprint := RightInteriorGeometry.outerFootprint q cfg C T cert u outerCells
      outerNonempty
  have outerBoundary := RightInteriorGeometry.outerBoundary q cfg C T cert u outerCells
      outerNonempty
  have twoPathEdges := RightInteriorGeometry.twoPathEdges (ListEndpointFacts.internalNeighbors)
  have touching_disjoint := RightInteriorGeometry.touching_disjoint
  have edgeEndpoint := RightInteriorGeometry.edgeEndpoint
  have threeBoundaries := RightInteriorGeometry.threeBoundaries (RightInteriorGeometry.rawIncident)
  have threeOwnersContradict := RightInteriorGeometry.threeOwnersContradict q cfg C T cert
  have threeOwnersAFContradict := RightInteriorGeometry.threeOwnersAFContradict q cfg C T cert
  have interfaceConclusion := RightInteriorGeometry.interfaceConclusion
  have raw_support :
      FootprintVertices (cert.P 0 true) ∩ FootprintVertices (cert.P 1 true) ⊆
        FootprintVertices (cert.Q 1 true) ∩ FootprintVertices (cert.P 1 true) :=
    (BandOrderedGeneralRawSupport q cfg C T cert).1
  have positiveCase (point : GaussianInt)
      (hk : Nat.card {is : Fin 3 × Bool //
        point ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2)
      (hA : point ∈ FootprintVertices (cert.P 0 true))
      (hC : point ∈ FootprintVertices (cert.P 1 true)) :
      point ∈ FootprintVertices (cert.Q 1 true) ∧
      (∀ y, y = point ∨ y = point + 1 ∨ y = point - 1 ∨
          y = point + ⟨0, 1⟩ ∨ y = point - ⟨0, 1⟩ →
        y ∈ FootprintVertices (cert.Q 1 true) ∨ y ∈ FootprintVertices (cert.P 1 true)) ∧
      (∀ z, z = point ∨ z = point - 1 ∨ z = point - ⟨0, 1⟩ ∨
          z = point - 1 - ⟨0, 1⟩ →
        z ∈ (cert.Q 1 true).cells ∨ z ∈ (cert.P 1 true).cells) :=
            RightInteriorConclusion.positiveCase q cfg C T cert twoPathEdges touching_disjoint
            edgeEndpoint threeBoundaries threeOwnersContradict threeOwnersAFContradict
            interfaceConclusion raw_support point hk hA hC
  constructor
  · exact positiveCase x hk
  · intro hB hD
    let F : GaussianInt → GaussianInt := fun z => t - z
    let v : GaussianInt := F x
    have hFinvol (z : GaussianInt) : F (F z) = z := by
      apply Zsqrtd.ext <;> simp [F]
    have image_mem (A B : Set GaussianInt) (hAB : F '' A = B)
        (z : GaussianInt) : z ∈ A ↔ F z ∈ B := RightInteriorGeometry.image_mem q u
            (RightInteriorGeometry.hFinj q u hFinvol) A B hAB z
    have parentFootprint (i : Fin 3) :
        F '' FootprintVertices (cert.P i true) =
          FootprintVertices (cert.P i false) := RightInteriorGeometry.parentFootprint q cfg C T
              cert u halfTurnFootprint outerFootprint i
    have parentBoundary := RightInteriorGeometry.parentBoundary q cfg C T cert u halfTurnBoundary
        outerNonempty outerBoundary
    have hboundaryFlip := RightInteriorGeometry.hboundaryFlip q cfg C T cert x u hFinvol
        image_mem parentBoundary (RightInteriorGeometry.parentBoundaryReverse q cfg C T cert u
        hFinvol parentBoundary)
    have hvA : v ∈ FootprintVertices (cert.P 0 true) := by
      exact (image_mem _ _ (parentFootprint 0) v).2 (by simpa [v, F] using hB)
    have hvC : v ∈ FootprintVertices (cert.P 1 true) := by
      exact (image_mem _ _ (parentFootprint 1) v).2 (by simpa [v, F] using hD)
    have hvk := RightInteriorGeometry.hvk q cfg C T cert x hk u hboundaryFlip
    have hpositive := positiveCase v hvk hvA hvC
    let wo := BandVectors.1 (q 3) (q 2)
    let wc := BandVectors.1 (cfg.firstPredecessor 1) (cfg.firstPredecessor 3)
    let delta : GaussianInt :=
      (GaussianQuarterTurn wo - wo) + (GaussianQuarterTurn wc - wc)
    have houterPlus := (cert.outer_occurrence 0 true).2.2
    have houterMinus := (cert.outer_occurrence 0 false).2.2
    have hchildPlus := (cert.plus_occurrence 1 true).2.2
    have hchildMinus := (cert.minus_occurrence 1 false).2.2
    dsimp [wo, wc] at houterPlus houterMinus hchildPlus hchildMinus
    have hdelta := RightInteriorGeometry.hdelta q cfg C T cert houterPlus houterMinus hchildPlus
        hchildMinus (RightInteriorGeometry.hquarterOffset) (RightInteriorGeometry.hdeltaRaw q cfg)
    have hQproto : BandPrototile (cfg.firstPredecessor 2) (cert.Q 1 true) :=
      (cert.plus_occurrence 1 true).1
    have hSproto : BandPrototile (cfg.firstPredecessor 2) (cert.S 1 false) :=
      (cert.minus_occurrence 1 false).1
    have hQtrans : BandPrototile (cfg.firstPredecessor 2)
        (TileTranslation (cert.Q 1 true) delta) :=
      BandPrototileTranslation _ _ _ hQproto
    have htransCells := (BandPrototileCentroidUnique (cfg.firstPredecessor 2)
      (TileTranslation (cert.Q 1 true) delta) (cert.S 1 false)
      hQtrans hSproto (RightInteriorGeometry.hQtransCentroid q cfg C T cert hdelta)).1
    have hrealQcentral := BandPrototileCentralSymmetry
      (cfg.firstPredecessor 2) (cert.Q 1 true) hQproto
    have hrealHQ : TileRealization (H (cert.Q 1 true)) =
        TileRealization (TileTranslation (cert.Q 1 true) delta) := RightInteriorGeometry.hrealHQ
            q cfg C T cert u halfTurnRealization (RightInteriorGeometry.hcentQS q cfg C T cert
            houterPlus houterMinus hchildPlus hchildMinus) hdelta hrealQcentral
    have hHQcells : (H (cert.Q 1 true)).cells = (cert.S 1 false).cells := by
      rw [cells_of_realization _ _ hrealHQ, htransCells]
    have hSLat : LatticeTile (cert.S 1 false) :=
      P4590T1PositivePrototileDisk _ _ hSproto (by
        rw [cfg.firstParentTwo]
        have hnonneg := (ProperBandCurvatureStructure q cfg.proper).2.1 (1 : Fin 3)
        have hn := cfg.noLine 2
        change 0 ≤ (q 2).1 at hnonneg
        omega)
    have childFoot : F '' FootprintVertices (cert.Q 1 true) =
        FootprintVertices (cert.S 1 false) := RightInteriorGeometry.childFoot q cfg C T cert u
            halfTurnFootprint (RightInteriorGeometry.hHQfoot q cfg C T cert u hHQcells
            (RightInteriorGeometry.hHQne q cfg C T cert u hHQcells hSLat))
    have moveFoot (U V : ProtoTile)
        (hUV : F '' FootprintVertices U = FootprintVertices V)
        (z : GaussianInt) (hz : F z ∈ FootprintVertices U) :
        z ∈ FootprintVertices V := RightInteriorGeometry.moveFoot q u hFinvol image_mem U V hUV z hz
    exact ⟨by
      exact moveFoot _ _ childFoot x (by simpa [hFinvol] using hpositive.1),
      (RightInteriorGeometry.hstar q cfg C T cert x hk u parentFootprint hvk hpositive childFoot
          moveFoot),
          (RightInteriorGeometry.hcellsAt1062 q cfg C T cert x u outerCells hpositive hHQcells
          (RightInteriorGeometry.moveCell q u hHcells) (RightInteriorGeometry.hcellLift q x u))⟩

end ApollonianSuperharmonic

end
