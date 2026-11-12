/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintInclusion

public import LeanPool.ApollonianSuperharmonic.CentrallyReflectedAt
public import LeanPool.ApollonianSuperharmonic.ExceptionalConnectorSegments
public import LeanPool.ApollonianSuperharmonic.PrecursorBoundaryArcData
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.P3161T2IncidentBoundary
public import LeanPool.ApollonianSuperharmonic.P3161T2PathSubwalk

-- [TABLET NODE: ExceptionalModifiedABPath]

/-!
# ExceptionalModifiedABPath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ExceptionalConnectorProof

private abbrev boundary_edge := BoundaryFootprintInclusion.boundaryEdge

private abbrev edge_vertex := BoundaryFootprintInclusion.edgeVertex

private theorem incident :
    ∀ (U : ProtoTile), ∀ (x : GaussianInt), Finset.Nonempty U.cells → x ∈ FootprintVertices U → ∃
        (j : Fin (4 : ℕ)), LatticeVertexIncidentCell x j ∈ U.cells := by
  classical
  intro U x hne hx
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

private theorem nonempty_touching :
    ∀ (U : ProtoTile), ∀ (V : ProtoTile), Finset.Nonempty U.cells → Finset.Nonempty V.cells →
        TileTouching U V → Disjoint U.cells V.cells ∧ SimpleGridPath (BoundaryFootprintVertices U
        ∩ BoundaryFootprintVertices V) (BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) := by
  classical
  intro U V hU hV ht
  rcases ht with h | h | h
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · rw [h.1] at hU
    simp at hU
  · rw [h.1] at hV
    simp at hV

private theorem common_boundary :
    (∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → ((x ∈ FootprintVertices U) → (∃
        j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells))) → (∀ (U : ProtoTile), ∀ (V :
            ProtoTile), Finset.Nonempty U.cells → Finset.Nonempty V.cells → Disjoint U.cells V.cells
        → ∀ x ∈ FootprintVertices U ∩ FootprintVertices V, x ∈ BoundaryFootprintVertices U ∩
        BoundaryFootprintVertices V) := by
  classical
  intro incident U V hU hV hd x hx
  obtain ⟨i, hi⟩ := incident U x hU hx.1
  obtain ⟨j, hj⟩ := incident V x hV hx.2
  exact ⟨P3161T2IncidentBoundary U x ⟨i, hi⟩
      ⟨j, fun h => Finset.disjoint_left.mp hd h hj⟩,
    P3161T2IncidentBoundary V x ⟨j, hj⟩
      ⟨i, fun h => Finset.disjoint_left.mp hd hi h⟩⟩

private theorem erase_loops :
    ∀ (R : GaussianInt → GaussianInt → Prop), ∀ (w : List GaussianInt), List.IsChain R w → ∃ (c :
        List GaussianInt), c.Nodup ∧ c.head? = w.head? ∧ c.getLast? = w.getLast? ∧ c.Sublist w ∧
        List.IsChain R c := by
  classical
  intro R w
  induction w with
  | nil => exact fun _ => ⟨[], by simp⟩
  | cons a w ih =>
    intro hw
    cases w with
    | nil => exact ⟨[a], by simp⟩
    | cons b w =>
      obtain ⟨c, hc, hh, ht, hs, hchain⟩ := ih hw.tail
      cases c with
      | nil => simp at hh
      | cons d c =>
        have hdb : d = b := by simpa using hh
        subst d
        by_cases ha : a ∈ b :: c
        · obtain ⟨l, r, heq⟩ := List.append_of_mem ha
          have hsub : (a :: r).Sublist (b :: c) := by
            rw [heq]
            exact List.sublist_append_right _ _
          refine ⟨a :: r, hc.sublist hsub, rfl, ?_,
            (hsub.trans hs).cons a, ?_⟩
          · rw [List.getLast?_cons_cons, ← ht, heq, List.getLast?_append_cons]
          · rw [heq] at hchain
            exact hchain.right_of_append
        · refine ⟨a :: b :: c, List.nodup_cons.mpr ⟨ha, hc⟩, rfl, ?_,
            hs.cons_cons a, ?_⟩
          · simpa only [List.getLast?_cons_cons] using ht
          · exact List.isChain_cons_cons.mpr
              ⟨(List.isChain_cons_cons.mp hw).1, hchain⟩

private theorem child_piece :
    (∀ (U : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈
        FootprintEdges U)) → ((∀ (U : ProtoTile), ∀ (x : GaussianInt), (x ∈
        BoundaryFootprintVertices U) → (x ∈ FootprintVertices U)) → ((∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (U.cells.Nonempty) → ((V.cells.Nonempty) → ((TileTouching U V) → (Disjoint
        U.cells V.cells ∧ SimpleGridPath (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices
        V) (BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V))))) → ((∀ (U : ProtoTile), ∀ (V
            : ProtoTile), (U.cells.Nonempty) → ((V.cells.Nonempty) → ((Disjoint U.cells V.cells)
            → (∀ (x : GaussianInt), (x ∈ FootprintVertices U ∩ FootprintVertices V) → (x ∈
        BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V))))) → ((∀ (R : GaussianInt →
        GaussianInt → Prop), ∀ w : List GaussianInt, w.IsChain R → ∃ c : List GaussianInt,
        c.Nodup ∧ c.head? = w.head? ∧ c.getLast? = w.getLast? ∧ c.Sublist w ∧ c.IsChain R) → (∀
            (U : ProtoTile), ∀ (V : ProtoTile), Finset.Nonempty U.cells → Finset.Nonempty V.cells →
        TileTouching U V → ∀ (x : GaussianInt), ∀ (y : GaussianInt), x ∈ FootprintVertices U ∩
        FootprintVertices V → y ∈ BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V → ∃
        (w : List GaussianInt), w.Nodup ∧ w.head? = some x ∧ w.getLast? = some y ∧ (∀ z ∈ w, z ∈
        FootprintVertices U ∩ FootprintVertices V) ∧ List.IsChain (fun (a b : GaussianInt) => {a,
        b} ∈ FootprintEdges U ∩ FootprintEdges V) w))))) := by
  classical
  intro boundary_edge boundary_vertex nonempty_touching common_boundary erase_loops U V hU hV ht
      x y hx hy
  obtain ⟨hd, hp⟩ := nonempty_touching U V hU hV ht
  obtain ⟨w, hh, hl, hv, he⟩ := P3161T2PathSubwalk hp x y
    (common_boundary U V hU hV hd x hx) hy
  have hchain : w.IsChain
      (fun a b => {a, b} ∈ FootprintEdges U ∩ FootprintEdges V) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro a b l r h
    exact ⟨boundary_edge U _ (he a b l r h).1,
      boundary_edge V _ (he a b l r h).2⟩
  obtain ⟨c, hc, hch, hcl, hsub, hce⟩ := erase_loops _ w hchain
  refine ⟨c, hc, hch.trans hh, hcl.trans hl, ?_, hce⟩
  intro z hz
  exact ⟨boundary_vertex U z (hv z (hsub.subset hz)).1,
    boundary_vertex V z (hv z (hsub.subset hz)).2⟩

private theorem middle_piece :
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), ∀ (Q2 :
        ProtoTile), ∀ (S3 : ProtoTile), ∀ (Q3 : ProtoTile), ∀ (S2 : ProtoTile), (O.cells ⊆
        B.cells) → ((S3.cells ⊆ B.cells) → ((Finset.Nonempty Q2.cells) → ((Finset.Nonempty
        S3.cells) → (∀ (arcs : PrecursorBoundaryArcData (TileCellComplement A O)
        (TileCellComplement B O) O O' Q2 S3 Q3 S2),
    let D := TileCellComplement A O
    (∀ (U : ProtoTile), ∀ (V : ProtoTile), (U.cells.Nonempty) → ((U.cells ⊆ V.cells) →
        (FootprintVertices U ⊆ FootprintVertices V))) → ((∀ (U : ProtoTile), ∀ (e : Finset
        GaussianInt), (e ∈ BoundaryFootprintEdges U) → (e ∈ FootprintEdges U)) → ((∀ (U :
            ProtoTile), ∀ (x : GaussianInt), (x ∈ BoundaryFootprintVertices U) → (x ∈
        FootprintVertices U)) → ((arcs.a ∈ BoundaryFootprintVertices Q2 ∧ arcs.a ∈
        BoundaryFootprintVertices S3 ∧ arcs.a ∈ BoundaryFootprintVertices O) → (∃ middle : List
        GaussianInt, middle.Nodup ∧ middle.head? = some arcs.a ∧ middle.getLast? = some arcs.b ∧
        (∀ z ∈ middle, z ∈ FootprintVertices D ∩ FootprintVertices O) ∧ middle.IsChain (fun x y
        => {x, y} ∈ FootprintEdges D ∩ FootprintEdges O) ∧ (∀ z ∈ middle, z ∈ FootprintVertices
        B))))))))) := by
  classical
  intro A B O O' Q2 S3 Q3 S2 hOb hS3 hQ2ne hS3ne arcs D vertices_mono boundary_edge
      boundary_vertex hfirst
  rcases arcs.branch with ⟨hOne, plus, minus, hpn, _, hph, hpl, _, _, hpv,
      _, hpe, _⟩ | ⟨hO, hab, ha, _⟩
  · have hpfoot : ∀ z ∈ plus,
        z ∈ FootprintVertices D ∩ FootprintVertices O := by
      intro z hz
      have hz' : z ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices O := by
        rw [← hpv]
        simpa using hz
      exact ⟨boundary_vertex D z hz'.1, boundary_vertex O z hz'.2⟩
    refine ⟨plus, hpn, hph, hpl, hpfoot, ?_, ?_⟩
    · apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro x y l r h
      exact ⟨boundary_edge D _ (hpe x y l r h).1,
        boundary_edge O _ (hpe x y l r h).2⟩
    · intro z hz
      exact vertices_mono O B hOne hOb (hpfoot z hz).2
  · refine ⟨[arcs.a], by simp, rfl, ?_, ?_, List.isChain_singleton _, ?_⟩
    · simpa using congrArg some hab
    · intro z hz
      have hza : z = arcs.a := by simpa using hz
      subst z
      refine ⟨vertices_mono Q2 D hQ2ne arcs.first_plus_child
        (boundary_vertex Q2 arcs.a hfirst.1), ?_⟩
      simp [FootprintVertices, hO, ha]
    · intro z hz
      have hza : z = arcs.a := by simpa using hz
      subst z
      exact vertices_mono S3 B hS3ne hS3
        (boundary_vertex S3 arcs.a hfirst.2.1)

private theorem splice :
    ∀ (R : GaussianInt → GaussianInt → Prop), ∀ (u : List GaussianInt), ∀ (v : List GaussianInt),
        ∀ (z : GaussianInt), u.getLast? = some z → v.head? = some z → List.IsChain R u →
        List.IsChain R v → List.IsChain R (u ++ v.tail) ∧ (u ++ v.tail).head? = u.head? ∧ (u ++
        v.tail).getLast? = v.getLast? := by
  classical
  intro R u v z hu hv cu cv
  have hune : u ≠ [] := by intro h; simp [h] at hu
  cases v with
  | nil => simp at hv
  | cons a v =>
    have haz : a = z := by simpa using hv
    subst a
    refine ⟨cu.append cv.tail ?_, ?_, ?_⟩
    · intro x hx y hy
      have hxz : x = z := by simpa [hu, eq_comm] using hx
      subst x
      exact cv.rel_head? hy
    · exact List.head?_append_of_ne_nil u hune
    · cases v with
      | nil => simpa using hu
      | cons b v =>
        simp only [List.tail_cons, List.getLast?_append_cons,
          List.getLast?_cons_cons]

end ExceptionalConnectorProof

theorem ExceptionalModifiedABPath :
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), ∀ (Q2 :
        ProtoTile), ∀ (S3 : ProtoTile), ∀ (Q3 : ProtoTile), ∀ (S2 : ProtoTile), ∀ (p1 :
        GaussianInt), ∀ (p2 : GaussianInt), (O.cells ⊆ A.cells) → ((O.cells ⊆ B.cells) →
        ((Q2.cells ⊆ A.cells) → ((S3.cells ⊆ B.cells) → ((Q3.cells ⊆ A.cells) → ((S2.cells ⊆
        B.cells) → ((Q2.cells.Nonempty) → ((S3.cells.Nonempty) → ((Q3.cells.Nonempty) →
        ((S2.cells.Nonempty) → ((TouchingTriple Q2 S3 O) → ((TouchingTriple Q3 S2 O) → ((p1 ∈
        FootprintVertices Q2 ∩ FootprintVertices S3) → ((p2 ∈ FootprintVertices Q3 ∩
        FootprintVertices S2) → ((TileTouching (TileCellComplement A O) O) → ((TileTouching
        (TileCellComplement B O) O) → ((CentrallyReflectedAt (TileCentroid O)
      (TileCellComplement A O) (TileCellComplement B O)) → ((QuarterTurnSymmetric O) → ((∀ x ∈
          FootprintVertices O, ∀ a : GaussianInt,
      x ∈ FootprintVertices (⟨{a}, a⟩ : ProtoTile) ->
        a ∈ A.cells ∨ a ∈ B.cells) → ((Nonempty (PrecursorBoundaryArcData
      (TileCellComplement A O) (TileCellComplement B O) O O'
      Q2 S3 Q3 S2)) → ((∃ x y : GaussianInt, x ≠ y ∧
      x ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B ∧
      y ∈ FootprintVertices (TileCellComplement A O) ∩ FootprintVertices B) → (Nonempty
          (ExceptionalConnectorSegments A B O Q2 S3 Q3 S2 p1 p2)))))))))))))))))))))) := by
  intro A B O O' Q2 S3 Q3 S2 p1 p2 hOa hOb hQ2 hS3 hQ3 hS2 hQ2ne hS3ne hQ3ne hS2ne
      hprecursorFirst hprecursorLast hp1 hp2 hcomplement hcomplementB hcentral hOsym hisolated
      harcs hcommonVertices
-- BODY
  classical
  obtain ⟨arcs⟩ := harcs
  let D := TileCellComplement A O
  have edges_mono (U V : ProtoTile) (h : U.cells ⊆ V.cells) :
      FootprintEdges U ⊆ FootprintEdges V := by
    rintro e ⟨c, hc, he⟩
    exact ⟨c, h hc, he⟩
  have vertices_mono (U V : ProtoTile) (hne : U.cells.Nonempty)
      (h : U.cells ⊆ V.cells) : FootprintVertices U ⊆ FootprintVertices V := by
    have hVne : V.cells.Nonempty := hne.mono h
    simp only [FootprintVertices, ite_eq_left hne, ite_eq_left hVne]
    rintro x ⟨c, hc, hx⟩
    exact ⟨c, h hc, hx⟩
  have boundary_edge (U : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges U) : e ∈ FootprintEdges U :=
          ExceptionalConnectorProof.boundary_edge U e he
  have edge_vertex (U : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges U) (x : GaussianInt) (hx : x ∈ e) :
      x ∈ FootprintVertices U := ExceptionalConnectorProof.edge_vertex U e he x hx
  have boundary_vertex (U : ProtoTile) (x : GaussianInt)
      (hx : x ∈ BoundaryFootprintVertices U) : x ∈ FootprintVertices U := by
    by_cases hne : U.cells.Nonempty
    · simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
      obtain ⟨e, he, hx⟩ := hx
      exact edge_vertex U e (boundary_edge U e he) x hx
    · simpa only [BoundaryFootprintVertices, FootprintVertices, ite_eq_right hne] using hx
  have incident (U : ProtoTile) (x : GaussianInt)
      (hne : U.cells.Nonempty) (hx : x ∈ FootprintVertices U) :
      ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells := ExceptionalConnectorProof.incident
          U x hne hx
  have nonempty_touching (U V : ProtoTile)
      (hU : U.cells.Nonempty) (hV : V.cells.Nonempty) (ht : TileTouching U V) :
      Disjoint U.cells V.cells ∧
        SimpleGridPath (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V)
          (BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) :=
              ExceptionalConnectorProof.nonempty_touching U V hU hV ht
  have common_boundary (U V : ProtoTile)
      (hU : U.cells.Nonempty) (hV : V.cells.Nonempty)
      (hd : Disjoint U.cells V.cells) (x : GaussianInt)
      (hx : x ∈ FootprintVertices U ∩ FootprintVertices V) :
      x ∈ BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V :=
          ExceptionalConnectorProof.common_boundary incident U V hU hV hd x hx
  -- Erasing a loop keeps a suffix beginning at the repeated vertex.
  have erase_loops (R : GaussianInt → GaussianInt → Prop) :
      ∀ w : List GaussianInt, w.IsChain R →
        ∃ c : List GaussianInt, c.Nodup ∧ c.head? = w.head? ∧
          c.getLast? = w.getLast? ∧ c.Sublist w ∧ c.IsChain R :=
              ExceptionalConnectorProof.erase_loops R
  have child_piece (U V : ProtoTile)
      (hU : U.cells.Nonempty) (hV : V.cells.Nonempty) (ht : TileTouching U V)
      (x y : GaussianInt) (hx : x ∈ FootprintVertices U ∩ FootprintVertices V)
      (hy : y ∈ BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V) :
      ∃ w : List GaussianInt, w.Nodup ∧ w.head? = some x ∧
        w.getLast? = some y ∧
        (∀ z ∈ w, z ∈ FootprintVertices U ∩ FootprintVertices V) ∧
        w.IsChain (fun a b => {a, b} ∈ FootprintEdges U ∩ FootprintEdges V) :=
            ExceptionalConnectorProof.child_piece boundary_edge boundary_vertex nonempty_touching
            common_boundary erase_loops U V hU hV ht x y hx hy
  have hfirst := (arcs.first_transition arcs.a).mpr rfl
  have hsecond := (arcs.second_transition arcs.b).mpr rfl
  obtain ⟨left, hln, hlh, hll, hlv, hle⟩ :=
    child_piece Q2 S3 hQ2ne hS3ne hprecursorFirst.1 p1 arcs.a hp1
      ⟨hfirst.1, hfirst.2.1⟩
  obtain ⟨revRight, hrn, hrh, hrl, hrv, hre⟩ :=
    child_piece Q3 S2 hQ3ne hS2ne hprecursorLast.1 p2 arcs.b hp2
      ⟨hsecond.1, hsecond.2.1⟩
  let right := revRight.reverse
  have hrightn : right.Nodup := List.nodup_reverse.mpr hrn
  have hrighth : right.head? = some arcs.b := by simpa [right] using hrl
  have hrightl : right.getLast? = some p2 := by simpa [right] using hrh
  have hrightv : ∀ z ∈ right,
      z ∈ FootprintVertices Q3 ∩ FootprintVertices S2 := by
    intro z hz
    exact hrv z (by simpa [right] using hz)
  have hrighte : right.IsChain
      (fun x y => {x, y} ∈ FootprintEdges Q3 ∩ FootprintEdges S2) := by
    apply List.isChain_reverse.mpr
    exact hre.imp (fun x y h => by simpa only [Finset.pair_comm] using h)
  have hleftRaw : ∀ z ∈ left, z ∈ FootprintVertices D ∩ FootprintVertices B := by
    intro z hz
    exact ⟨vertices_mono Q2 D hQ2ne arcs.first_plus_child (hlv z hz).1,
      vertices_mono S3 B hS3ne hS3 (hlv z hz).2⟩
  have hrightRaw : ∀ z ∈ right, z ∈ FootprintVertices D ∩ FootprintVertices B := by
    intro z hz
    exact ⟨vertices_mono Q3 D hQ3ne arcs.second_plus_child (hrightv z hz).1,
      vertices_mono S2 B hS2ne hS2 (hrightv z hz).2⟩
  have hleftEdges : left.IsChain
      (fun x y => {x, y} ∈ FootprintEdges D ∩ FootprintEdges B) :=
    hle.imp (fun _ _ h => ⟨edges_mono Q2 D arcs.first_plus_child h.1,
      edges_mono S3 B hS3 h.2⟩)
  have hrightEdges : right.IsChain
      (fun x y => {x, y} ∈ FootprintEdges D ∩ FootprintEdges B) :=
    hrighte.imp (fun _ _ h => ⟨edges_mono Q3 D arcs.second_plus_child h.1,
      edges_mono S2 B hS2 h.2⟩)
  have hempty : O.cells = ∅ → arcs.a = arcs.b ∧ arcs.a = O.anchor := by
    intro hO
    rcases arcs.branch with ⟨hne, _⟩ | ⟨_, hab, ha, _⟩
    · rw [hO] at hne
      simp at hne
    · exact ⟨hab, ha⟩
  -- The empty branch contributes only its exact anchor, never an edge.
  have middle_piece : ∃ middle : List GaussianInt,
      middle.Nodup ∧ middle.head? = some arcs.a ∧
      middle.getLast? = some arcs.b ∧
      (∀ z ∈ middle, z ∈ FootprintVertices D ∩ FootprintVertices O) ∧
      middle.IsChain (fun x y => {x, y} ∈ FootprintEdges D ∩ FootprintEdges O) ∧
      (∀ z ∈ middle, z ∈ FootprintVertices B) := ExceptionalConnectorProof.middle_piece A B O O'
          Q2 S3 Q3 S2 hOb hS3 hQ2ne hS3ne arcs vertices_mono boundary_edge boundary_vertex hfirst
  obtain ⟨middle, hmn, hmh, hml, hmv, hme, hmb⟩ := middle_piece
  have hmiddleRaw : ∀ z ∈ middle,
      z ∈ FootprintVertices D ∩ FootprintVertices B :=
    fun z hz => ⟨(hmv z hz).1, hmb z hz⟩
  have hmiddleEdges : middle.IsChain
      (fun x y => {x, y} ∈ FootprintEdges D ∩ FootprintEdges B) :=
    hme.imp (fun _ _ h => ⟨h.1, edges_mono O B hOb h.2⟩)
  have splice (R : GaussianInt → GaussianInt → Prop)
      (u v : List GaussianInt) (z : GaussianInt)
      (hu : u.getLast? = some z) (hv : v.head? = some z)
      (cu : u.IsChain R) (cv : v.IsChain R) :
      (u ++ v.tail).IsChain R ∧ (u ++ v.tail).head? = u.head? ∧
        (u ++ v.tail).getLast? = v.getLast? := ExceptionalConnectorProof.splice R u v z hu hv cu cv
  obtain ⟨hlmc, hlmh, hlml⟩ := splice _ left middle arcs.a hll hmh
    hleftEdges hmiddleEdges
  obtain ⟨hwc, hwh, hwl⟩ := splice _ (left ++ middle.tail) right arcs.b
    (hlml.trans hml) hrighth hlmc hrightEdges
  let walk := left ++ middle.tail ++ right.tail
  have hwalkHead : walk.head? = some p1 := hwh.trans (hlmh.trans hlh)
  have hwalkLast : walk.getLast? = some p2 := hwl.trans hrightl
  have hwalkRaw : ∀ z ∈ walk, z ∈ FootprintVertices D ∩ FootprintVertices B := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact hleftRaw z hz
      · exact hmiddleRaw z (List.mem_of_mem_tail hz)
    · exact hrightRaw z (List.mem_of_mem_tail hz)
  have hwalkSupport : ∀ z ∈ walk,
      z ∈ (FootprintVertices Q2 ∩ FootprintVertices S3) ∪ FootprintVertices O ∪
        (FootprintVertices Q3 ∩ FootprintVertices S2) := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact Or.inl (Or.inl (hlv z hz))
      · exact Or.inl (Or.inr (hmv z (List.mem_of_mem_tail hz)).2)
    · exact Or.inr (hrightv z (List.mem_of_mem_tail hz))
  obtain ⟨connector, hcn, hch, hcl, hcs, hce⟩ := erase_loops _ walk hwc
  exact ⟨{
    precursor_in_left := hOa
    precursor_in_right := hOb
    first_left_child := hQ2
    first_right_child := hS3
    second_left_child := hQ3
    second_right_child := hS2
    a := arcs.a
    b := arcs.b
    left := left
    middle := middle
    right := right
    walk := walk
    connector := connector
    left_nodup := hln
    middle_nodup := hmn
    right_nodup := hrightn
    left_head := hlh
    left_last := hll
    middle_head := hmh
    middle_last := hml
    right_head := hrighth
    right_last := hrightl
    walk_order := rfl
    walk_raw := hwalkRaw
    walk_edges := fun _ _ _ _ h =>
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hwc h
    left_vertices := hlv
    middle_vertices := hmv
    right_vertices := hrightv
    left_edges := fun _ _ _ _ h =>
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hle h
    middle_edges := fun _ _ _ _ h =>
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hme h
    right_edges := fun _ _ _ _ h =>
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hrighte h
    first_cut_unique := arcs.first_transition
    second_cut_unique := arcs.second_transition
    empty_cut := hempty
    connector_nodup := hcn
    connector_head := hch.trans hwalkHead
    connector_last := hcl.trans hwalkLast
    connector_raw := fun z hz => hwalkRaw z (hcs.subset hz)
    connector_edges := fun _ _ _ _ h =>
      List.isChain_iff_forall_rel_of_append_cons_cons.mp hce h
    connector_from_walk := hcs
    connector_support := fun z hz => hwalkSupport z (hcs.subset hz)
    common_vertices := hcommonVertices }⟩

end ApollonianSuperharmonic

end
