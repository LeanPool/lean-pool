/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.CommonFootprintEdgeVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle

-- [TABLET NODE: DisjointBoundaryCommonEdgeGraphAcyclic]

/-!
# DisjointBoundaryCommonEdgeGraphAcyclic

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CommonBoundaryAcyclicityConstruction

private noncomputable abbrev X (U : ProtoTile) (V : ProtoTile) := CommonFootprintEdgeVertices U V

private noncomputable abbrev G (U : ProtoTile) (V : ProtoTile) : SimpleGraph (X U V) := by
  classical
  let X := CommonFootprintEdgeVertices U V
  change (SimpleGraph X)
  exact SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈
      FootprintEdges U ∩ FootprintEdges V

private theorem cycle_subcycle_eq {B : SimpleGraph GaussianInt} {u w : GaussianInt}
      (outer : B.Walk u u) (inner : B.Walk w w)
      (houter : outer.IsCycle) (hinner : inner.IsCycle)
      (hle : inner.toSubgraph ≤ outer.toSubgraph) :
      inner.toSubgraph = outer.toSubgraph := by
  classical
  have neighbor_eq {a : GaussianInt} (ha : a ∈ inner.toSubgraph.verts) :
      inner.toSubgraph.neighborSet a = outer.toSubgraph.neighborSet a := by
    apply Set.eq_of_subset_of_ncard_le
    · intro b hab
      exact hle.2 hab
    · rw [hinner.ncard_neighborSet_toSubgraph_eq_two
        (inner.mem_verts_toSubgraph.mp ha)]
      rw [houter.ncard_neighborSet_toSubgraph_eq_two
        (outer.mem_verts_toSubgraph.mp (hle.1 ha))]
    · exact SimpleGraph.Walk.finite_neighborSet_toSubgraph outer
  have propagate {a b : GaussianInt} (ha : a ∈ inner.toSubgraph.verts)
      (hab : outer.toSubgraph.Adj a b) : b ∈ inner.toSubgraph.verts := by
    have hb : b ∈ inner.toSubgraph.neighborSet a := by
      rw [neighbor_eq ha]
      exact hab
    exact inner.toSubgraph.edge_vert hb.symm
  have verts_eq : inner.toSubgraph.verts = outer.toSubgraph.verts := by
    apply Set.Subset.antisymm hle.1
    intro z hz
    have hwInner : w ∈ inner.toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact inner.start_mem_support
    have hwOuter : w ∈ outer.toSubgraph.verts := hle.1 hwInner
    obtain ⟨walk⟩ := outer.toSubgraph_connected
      ⟨w, hwOuter⟩ ⟨z, hz⟩
    have walk_end_mem :
        ∀ {a b : outer.toSubgraph.verts}
          (q : outer.toSubgraph.coe.Walk a b),
          a.1 ∈ inner.toSubgraph.verts → b.1 ∈ inner.toSubgraph.verts := by
      intro a b q ha
      induction q with
      | nil => exact ha
      | @cons a b d hab q ih =>
          apply ih
          exact propagate ha (by simpa using hab)
    exact walk_end_mem walk hwInner
  apply SimpleGraph.Subgraph.ext
  · exact verts_eq
  · funext a b
    apply propext
    constructor
    · intro hab
      exact hle.2 hab
    · intro hab
      have ha : a ∈ inner.toSubgraph.verts := verts_eq ▸ outer.toSubgraph.edge_vert hab
      have : b ∈ inner.toSubgraph.neighborSet a := by
        rw [neighbor_eq ha]
        exact hab
      exact this

private noncomputable abbrev boundaryGraph (T : ProtoTile) : SimpleGraph GaussianInt := by
  classical
  exact SimpleGraph.fromRel fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T

private theorem pair_eq_iff_sym2 (a b r s' : GaussianInt) :
      ({a, b} : Finset GaussianInt) = {r, s'} ↔ s(a, b) = s(r, s') := by
  classical
  constructor
  · intro h
    have hs : ({a, b} : Set GaussianInt) = {r, s'} := by
      ext t
      have ht := congrArg (fun e : Finset GaussianInt => t ∈ e) h
      apply Iff.of_eq
      simpa only [Finset.mem_insert, Finset.mem_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] using ht
    rw [Set.pair_eq_pair_iff] at hs
    simpa [Sym2.eq] using hs
  · intro h
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h
    rcases h with h | h
    · simp [h.1, h.2]
    · simp [h.1, h.2, Finset.pair_comm]

private theorem boundary_cycle (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T)) :
      ∃ (z : GaussianInt) (d : (boundaryGraph T).Walk z z), d.IsCycle ∧
        ∀ {a b : GaussianInt}, a ≠ b →
          (({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
            d.toSubgraph.Adj a b) := by
  classical
  let boundaryGraph (T : ProtoTile) : SimpleGraph GaussianInt :=
    SimpleGraph.fromRel fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have pair_eq_iff_sym2 (a b r s' : GaussianInt) :
      ({a, b} : Finset GaussianInt) = {r, s'} ↔ s(a, b) = s(r, s') := pair_eq_iff_sym2 a b r s'
  change (∃ (z : GaussianInt) (d : (boundaryGraph T).Walk z z), d.IsCycle ∧
        ∀ {a b : GaussianInt}, a ≠ b →
          (({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
            d.toSubgraph.Adj a b))
  obtain ⟨p, x, y, hpNodup, hpLength, hpHead, hpLast, _, hclose,
    hpAdj, hpEdges⟩ := ht
  have hpne : p ≠ [] := by intro h; simp [h] at hpLength
  have hxy : y ≠ x := by
    intro h
    subst y
    simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hclose
    omega
  have graph_adj_iff (a b : GaussianInt) :
      (boundaryGraph T).Adj a b ↔ a ≠ b ∧
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T := by
    simp only [boundaryGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hne, hab | hba⟩
      · exact ⟨hne, hab⟩
      · exact ⟨hne, Finset.pair_comm b a ▸ hba⟩
    · rintro ⟨hne, hab⟩
      exact ⟨hne, Or.inl hab⟩
  have hpChain : List.IsChain (boundaryGraph T).Adj p := by
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro a b l₁ l₂ heq
    apply (graph_adj_iff a b).mpr
    refine ⟨?_, ?_⟩
    · have hadj := hpAdj a b l₁ l₂ heq
      intro hab
      subst b
      simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hadj
      omega
    · exact (hpEdges {a, b}).mpr (Or.inr ⟨a, b, l₁, l₂, heq, rfl⟩)
  have hx : p.head hpne = x := by
    exact (List.head_eq_iff_head?_eq_some hpne).mpr hpHead
  have hy : p.getLast hpne = y := by
    exact (List.getLast_eq_iff_getLast?_eq_some hpne).mpr hpLast
  let q : (boundaryGraph T).Walk x y :=
    (SimpleGraph.Walk.ofSupport p hpne hpChain).copy hx hy
  have hqSupport : q.support = p := by
    simp [q]
  have hqPath : q.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hqSupport]
    exact hpNodup
  have hcloseAdj : (boundaryGraph T).Adj y x :=
    (graph_adj_iff y x).mpr ⟨hxy,
      (hpEdges {y, x}).mpr (Or.inl rfl)⟩
  have hcloseNotMem : s(y, x) ∉ q.edges := by
    intro hmem
    have hlen := hqPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hqLength : q.length = p.length - 1 := by
      simp [q]
    omega
  let d : (boundaryGraph T).Walk y y := q.cons hcloseAdj
  have hdCycle : d.IsCycle := by
    change (q.cons hcloseAdj).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨hqPath, hcloseNotMem⟩
  refine ⟨y, d, hdCycle, ?_⟩
  intro a b hab
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  simp only [d, SimpleGraph.Walk.edges_cons, List.mem_cons]
  rw [hpEdges]
  constructor
  · intro he
    rcases he with he | ⟨r, s', l₁, l₂, heq, hrs⟩
    · left
      exact (pair_eq_iff_sym2 a b y x).mp he
    · right
      rw [SimpleGraph.Walk.edges_eq_zipWith_support, hqSupport]
      have adjacent_mem_zip (l₁ l₂ : List GaussianInt)
          (r s' : GaussianInt) : s(r, s') ∈
            List.zipWith (fun x y => s(x, y))
              (l₁ ++ r :: s' :: l₂) (l₁ ++ r :: s' :: l₂).tail := by
        induction l₁ with
        | nil => simp
        | cons t l ih =>
            cases l with
            | nil => simp
            | cons r' l =>
                simp only [List.cons_append, List.tail_cons,
                  List.zipWith_cons_cons, List.mem_cons]
                exact Or.inr ih
      have hm : s(r, s') ∈
          List.zipWith (fun x y => s(x, y)) p p.tail := by
        rw [heq]
        exact adjacent_mem_zip l₁ l₂ r s'
      have hsym : s(a, b) = s(r, s') := by
        exact (pair_eq_iff_sym2 a b r s').mp hrs
      exact hsym ▸ hm
  · intro he
    rcases he with he | he
    · left
      exact (pair_eq_iff_sym2 a b y x).mpr he
    · right
      rw [SimpleGraph.Walk.edges_eq_zipWith_support, hqSupport] at he
      rw [List.mem_iff_getElem] at he
      obtain ⟨i, hi, hieq⟩ := he
      have hi' : i + 1 < p.length := by
        simp [List.length_zipWith] at hi
        omega
      let l₁ := p.take i
      let l₂ := p.drop (i + 2)
      have hpdecomp : p = l₁ ++ p[i] :: p[i + 1] :: l₂ := by
        simp only [l₁, l₂]
        calc
          p = p.take i ++ p.drop i := (List.take_append_drop i p).symm
          _ = p.take i ++ p[i] :: p.drop (i + 1) := by
            rw [List.drop_eq_getElem_cons (by omega)]
          _ = p.take i ++ p[i] :: p[i + 1] :: p.drop (i + 2) := by
            rw [List.drop_eq_getElem_cons hi']
      refine ⟨p[i], p[i + 1], l₁, l₂, hpdecomp, ?_⟩
      have hieq' : s(p[i], p[i + 1]) = s(a, b) := by
        simpa using hieq
      exact (pair_eq_iff_sym2 a b p[i] p[i + 1]).mpr hieq'.symm

private theorem boundary_pair_common (U : ProtoTile) (V : ProtoTile) (v : ↑(X U V)) (c : (G U
    V).Walk v v) (hc : c.IsCycle) (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T))
      (hsub : FootprintEdges U ∩ FootprintEdges V ⊆
        BoundaryFootprintEdges T) :
      ∀ {a b : GaussianInt}, a ≠ b →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges U ∩ FootprintEdges V := by
  classical
  let X := CommonFootprintEdgeVertices U V
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈
      FootprintEdges U ∩ FootprintEdges V
  have cycle_subcycle_eq {B : SimpleGraph GaussianInt} {u w : GaussianInt}
      (outer : B.Walk u u) (inner : B.Walk w w)
      (houter : outer.IsCycle) (hinner : inner.IsCycle)
      (hle : inner.toSubgraph ≤ outer.toSubgraph) :
      inner.toSubgraph = outer.toSubgraph := cycle_subcycle_eq (B := B) (u := u) (w := w) outer
          inner houter hinner hle
  let boundaryGraph (T : ProtoTile) : SimpleGraph GaussianInt :=
    SimpleGraph.fromRel fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have boundary_cycle (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T)) :
      ∃ (z : GaussianInt) (d : (boundaryGraph T).Walk z z), d.IsCycle ∧
        ∀ {a b : GaussianInt}, a ≠ b →
          (({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
            d.toSubgraph.Adj a b) := boundary_cycle T ht
  obtain ⟨z, outer, houter, houtAdj⟩ := boundary_cycle T ht
  let f : G →g boundaryGraph T := {
    toFun := fun a => a.1
    map_rel' := by
      intro a b hab
      have hne : a.1 ≠ b.1 := by
        intro h
        apply hab.ne
        exact Subtype.ext h
      have hab' : ({a.1, b.1} : Finset GaussianInt) ∈
          FootprintEdges U ∩ FootprintEdges V := by
        simp only [G, SimpleGraph.fromRel_adj] at hab
        rcases hab.2 with hab | hab
        · exact hab
        · simpa [Finset.pair_comm] using hab
      simp only [boundaryGraph, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl (hsub hab')⟩ }
  let inner := c.map f
  have hinner : inner.IsCycle := hc.map Subtype.val_injective
  have hadjle {a b : GaussianInt}
      (hab : inner.toSubgraph.Adj a b) : outer.toSubgraph.Adj a b := by
    have habB : (boundaryGraph T).Adj a b := inner.toSubgraph.adj_sub hab
    have hne : a ≠ b := habB.ne
    apply (houtAdj hne).mp
    simp only [boundaryGraph, SimpleGraph.fromRel_adj] at habB
    rcases habB.2 with habB | habB
    · exact habB
    · simpa [Finset.pair_comm] using habB
  have hle : inner.toSubgraph ≤ outer.toSubgraph := by
    refine ⟨?_, ?_⟩
    · intro a ha
      have hncard := hinner.ncard_neighborSet_toSubgraph_eq_two
        (inner.mem_verts_toSubgraph.mp ha)
      have hn : inner.toSubgraph.neighborSet a |>.Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero
        omega
      obtain ⟨b, hb⟩ := hn
      exact outer.toSubgraph.edge_vert (hadjle hb)
    · intro a b hab
      exact hadjle hab
  have heq := cycle_subcycle_eq outer inner houter hinner hle
  intro a b hab hboundary
  have houterAdj : outer.toSubgraph.Adj a b := (houtAdj hab).mp hboundary
  have hinnerAdj : inner.toSubgraph.Adj a b := heq ▸ houterAdj
  change (c.map f).toSubgraph.Adj a b at hinnerAdj
  rw [SimpleGraph.Walk.toSubgraph_map, SimpleGraph.Subgraph.map_adj] at hinnerAdj
  rcases hinnerAdj with ⟨a', b', hab', ha', hb'⟩
  have hG : G.Adj a' b' := c.toSubgraph.adj_sub hab'
  have hG' : ({a'.1, b'.1} : Finset GaussianInt) ∈
      FootprintEdges U ∩ FootprintEdges V := by
    simp only [G, SimpleGraph.fromRel_adj] at hG
    rcases hG.2 with hG | hG
    · exact hG
    · simpa [Finset.pair_comm] using hG
  rw [← ha', ← hb']
  exact hG'

private theorem hsubU (U : ProtoTile) (V : ProtoTile) (hedges : FootprintEdges U ∩ FootprintEdges
    V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges U := by
  classical
  intro e he
  have he' : e ∈ BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
    rw [← hedges]
    exact he
  exact he'.1

private theorem hsubV (U : ProtoTile) (V : ProtoTile) (hedges : FootprintEdges U ∩ FootprintEdges
    V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges V := by
  classical
  intro e he
  have he' : e ∈ BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
    rw [← hedges]
    exact he
  exact he'.2

private theorem vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := by
  classical
  have vertical_unique (a b : GaussianInt)
      (h : ({a, a + ⟨0, 1⟩} : Finset GaussianInt) =
        {b, b + ⟨0, 1⟩}) : a = b := by
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]
      simp
    have ha1 : a + ⟨0, 1⟩ ∈
        ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    · exact hab
    · exact hab
    · apply_fun Zsqrtd.im at hab ha1b
      simp at hab ha1b
      omega
    · apply_fun Zsqrtd.im at hab ha1b
      simp at hab ha1b
      omega
  have horizontal_vertical_ne (a b : GaussianInt) :
      ({a, a + 1} : Finset GaussianInt) ≠
        {b, b + ⟨0, 1⟩} := by
    intro h
    have ha : a ∈ ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]
      simp
    have ha1 : a + 1 ∈
        ({b, b + ⟨0, 1⟩} : Finset GaussianInt) := by
      rw [← h]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ha1
    rcases ha with hab | hab <;> rcases ha1 with ha1b | ha1b
    all_goals
      apply_fun Zsqrtd.re at hab ha1b
      simp at hab ha1b
      omega
  constructor
  · rintro ⟨a, (⟨ha, hocc⟩ | ⟨ha, hocc⟩)⟩
    · exact False.elim (horizontal_vertical_ne a z ha.symm)
    · have haz := vertical_unique a z ha.symm
      simpa [haz] using hocc
  · intro h
    exact ⟨z, Or.inr ⟨rfl, h⟩⟩

private theorem huOut (U : ProtoTile) (u : ApollonianSuperharmonic.LatticeCell) (huMax : ∀ x' ∈
    U.cells, x'.re ≤ u.re) : u + 1 ∉ U.cells := by
  classical
  intro hu1
  have := huMax (u + 1) hu1
  simp at this

private theorem hvOut (V : ProtoTile) (v' : ApollonianSuperharmonic.LatticeCell) (hvMax : ∀ x' ∈
    V.cells, x'.re ≤ v'.re) : v' + 1 ∉ V.cells := by
  classical
  intro hv1
  have := hvMax (v' + 1) hv1
  simp at this

private theorem huNotV (U : ProtoTile) (V : ProtoTile) (hdisjoint : Disjoint U.cells V.cells) (u
    : ApollonianSuperharmonic.LatticeCell) (hu : u ∈ U.cells) : u ∉ V.cells := by
  classical
  exact Finset.disjoint_left.mp hdisjoint hu

private theorem hvNotU (U : ProtoTile) (V : ProtoTile) (hdisjoint : Disjoint U.cells V.cells) (v'
    : ApollonianSuperharmonic.LatticeCell) (hv' : v' ∈ V.cells) : v' ∉ U.cells := by
  classical
  exact Finset.disjoint_left.mp hdisjoint.symm hv'

private theorem hUne (u : ApollonianSuperharmonic.LatticeCell) : u + 1 ≠ u + 1 + ⟨0, 1⟩ := by
  classical
  intro h
  apply_fun Zsqrtd.im at h
  simp at h

private theorem hVne (v' : ApollonianSuperharmonic.LatticeCell) : v' + 1 ≠ v' + 1 + ⟨0, 1⟩ := by
  classical
  intro h
  apply_fun Zsqrtd.im at h
  simp at h

private theorem hUright (U : ProtoTile) (u : ApollonianSuperharmonic.LatticeCell) (hu : u ∈
    U.cells) (huMax : ∀ x' ∈ U.cells, x'.re ≤ u.re) : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset
    GaussianInt) ∈
      BoundaryFootprintEdges U := by
  classical
  have vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := vertical_boundary_iff T z
  have huOut : u + 1 ∉ U.cells := huOut U u huMax
  apply (vertical_boundary_iff U (u + 1)).mpr
  right
  simpa [Zsqrtd.ext_iff] using And.intro huOut hu

private theorem hVright (V : ProtoTile) (v' : ApollonianSuperharmonic.LatticeCell) (hv' : v' ∈
    V.cells) (hvMax : ∀ x' ∈ V.cells, x'.re ≤ v'.re) : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset
    GaussianInt) ∈
      BoundaryFootprintEdges V := by
  classical
  have vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := vertical_boundary_iff T z
  have hvOut : v' + 1 ∉ V.cells := hvOut V v' hvMax
  apply (vertical_boundary_iff V (v' + 1)).mpr
  right
  simpa [Zsqrtd.ext_iff] using And.intro hvOut hv'

private theorem hUrightV (U : ProtoTile) (V : ProtoTile) (hUcycle : SimpleGridCycle
    (BoundaryFootprintVertices U)
      (BoundaryFootprintEdges U)) (hedges : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) (v : ↑(X U V)) (u :
          ApollonianSuperharmonic.LatticeCell) (c : (G U V).Walk v v) (hu : u ∈ U.cells) (huMax :
          ∀ x' ∈ U.cells, x'.re ≤ u.re) (hc : c.IsCycle) : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset
          GaussianInt) ∈
      BoundaryFootprintEdges V := by
  classical
  have boundary_pair_common (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T))
      (hsub : FootprintEdges U ∩ FootprintEdges V ⊆
        BoundaryFootprintEdges T) :
      ∀ {a b : GaussianInt}, a ≠ b →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges U ∩ FootprintEdges V :=
            boundary_pair_common U V v c hc T ht hsub
  have hsubU : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges U := hsubU U V hedges
  have hUne : u + 1 ≠ u + 1 + ⟨0, 1⟩ := hUne u
  have hUright : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U := hUright U u hu huMax
  have hUcommon := boundary_pair_common U hUcycle hsubU hUne hUright
  have : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
    rw [← hedges]
    exact hUcommon
  exact this.2

private theorem hVrightU (U : ProtoTile) (V : ProtoTile) (hVcycle : SimpleGridCycle
    (BoundaryFootprintVertices V)
      (BoundaryFootprintEdges V)) (hedges : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) (v : ↑(X U V)) (v' :
          ApollonianSuperharmonic.LatticeCell) (c : (G U V).Walk v v) (hv' : v' ∈ V.cells) (hvMax
          : ∀ x' ∈ V.cells, x'.re ≤ v'.re) (hc : c.IsCycle) : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset
          GaussianInt) ∈
      BoundaryFootprintEdges U := by
  classical
  have boundary_pair_common (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T))
      (hsub : FootprintEdges U ∩ FootprintEdges V ⊆
        BoundaryFootprintEdges T) :
      ∀ {a b : GaussianInt}, a ≠ b →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges U ∩ FootprintEdges V :=
            boundary_pair_common U V v c hc T ht hsub
  have hsubV : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges V := hsubV U V hedges
  have hVne : v' + 1 ≠ v' + 1 + ⟨0, 1⟩ := hVne v'
  have hVright : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges V := hVright V v' hv' hvMax
  have hVcommon := boundary_pair_common V hVcycle hsubV hVne hVright
  have : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V := by
    rw [← hedges]
    exact hVcommon
  exact this.1

private theorem hu1V (U : ProtoTile) (V : ProtoTile) (hdisjoint : Disjoint U.cells V.cells)
    (hUcycle : SimpleGridCycle (BoundaryFootprintVertices U)
      (BoundaryFootprintEdges U)) (hedges : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) (v : ↑(X U V)) (u :
          ApollonianSuperharmonic.LatticeCell) (c : (G U V).Walk v v) (hu : u ∈ U.cells) (huMax :
          ∀ x' ∈ U.cells, x'.re ≤ u.re) (hc : c.IsCycle) : u + 1 ∈ V.cells := by
  classical
  have vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := vertical_boundary_iff T z
  have huNotV : u ∉ V.cells := huNotV U V hdisjoint u hu
  have hUrightV : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges V := hUrightV U V hUcycle hedges v u c hu huMax hc
  rcases (vertical_boundary_iff V (u + 1)).mp hUrightV with h | h
  · exact h.1
  · exfalso
    apply huNotV
    simpa [Zsqrtd.ext_iff] using h.2

private theorem hv1U (U : ProtoTile) (V : ProtoTile) (hdisjoint : Disjoint U.cells V.cells)
    (hVcycle : SimpleGridCycle (BoundaryFootprintVertices V)
      (BoundaryFootprintEdges V)) (hedges : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) (v : ↑(X U V)) (v' :
          ApollonianSuperharmonic.LatticeCell) (c : (G U V).Walk v v) (hv' : v' ∈ V.cells) (hvMax
          : ∀ x' ∈ V.cells, x'.re ≤ v'.re) (hc : c.IsCycle) : v' + 1 ∈ U.cells := by
  classical
  have vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) := vertical_boundary_iff T z
  have hvNotU : v' ∉ U.cells := hvNotU U V hdisjoint v' hv'
  have hVrightU : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U := hVrightU U V hVcycle hedges v v' c hv' hvMax hc
  rcases (vertical_boundary_iff U (v' + 1)).mp hVrightU with h | h
  · exact h.1
  · exfalso
    apply hvNotU
    simpa [Zsqrtd.ext_iff] using h.2

end CommonBoundaryAcyclicityConstruction

theorem DisjointBoundaryCommonEdgeGraphAcyclic (U V : ProtoTile)
    (hdisjoint : Disjoint U.cells V.cells)
    (hUcycle : SimpleGridCycle (BoundaryFootprintVertices U)
      (BoundaryFootprintEdges U))
    (hVcycle : SimpleGridCycle (BoundaryFootprintVertices V)
      (BoundaryFootprintEdges V))
    (hcommon : (FootprintEdges U ∩ FootprintEdges V).Nonempty)
    (hedges : FootprintEdges U ∩ FootprintEdges V =
      BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) :
    let X := CommonFootprintEdgeVertices U V
    let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
      ({a.1, b.1} : Finset GaussianInt) ∈
        FootprintEdges U ∩ FootprintEdges V
    G.IsAcyclic := by
-- BODY
  classical
  dsimp only
  let X := CommonFootprintEdgeVertices U V
  let G : SimpleGraph X := SimpleGraph.fromRel fun a b =>
    ({a.1, b.1} : Finset GaussianInt) ∈
      FootprintEdges U ∩ FootprintEdges V
  change G.IsAcyclic
  intro v c hc
  have cycle_subcycle_eq {B : SimpleGraph GaussianInt} {u w : GaussianInt}
      (outer : B.Walk u u) (inner : B.Walk w w)
      (houter : outer.IsCycle) (hinner : inner.IsCycle)
      (hle : inner.toSubgraph ≤ outer.toSubgraph) :
      inner.toSubgraph = outer.toSubgraph :=
          CommonBoundaryAcyclicityConstruction.cycle_subcycle_eq (B := B) (u := u) (w := w) outer
          inner houter hinner hle
  let boundaryGraph (T : ProtoTile) : SimpleGraph GaussianInt :=
    SimpleGraph.fromRel fun a b =>
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have pair_eq_iff_sym2 (a b r s' : GaussianInt) :
      ({a, b} : Finset GaussianInt) = {r, s'} ↔ s(a, b) = s(r, s') :=
          CommonBoundaryAcyclicityConstruction.pair_eq_iff_sym2 a b r s'
  have boundary_cycle (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T)) :
      ∃ (z : GaussianInt) (d : (boundaryGraph T).Walk z z), d.IsCycle ∧
        ∀ {a b : GaussianInt}, a ≠ b →
          (({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
            d.toSubgraph.Adj a b) := CommonBoundaryAcyclicityConstruction.boundary_cycle T ht
  have boundary_pair_common (T : ProtoTile)
      (ht : SimpleGridCycle (BoundaryFootprintVertices T)
        (BoundaryFootprintEdges T))
      (hsub : FootprintEdges U ∩ FootprintEdges V ⊆
        BoundaryFootprintEdges T) :
      ∀ {a b : GaussianInt}, a ≠ b →
        ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges U ∩ FootprintEdges V :=
            CommonBoundaryAcyclicityConstruction.boundary_pair_common U V v c hc T ht hsub
  have hsubU : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges U := CommonBoundaryAcyclicityConstruction.hsubU U V hedges
  have hsubV : FootprintEdges U ∩ FootprintEdges V ⊆
      BoundaryFootprintEdges V := CommonBoundaryAcyclicityConstruction.hsubV U V hedges
  have vertical_boundary_iff (T : ProtoTile) (z : GaussianInt) :
      ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ↔
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells)) :=
              CommonBoundaryAcyclicityConstruction.vertical_boundary_iff T z
  obtain ⟨e, heU, heV⟩ := hcommon
  obtain ⟨u0, hu0, _⟩ := heU
  obtain ⟨v0, hv0, _⟩ := heV
  obtain ⟨u, hu, huMax⟩ :=
    U.cells.exists_max_image (fun q => q.re) ⟨u0, hu0⟩
  obtain ⟨v', hv', hvMax⟩ :=
    V.cells.exists_max_image (fun q => q.re) ⟨v0, hv0⟩
  have huOut : u + 1 ∉ U.cells := CommonBoundaryAcyclicityConstruction.huOut U u huMax
  have hvOut : v' + 1 ∉ V.cells := CommonBoundaryAcyclicityConstruction.hvOut V v' hvMax
  have huNotV : u ∉ V.cells := CommonBoundaryAcyclicityConstruction.huNotV U V hdisjoint u hu
  have hvNotU : v' ∉ U.cells := CommonBoundaryAcyclicityConstruction.hvNotU U V hdisjoint v' hv'
  have hUne : u + 1 ≠ u + 1 + ⟨0, 1⟩ := CommonBoundaryAcyclicityConstruction.hUne u
  have hVne : v' + 1 ≠ v' + 1 + ⟨0, 1⟩ := CommonBoundaryAcyclicityConstruction.hVne v'
  have hUright : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U := CommonBoundaryAcyclicityConstruction.hUright U u hu huMax
  have hVright : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges V := CommonBoundaryAcyclicityConstruction.hVright V v' hv' hvMax
  have hUcommon := boundary_pair_common U hUcycle hsubU hUne hUright
  have hVcommon := boundary_pair_common V hVcycle hsubV hVne hVright
  have hUrightV : ({u + 1, u + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges V := CommonBoundaryAcyclicityConstruction.hUrightV U V hUcycle
          hedges v u c hu huMax hc
  have hVrightU : ({v' + 1, v' + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U := CommonBoundaryAcyclicityConstruction.hVrightU U V hVcycle
          hedges v v' c hv' hvMax hc
  have hu1V : u + 1 ∈ V.cells := CommonBoundaryAcyclicityConstruction.hu1V U V hdisjoint hUcycle
      hedges v u c hu huMax hc
  have hv1U : v' + 1 ∈ U.cells := CommonBoundaryAcyclicityConstruction.hv1U U V hdisjoint hVcycle
      hedges v v' c hv' hvMax hc
  have huv := hvMax (u + 1) hu1V
  have hvu := huMax (v' + 1) hv1U
  simp at huv hvu
  omega

end ApollonianSuperharmonic

end
