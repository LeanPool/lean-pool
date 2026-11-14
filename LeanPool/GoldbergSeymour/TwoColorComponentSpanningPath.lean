/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Two Color Component Spanning Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorComponentSpanningPath {V E : Type*}
    [Finite V] [Finite E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hproper : IsProperEdgeColoring G phi)
    (z : Sum V E) :
    ∃ (u v : Sum V E) (p : (TwoColorIncidenceGraph G phi alpha beta).Walk u v),
    p.IsPath ∧ {x | x ∈ p.support} = TwoColorComponent G phi alpha beta z := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := H.connectedComponentMk z
  let : Nonempty C := ⟨⟨z, by
    change z ∈ C.supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    ⟩⟩
  obtain ⟨a, b, q, hq, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length C.toSimpleGraph
  have hqall : ∀ x : C, x ∈ q.support := by
    intro x
    by_contra hx
    have hboundary : ∃ v w : C, v ∈ q.support ∧ w ∉ q.support ∧
        C.toSimpleGraph.Adj v w := by
      by_contra hno
      push Not at hno
      have hr : C.toSimpleGraph.Reachable a x :=
        C.connected_toSimpleGraph.preconnected a x
      have hm := hr.mem_subgraphVerts
        (H := (⊤ : C.toSimpleGraph.Subgraph).induce {y | y ∈ q.support})
        (fun v hv w hadj => by
          have hv' : v ∈ q.support := by simpa using hv
          have hw' : w ∈ q.support := by
            by_contra hw'
            exact hno v w hv' hw' (by simpa using hadj)
          exact ⟨hv', hw', hadj⟩)
        (by simp)
      have : x ∈ q.support := by simpa using hm
      exact hx this
    obtain ⟨v, w, hv, hw, hvw⟩ := hboundary
    obtain ⟨i, hvi, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    have hle : i ≤ q.length := hi
    have hvi' : q.getVert i = v := hvi
    by_cases hi0 : i = 0
    · have hvstart : v = a := by
        calc
          v = q.getVert i := hvi'.symm
          _ = q.getVert 0 := congrArg q.getVert hi0
          _ = a := q.getVert_zero
      subst v
      have hend : C.toSimpleGraph.Adj a w := by simpa [hvi', hi0] using hvw
      have hnew : (q.reverse.concat hend).IsPath :=
        hq.reverse.concat (by simpa using hw) hend
      have hlong := hmax _ _ _ hnew
      simp at hlong
    by_cases hil : i = q.length
    · have hvend : v = b := by
        rw [← hvi', hq.getVert_eq_end_iff hle]
        exact hil
      subst v
      have hend : C.toSimpleGraph.Adj b w := by simpa [hvi', hil] using hvw
      have hnew : (q.concat hend).IsPath := hq.concat hw hend
      have hlong := hmax _ _ _ hnew
      simp at hlong
    have hi_prev : i - 1 ≤ q.length := by omega
    have hi_next : i + 1 ≤ q.length := by omega
    have hleft : C.toSimpleGraph.Adj (q.getVert i) (q.getVert (i - 1)) := by
      have hi_eq : i - 1 + 1 = i := by omega
      rw [← hi_eq]
      exact (q.adj_getVert_succ (by omega : i - 1 < q.length)).symm
    have hright : C.toSimpleGraph.Adj (q.getVert i) (q.getVert (i + 1)) := by
      exact q.adj_getVert_succ (by omega : i < q.length)
    have hne_left : q.getVert (i - 1) ≠ w := by
      intro he
      apply hw
      rw [← he]
      exact q.getVert_mem_support _
    have hne_right : q.getVert (i + 1) ≠ w := by
      intro he
      apply hw
      rw [← he]
      exact q.getVert_mem_support _
    have hne_lr : q.getVert (i - 1) ≠ q.getVert (i + 1) := by
      intro he
      have := hq.getVert_injOn
        (show i - 1 ≤ q.length by omega) (show i + 1 ≤ q.length by omega) he
      omega
    let : Fintype (H.neighborSet (v : Sum V E)) := Fintype.ofFinite _
    have hthree : 3 ≤ @SimpleGraph.degree _ H (v : Sum V E) (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset (Sum V E) :=
        {(w : Sum V E), (q.getVert (i - 1) : Sum V E), (q.getVert (i + 1) : Sum V E)}
      have hs : s ⊆ (H.neighborFinset (v : Sum V E)) := by
        intro y hy
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using
            (C.toSimpleGraph_adj v.property w.property).mp hvw
        · have hleft' : C.toSimpleGraph.Adj v (q.getVert (i - 1)) := by
            rw [← hvi']
            exact hleft
          simpa [SimpleGraph.mem_neighborFinset] using
            (C.toSimpleGraph_adj v.property (q.getVert (i - 1)).property).mp hleft'
        · have hright' : C.toSimpleGraph.Adj v (q.getVert (i + 1)) := by
            rw [← hvi']
            exact hright
          simpa [SimpleGraph.mem_neighborFinset] using
            (C.toSimpleGraph_adj v.property (q.getVert (i + 1)).property).mp hright'
      have hc : 3 ≤ s.card := by
        have hwl : (w : Sum V E) ≠ (q.getVert (i - 1) : Sum V E) := by
          intro he
          apply hne_left
          exact Subtype.ext he.symm
        have hwr : (w : Sum V E) ≠ (q.getVert (i + 1) : Sum V E) := by
          intro he
          apply hne_right
          exact Subtype.ext he.symm
        have hlr : (q.getVert (i - 1) : Sum V E) ≠
            (q.getVert (i + 1) : Sum V E) := by
          intro he
          apply hne_lr
          exact Subtype.ext he
        simp [s, hwl, hwr, hlr]
      exact le_trans hc (Finset.card_le_card hs)
    have hdegree : @SimpleGraph.degree _ H v (Fintype.ofFinite _) ≤ 2 := by
      simpa [H] using TwoColorIncidenceDegreeAtMostTwo G phi alpha beta hproper (v : Sum V E)
    omega
  let p := q.map C.toSimpleGraph_hom
  refine ⟨C.toSimpleGraph_hom a, C.toSimpleGraph_hom b, p, ?_, ?_⟩
  · exact hq.map (by intro x y h; exact Subtype.ext h)
  · ext x
    constructor
    · intro hx
      rw [SimpleGraph.Walk.support_map] at hx
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
      exact hxy ▸ y.property
    · intro hx
      have hy : (⟨x, hx⟩ : C) ∈ q.support := hqall ⟨x, hx⟩
      change x ∈ (q.map C.toSimpleGraph_hom).support
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hy, rfl⟩

/-- Three vertices with at most one neighbor in one two-color component cannot all differ. -/
theorem TwoColorComponent.leaf_eq_or_eq {V E : Type*} [Finite V] [Finite E]
    {G : LooplessMultigraph V E} {k : ℕ} (phi : PartialEdgeColoring E k) (a b : Fin k)
    (proper : IsProperEdgeColoring G phi) (x y z : V ⊕ E)
    (leafX : ((TwoColorIncidenceGraph G phi a b).neighborSet x).Subsingleton)
    (leafY : ((TwoColorIncidenceGraph G phi a b).neighborSet y).Subsingleton)
    (leafZ : ((TwoColorIncidenceGraph G phi a b).neighborSet z).Subsingleton)
    (sameXY : TwoColorComponent G phi a b x = TwoColorComponent G phi a b y)
    (sameXZ : TwoColorComponent G phi a b x = TwoColorComponent G phi a b z) :
    x = y ∨ x = z ∨ y = z := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  by_contra different
  push Not at different
  obtain ⟨u, v, path, isPath, support⟩ := TwoColorComponentSpanningPath G phi a b proper x
  have memberX : x ∈ path.support := by
    change x ∈ {t | t ∈ path.support}
    rw [support]
    rfl
  have memberY : y ∈ path.support := by
    change y ∈ {t | t ∈ path.support}
    rw [support, sameXY]
    rfl
  have memberZ : z ∈ path.support := by
    change z ∈ {t | t ∈ path.support}
    rw [support, sameXZ]
    rfl
  have endpoint (t : V ⊕ E)
      (leaf : ((TwoColorIncidenceGraph G phi a b).neighborSet t).Subsingleton)
      (member : t ∈ path.support) : t = u ∨ t = v := by
    by_contra neither
    push Not at neither
    exact (isPath.isTrail.notMem_support_of_subsingleton_neighborSet
      neither.1 neither.2 leaf) member
  have endsX := endpoint x leafX memberX
  have endsY := endpoint y leafY memberY
  have endsZ := endpoint z leafZ memberZ
  rcases endsX with xu | xv <;> rcases endsY with yu | yv <;> rcases endsZ with zu | zv
  · exact different.1 (xu.trans yu.symm)
  · exact different.1 (xu.trans yu.symm)
  · exact different.2.1 (xu.trans zu.symm)
  · exact different.2.2 (yv.trans zv.symm)
  · exact different.2.2 (yu.trans zu.symm)
  · exact different.2.1 (xv.trans zv.symm)
  · exact different.1 (xv.trans yv.symm)
  · exact different.1 (xv.trans yv.symm)

end GoldbergSeymour

end
