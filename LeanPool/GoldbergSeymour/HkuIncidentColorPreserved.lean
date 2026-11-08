/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuMissingStoredMonotone
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Hku Incident Color Preserved

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hcomponent_179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds),
    ∀ c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc,
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        TreeExit (series.data.tree q.succ.castSucc) secondStable gamma choice.color choice.vertex
        → (
    ∀ (w : V), gamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
        (Sum.inl w) ≤ (1 : ℕ)) → (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
        (Sum.inl choice.vertex) ≤ (1 : ℕ) →
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G secondStable gamma choice.color (Sum.inl choice.vertex) → w = choice.vertex := by
  classical
  intro V E _ _ _ G k rounds e0 input series q c hc gamma secondStable secondStableProper choice
      exitWitness hdegree hvdegree w hwT hwC
  rcases exitWitness with ⟨u, path, pathData⟩
  rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
  have hne : ¬ path.Nil := by
    intro hn
    have : path.length = 0 := by simpa [SimpleGraph.Walk.nil_iff_support_eq] using hn
    omega
  have huDegree := hdegree u endOnly.1
  let H := TwoColorIncidenceGraph G secondStable gamma choice.color
  have hbound : ∀ x, @SimpleGraph.degree _ H x (Fintype.ofFinite _) ≤ 2 := by
    intro x
    exact TwoColorIncidenceDegreeAtMostTwo G secondStable gamma choice.color
      secondStableProper x
  have closed : ∀ x, x ∈ path.support → ∀ y, H.Adj x y → y ∈ path.support := by
    intro x hx y hxy
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hn0 : n = 0
    · subst n
      have hx0 : x = Sum.inl u := by simpa using hn.symm
      let : Fintype (H.neighborSet x) := Fintype.ofFinite _
      have card : Fintype.card (H.neighborSet x) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert huDegree using 1
        cases hx0
        exact congrArg (fun z => @SimpleGraph.degree _ H (Sum.inl u) z) (Subsingleton.elim _ _)
      have hy' : y ∈ H.neighborSet x := by simpa [SimpleGraph.mem_neighborSet] using hxy
      have hn' : path.getVert 1 ∈ H.neighborSet x := by
        simpa [hx0, SimpleGraph.mem_neighborSet] using path.adj_getVert_succ (show 0 <
            path.length by omega)
      have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
      have hey : y = path.getVert 1 := congrArg Subtype.val heq
      rw [hey]
      exact path.getVert_mem_support 1
    by_cases hlast : n = path.length
    · have hx1 : x = Sum.inl choice.vertex := by
        rw [← hn, pathIs.getVert_eq_end_iff hnle]
        exact hlast
      let : Fintype (H.neighborSet x) := Fintype.ofFinite _
      have card : Fintype.card (H.neighborSet x) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert hvdegree using 1
        cases hx1
        exact congrArg (fun z => @SimpleGraph.degree _ H (Sum.inl choice.vertex) z)
            (Subsingleton.elim _ _)
      have hy' : y ∈ H.neighborSet x := by simpa [SimpleGraph.mem_neighborSet] using hxy
      have hp : path.getVert (path.length - 1) ∈ H.neighborSet x := by
        have ha : H.Adj (Sum.inl choice.vertex) (path.getVert (path.length - 1)) := by
          simpa [H, show path.length - 1 + 1 = path.length by omega] using
            (path.adj_getVert_succ (show path.length - 1 < path.length by omega)).symm
        simpa [hx1, SimpleGraph.mem_neighborSet] using ha
      have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
      have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
      rw [hey]
      exact path.getVert_mem_support _
    have hl : H.Adj (path.getVert n) (path.getVert (n - 1)) := by
      rw [← show n - 1 + 1 = n by omega]
      exact (path.adj_getVert_succ (by omega)).symm
    have hr : H.Adj (path.getVert n) (path.getVert (n + 1)) := path.adj_getVert_succ (by omega)
    by_contra hyout
    have hyout' := hxy
    rw [← hn] at hyout'
    have hnl : path.getVert (n - 1) ≠ y := by
      intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
    have hnr : path.getVert (n + 1) ≠ y := by
      intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
    have hnp : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
      intro h
      have hi := pathIs.getVert_injOn (show n - 1 ≤ path.length by omega)
        (show n + 1 ≤ path.length by omega) h
      omega
    let : Fintype (H.neighborSet (path.getVert n)) := Fintype.ofFinite _
    have three : 3 ≤ H.degree (path.getVert n) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
      have hs : s ⊆ H.neighborFinset (path.getVert n) := by
        intro t ht
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hyout'
        · simpa [SimpleGraph.mem_neighborFinset] using hl
        · simpa [SimpleGraph.mem_neighborFinset] using hr
      have hc : 3 ≤ s.card := by simp [s, hnp, hnl.symm, hnr.symm]
      exact hc.trans (Finset.card_le_card hs)
    have upper : @SimpleGraph.degree _ H (path.getVert n) (Fintype.ofFinite _) ≤ 2 :=
      hbound (path.getVert n)
    exact (by omega : False).elim
  have reach : H.Reachable (Sum.inl choice.vertex) (Sum.inl w) := by
    change H.connectedComponentMk (Sum.inl w) =
      H.connectedComponentMk (Sum.inl choice.vertex) at hwC
    exact SimpleGraph.ConnectedComponent.eq.mp hwC |>.symm
  have ws : Sum.inl w ∈ path.support := by
    apply reach.mem_subgraphVerts (H := (⊤ : H.Subgraph).induce {x | x ∈ path.support})
      (fun x hx y hadj => ⟨by simpa using hx, closed x (by simpa using hx) y hadj, hadj⟩)
      (by simp)
  exact (endOnly.2 w hwT).mp ws

private theorem helper_hbase_286.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (f : E) (c : Fin k),
        TreeIncidentEdge (series.data.tree q.succ.castSucc) f → series.data.coloring q.castSucc f
        = some c → c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.succ.castSucc) ∪ TashkinovStoredColors series.data q.castSucc →
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)), StableColoring (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc)) choice.selected
        secondStable → secondStable f = series.data.coloring q.castSucc f := by
  classical
  intro V E _ _ _ G k rounds e0 input series q f c hf hfc hc secondStable choice
      secondStableRelation
  have hs : choice.selected f = series.data.coloring q.castSucc f :=
    choice.selectedStable.1 f hf ⟨c, hc, hfc⟩
  have hm : c ∈ TreeMissingColors choice.selected
      (series.data.tree q.succ.castSucc) ∪
      insert choice.color (TashkinovStoredColors series.data q.castSucc) := by
    have hc' := hc
    simp only [Finset.mem_union] at hc'
    rcases hc' with hc | hc
    · apply Finset.mem_union.mpr
      apply Or.inl
      obtain ⟨v, hv, hcv⟩ : ∃ v, v ∈ TreeSequenceVertexSet
          (series.data.tree q.succ.castSucc) ∧ c ∈ MissingColors G
          (series.data.coloring q.castSucc) v := by
        unfold TreeMissingColors at hc
        simpa only [Finset.mem_biUnion] using hc
      have hcv' : c ∈ MissingColors G choice.selected v := by
        rw [choice.selectedStable.2 v hv]
        exact hcv
      simpa only [TreeMissingColors, Finset.mem_biUnion] using ⟨v, hv, hcv'⟩
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_insert_of_mem hc)
  exact (secondStableRelation.1 f hf ⟨c, hm, hs.trans hfc⟩).trans hs

private theorem helper_hincident_309.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (gamma : Fin k) (secondStable :
        PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        StableColoring (series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data q.castSucc)) choice.selected secondStable → gamma ∈
        MissingColors G secondStable choice.vertex → (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G secondStable gamma choice.color (Sum.inl choice.vertex) → w = choice.vertex) →
    ∀ (g : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) g → Sum.inr g ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → g =
        choice.edge := by
  classical
  intro V E _ _ _ G k rounds e0 input series q gamma secondStable secondStableProper choice
      secondStableRelation hmissing hcomponent g hgi hg
  rcases hgi with ⟨w, hw, hwg⟩
  have hsupport : Sum.inr g ∈
      (TwoColorIncidenceGraph G secondStable gamma choice.color).support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := TwoColorIncidenceGraph G secondStable gamma choice.color)
      (u := Sum.inr g) (v := Sum.inl choice.vertex) (by simp)
    exact SimpleGraph.ConnectedComponent.eq.mp hg
  obtain ⟨r, hr⟩ :=
    (TwoColorIncidenceGraph G secondStable gamma choice.color).mem_support.mp hsupport
  have hcol : secondStable g = some gamma ∨ secondStable g = some choice.color := by
    cases r with
    | inl x => exact hr.2
    | inr x => simp [TwoColorIncidenceGraph] at hr
  have hvertex : Sum.inl w ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
        (Sum.inl w) = _
    have hadj : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
        (Sum.inl w) (Sum.inr g) := by
      simp [TwoColorIncidenceGraph, hwg, hcol]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hg
  have hw_eq : w = choice.vertex := hcomponent w hw hvertex
  subst w
  have hne : secondStable g = some gamma → False := by
    intro hh
    have hn : gamma ∉ PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hmissing
    apply hn
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hwg, hh⟩
  have hgcol : secondStable g = some choice.color := hcol.resolve_left hne
  have hecol : secondStable choice.edge = some choice.color := by
    exact (secondStableRelation.1 choice.edge
      ⟨choice.vertex, hw, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
        choice.edgeColor⟩).trans choice.edgeColor
  by_contra hneedge
  exact (secondStableProper hneedge ⟨choice.vertex, hwg, choice.edgeIncident⟩ hgcol hecol).elim

private theorem helper_branch_364.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (f : E) (c : Fin k),
        series.data.coloring q.castSucc f = some c → c ∈ TreeMissingColors (series.data.coloring
        q.castSucc) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data
        q.castSucc →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)), StableColoring (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc)) choice.selected
        secondStable → series.data.coloring q.succ = TwoColorComponentSwap G secondStable gamma
        choice.color (Sum.inl choice.vertex) → series.data.stored q.succ = { choice.color, gamma }
        → series.data.connectingEdges q.succ = { choice.edge } → series.data.kind q.succ = some
        TashkinovExtensionKind.PE → series.data.delta q.succ = some choice.color →
        series.data.gamma q.succ = some gamma → gamma ∈ MissingColors G secondStable choice.vertex
        → secondStable f = series.data.coloring q.castSucc f → (
    ∀ (g : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) g → Sum.inr g ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → g =
        choice.edge) →
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), Incident G v f → (Sum.inl v ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → v =
        choice.vertex) → Sum.inr f ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → (series.data.coloring q.succ f = series.data.coloring q.castSucc f ∨
        series.data.kind q.succ = some TashkinovExtensionKind.PE ∧ series.data.connectingEdges
        q.succ = { f } ∧ series.data.delta q.succ = some c ∧
    ∃ (gamma : Fin k), series.data.gamma q.succ = some gamma ∧ series.data.coloring q.succ f =
        some gamma) ∧
    ∃ (d : Fin k), series.data.coloring q.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series q f c hfc hc gamma secondStable choice
      secondStableRelation currentColoring currentStored currentEdges currentKind currentDelta
      currentGamma hmissing hbase hincident v hv hvf hvertexComp hcomp
  have hfcol : secondStable f = some gamma ∨
      secondStable f = some choice.color := by
    have hfsupport : Sum.inr f ∈
        (TwoColorIncidenceGraph G secondStable gamma choice.color).support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := TwoColorIncidenceGraph G secondStable gamma choice.color)
        (u := Sum.inr f) (v := Sum.inl choice.vertex) (by simp)
      exact SimpleGraph.ConnectedComponent.eq.mp hcomp
    obtain ⟨r, hr⟩ :=
      (TwoColorIncidenceGraph G secondStable gamma choice.color).mem_support.mp hfsupport
    cases r with
    | inl x => exact hr.2
    | inr x => simp [TwoColorIncidenceGraph] at hr
  have hvcomp : Sum.inl v ∈ TwoColorComponent G secondStable gamma
      choice.color (Sum.inl choice.vertex) := by
    change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
      (Sum.inl v) = _
    have hadj : (TwoColorIncidenceGraph G secondStable gamma choice.color).Adj
        (Sum.inl v) (Sum.inr f) := by
      simp [TwoColorIncidenceGraph, hvf, hfcol]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hcomp
  have hv_eq : v = choice.vertex := hvertexComp hvcomp
  have hfedge : f = choice.edge := hincident f ⟨v, hv, hvf⟩ hcomp
  subst f
  have hecol : secondStable choice.edge = some choice.color := by
    exact (secondStableRelation.1 choice.edge
      ⟨choice.vertex, by rw [← hv_eq]; exact hv, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
        choice.edgeColor⟩).trans choice.edgeColor
  have hce : c = choice.color := by
    apply Option.some.inj
    exact hfc.symm.trans (hbase.symm.trans hecol)
  subst c
  have hneq : choice.color ≠ gamma := by
    intro heq
    have hn : gamma ∉ PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hmissing
    apply hn
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨choice.edge, choice.edgeIncident,
      heq ▸ hecol⟩
  refine ⟨Or.inr ⟨currentKind, ?_, currentDelta, ?_⟩, ?_⟩
  · simp [currentEdges]
  · refine ⟨gamma, currentGamma, ?_⟩
    rw [congrFun currentColoring choice.edge]
    simp [TwoColorComponentSwap, hcomp, hecol, hneq]
  · refine ⟨gamma, ?_, ?_⟩
    · rw [congrFun currentColoring choice.edge]
      simp [TwoColorComponentSwap, hcomp, hecol, hneq]
    · by_cases hm : gamma ∈ TreeMissingColors
          (series.data.coloring q.succ)
          (series.data.tree q.succ.castSucc)
      · apply Finset.mem_union.mpr
        exact Or.inl hm
      · apply Finset.mem_union.mpr
        apply Or.inr
        simp only [TashkinovStoredColors]
        have qnz : q.succ.val ≠ 0 := by
          intro hz
          apply Fin.succ_ne_zero q
          apply Fin.ext
          exact hz
        rw [ite_eq_right qnz]
        simp only [Finset.mem_sdiff, Finset.mem_biUnion]
        constructor
        · refine ⟨q.succ, ?_⟩
          simp [currentStored]
        · simpa using hm

private theorem helper_branch_101.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (f : E) (c : Fin k),
        TreeIncidentEdge (series.data.tree q.succ.castSucc) f → series.data.coloring q.castSucc f
        = some c → c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.succ.castSucc) ∪ TashkinovStoredColors series.data q.castSucc → TreeMissingColors
        (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc ⊆ TreeMissingColors (series.data.coloring
        q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.succ ∧
        TreeMissingColors (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ ⊆ TreeMissingColors (series.data.coloring q.succ)
        (series.data.tree q.succ.succ) ∪ TashkinovStoredColors series.data q.succ →
    ∀ (i : Fin rounds), IsProperEdgeColoring G (series.data.coloring i.castSucc) →
        IsOneEdgeUncolored (series.data.coloring i.castSucc) e0 → ColoredVertexSetClosed G
        (series.data.coloring i.castSucc) (TreeSequenceVertexSet (series.data.tree
        i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (series.data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate series.data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree i.succ.castSucc)
        (TashkinovStoredColors series.data i.castSucc) (series.data.coloring i.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data i.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (series.data.tree
        i.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor series.data i.castSucc choice.selected choice.vertex
        gamma →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        StableColoring (series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data i.castSucc)) choice.selected secondStable → TreeExit
        (series.data.tree i.succ.castSucc) secondStable gamma choice.color choice.vertex →
        series.data.coloring i.succ = TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) → IsProperEdgeColoring G (series.data.coloring i.succ) →
        IsOneEdgeUncolored (series.data.coloring i.succ) e0 → series.data.stored i.succ =
        { choice.color, gamma } → series.data.connectingEdges i.succ = { choice.edge } →
        series.data.kind i.succ = some TashkinovExtensionKind.PE → series.data.chosenVertex i.succ
        = some choice.vertex → series.data.outsideVertex i.succ = some choice.otherEndpoint →
        series.data.delta i.succ = some choice.color → series.data.gamma i.succ = some gamma →
        TashkinovClosure (series.data.coloring i.succ) (series.data.tree i.succ.castSucc)
        (series.data.tree i.succ.succ) → TreeSequenceInitialSegment (series.data.tree
        i.succ.castSucc) (series.data.tree i.succ.succ) → (series.data.tree
        i.succ.castSucc).length < (series.data.tree i.succ.succ).length → i.succ ≠ (0 : Fin
        (rounds + (1 : ℕ))) → i.succ = q.succ → (series.data.coloring q.succ f =
        series.data.coloring q.castSucc f ∨ series.data.kind q.succ = some
        TashkinovExtensionKind.PE ∧ series.data.connectingEdges q.succ = { f } ∧ series.data.delta
        q.succ = some c ∧
    ∃ (gamma : Fin k), series.data.gamma q.succ = some gamma ∧ series.data.coloring q.succ f =
        some gamma) ∧
    ∃ (d : Fin k), series.data.coloring q.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series q f c hf hfc hc monotone i previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternativeFails gamma gammaRule secondStable secondStableProper secondStableRelation
      exitWitness currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension hj hjeq
  have hvals := congrArg Fin.val hjeq
  simp at hvals
  have hi : i = q := by apply Fin.ext; omega
  subst i
  have hmissing : gamma ∈ MissingColors G secondStable choice.vertex := by
    exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
  have hdegree := fun w hw ↦ TwoColorMissingVertexDegreeAtMostOne G secondStable
    secondStableProper gamma choice.color w hw
  have hvdegree := hdegree choice.vertex (Or.inl hmissing)
  have hcomponent := @helper_hcomponent_179 V E inferInstance inferInstance inferInstance G k rounds
      e0 input series q c hc gamma secondStable secondStableProper choice exitWitness hdegree
      hvdegree
  have hbase := @helper_hbase_286 V E inferInstance inferInstance inferInstance G k rounds e0 input
      series q f c hf hfc hc secondStable choice secondStableRelation
  have hincident := @helper_hincident_309 V E inferInstance inferInstance inferInstance G k rounds
      e0 input series q gamma secondStable secondStableProper choice secondStableRelation hmissing
      hcomponent
  have hswap : ∀ g, ¬ Sum.inr g ∈ TwoColorComponent G secondStable gamma
      choice.color (Sum.inl choice.vertex) →
      TwoColorComponentSwap G secondStable gamma choice.color
        (Sum.inl choice.vertex) g = secondStable g := by
    intro g hg
    simp [TwoColorComponentSwap, hg]
  rcases hf with ⟨v, hv, hvf⟩
  have hvertexComp : Sum.inl v ∈ TwoColorComponent G secondStable gamma
      choice.color (Sum.inl choice.vertex) → v = choice.vertex :=
    fun h => hcomponent v hv h
  by_cases hcomp : Sum.inr f ∈ TwoColorComponent G secondStable gamma
      choice.color (Sum.inl choice.vertex)
  · exact @helper_branch_364 V E inferInstance inferInstance inferInstance G k rounds e0 input
      series q f c hfc hc gamma secondStable choice secondStableRelation currentColoring
      currentStored currentEdges currentKind currentDelta currentGamma hmissing hbase hincident v
      hv hvf hvertexComp hcomp
  · have hnew := hswap f hcomp
    have hcur : series.data.coloring q.succ f =
        TwoColorComponentSwap G secondStable gamma choice.color
          (Sum.inl choice.vertex) f := congrFun currentColoring f
    refine ⟨Or.inl (hcur.trans (hnew.trans hbase)), ?_⟩
    exact ⟨c, (hcur.trans (hnew.trans hbase)).trans hfc, monotone.1 hc⟩

theorem HkuIncidentColorPreserved {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (f : E) (c : Fin k)
    (hf : TreeIncidentEdge (series.data.tree q.succ.castSucc) f)
    (hfc : series.data.coloring q.castSucc f = some c)
    (hc : c ∈ TreeMissingColors (series.data.coloring q.castSucc)
          (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc) :
    (series.data.coloring q.succ f = series.data.coloring q.castSucc f ∨
        (series.data.kind q.succ = some TashkinovExtensionKind.PE ∧
          series.data.connectingEdges q.succ = { f } ∧
            series.data.delta q.succ = some c ∧
              ∃ gamma : Fin k,
                series.data.gamma q.succ = some gamma ∧
                  series.data.coloring q.succ f = some gamma)) ∧
      ∃ d : Fin k,
        series.data.coloring q.succ f = some d ∧
          d ∈
            TreeMissingColors (series.data.coloring q.succ)
                (series.data.tree q.succ.castSucc) ∪
              TashkinovStoredColors series.data q.succ := by
  classical
  have monotone := (HkuMissingStoredMonotone G k rounds e0 input series q)
  have process :
    ∀ j : Fin (rounds + 1), j ≠ 0 → j = q.succ → (series.data.coloring q.succ f =
        series.data.coloring q.castSucc f ∨ (series.data.kind q.succ = some
        TashkinovExtensionKind.PE ∧ series.data.connectingEdges q.succ = {f} ∧ series.data.delta
        q.succ = some c ∧
    ∃ gamma : Fin k, series.data.gamma q.succ = some gamma ∧ series.data.coloring q.succ f = some
        gamma)) ∧
    ∃ d : Fin k, series.data.coloring q.succ f = some d ∧ d ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ := by
    intro j hj hjeq
    cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (hj (by omega)).elim
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hjeq
    simp at hvals
    have hi : i = q := by apply Fin.ext; omega
    subst i
    have hcolor : series.data.coloring q.succ =
        series.data.coloring q.castSucc := by
      rw [← hjeq, currentColoring]
    refine ⟨Or.inl (congrFun hcolor f), ?_⟩
    exact ⟨c, hcolor ▸ hfc, monotone.1 hc⟩
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hjeq
    simp at hvals
    have hi : i = q := by apply Fin.ext; omega
    subst i
    have hf' := choice.selectedStable.1 f hf ⟨c, hc, hfc⟩
    have hcolor : series.data.coloring q.succ f = choice.selected f :=
      congrFun currentColoring f
    refine ⟨Or.inl (hcolor.trans hf'), ?_⟩
    refine ⟨c, (hcolor.trans hf').trans hfc, monotone.1 hc⟩
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_101 V E inferInstance inferInstance inferInstance G k rounds e0
              input series q f c hf hfc hc monotone i previousProper previousOneUncolored
              previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
              gamma gammaRule secondStable secondStableProper secondStableRelation exitWitness
              currentColoring currentProper currentOneUncolored currentStored currentEdges
              currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension hj hjeq
  exact process q.succ (Fin.succ_ne_zero q) rfl

end GoldbergSeymour

end
