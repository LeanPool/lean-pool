/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HkuMissingStoredMonotone
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.StableColoringIncidentEdgeCriterion
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Parallel Extension Undo Stable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hclosed_201.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)), chosenGamma ∈ MissingColors G secondStable
        choice.vertex → (
    ∀ (w : V), chosenGamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) (@Sum.inl V E w)
        (@Subtype.fintype (Sum V E) (@Membership.mem (Sum V E) (Set (Sum V E))
        (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E w))) (fun (a : Sum V E) ↦ @SimpleGraph.neighborSet.memDecidable (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E w) (fun (a b : Sum V E) ↦ Classical.propDecidable (@SimpleGraph.Adj (Sum V
        E) (@TwoColorIncidenceGraph V E G k secondStable chosenGamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series)
        (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat
        (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V
        E inst_1 G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input
        series) (@Fin.castSucc rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) choice)) a b)) a) (@instFintypeSum V E inst inst_1)) ≤ (1 : ℕ)) →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Walk
        (Sum.inl u) (Sum.inl choice.vertex)), path.IsPath → (2 : ℕ) ≤ path.length → (
    ∀ (x : V ⊕ E), @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x (@Fintype.ofFinite
        (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x)) (@Subtype.finite
        (Sum V E) (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x)))) ≤ (2 : ℕ)) →
        @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable chosenGamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series)
        (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat
        (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V
        E inst_1 G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input
        series) (@Fin.castSucc rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) choice)) (@Sum.inl V E u) (@Subtype.fintype (Sum V E) (@Membership.mem (Sum V
        E) (Set (Sum V E)) (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E u))) (fun (a : Sum V E) ↦ @SimpleGraph.neighborSet.memDecidable (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E u) (fun (a b : Sum V E) ↦ Classical.propDecidable (@SimpleGraph.Adj (Sum V
        E) (@TwoColorIncidenceGraph V E G k secondStable chosenGamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series)
        (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat
        (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V
        E inst_1 G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input
        series) (@Fin.castSucc rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) choice)) a b)) a) (@instFintypeSum V E inst inst_1)) ≤ (1 : ℕ) →
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj x y → y ∈
        path.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable choice hmissing hdegree u
      path pathIs pathLen hdegreeBound huDegree x hx y hxy
  obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hn0 : n = 0
  · subst n
    have hx0 : x = Sum.inl u := by simpa using hn.symm
    let graph := TwoColorIncidenceGraph G secondStable chosenGamma choice.color
    let : Fintype (graph.neighborSet x) := Fintype.ofFinite _
    have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      convert huDegree using 1
      cases hx0
      exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl u) z)
        (Subsingleton.elim _ _)
    have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using
        hxy
    have hn' : path.getVert 1 ∈ graph.neighborSet x := by
      simpa [graph, hx0, SimpleGraph.mem_neighborSet] using
        path.adj_getVert_succ (show 0 < path.length by omega)
    have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
    have hey : y = path.getVert 1 := congrArg Subtype.val heq
    rw [hey]
    exact path.getVert_mem_support 1
  by_cases hlast : n = path.length
  · have hx1 : x = Sum.inl choice.vertex := by
      rw [← hn, pathIs.getVert_eq_end_iff hnle]
      exact hlast
    let graph := TwoColorIncidenceGraph G secondStable chosenGamma choice.color
    let : Fintype (graph.neighborSet x) := Fintype.ofFinite _
    have card : Fintype.card (graph.neighborSet x) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      convert hdegree choice.vertex (Or.inl hmissing) using 1
      cases hx1
      exact congrArg (fun z => @SimpleGraph.degree _ graph (Sum.inl choice.vertex) z)
        (Subsingleton.elim _ _)
    have hy' : y ∈ graph.neighborSet x := by simpa [graph, SimpleGraph.mem_neighborSet] using
        hxy
    have hp : path.getVert (path.length - 1) ∈ graph.neighborSet x := by
      have ha : graph.Adj (Sum.inl choice.vertex) (path.getVert (path.length - 1)) := by
        simpa [graph, show path.length - 1 + 1 = path.length by omega] using
          (path.adj_getVert_succ (show path.length - 1 < path.length by omega)).symm
      simpa [hx1, SimpleGraph.mem_neighborSet] using ha
    have heq := Fintype.card_le_one_iff.mp card ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
    have hey : y = path.getVert (path.length - 1) := congrArg Subtype.val heq
    rw [hey]
    exact path.getVert_mem_support _
  have hl : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj
      (path.getVert n) (path.getVert (n - 1)) := by
    rw [← show n - 1 + 1 = n by omega]
    exact (path.adj_getVert_succ (by omega)).symm
  have hnlt : n < path.length := lt_of_le_of_ne hnle hlast
  have hr := path.adj_getVert_succ hnlt
  by_contra hyout
  rw [← hn] at hxy
  have hnl : path.getVert (n - 1) ≠ y := by
    intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
  have hnr : path.getVert (n + 1) ≠ y := by
    intro h; apply hyout; rw [← h]; exact path.getVert_mem_support _
  have hnp : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
    intro h
    have hi := pathIs.getVert_injOn (show n - 1 ≤ path.length by omega)
      (show n + 1 ≤ path.length by omega) h
    omega
  let graph := TwoColorIncidenceGraph G secondStable chosenGamma choice.color
  let : Fintype (graph.neighborSet (path.getVert n)) := Fintype.ofFinite _
  have three : 3 ≤ graph.degree (path.getVert n) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let s : Finset _ := {y, path.getVert (n - 1), path.getVert (n + 1)}
    have hs : s ⊆ graph.neighborFinset (path.getVert n) := by
      intro t ht
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hxy
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hl
      · simpa [graph, SimpleGraph.mem_neighborFinset] using hr
    have hc : 3 ≤ s.card := by simp [s, hnp, hnl.symm, hnr.symm]
    exact hc.trans (Finset.card_le_card hs)
  have upper : graph.degree (path.getVert n) ≤ 2 := hdegreeBound (path.getVert n)
  omega

private theorem helper_hsigmaEdge_358.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma : PartialEdgeColoring E k),
        IsProperEdgeColoring G sigma → StableColoring (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.succ) (series.data.coloring q.succ) sigma →
    ∀ (chosenGamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        series.data.coloring q.succ = TwoColorComponentSwap G secondStable chosenGamma
        choice.color (Sum.inl choice.vertex) → series.data.stored q.succ = (insert choice.color
        ({ chosenGamma } : Finset (Fin k)) : Finset (Fin k)) → series.data.gamma q.succ = some
        chosenGamma → choice.vertex ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) → (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G sigma chosenGamma choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex) →
        chosenGamma ∈ MissingColors G secondStable choice.vertex →
    ∀ (_ : V), (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some chosenGamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → chosenGamma ≠ choice.color → Sum.inr
        choice.edge ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) →
    ∀ (e : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma hsigmaProper hsigmaStable chosenGamma
      secondStable secondStableProper choice currentColoring currentStored hgamma hv hcomponent
      hmissing u hcompEdge hchoiceSecond hneq hfcomponent e heT heC
  rcases heT with ⟨w, hw, hwe⟩
  have hgamma : sigma choice.edge = some chosenGamma := by
    have hsc := hsigmaStable.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    have hctrl : ∃ c ∈ TreeMissingColors (series.data.coloring q.succ)
        (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.succ,
        series.data.coloring q.succ choice.edge = some c := by
      refine ⟨chosenGamma, ?_, ?_⟩
      · by_cases hm : chosenGamma ∈ TreeMissingColors (series.data.coloring q.succ)
            (series.data.tree q.succ.castSucc)
        · exact Finset.mem_union.mpr (Or.inl hm)
        · apply Finset.mem_union.mpr
          right
          unfold TashkinovStoredColors
          split
          · simp_all
          simp only [Finset.mem_sdiff, Finset.mem_biUnion]
          constructor
          · refine ⟨q.succ, ?_, ?_⟩
            · simp
            · simp [currentStored]
          · simpa using hm
      · rw [currentColoring]
        simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond]
    exact (hsc hctrl).trans (by
      rw [currentColoring]
      simp [TwoColorComponentSwap, hfcomponent, hchoiceSecond])
  have hecol : sigma e = some chosenGamma ∨ sigma e = some choice.color := by
    have hs : Sum.inr e ∈
        (TwoColorIncidenceGraph G sigma chosenGamma choice.color).support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := TwoColorIncidenceGraph G sigma chosenGamma choice.color)
        (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
      exact SimpleGraph.ConnectedComponent.eq.mp heC
    obtain ⟨r, hr⟩ :=
      (TwoColorIncidenceGraph G sigma chosenGamma choice.color).mem_support.mp hs
    cases r with
    | inl x => exact hr.2
    | inr x => simp [TwoColorIncidenceGraph] at hr
  have hwC : Sum.inl w ∈ TwoColorComponent G sigma chosenGamma choice.color
      (Sum.inl choice.vertex) := by
    have hadj : (TwoColorIncidenceGraph G sigma chosenGamma choice.color).Adj
        (Sum.inl w) (Sum.inr e) := by
      simp [TwoColorIncidenceGraph, hwe, hecol]
    change (TwoColorIncidenceGraph G sigma chosenGamma choice.color).connectedComponentMk
        (Sum.inl w) = _
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
  have hwv := (hcomponent w hw).mp hwC
  subst w
  rcases hecol with hec | hec
  · have hp : chosenGamma ∈ PresentColors G sigma choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hwe, hec⟩
    by_contra hne
    exact (hsigmaProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec hgamma).elim
  · by_contra hne
    have hcolor : sigma e = some choice.color := hec
    have hmissColor : choice.color ∈ MissingColors G sigma choice.vertex := by
      rw [hsigmaStable.2 choice.vertex hv]
      rw [MissingColors]
      simp only [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_univ _
      · intro hp
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rcases hp with ⟨a, hae, hac⟩
        by_cases ha : Sum.inr a ∈
            TwoColorComponent G secondStable chosenGamma choice.color
              (Sum.inl choice.vertex)
        · rcases hcompEdge a ha with hag | hacs
          · have hn : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
              simpa [MissingColors] using hmissing
            exact hn (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨a, hae, hag⟩)
          · rw [currentColoring] at hac
            simp [TwoColorComponentSwap, ha, hacs, hneq, hneq.symm] at hac
        · rw [currentColoring] at hac
          have hac' : secondStable a = some choice.color := by
            simpa [TwoColorComponentSwap, ha] using hac
          have hne : a ≠ choice.edge := by
            intro heq
            apply ha
            exact heq ▸ hfcomponent
          exact (secondStableProper hne ⟨choice.vertex, hae, choice.edgeIncident⟩
            hac' hchoiceSecond).elim
    have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
      change choice.color ∈ Finset.univ \ PresentColors G sigma choice.vertex at hmissColor
      exact (Finset.mem_sdiff.mp hmissColor).2
    exact (hnot (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hwe, hcolor⟩)).elim

private theorem helper_stableSecond_588.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma :
        PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma e0 →
        StableColoring (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data
        q.succ) (series.data.coloring q.succ) sigma →
    ∀ (chosenGamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        StableColoring (series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable → series.data.coloring q.succ = TwoColorComponentSwap G secondStable
        chosenGamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
        (series.data.coloring q.succ) → IsOneEdgeUncolored (series.data.coloring q.succ) e0 → (
    ∀ (w : V), chosenGamma ∈ MissingColors G secondStable w ∨ choice.color ∈ MissingColors G
        secondStable w → @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) (@Sum.inl V E w)
        (@Subtype.fintype (Sum V E) (@Membership.mem (Sum V E) (Set (Sum V E))
        (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E w))) (fun (a : Sum V E) ↦ @SimpleGraph.neighborSet.memDecidable (Sum V E)
        (@TwoColorIncidenceGraph V E G k secondStable chosenGamma (@MaximumDefectiveChoice.color V
        E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V
        E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat
        (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit
        1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice))
        (@Sum.inl V E w) (fun (a b : Sum V E) ↦ Classical.propDecidable (@SimpleGraph.Adj (Sum V
        E) (@TwoColorIncidenceGraph V E G k secondStable chosenGamma
        (@MaximumDefectiveChoice.color V E inst inst_1 G k e0 (@TashkinovSeriesData.tree V E G k
        rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series)
        (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) rounds (@OfNat.ofNat Nat
        (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ rounds q))) (@TashkinovStoredColors V
        E inst_1 G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input
        series) (@Fin.castSucc rounds q)) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds q)) choice)) a b)) a) (@instFintypeSum V E inst inst_1)) ≤ (1 : ℕ)) →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Walk
        (Sum.inl u) (Sum.inl choice.vertex)), (
    ∀ (x : V ⊕ E), @SimpleGraph.degree (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x (@Fintype.ofFinite
        (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k
        secondStable chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x)) (@Subtype.finite
        (Sum V E) (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) (@TwoColorIncidenceGraph V E G k secondStable
        chosenGamma (@MaximumDefectiveChoice.color V E inst inst_1 G k e0
        (@TashkinovSeriesData.tree V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1 inst_2
        G k rounds e0 input series) (@Fin.castSucc (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat
        instAddNat) rounds (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@Fin.succ
        rounds q))) (@TashkinovStoredColors V E inst_1 G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q))
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.castSucc rounds q)) choice)) x)))) ≤ (2 : ℕ)) → (
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj x y → y ∈
        path.support) → (
    ∀ y ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex), y ∈
        path.support) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some chosenGamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → (
    ∀ (e : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge) → (
    ∀ (e : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge) →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex); IsProperEdgeColoring G undone → IsOneEdgeUncolored undone e0 →
        TreeMissingColors secondStable (series.data.tree q.succ.castSucc) = TreeMissingColors
        choice.selected (series.data.tree q.succ.castSucc) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G sigma chosenGamma choice.color (Sum.inl
        choice.vertex) → sigma e = some chosenGamma ∨ sigma e = some choice.color) → choice.color
        ∈ MissingColors G sigma choice.vertex → (
    ∀ c ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)), c ∈
        TreeMissingColors (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ) → chosenGamma ∈ TreeMissingColors
        choice.selected (series.data.tree q.succ.castSucc) ∪ (insert choice.color
        (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) → StableColoring
        (series.data.tree q.succ.castSucc) (insert choice.color (TashkinovStoredColors series.data
        q.castSucc) : Finset (Fin k)) secondStable undone := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma hsigmaProper hsigmaOneUncolored hsigmaStable
      chosenGamma secondStable secondStableProper secondStableOneUncolored choice
      secondStableRelation currentColoring currentProper currentOneUncolored hdegree u path
      hdegreeBound hclosed hpathComponent hcompEdge hchoiceSecond htreeEdge hsigmaEdge undone
      undoneProper undoneOne treeSecondSelected sigmaComponentColor sigmaColorMissing
      currentControl gammaControl
  apply (sc1 G e0 (series.data.tree q.succ.castSucc)
    (insert choice.color (TashkinovStoredColors series.data q.castSucc))
    secondStable undone secondStableProper secondStableOneUncolored
    undoneProper undoneOne).2
  intro f hf h
  rcases h with h | h
  · rcases h with ⟨c, hc, hcf⟩
    rw [treeSecondSelected] at hc
    have h' := ((sc1 G e0 (series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors series.data q.castSucc))
      choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
      secondStableProper secondStableOneUncolored).mp secondStableRelation) f hf
      (Or.inr ⟨c, hc, hcf⟩)
    have hs := hsigmaStable.1 f hf
    by_cases hsf : Sum.inr f ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex)
    · have ef := hsigmaEdge f hf hsf
      subst f
      rcases sigmaComponentColor choice.edge hsf with hec | hec
      · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
      · exfalso
        have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
          simpa [MissingColors] using sigmaColorMissing
        apply hnot
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨choice.edge, choice.edgeIncident, hec⟩
    · have hu : undone f = sigma f := by
        change (if Sum.inr f ∈
          TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) then
            (if sigma f = some chosenGamma then some choice.color
            else if sigma f = some choice.color then some chosenGamma else sigma f)
          else sigma f) = sigma f
        exact ite_eq_right hsf
      rw [hu]
      clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
        hsigmaEdge sigmaComponentColor
      by_cases ha : Sum.inr f ∈
          TwoColorComponent G secondStable chosenGamma choice.color
            (Sum.inl choice.vertex)
      · have he := htreeEdge f hf ha
        subst f
        have hcGamma := currentControl chosenGamma gammaControl
        have hsGamma := hsigmaStable.1 choice.edge
          ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
          ⟨chosenGamma, hcGamma, by
            rw [currentColoring]
            simp [TwoColorComponentSwap, ha, hchoiceSecond]⟩
        have hcurGamma : series.data.coloring q.succ choice.edge =
            some chosenGamma := by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha, hchoiceSecond]
        have hsigGamma : sigma choice.edge = some chosenGamma :=
          hsGamma.trans hcurGamma
        have hmem : Sum.inr choice.edge ∈
            TwoColorComponent G sigma chosenGamma choice.color
              (Sum.inl choice.vertex) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
        exact (hsf hmem).elim
      · have hcur : series.data.coloring q.succ f = some c := by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha, hcf]
        have hsig := hsigmaStable.1 f hf
          ⟨c, currentControl c hc, hcur⟩
        exact hsig.trans (hcur.trans hcf.symm)
  · rcases h with ⟨c, hc, hcf⟩
    by_cases hsf : Sum.inr f ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex)
    · have ef := hsigmaEdge f hf hsf
      subst f
      rcases sigmaComponentColor choice.edge hsf with hec | hec
      · simp [undone, TwoColorComponentSwap, hsf, hec, hchoiceSecond]
      · exfalso
        have hnot : choice.color ∉ PresentColors G sigma choice.vertex := by
          simpa [MissingColors] using sigmaColorMissing
        apply hnot
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨choice.edge, choice.edgeIncident, hec⟩
    · have hu : undone f = sigma f := by
        change (if Sum.inr f ∈
          TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) then
            (if sigma f = some chosenGamma then some choice.color
            else if sigma f = some choice.color then some chosenGamma else sigma f)
          else sigma f) = sigma f
        exact ite_eq_right hsf
      rw [hu]
      clear hdegree hdegreeBound hclosed hpathComponent hcompEdge
        hsigmaEdge sigmaComponentColor
      rw [treeSecondSelected] at hc
      by_cases ha : Sum.inr f ∈
          TwoColorComponent G secondStable chosenGamma choice.color
            (Sum.inl choice.vertex)
      · have he := htreeEdge f hf ha
        subst f
        have hcGamma := currentControl chosenGamma gammaControl
        have hsGamma := hsigmaStable.1 choice.edge
          ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
          ⟨chosenGamma, hcGamma, by
            rw [currentColoring]
            simp [TwoColorComponentSwap, ha, hchoiceSecond]⟩
        have hcurGamma : series.data.coloring q.succ choice.edge =
            some chosenGamma := by
          rw [currentColoring]
          simp [TwoColorComponentSwap, ha, hchoiceSecond]
        have hsigGamma : sigma choice.edge = some chosenGamma :=
          hsGamma.trans hcurGamma
        have hmem : Sum.inr choice.edge ∈
            TwoColorComponent G sigma chosenGamma choice.color
              (Sum.inl choice.vertex) := by
          apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          simp [TwoColorIncidenceGraph, choice.edgeIncident, hsigGamma]
        exact (hsf hmem).elim
      · have hsigmaValue : sigma f = some c := hu.symm.trans hcf
        have hsig := ((sc1 G e0 (series.data.tree q.succ.castSucc)
          (TashkinovStoredColors series.data q.succ)
          (series.data.coloring q.succ) sigma currentProper currentOneUncolored
          hsigmaProper hsigmaOneUncolored).mp hsigmaStable) f hf
          (Or.inr ⟨c, currentControl c hc, hsigmaValue⟩)
        have hcur : series.data.coloring q.succ f = some c :=
          (Eq.symm hsig).trans hsigmaValue
        have hsecond : secondStable f = some c := by
          have hcs : series.data.coloring q.succ f = secondStable f := by
            rw [currentColoring]
            simp [TwoColorComponentSwap, ha]
          exact hcs.symm.trans hcur
        exact hsig.trans (hcur.trans hsecond.symm)

private theorem helper_stableSelected_718.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma : PartialEdgeColoring E k)
        (chosenGamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable → IsOneEdgeUncolored secondStable e0 →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        StableColoring (series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex); IsProperEdgeColoring G undone → IsOneEdgeUncolored undone e0 →
        TreeMissingColors secondStable (series.data.tree q.succ.castSucc) = TreeMissingColors
        choice.selected (series.data.tree q.succ.castSucc) → StableColoring (series.data.tree
        q.succ.castSucc) (insert choice.color (TashkinovStoredColors series.data q.castSucc) :
        Finset (Fin k)) secondStable undone → StableColoring (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k))
        choice.selected undone := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma chosenGamma secondStable secondStableProper
      secondStableOneUncolored choice secondStableRelation undone undoneProper undoneOne
      treeSecondSelected stableSecond
  apply (sc1 G e0 (series.data.tree q.succ.castSucc)
    (insert choice.color (TashkinovStoredColors series.data q.castSucc))
    choice.selected undone choice.selectedProper choice.selectedOneUncolored
    undoneProper undoneOne).2
  have stableSecondCriterion :=
    ((sc1 G e0 (series.data.tree q.succ.castSucc)
      (insert choice.color (TashkinovStoredColors series.data q.castSucc))
      secondStable undone secondStableProper secondStableOneUncolored
      undoneProper undoneOne).mp stableSecond)
  intro f hf h
  rcases h with h | h
  · rcases h with ⟨c, hc, hcf⟩
    have hrel := secondStableRelation.1 f hf
      ⟨c, hc, hcf⟩
    have hc2 := hc
    rw [← treeSecondSelected] at hc2
    have hstable := stableSecondCriterion f hf
      (Or.inl ⟨c, hc2, hrel.trans hcf⟩)
    exact hstable.trans hrel
  · rcases h with ⟨c, hc, hcf⟩
    have hc2 := hc
    rw [← treeSecondSelected] at hc2
    have hstable := stableSecondCriterion f hf
      (Or.inr ⟨c, hc2, hcf⟩)
    have hsecond : secondStable f = some c := hstable.symm.trans hcf
    have relationCriterion :=
      ((sc1 G e0 (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc))
        choice.selected secondStable choice.selectedProper choice.selectedOneUncolored
        secondStableProper secondStableOneUncolored).mp secondStableRelation)
    have hrel := relationCriterion f hf (Or.inr ⟨c, hc, hsecond⟩)
    exact hstable.trans hrel

private theorem helper_branch_1099.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (v : V) (gamma delta : Fin k),
        series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k) (ci : Fin rounds), IsProperEdgeColoring G
        (series.data.coloring ci.castSucc) → IsOneEdgeUncolored (series.data.coloring ci.castSucc)
        e0 → ColoredVertexSetClosed G (series.data.coloring ci.castSucc) (TreeSequenceVertexSet
        (series.data.tree ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (series.data.coloring ci.castSucc) (TreeSequenceVertexSet (series.data.tree
        ci.succ.castSucc)) → ¬Nonempty (RevisitingExtensionCertificate series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors series.data ci.castSucc) (series.data.coloring ci.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data ci.castSucc) : Finset (Fin k)) choice.selected pi →
        Disjoint (MissingColors G pi choice.otherEndpoint) (TreeMissingColors pi (series.data.tree
        ci.succ.castSucc))) → series.data.coloring ci.succ = choice.selected → series.data.stored
        ci.succ = ({ choice.color } : Finset (Fin k)) → series.data.connectingEdges ci.succ =
        ({ choice.edge } : Finset E) → series.data.kind ci.succ = some TashkinovExtensionKind.SE →
        series.data.chosenVertex ci.succ = some choice.vertex → series.data.outsideVertex ci.succ
        = some choice.otherEndpoint → series.data.delta ci.succ = some choice.color →
        series.data.gamma ci.succ = none →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (series.data.tree ci.succ.castSucc)
        choice.edge adjoined → TashkinovClosure (series.data.coloring ci.succ) adjoined
        (series.data.tree ci.succ.succ) → TreeSequenceInitialSegment (series.data.tree
        ci.succ.castSucc) (series.data.tree ci.succ.succ) → (series.data.tree
        ci.succ.castSucc).length < (series.data.tree ci.succ.succ).length → q.succ = ci.succ →
    ∃ (selected : PartialEdgeColoring E k) (secondStable : PartialEdgeColoring E k),
        IsProperEdgeColoring G selected ∧ IsOneEdgeUncolored selected e0 ∧ StableColoring
        (series.data.tree ci.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc) selected ∧ IsProperEdgeColoring G secondStable ∧
        IsOneEdgeUncolored secondStable e0 ∧ StableColoring (series.data.tree ci.succ.castSucc)
        (insert delta (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) selected
        secondStable ∧ series.data.coloring ci.succ = TwoColorComponentSwap G secondStable gamma
        delta (Sum.inl v) ∧
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma delta (Sum.inl v);
        StableColoring (series.data.tree ci.succ.castSucc) (insert delta (TashkinovStoredColors
        series.data q.castSucc) : Finset (Fin k)) secondStable undone ∧ StableColoring
        (series.data.tree ci.succ.castSucc) (insert delta (TashkinovStoredColors series.data
        q.castSucc) : Finset (Fin k)) selected undone ∧ StableColoring (series.data.tree
        ci.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc) undone := by
  classical
  intro V E _ _ _ G k rounds e0 input series q v gamma delta hkind sigma ci previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternative currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension target_eq
  have value := congrArg Fin.val target_eq
  simp at value
  have ci_eq : ci = q := by apply Fin.ext; omega
  subst ci
  rw [currentKind] at hkind
  simp at hkind

private theorem helper_branch_1110.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (v : V) (gamma delta : Fin k),
        series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k) (ci : Fin rounds), IsProperEdgeColoring G
        (series.data.coloring ci.castSucc) → IsOneEdgeUncolored (series.data.coloring ci.castSucc)
        e0 → ColoredVertexSetClosed G (series.data.coloring ci.castSucc) (TreeSequenceVertexSet
        (series.data.tree ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G
        (series.data.coloring ci.castSucc) (TreeSequenceVertexSet (series.data.tree
        ci.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate series.data ci.castSucc), series.data.coloring
        ci.succ = series.data.coloring ci.castSucc → series.data.stored ci.succ = (insert
        available.delta ({ available.gamma } : Finset (Fin k)) : Finset (Fin k)) →
        series.data.connectingEdges ci.succ = ({ available.edge } : Finset E) → series.data.kind
        ci.succ = some TashkinovExtensionKind.RE → series.data.chosenVertex ci.succ = some
        available.insideEndpoint → series.data.outsideVertex ci.succ = some
        available.outsideEndpoint → series.data.delta ci.succ = some available.delta →
        series.data.gamma ci.succ = some available.gamma →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (series.data.tree ci.succ.castSucc)
        available.edge adjoined → TashkinovClosure (series.data.coloring ci.succ) adjoined
        (series.data.tree ci.succ.succ) → TreeSequenceInitialSegment (series.data.tree
        ci.succ.castSucc) (series.data.tree ci.succ.succ) → (series.data.tree
        ci.succ.castSucc).length < (series.data.tree ci.succ.succ).length → q.succ = ci.succ →
    ∃ (selected : PartialEdgeColoring E k) (secondStable : PartialEdgeColoring E k),
        IsProperEdgeColoring G selected ∧ IsOneEdgeUncolored selected e0 ∧ StableColoring
        (series.data.tree ci.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc) selected ∧ IsProperEdgeColoring G secondStable ∧
        IsOneEdgeUncolored secondStable e0 ∧ StableColoring (series.data.tree ci.succ.castSucc)
        (insert delta (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) selected
        secondStable ∧ series.data.coloring ci.succ = TwoColorComponentSwap G secondStable gamma
        delta (Sum.inl v) ∧
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma delta (Sum.inl v);
        StableColoring (series.data.tree ci.succ.castSucc) (insert delta (TashkinovStoredColors
        series.data q.castSucc) : Finset (Fin k)) secondStable undone ∧ StableColoring
        (series.data.tree ci.succ.castSucc) (insert delta (TashkinovStoredColors series.data
        q.castSucc) : Finset (Fin k)) selected undone ∧ StableColoring (series.data.tree
        ci.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc) undone := by
  classical
  intro V E _ _ _ G k rounds e0 input series q v gamma delta hkind sigma ci previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed available currentColoring
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension
      target_eq
  have value := congrArg Fin.val target_eq
  simp at value
  have ci_eq : ci = q := by apply Fin.ext; omega
  subst ci
  rw [currentKind] at hkind
  simp at hkind

private theorem helper_hpathComponent_1164.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)) (u : V) (path : (TwoColorIncidenceGraph G secondStable
        chosenGamma choice.color).Walk (Sum.inl u) (Sum.inl choice.vertex)), (
    ∀ x ∈ path.support,
    ∀ (y : V ⊕ E), (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj x y → y ∈
        path.support) →
    ∀ y ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex), y ∈
        path.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable choice u path hclosed y hy
  let graph := TwoColorIncidenceGraph G secondStable chosenGamma choice.color
  have reach : graph.Reachable (Sum.inl choice.vertex) y := by
    change graph.connectedComponentMk y = graph.connectedComponentMk (Sum.inl choice.vertex)
        at hy
    exact SimpleGraph.ConnectedComponent.eq.mp hy |>.symm
  exact reach.mem_subgraphVerts (H := (⊤ : graph.Subgraph).induce {x | x ∈ path.support})
    (fun x hx z hadj => ⟨by simpa using hx, hclosed x (by simpa using hx) z hadj, hadj⟩)
    (by simp)

private theorem helper_hcompEdge_1176.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)) (_ : V) (e : E), Sum.inr e ∈ TwoColorComponent G
        secondStable chosenGamma choice.color (Sum.inl choice.vertex) → secondStable e = some
        chosenGamma ∨ secondStable e = some choice.color := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable choice u e he
  have hs : Sum.inr e ∈
      (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := TwoColorIncidenceGraph G secondStable chosenGamma choice.color)
      (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
    exact SimpleGraph.ConnectedComponent.eq.mp he
  obtain ⟨r, hr⟩ :=
    (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).mem_support.mp hs
  cases r with
  | inl x => exact hr.2
  | inr x => simp [TwoColorIncidenceGraph] at hr

private theorem helper_hchoiceSecond_1192.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (secondStable :
        PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0 (series.data.tree
        q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc)), StableColoring (series.data.tree q.succ.castSucc) (insert choice.color
        (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) choice.selected
        secondStable → secondStable choice.edge = some choice.color := by
  classical
  intro V E _ _ _ G k rounds e0 input series q secondStable choice secondStableRelation
  have heq := secondStableRelation.1 choice.edge
    ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
    ⟨choice.color, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self _ _)),
      choice.edgeColor⟩
  exact heq.trans choice.edgeColor

private theorem helper_hneq_1198.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)), chosenGamma ∈ MissingColors G secondStable
        choice.vertex → secondStable choice.edge = some choice.color → chosenGamma ≠ choice.color
  := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable choice hmissing
      hchoiceSecond heq
  have hp : chosenGamma ∈ PresentColors G secondStable choice.vertex := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨choice.edge, choice.edgeIncident, heq ▸ hchoiceSecond⟩
  have hpnot : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
    simpa [MissingColors] using hmissing
  exact hpnot hp

private theorem helper_htreeEdge_1211.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        chosenGamma ∈ MissingColors G secondStable choice.vertex →
    ∀ (u : V) (path : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Walk
        (Sum.inl u) (Sum.inl choice.vertex)), ((chosenGamma ∈ MissingColors G secondStable u ∨
        choice.color ∈ MissingColors G secondStable u) ∧
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), Sum.inl w ∈ path.support ↔ w =
        choice.vertex) → (
    ∀ y ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex), y ∈
        path.support) → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some chosenGamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color →
    ∀ (e : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) e → Sum.inr e ∈
        TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex) → e =
        choice.edge := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable secondStableProper choice
      hmissing u path endOnly hpathComponent hcompEdge hchoiceSecond e heT heC
  rcases heT with ⟨w, hw, hwe⟩
  have hwC : Sum.inl w ∈ TwoColorComponent G secondStable chosenGamma choice.color
      (Sum.inl choice.vertex) := by
    have hadj : (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj
        (Sum.inl w) (Sum.inr e) := by
      simp [TwoColorIncidenceGraph, hwe, hcompEdge e heC]
    change (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).connectedComponentMk
        (Sum.inl w) = _
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
  have hwv : w = choice.vertex := (endOnly.2 w hw).mp (hpathComponent _ hwC)
  subst w
  rcases hcompEdge e heC with hec | hec
  · have hnot : secondStable e ≠ some chosenGamma := by
      intro heq
      have hp : chosenGamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hwe, heq⟩
      have hm : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hmissing
      exact hm hp
    exact (hnot hec).elim
  · by_contra hne
    exact (secondStableProper hne ⟨choice.vertex, hwe, choice.edgeIncident⟩ hec
      hchoiceSecond).elim

private theorem helper_undoneOne_1250.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma : PartialEdgeColoring E k),
        IsOneEdgeUncolored sigma e0 →
    ∀ (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (series.data.tree
        q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc)), chosenGamma ≠ choice.color →
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex); IsOneEdgeUncolored undone e0 := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma hsigmaOneUncolored chosenGamma choice hneq
      undone
  unfold IsOneEdgeUncolored
  constructor
  · by_cases he : Sum.inr e0 ∈
      TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex)
    · simp [undone, TwoColorComponentSwap, he, hsigmaOneUncolored.1]
    · simp [undone, TwoColorComponentSwap, he, hsigmaOneUncolored.1]
  · intro e he
    obtain ⟨c, hc⟩ := hsigmaOneUncolored.2 e he
    by_cases hec : Sum.inr e ∈
        TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex)
    · by_cases hcg : c = chosenGamma
      · exact ⟨choice.color, by simp [undone, TwoColorComponentSwap, hec, hc, hcg]⟩
      · by_cases hcd : c = choice.color
        · exact ⟨chosenGamma, by simp [undone, TwoColorComponentSwap, hec, hc, hcd,
            hneq.symm]⟩
        · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc, hcg, hcd]⟩
    · exact ⟨c, by simp [undone, TwoColorComponentSwap, hec, hc]⟩

private theorem helper_treeMissingTransport_1268.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (a b : PartialEdgeColoring E k), (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc), MissingColors G a w =
        MissingColors G b w) → TreeMissingColors a (series.data.tree q.succ.castSucc) =
        TreeMissingColors b (series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series q a b hab
  ext c
  unfold TreeMissingColors
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, hw, by rw [hab w hw] at hc; exact hc⟩
  · rintro ⟨w, hw, hc⟩
    exact ⟨w, hw, by rw [hab w hw]; exact hc⟩

private theorem helper_sigmaComponentColor_1288.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma : PartialEdgeColoring E k)
        (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (series.data.tree
        q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc)) (_ : V) (e : E), Sum.inr e ∈ TwoColorComponent G sigma chosenGamma
        choice.color (Sum.inl choice.vertex) → sigma e = some chosenGamma ∨ sigma e = some
        choice.color := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma chosenGamma choice u e he
  have hs : Sum.inr e ∈
      (TwoColorIncidenceGraph G sigma chosenGamma choice.color).support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := TwoColorIncidenceGraph G sigma chosenGamma choice.color)
      (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
    exact SimpleGraph.ConnectedComponent.eq.mp he
  obtain ⟨r, hr⟩ :=
    (TwoColorIncidenceGraph G sigma chosenGamma choice.color).mem_support.mp hs
  cases r with
  | inl x => exact hr.2
  | inr x => simp [TwoColorIncidenceGraph] at hr

private theorem helper_currentColorMissing_1304.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc) (series.data.coloring q.castSucc)),
        series.data.coloring q.succ = TwoColorComponentSwap G secondStable chosenGamma
        choice.color (Sum.inl choice.vertex) → chosenGamma ∈ MissingColors G secondStable
        choice.vertex → (
    ∀ (e : E), Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some chosenGamma ∨ secondStable e = some choice.color) →
        secondStable choice.edge = some choice.color → chosenGamma ≠ choice.color → Sum.inr
        choice.edge ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → choice.color ∈ MissingColors G (series.data.coloring q.succ)
        choice.vertex := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable secondStableProper choice
      currentColoring hmissing hcompEdge hchoiceSecond hneq hfcomponent
  rw [MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hp
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  rcases hp with ⟨e, he, hec⟩
  rw [currentColoring] at hec
  by_cases hecomp : Sum.inr e ∈
      TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl choice.vertex)
  · rcases hcompEdge e hecomp with hegamma | hecolor
    · have hm : chosenGamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hmissing
      apply hm
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hegamma⟩
    · simp [TwoColorComponentSwap, hecomp, hecolor, hneq, hneq.symm] at hec
  · have hecolor : secondStable e = some choice.color := by
      simpa [TwoColorComponentSwap, hecomp] using hec
    by_cases heq : e = choice.edge
    · subst e
      exact (hecomp hfcomponent).elim
    · exact (secondStableProper heq ⟨choice.vertex, he, choice.edgeIncident⟩
        hecolor hchoiceSecond).elim

private theorem helper_currentControl_1340.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k) (choice :
        MaximumDefectiveChoice G e0 (series.data.tree q.succ.castSucc) (TashkinovStoredColors
        series.data q.castSucc) (series.data.coloring q.castSucc)), series.data.stored q.succ =
        (insert choice.color ({ chosenGamma } : Finset (Fin k)) : Finset (Fin k)) →
        TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) = TreeMissingColors
        (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) →
    ∀ c ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)), c ∈
        TreeMissingColors (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma choice currentStored
      treeSelectedPrevious c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · apply (HkuMissingStoredMonotone G k rounds e0 input series q).1
    rw [treeSelectedPrevious] at hc
    exact Finset.mem_union.mpr (Or.inl hc)
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · by_cases hm : choice.color ∈ TreeMissingColors
          (series.data.coloring q.succ) (series.data.tree q.succ.castSucc)
      · exact Finset.mem_union.mpr (Or.inl hm)
      · apply Finset.mem_union.mpr
        right
        unfold TashkinovStoredColors
        split
        · simp_all
        · simp only [Finset.mem_sdiff, Finset.mem_biUnion]
          exact ⟨⟨q.succ, by simp, by simp [currentStored]⟩, hm⟩
    · exact (HkuMissingStoredMonotone G k rounds e0 input series q).1
        (Finset.mem_union.mpr (Or.inr hc))

private theorem helper_gammaControl_1367.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (chosenGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc)), StableColoring (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k))
        choice.selected secondStable → choice.vertex ∈ TreeSequenceVertexSet (series.data.tree
        q.succ.castSucc) → chosenGamma ∈ MissingColors G secondStable choice.vertex → chosenGamma
        ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k rounds e0 input series q chosenGamma secondStable choice
      secondStableRelation hv hmissing
  apply Finset.mem_union.mpr
  left
  unfold TreeMissingColors
  simp only [Finset.mem_biUnion]
  refine ⟨choice.vertex, hv, ?_⟩
  rw [← secondStableRelation.2 choice.vertex
    choice.vertexDefective.1]
  exact hmissing

private theorem helper_branch_1407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (q : Fin rounds) (sigma : PartialEdgeColoring E k)
        (chosenGamma : Fin k) (choice : MaximumDefectiveChoice G e0 (series.data.tree
        q.succ.castSucc) (TashkinovStoredColors series.data q.castSucc) (series.data.coloring
        q.castSucc)),
    let undone : PartialEdgeColoring E k := TwoColorComponentSwap G sigma chosenGamma choice.color
        (Sum.inl choice.vertex); TreeMissingColors choice.selected (series.data.tree
        q.succ.castSucc) = TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree
        q.succ.castSucc) → (
    ∀ (f : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) f → ((
    ∃ c ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)),
        choice.selected f = some c) ∨
    ∃ c ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ (insert
        choice.color (TashkinovStoredColors series.data q.castSucc) : Finset (Fin k)), undone f =
        some c) → undone f = choice.selected f) → (
    ∀ (f : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) f → ((
    ∃ c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc, series.data.coloring q.castSucc f = some c)
        ∨
    ∃ c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc, choice.selected f = some c) →
        choice.selected f = series.data.coloring q.castSucc f) →
    ∀ (f : E), TreeIncidentEdge (series.data.tree q.succ.castSucc) f → (
    ∃ c ∈ TreeMissingColors (series.data.coloring q.castSucc) (series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors series.data q.castSucc, series.data.coloring q.castSucc f = some c)
        → undone f = series.data.coloring q.castSucc f := by
  classical
  intro V E _ _ _ G k rounds e0 input series q sigma chosenGamma choice undone
      treeSelectedPrevious selectedCriterion previousCriterion f hf h
  rcases h with ⟨c, hc, hcf⟩
  have hsel := previousCriterion f hf (Or.inl ⟨c, hc, hcf⟩)
  have hc2 : c ∈ TreeMissingColors choice.selected
      (series.data.tree q.succ.castSucc) ∪
      insert choice.color (TashkinovStoredColors series.data q.castSucc) := by
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union.mpr (Or.inl (by rw [treeSelectedPrevious]; exact hc))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem hc))
  have hstable := selectedCriterion f hf
    (Or.inl ⟨c, hc2, hsel.trans hcf⟩)
  exact hstable.trans hsel

theorem ParallelExtensionUndoStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds)
    (v : V) (gamma delta : Fin k)
    (hkind : series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hvertex : series.data.chosenVertex q.succ = some v)
    (hgamma : series.data.gamma q.succ = some gamma)
    (hdelta : series.data.delta q.succ = some delta)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOneUncolored : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring (series.data.tree q.succ.castSucc)
      (TashkinovStoredColors series.data q.succ)
      (series.data.coloring q.succ) sigma)
    (hv : v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc))
    (hcomponent : ∀ w,
      w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) →
      (Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) ↔
        w = v)) :
    ∃ selected secondStable : PartialEdgeColoring E k,
      IsProperEdgeColoring G selected ∧
      IsOneEdgeUncolored selected e0 ∧
      StableColoring (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc) selected ∧
      IsProperEdgeColoring G secondStable ∧
      IsOneEdgeUncolored secondStable e0 ∧
      StableColoring (series.data.tree q.succ.castSucc)
        (insert delta (TashkinovStoredColors series.data q.castSucc))
        selected secondStable ∧
      series.data.coloring q.succ =
        TwoColorComponentSwap G secondStable gamma delta (Sum.inl v) ∧
      StableColoring (series.data.tree q.succ.castSucc)
          (insert delta (TashkinovStoredColors series.data q.castSucc))
          secondStable (TwoColorComponentSwap G sigma gamma delta (Sum.inl v)) ∧
        StableColoring (series.data.tree q.succ.castSucc)
          (insert delta (TashkinovStoredColors series.data q.castSucc))
          selected (TwoColorComponentSwap G sigma gamma delta (Sum.inl v)) ∧
        StableColoring (series.data.tree q.succ.castSucc)
          (TashkinovStoredColors series.data q.castSucc)
          (series.data.coloring q.castSucc) (TwoColorComponentSwap G sigma gamma delta (Sum.inl
              v)) := by
  classical
  generalize target_eq : q.succ = target
  cases series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          apply helper_branch_1099 <;> assumption
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          apply helper_branch_1110 <;> assumption
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have value := congrArg Fin.val target_eq
    simp at value
    have ci_eq : ci = q := by apply Fin.ext; omega
    subst ci
    rw [currentKind] at hkind
    have delta_eq : delta = choice.color := Option.some.inj (hdelta.symm.trans currentDelta)
    have gamma_eq : gamma = chosenGamma := Option.some.inj (hgamma.symm.trans currentGamma)
    have vertex_eq : v = choice.vertex := Option.some.inj (hvertex.symm.trans currentVertex)
    subst delta
    subst gamma
    subst v
    refine ⟨choice.selected, secondStable, choice.selectedProper,
      choice.selectedOneUncolored, choice.selectedStable,
      secondStableProper, secondStableOneUncolored, secondStableRelation,
      currentColoring, ?_⟩
    dsimp
    have hmissing : chosenGamma ∈ MissingColors G secondStable choice.vertex := by
      exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸ gammaRule.1
    have hdegree : ∀ w, chosenGamma ∈ MissingColors G secondStable w ∨
        choice.color ∈ MissingColors G secondStable w →
        (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).degree
          (Sum.inl w) ≤ 1 := by
      intro w hw
      exact TwoColorMissingVertexDegreeAtMostOne G secondStable secondStableProper
        chosenGamma choice.color w hw
    rcases exitWitness with ⟨u, path, pathData⟩
    rcases pathData with ⟨pathIs, pathLen, uOut, endTree, endOnly⟩
    have hdegreeBound : ∀ x, @SimpleGraph.degree _
        (TwoColorIncidenceGraph G secondStable chosenGamma choice.color) x
        (Fintype.ofFinite _) ≤ 2 := by
      intro x
      exact TwoColorIncidenceDegreeAtMostTwo G secondStable chosenGamma choice.color
        secondStableProper x
    have huDegree := hdegree u endOnly.1
    have hclosed : ∀ x, x ∈ path.support → ∀ y,
        (TwoColorIncidenceGraph G secondStable chosenGamma choice.color).Adj x y →
        y ∈ path.support := by
      apply helper_hclosed_201 <;> assumption
    have hpathComponent : ∀ y,
        y ∈ TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) → y ∈ path.support := by
      apply helper_hpathComponent_1164; assumption
    have hcompEdge :
    ∀ e, Sum.inr e ∈ TwoColorComponent G secondStable chosenGamma choice.color (Sum.inl
        choice.vertex) → secondStable e = some chosenGamma ∨ secondStable e = some choice.color
  := by
      apply helper_hcompEdge_1176; assumption
    have hchoiceSecond : secondStable choice.edge = some choice.color := by
      apply helper_hchoiceSecond_1192; assumption
    have hneq : chosenGamma ≠ choice.color := by
      apply helper_hneq_1198 <;> assumption
    have hfcomponent : Sum.inr choice.edge ∈
        TwoColorComponent G secondStable chosenGamma choice.color
          (Sum.inl choice.vertex) := by
      apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [TwoColorIncidenceGraph, choice.edgeIncident, hchoiceSecond]
    have htreeEdge :
    ∀ e, TreeIncidentEdge (series.data.tree q.succ.castSucc) e → Sum.inr e ∈ TwoColorComponent G
        secondStable chosenGamma choice.color (Sum.inl choice.vertex) → e = choice.edge := by
      apply helper_htreeEdge_1211 <;> assumption
    have hsigmaEdge := @helper_hsigmaEdge_358 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@rounds) (@e0) (@input) (@series) (@q) (@sigma) (@hsigmaProper) (@hsigmaStable)
        (@chosenGamma) (@secondStable) (@secondStableProper) (@choice) (@currentColoring)
        (@currentStored) (@hgamma) (@hv) (@hcomponent) (@hmissing) (@u) (@hcompEdge)
        (@hchoiceSecond) (@hneq) (@hfcomponent)
    let undone := TwoColorComponentSwap G sigma chosenGamma choice.color
      (Sum.inl choice.vertex)
    have undoneProper : IsProperEdgeColoring G undone := by
      exact TwoColorComponentSwapProper G sigma chosenGamma choice.color hneq
        hsigmaProper (Sum.inl choice.vertex)
    have undoneOne : IsOneEdgeUncolored undone e0 := by
      apply helper_undoneOne_1250 <;> assumption
    have treeMissingTransport : ∀ (a b : PartialEdgeColoring E k),
        (∀ w, w ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) →
          MissingColors G a w = MissingColors G b w) →
        TreeMissingColors a (series.data.tree q.succ.castSucc) =
          TreeMissingColors b (series.data.tree q.succ.castSucc) := by
      apply helper_treeMissingTransport_1268
    have treeSecondSelected :
        TreeMissingColors secondStable (series.data.tree q.succ.castSucc) =
          TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) :=
      treeMissingTransport secondStable choice.selected (by
        intro w hw
        exact secondStableRelation.2 w hw)
    have sigmaComponentColor :
    ∀ e, Sum.inr e ∈ TwoColorComponent G sigma chosenGamma choice.color (Sum.inl choice.vertex) →
        sigma e = some chosenGamma ∨ sigma e = some choice.color := by
      apply helper_sigmaComponentColor_1288; assumption
    have currentColorMissing := @helper_currentColorMissing_1304 (@V) (@E) inferInstance
        inferInstance inferInstance (@G) (@k) (@rounds) (@e0) (@input) (@series) (@q) (@chosenGamma)
        (@secondStable) (@secondStableProper) (@choice) (@currentColoring) (@hmissing) (@hcompEdge)
        (@hchoiceSecond) (@hneq) (@hfcomponent)
    have sigmaColorMissing : choice.color ∈
        MissingColors G sigma choice.vertex := by
      rw [hsigmaStable.2 choice.vertex hv]
      exact currentColorMissing
    have treeSelectedPrevious :
        TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) =
          TreeMissingColors (series.data.coloring q.castSucc)
            (series.data.tree q.succ.castSucc) :=
      treeMissingTransport choice.selected (series.data.coloring q.castSucc) (by
        intro w hw
        exact choice.selectedStable.2 w hw)
    have currentControl :
    ∀ c, c ∈ TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪ insert
        choice.color (TashkinovStoredColors series.data q.castSucc) → c ∈ TreeMissingColors
        (series.data.coloring q.succ) (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors
        series.data q.succ := by
      apply helper_currentControl_1340 <;> assumption
    have selectedStableFact := choice.selectedStable
    have sigmaStableFact := hsigmaStable
    have relationFact := secondStableRelation
    have gammaControl : chosenGamma ∈
        TreeMissingColors choice.selected (series.data.tree q.succ.castSucc) ∪
          insert choice.color (TashkinovStoredColors series.data q.castSucc) := by
      apply helper_gammaControl_1367 <;> assumption
    have stableSecond : StableColoring
        (series.data.tree q.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data q.castSucc))
        secondStable undone := by
      apply GoldbergSeymour.helper_stableSecond_588 <;> assumption
    have stableSelected := @helper_stableSelected_718 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@rounds) (@e0) (@input) (@series) (@q) (@sigma) (@chosenGamma)
        (@secondStable) (@secondStableProper) (@secondStableOneUncolored) (@choice)
        (@secondStableRelation) (@undoneProper) (@undoneOne) (@treeSecondSelected) (@stableSecond)
    exact ⟨stableSecond, stableSelected, by
      apply (sc1 G e0 (series.data.tree q.succ.castSucc)
        (TashkinovStoredColors series.data q.castSucc)
        (series.data.coloring q.castSucc) undone
        (by exact previousProper) (by exact previousOneUncolored)
        undoneProper undoneOne).2
      have selectedCriterion :=
        ((sc1 G e0 (series.data.tree q.succ.castSucc)
          (insert choice.color (TashkinovStoredColors series.data q.castSucc))
          choice.selected undone choice.selectedProper choice.selectedOneUncolored
          undoneProper undoneOne).mp stableSelected)
      have previousCriterion :=
        ((sc1 G e0 (series.data.tree q.succ.castSucc)
          (TashkinovStoredColors series.data q.castSucc)
          (series.data.coloring q.castSucc) choice.selected
          previousProper previousOneUncolored choice.selectedProper
          choice.selectedOneUncolored).mp choice.selectedStable)
      intro f hf h
      rcases h with h | h
      · apply helper_branch_1407 <;> assumption
      · rcases h with ⟨c, hc, hcf⟩
        have hc2 := hc
        have hc2 : c ∈ TreeMissingColors choice.selected
            (series.data.tree q.succ.castSucc) ∪
            insert choice.color (TashkinovStoredColors series.data q.castSucc) := by
          rcases Finset.mem_union.mp hc with hc | hc
          · exact Finset.mem_union.mpr (Or.inl (by rw [treeSelectedPrevious]; exact hc))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem hc))
        have hstable := selectedCriterion f hf (Or.inr ⟨c, hc2, hcf⟩)
        have hsel := previousCriterion f hf
          (Or.inr ⟨c, hc, hstable.symm.trans hcf⟩)
        exact hstable.trans hsel⟩

end GoldbergSeymour

end
