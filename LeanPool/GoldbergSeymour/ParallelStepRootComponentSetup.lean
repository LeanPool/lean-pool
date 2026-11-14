/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorPathComponent
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Parallel Step Root Component Setup

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_239.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t : Fin rounds) (peGamma : Fin k)
        (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (series.data.tree t.succ.castSucc) (TashkinovStoredColors series.data t.castSucc)
        (series.data.coloring t.castSucc)), series.data.coloring t.succ = TwoColorComponentSwap G
        secondStable peGamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
        (series.data.coloring t.succ) → TreeSequenceInitialSegment (series.data.tree
        t.succ.castSucc) (series.data.tree t.succ.succ) →
    let T : TreeSequence G e0 := series.data.tree t.succ.castSucc;
    let X : Finset V := TreeSequenceVertexSet T; (
    ∀ v ∈ X,
    ∃ (f : E), Incident G v f ∧ secondStable f = some choice.color) → peGamma ≠ choice.color →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G secondStable peGamma choice.color; (
    ∀ w ∈ X, Sum.inl w ∈ TwoColorComponent G secondStable peGamma choice.color (Sum.inl
        choice.vertex) ↔ w = choice.vertex) → (H.neighborSet (Sum.inl choice.vertex)).Subsingleton
        → (
    ∀ (f : E), TwoColorComponentSwap G secondStable peGamma choice.color (Sum.inl choice.vertex) f
        = some peGamma ∨ TwoColorComponentSwap G secondStable peGamma choice.color (Sum.inl
        choice.vertex) f = some choice.color ↔ secondStable f = some peGamma ∨ secondStable f =
        some choice.color) → peGamma ≠ choice.color ∧ IsProperEdgeColoring G (series.data.coloring
        t.succ) ∧ TreeSequenceInitialSegment (series.data.tree t.succ.castSucc) (series.data.tree
        t.succ.succ) ∧ choice.vertex ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) ∧
        TwoColorPathComponent G (series.data.coloring t.succ) peGamma choice.color (Sum.inl
        choice.vertex) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G (series.data.coloring t.succ) peGamma choice.color (Sum.inl choice.vertex) ↔ w =
        choice.vertex) ∧
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc), v ≠ choice.vertex →
    ∃ (f : E), Sum.inr f ∈ TwoColorComponent G (series.data.coloring t.succ) peGamma choice.color
        (Sum.inl v) := by
  classical
  intro V E _ _ _ G k rounds e0 input series t peGamma secondStable choice currentColoring
      currentProper orderedExtension T X hcolorEdge hgammaNe H hrootOld rootLeaf colorPair
  have graphPreserved : TwoColorIncidenceGraph G
      (series.data.coloring t.succ) peGamma choice.color = H := by
    rw [currentColoring]
    ext x y
    cases x with
    | inl v =>
      cases y with
      | inl w => simp [H, TwoColorIncidenceGraph]
      | inr f =>
        simp only [H, TwoColorIncidenceGraph]
        exact and_congr_right (fun _ => colorPair f)
    | inr e =>
      cases y with
      | inl v =>
        simp only [H, TwoColorIncidenceGraph]
        exact and_congr_right (fun _ => colorPair e)
      | inr f => simp [H, TwoColorIncidenceGraph]
  have componentPreserved (z : Sum V E) :
      TwoColorComponent G (series.data.coloring t.succ)
          peGamma choice.color z =
        TwoColorComponent G secondStable peGamma choice.color z := by
    unfold TwoColorComponent
    rw [graphPreserved]
  refine ⟨hgammaNe, currentProper, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [T] using orderedExtension
  · simpa [T, X] using choice.vertexDefective.1
  · refine ⟨hgammaNe, Sum.inl choice.vertex, ?_, ?_⟩
    · change (TwoColorIncidenceGraph G (series.data.coloring t.succ)
        peGamma choice.color).connectedComponentMk (Sum.inl choice.vertex) =
        (TwoColorIncidenceGraph G (series.data.coloring t.succ)
        peGamma choice.color).connectedComponentMk (Sum.inl choice.vertex)
      rfl
    · rw [graphPreserved]
      exact rootLeaf
  · intro w hw
    rw [componentPreserved]
    exact hrootOld w (by simpa [T, X] using hw)
  · intro v hv hvne
    obtain ⟨f, hfIncident, hfColor⟩ :=
      hcolorEdge v (by simpa [T, X] using hv)
    have hfNotRoot : Sum.inr f ∉
        TwoColorComponent G secondStable peGamma choice.color
          (Sum.inl choice.vertex) := by
      intro hfRoot
      have hvRoot : Sum.inl v ∈
          TwoColorComponent G secondStable peGamma choice.color
            (Sum.inl choice.vertex) := by
        change H.connectedComponentMk (Sum.inl v) =
          H.connectedComponentMk (Sum.inl choice.vertex)
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (by simp [H, TwoColorIncidenceGraph, hfIncident, hfColor])).trans
            hfRoot
      exact hvne ((hrootOld v (by simpa [T, X] using hv)).mp hvRoot)
    have hfCurrent : series.data.coloring t.succ f =
        some choice.color := by
      rw [congrFun currentColoring f]
      simp [TwoColorComponentSwap, hfNotRoot, hfColor]
    refine ⟨f, ?_⟩
    change (TwoColorIncidenceGraph G (series.data.coloring t.succ)
        peGamma choice.color).connectedComponentMk (Sum.inr f) =
      (TwoColorIncidenceGraph G (series.data.coloring t.succ)
        peGamma choice.color).connectedComponentMk (Sum.inl v)
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hfIncident, hfCurrent]

private theorem helper_continuation_253.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t : Fin rounds) (peGamma : Fin k)
        (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree t.succ.castSucc)
        (TashkinovStoredColors series.data t.castSucc) (series.data.coloring t.castSucc)),
        TreeExit (series.data.tree t.succ.castSucc) secondStable peGamma choice.color
        choice.vertex → series.data.coloring t.succ = TwoColorComponentSwap G secondStable peGamma
        choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G (series.data.coloring
        t.succ) → TreeSequenceInitialSegment (series.data.tree t.succ.castSucc) (series.data.tree
        t.succ.succ) →
    let T : TreeSequence G e0 := series.data.tree t.succ.castSucc;
    let X : Finset V := TreeSequenceVertexSet T;
    ∀ (_ : Fin k), (
    ∀ v ∈ X,
    ∃ (f : E), Incident G v f ∧ secondStable f = some choice.color) → peGamma ∈ MissingColors G
        secondStable choice.vertex → peGamma ≠ choice.color →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G secondStable peGamma choice.color; (
    ∀ (v : V), peGamma ∈ MissingColors G secondStable v ∨ choice.color ∈ MissingColors G
        secondStable v → @SimpleGraph.degree (Sum V E) H (@Sum.inl V E v) (@Fintype.ofFinite
        (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v)))
        (@Subtype.finite (Sum V E) (@Finite.instSum V E (@Finite.of_fintype V inst)
        (@Finite.of_fintype E inst_1)) (@Membership.mem (Sum V E) (Set (Sum V E))
        (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v)))))
        ≤ (1 : ℕ)) → peGamma ≠ choice.color ∧ IsProperEdgeColoring G (series.data.coloring t.succ)
        ∧ TreeSequenceInitialSegment (series.data.tree t.succ.castSucc) (series.data.tree
        t.succ.succ) ∧ choice.vertex ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) ∧
        TwoColorPathComponent G (series.data.coloring t.succ) peGamma choice.color (Sum.inl
        choice.vertex) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G (series.data.coloring t.succ) peGamma choice.color (Sum.inl choice.vertex) ↔ w =
        choice.vertex) ∧
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc), v ≠ choice.vertex →
    ∃ (f : E), Sum.inr f ∈ TwoColorComponent G (series.data.coloring t.succ) peGamma choice.color
        (Sum.inl v) := by
  classical
  intro V E _ _ _ G k rounds e0 input series t peGamma secondStable secondStableProper choice
      exitWitness currentColoring currentProper orderedExtension T X defectiveColor hcolorEdge
      hgammaMissing hgammaNe H missingDegree
  rcases exitWitness with ⟨outside, path, pathIs, pathLength,
    outsideNotTree, supportInTree, outsideMissing, pathOnly⟩
  have hdegreeBound : ∀ x,
      @SimpleGraph.degree _ H x (Fintype.ofFinite _) ≤ 2 := by
    intro x
    simpa [H] using TwoColorIncidenceDegreeAtMostTwo G secondStable
      peGamma choice.color secondStableProper x
  have pathClosed : ∀ x, x ∈ path.support → ∀ y, H.Adj x y →
      y ∈ path.support := by
    intro x hx y hxy
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hn0 : n = 0
    · subst n
      have hx0 : x = Sum.inl outside := by simpa using hn.symm
      let : Fintype (H.neighborSet x) := Fintype.ofFinite _
      have card : Fintype.card (H.neighborSet x) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert missingDegree outside outsideMissing using 1
        cases hx0
        exact congrArg (fun z => @SimpleGraph.degree _ H
          (Sum.inl outside) z) (Subsingleton.elim _ _)
      have hy' : y ∈ H.neighborSet x := by
        simpa [SimpleGraph.mem_neighborSet] using hxy
      have hn' : path.getVert 1 ∈ H.neighborSet x := by
        simpa [hx0, SimpleGraph.mem_neighborSet] using
          path.adj_getVert_succ (show 0 < path.length by omega)
      have heq := Fintype.card_le_one_iff.mp card
        ⟨y, hy'⟩ ⟨path.getVert 1, hn'⟩
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
        convert missingDegree choice.vertex (Or.inl hgammaMissing) using 1
        cases hx1
        exact congrArg (fun z => @SimpleGraph.degree _ H
          (Sum.inl choice.vertex) z) (Subsingleton.elim _ _)
      have hy' : y ∈ H.neighborSet x := by
        simpa [SimpleGraph.mem_neighborSet] using hxy
      have hp : path.getVert (path.length - 1) ∈ H.neighborSet x := by
        have ha : H.Adj (Sum.inl choice.vertex)
            (path.getVert (path.length - 1)) := by
          simpa [show path.length - 1 + 1 = path.length by omega] using
            (path.adj_getVert_succ
              (show path.length - 1 < path.length by omega)).symm
        simpa [hx1, SimpleGraph.mem_neighborSet] using ha
      have heq := Fintype.card_le_one_iff.mp card
        ⟨y, hy'⟩ ⟨path.getVert (path.length - 1), hp⟩
      have hey : y = path.getVert (path.length - 1) :=
        congrArg Subtype.val heq
      rw [hey]
      exact path.getVert_mem_support _
    have hleft : H.Adj (path.getVert n) (path.getVert (n - 1)) := by
      rw [← show n - 1 + 1 = n by omega]
      exact (path.adj_getVert_succ (by omega)).symm
    have hnlt : n < path.length := lt_of_le_of_ne hnle hlast
    have hright := path.adj_getVert_succ hnlt
    by_contra hyout
    rw [← hn] at hxy
    have hneLeft : path.getVert (n - 1) ≠ y := by
      intro h
      apply hyout
      rw [← h]
      exact path.getVert_mem_support _
    have hneRight : path.getVert (n + 1) ≠ y := by
      intro h
      apply hyout
      rw [← h]
      exact path.getVert_mem_support _
    have hneSides : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
      intro h
      have hi := pathIs.getVert_injOn
        (show n - 1 ≤ path.length by omega)
        (show n + 1 ≤ path.length by omega) h
      omega
    let : Fintype (H.neighborSet (path.getVert n)) := Fintype.ofFinite _
    have three : 3 ≤ @SimpleGraph.degree _ H (path.getVert n)
        (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset (Sum V E) :=
        {y, path.getVert (n - 1), path.getVert (n + 1)}
      have hs : s ⊆ H.neighborFinset (path.getVert n) := by
        intro z hz
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hxy
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc : 3 ≤ s.card := by
        simp [s, hneSides,
          hneLeft.symm, hneRight.symm]
      exact hc.trans (Finset.card_le_card hs)
    have upper : @SimpleGraph.degree _ H (path.getVert n)
        (Fintype.ofFinite _) ≤ 2 := hdegreeBound (path.getVert n)
    omega
  have hrootOld : ∀ w : V, w ∈ X →
      (Sum.inl w ∈ TwoColorComponent G secondStable peGamma
        choice.color (Sum.inl choice.vertex) ↔ w = choice.vertex) := by
    intro w hw
    constructor
    · intro hwComponent
      have reachable : H.Reachable (Sum.inl choice.vertex) (Sum.inl w) := by
        change H.connectedComponentMk (Sum.inl w) =
          H.connectedComponentMk (Sum.inl choice.vertex) at hwComponent
        exact SimpleGraph.ConnectedComponent.eq.mp hwComponent |>.symm
      have hwPath : Sum.inl w ∈ path.support := by
        apply reachable.mem_subgraphVerts
          (H := (⊤ : H.Subgraph).induce {x | x ∈ path.support})
          (fun x hx y hadj =>
            ⟨by simpa using hx,
              pathClosed x (by simpa using hx) y hadj, hadj⟩)
          (by simp)
      exact (pathOnly w hw).mp hwPath
    · rintro rfl
      change H.connectedComponentMk (Sum.inl choice.vertex) =
        H.connectedComponentMk (Sum.inl choice.vertex)
      rfl
  have rootLeaf : Set.Subsingleton
      (H.neighborSet (Sum.inl choice.vertex)) := by
    let : Fintype (H.neighborSet (Sum.inl choice.vertex)) :=
      Fintype.ofFinite _
    have hcard : Fintype.card (H.neighborSet (Sum.inl choice.vertex)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact missingDegree choice.vertex (Or.inl hgammaMissing)
    intro a ha b hb
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hcard ⟨a, ha⟩ ⟨b, hb⟩)
  have colorPair (f : E) :
      (TwoColorComponentSwap G secondStable peGamma choice.color
            (Sum.inl choice.vertex) f = some peGamma ∨
        TwoColorComponentSwap G secondStable peGamma choice.color
            (Sum.inl choice.vertex) f = some choice.color) ↔
      (secondStable f = some peGamma ∨
        secondStable f = some choice.color) := by
    by_cases hfComponent : Sum.inr f ∈
        TwoColorComponent G secondStable peGamma choice.color
          (Sum.inl choice.vertex)
    · by_cases hfg : secondStable f = some peGamma
      · simp [TwoColorComponentSwap, hfComponent, hfg, hgammaNe]
      · by_cases hfd : secondStable f = some choice.color
        · simp [TwoColorComponentSwap, hfComponent, hfd, hgammaNe]
        · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
    · simp [TwoColorComponentSwap, hfComponent]
  exact @helper_continuation_239 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@rounds) (@e0) (@input) (@series) (@t) (@peGamma) (@secondStable) (@choice)
      (@currentColoring) (@currentProper) (@orderedExtension) (@hcolorEdge) (@hgammaNe)
      (@hrootOld) (@rootLeaf) (@colorPair)
private theorem helper_branch_100.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t : Fin rounds) (support : V) (gamma delta
        : Fin k), series.data.chosenVertex t.succ = some support → series.data.gamma t.succ = some
        gamma → series.data.delta t.succ = some delta →
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
    ∀ (peGamma : Fin k), ParallelExtensionColor series.data i.castSucc choice.selected
        choice.vertex peGamma →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        IsOneEdgeUncolored secondStable e0 → StableColoring (series.data.tree i.succ.castSucc)
        (insert choice.color (TashkinovStoredColors series.data i.castSucc)) choice.selected
        secondStable → TreeExit (series.data.tree i.succ.castSucc) secondStable peGamma
        choice.color choice.vertex → series.data.coloring i.succ = TwoColorComponentSwap G
        secondStable peGamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
        (series.data.coloring i.succ) → IsOneEdgeUncolored (series.data.coloring i.succ) e0 →
        series.data.stored i.succ = { choice.color, peGamma } → series.data.connectingEdges i.succ
        = { choice.edge } → series.data.kind i.succ = some TashkinovExtensionKind.PE →
        series.data.chosenVertex i.succ = some choice.vertex → series.data.outsideVertex i.succ =
        some choice.otherEndpoint → series.data.delta i.succ = some choice.color →
        series.data.gamma i.succ = some peGamma → TashkinovClosure (series.data.coloring i.succ)
        (series.data.tree i.succ.castSucc) (series.data.tree i.succ.succ) →
        TreeSequenceInitialSegment (series.data.tree i.succ.castSucc) (series.data.tree
        i.succ.succ) → (series.data.tree i.succ.castSucc).length < (series.data.tree
        i.succ.succ).length → t.succ = i.succ → gamma ≠ delta ∧ IsProperEdgeColoring G
        (series.data.coloring i.succ) ∧ TreeSequenceInitialSegment (series.data.tree
        i.succ.castSucc) (series.data.tree i.succ.succ) ∧ support ∈ TreeSequenceVertexSet
        (series.data.tree i.succ.castSucc) ∧ TwoColorPathComponent G (series.data.coloring i.succ)
        gamma delta (Sum.inl support) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc), Sum.inl w ∈ TwoColorComponent
        G (series.data.coloring i.succ) gamma delta (Sum.inl support) ↔ w = support) ∧
    ∀ v ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc), v ≠ support →
    ∃ (f : E), Sum.inr f ∈ TwoColorComponent G (series.data.coloring i.succ) gamma delta (Sum.inl
        v) := by
  classical
  intro V E _ _ _ G k rounds e0 input series t support gamma delta htVertex htGamma htDelta i
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternativeFails peGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension hslot
  have hi : i = t := by
    apply Fin.ext
    have h := congrArg Fin.val hslot
    simp at h
    omega
  subst i
  have hsupport : choice.vertex = support :=
    Option.some.inj (currentVertex.symm.trans htVertex)
  have hgamma : peGamma = gamma :=
    Option.some.inj (currentGamma.symm.trans htGamma)
  have hdelta : choice.color = delta :=
    Option.some.inj (currentDelta.symm.trans htDelta)
  subst support
  subst gamma
  subst delta
  let T := series.data.tree t.succ.castSucc
  let X := TreeSequenceVertexSet T
  let C0 := TashkinovStoredColors series.data t.castSucc
  let C := insert choice.color
    (TashkinovStoredColors series.data t.castSucc)
  have boundaryIncident : ∀ {f : E}, f ∈ BoundaryEdges G X →
      TreeIncidentEdge T f := by
    intro f hf
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf
    obtain ⟨v, hv, w, hw, hends⟩ := hf
    exact ⟨v, hv, by simp [Incident, hends]⟩
  let previousSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨series.data.coloring t.castSucc,
      previousProper, previousOneUncolored⟩
  let selectedSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨choice.selected,
      choice.selectedProper, choice.selectedOneUncolored⟩
  have selectedForward : StableColoring T C0
      previousSubtype.1 selectedSubtype.1 := by
    simpa [T, C0, previousSubtype, selectedSubtype] using
      choice.selectedStable
  have selectedReverse : StableColoring T C0
      selectedSubtype.1 previousSubtype.1 := by
    exact (sc2 G e0 T C0).symm selectedForward
  have selectedClosed : ColoredVertexSetClosed G choice.selected X := by
    intro f c v hf hv hfc hcmissing
    have hpreviousMissing : c ∈ MissingColors G
        (series.data.coloring t.castSucc) v := by
      rw [← choice.selectedStable.2 v (by simpa [T, X] using hv)]
      exact hcmissing
    have hfixed : series.data.coloring t.castSucc f = choice.selected f := by
      apply selectedReverse.1 f (boundaryIncident hf)
      refine ⟨c, ?_, hfc⟩
      apply Finset.mem_union_left
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hv, hcmissing⟩
    exact previousClosed hf hv (hfixed.trans hfc) hpreviousMissing
  let secondSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨secondStable, secondStableProper, secondStableOneUncolored⟩
  have secondForward : StableColoring T C
      selectedSubtype.1 secondSubtype.1 := by
    simpa [T, C, selectedSubtype, secondSubtype] using
      secondStableRelation
  have secondReverse : StableColoring T C
      secondSubtype.1 selectedSubtype.1 := by
    exact (sc2 G e0 T C).symm secondForward
  have secondClosed : ColoredVertexSetClosed G secondStable X := by
    intro f c v hf hv hfc hcmissing
    have hselectedMissing : c ∈ MissingColors G choice.selected v := by
      rw [← secondStableRelation.2 v (by simpa [T, X] using hv)]
      exact hcmissing
    have hfixed : choice.selected f = secondStable f := by
      apply secondReverse.1 f (boundaryIncident hf)
      refine ⟨c, ?_, hfc⟩
      apply Finset.mem_union_left
      simp only [TreeMissingColors, Finset.mem_biUnion]
      exact ⟨v, hv, hcmissing⟩
    exact selectedClosed hf hv (hfixed.trans hfc) hselectedMissing
  obtain ⟨defectiveColor, defectiveColorData, hchoiceBoundaryColor⟩ :=
    choice.edgeDefective
  have hdefectiveColor : defectiveColor = choice.color := by
    have hcolor := (Finset.mem_filter.mp hchoiceBoundaryColor).2
    exact Option.some.inj (hcolor.symm.trans choice.edgeColor)
  have hchoiceBoundary : choice.edge ∈ BoundaryEdges G X := by
    exact (Finset.mem_filter.mp hchoiceBoundaryColor).1
  have hchoiceSecond : secondStable choice.edge = some choice.color := by
    have hfixed := secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color,
        Finset.mem_union_right _ (Finset.mem_insert_self _ _),
        choice.edgeColor⟩
    exact hfixed.trans choice.edgeColor
  have hcolorPresent : ∀ v : V, v ∈ X →
      choice.color ∈ PresentColors G secondStable v := by
    intro v hv
    have hnotMissing : choice.color ∉ MissingColors G secondStable v :=
      secondClosed hchoiceBoundary hv hchoiceSecond
    simpa [MissingColors] using hnotMissing
  have hcolorEdge : ∀ v : V, v ∈ X →
      ∃ f : E, Incident G v f ∧
        secondStable f = some choice.color := by
    intro v hv
    simpa [PresentColors] using hcolorPresent v hv
  have hgammaMissing : peGamma ∈
      MissingColors G secondStable choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hgammaNe : peGamma ≠ choice.color := by
    intro h
    have hpresent : peGamma ∈
        PresentColors G secondStable choice.vertex := by
      simpa [h] using hcolorPresent choice.vertex choice.vertexDefective.1
    have hnotPresent : peGamma ∉
        PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hgammaMissing
    exact hnotPresent hpresent
  let H := TwoColorIncidenceGraph G secondStable peGamma choice.color
  have missingDegree :
    ∀ v : V, peGamma ∈ MissingColors G secondStable v ∨ choice.color ∈ MissingColors G
        secondStable v → @SimpleGraph.degree _ H (Sum.inl v) (Fintype.ofFinite _) ≤ 1 := by
    intro v hv
    exact TwoColorMissingVertexDegreeAtMostOne G secondStable secondStableProper
      peGamma choice.color v (neighborEnumeration := Fintype.ofFinite _) hv
  exact @helper_continuation_253 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@rounds) (@e0) (@input) (@series) (@t) (@peGamma) (@secondStable) (@secondStableProper)
      (@choice) (@exitWitness) (@currentColoring) (@currentProper) (@orderedExtension)
      (@defectiveColor) (@hcolorEdge) (@hgammaMissing) (@hgammaNe) (@missingDegree)
theorem ParallelStepRootComponentSetup {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t : Fin rounds) (support : V) (gamma delta : Fin k)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htVertex : series.data.chosenVertex t.succ = some support)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta) :
    gamma ≠ delta ∧
      IsProperEdgeColoring G (series.data.coloring t.succ) ∧
      TreeSequenceInitialSegment
        (series.data.tree t.succ.castSucc)
        (series.data.tree t.succ.succ) ∧
      support ∈
        TreeSequenceVertexSet (series.data.tree t.succ.castSucc) ∧
      TwoColorPathComponent G (series.data.coloring t.succ)
        gamma delta (Sum.inl support) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G
            (series.data.coloring t.succ) gamma delta
            (Sum.inl support) ↔ w = support)) ∧
      ∀ v : V,
        v ∈ TreeSequenceVertexSet (series.data.tree t.succ.castSucc) →
        v ≠ support →
        ∃ f : E, Sum.inr f ∈ TwoColorComponent G
          (series.data.coloring t.succ) gamma delta (Sum.inl v) := by
  classical
  generalize hslot : t.succ = slot
  cases series.certified slot with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero t hslot).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hi : i = t := by
      apply Fin.ext
      have h := congrArg Fin.val hslot
      simp at h
      omega
    subst i
    rw [currentKind] at htKind
    simp at htKind
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hi : i = t := by
      apply Fin.ext
      have h := congrArg Fin.val hslot
      simp at h
      omega
    subst i
    rw [currentKind] at htKind
    simp at htKind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      peGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_100 V E inferInstance inferInstance inferInstance G k rounds e0
              input series t support gamma delta htVertex htGamma htDelta i previousProper
              previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
              seriesAlternativeFails peGamma gammaRule secondStable secondStableProper
              secondStableOneUncolored secondStableRelation exitWitness currentColoring
              currentProper currentOneUncolored currentStored currentEdges currentKind
              currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension hslot
end GoldbergSeymour

end
