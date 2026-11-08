/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.UnsupportedVertexColors

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Hku Unsupported Vertex Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hcomponent_167.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (i : Fin rounds)
    (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
    secondStable → ∀ (choice : MaximumDefectiveChoice G e0 (series.data.tree i.succ.castSucc)
    (TashkinovStoredColors series.data i.castSucc) (series.data.coloring i.castSucc)),
    TreeExit (series.data.tree i.succ.castSucc) secondStable gamma choice.color choice.vertex
    → gamma ∈ MissingColors G secondStable choice.vertex → (∀ (w : V), gamma ∈ MissingColors G
    secondStable w ∨ choice.color ∈ MissingColors G secondStable w → (TwoColorIncidenceGraph G
    secondStable gamma choice.color).degree (Sum.inl w) ≤ (1 : ℕ)) → (TwoColorIncidenceGraph G
    secondStable gamma choice.color).degree (Sum.inl choice.vertex) ≤ (1 : ℕ) → ∀ y ∈
    TreeSequenceVertexSet (series.data.tree i.castSucc.succ), Sum.inl y ∈ TwoColorComponent G
    secondStable gamma choice.color (Sum.inl choice.vertex) → y = choice.vertex := by
  classical
  intro V E _ _ _ G k rounds e0 input series i gamma secondStable secondStableProper choice
      exitWitness hmissing degree_one_of_missing hdegree_one y hyT hyC
  rcases exitWitness with ⟨u, path, pathData⟩
  rcases pathData with ⟨path_is, path_len, u_not_tree, endpoint_tree, endpoint_only⟩
  have path_nonempty : ¬ path.Nil := by
    intro hnil
    have : path.length = 0 := by simpa [SimpleGraph.Walk.nil_iff_support_eq] using hnil
    omega
  have endpoint_missing : gamma ∈ MissingColors G secondStable choice.vertex := hmissing
  have outside_degree : (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
      (Sum.inl u) ≤ 1 := by
    apply degree_one_of_missing u
    exact endpoint_only.1
  let H := TwoColorIncidenceGraph G secondStable gamma choice.color
  have outside_degree' : H.degree (Sum.inl u) ≤ 1 := outside_degree
  have hdegree_one' : H.degree (Sum.inl choice.vertex) ≤ 1 := hdegree_one
  have all_degree : ∀ w, @SimpleGraph.degree _ H w (Fintype.ofFinite _) ≤ 2 := by
    intro w
    exact TwoColorIncidenceDegreeAtMostTwo G secondStable gamma choice.color
      secondStableProper w
  have support_closed : ∀ w, w ∈ path.support → ∀ z, H.Adj w z → z ∈ path.support := by
    intro w hw z hwz
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
    by_cases hn0 : n = 0
    · subst n
      have hwstart : w = Sum.inl u := by simpa using hn.symm
      let : Fintype (H.neighborSet w) := Fintype.ofFinite _
      have hcard : Fintype.card (H.neighborSet w) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert outside_degree' using 1
        cases hwstart
        exact congrArg (fun inst : Fintype (H.neighborSet (Sum.inl u)) =>
          @SimpleGraph.degree _ H (Sum.inl u) inst) (Subsingleton.elim _ _)
      have hzmem : z ∈ H.neighborSet w := by simpa [SimpleGraph.mem_neighborSet] using hwz
      have hnext : path.getVert 1 ∈ H.neighborSet w := by
        simpa [hwstart, SimpleGraph.mem_neighborSet] using path.adj_getVert_succ (show 0 <
            path.length by omega)
      have heq := Fintype.card_le_one_iff.mp hcard
        ⟨z, hzmem⟩ ⟨path.getVert 1, hnext⟩
      have hz_eq : z = path.getVert 1 := congrArg Subtype.val heq
      simp [hz_eq]
    by_cases hne : n = path.length
    · have hwend : w = Sum.inl choice.vertex := by
        rw [← hn, path_is.getVert_eq_end_iff hnle]
        exact hne
      let : Fintype (H.neighborSet w) := Fintype.ofFinite _
      have hcard : Fintype.card (H.neighborSet w) ≤ 1 := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        convert hdegree_one' using 1
        cases hwend
        exact congrArg (fun inst : Fintype (H.neighborSet (Sum.inl choice.vertex)) =>
          @SimpleGraph.degree _ H (Sum.inl choice.vertex) inst) (Subsingleton.elim _ _)
      have hzmem : z ∈ H.neighborSet w := by simpa [SimpleGraph.mem_neighborSet] using hwz
      have hprev : path.getVert (path.length - 1) ∈ H.neighborSet w := by
        have hadj : H.Adj (Sum.inl choice.vertex)
            (path.getVert (path.length - 1)) := by
          have hlt : path.length - 1 < path.length := by omega
          simpa [H, show path.length - 1 + 1 = path.length by omega] using
            (path.adj_getVert_succ hlt).symm
        have hprev' : path.getVert (path.length - 1) ∈
            H.neighborSet (Sum.inl choice.vertex) := by
          simpa [SimpleGraph.mem_neighborSet] using hadj
        simpa [hwend] using hprev'
      have heq := Fintype.card_le_one_iff.mp hcard
        ⟨z, hzmem⟩ ⟨path.getVert (path.length - 1), hprev⟩
      have hz_eq : z = path.getVert (path.length - 1) := congrArg Subtype.val heq
      simp [hz_eq]
    have hleft : H.Adj (path.getVert n) (path.getVert (n - 1)) := by
      rw [← show n - 1 + 1 = n by omega]
      exact (path.adj_getVert_succ (by omega)).symm
    have hright : H.Adj (path.getVert n) (path.getVert (n + 1)) :=
      path.adj_getVert_succ (by omega)
    by_contra hznot
    have hwz' := hwz
    rw [← hn] at hwz'
    have hneleft : path.getVert (n - 1) ≠ z := by
      intro he
      apply hznot
      rw [← he]
      exact path.getVert_mem_support _
    have hneright : path.getVert (n + 1) ≠ z := by
      intro he
      apply hznot
      rw [← he]
      exact path.getVert_mem_support _
    have hnelr : path.getVert (n - 1) ≠ path.getVert (n + 1) := by
      have hnlt : n < path.length := by omega
      intro he
      have hi := path_is.getVert_injOn (show n - 1 ≤ path.length by omega)
        (show n + 1 ≤ path.length by omega) he
      omega
    let : Fintype (H.neighborSet (path.getVert n)) := Fintype.ofFinite _
    have hthree : 3 ≤ H.degree (path.getVert n) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset _ := {z, path.getVert (n - 1), path.getVert (n + 1)}
      have hs : s ⊆ H.neighborFinset (path.getVert n) := by
        intro t ht
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hwz'
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hc : 3 ≤ s.card := by
        simp [s, hnelr, hneleft.symm, hneright.symm]
      exact hc.trans (Finset.card_le_card hs)
    have hupper : @SimpleGraph.degree _ H (path.getVert n) (Fintype.ofFinite _) ≤ 2 :=
      all_degree (path.getVert n)
    omega
  have reach : H.Reachable (Sum.inl choice.vertex) (Sum.inl y) := by
    change (TwoColorIncidenceGraph G secondStable gamma choice.color).Reachable _ _
    change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
      (Sum.inl y) =
      (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
        (Sum.inl choice.vertex) at hyC
    exact SimpleGraph.ConnectedComponent.eq.mp hyC |>.symm
  have ypath : Sum.inl y ∈ path.support := by
    apply reach.mem_subgraphVerts
      (H := (⊤ : H.Subgraph).induce {w | w ∈ path.support})
      (fun w hw z hadj => by
        exact ⟨by simpa using hw, support_closed w (by simpa using hw) z hadj,
          hadj⟩)
      (by simp)
  exact (endpoint_only.2 y hyT).mp ypath

private theorem helper_vertex_step_297.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (_ : V) (i : Fin
    rounds) (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice :
    MaximumDefectiveChoice G e0 (series.data.tree i.succ.castSucc) (TashkinovStoredColors
    series.data i.castSucc) (series.data.coloring i.castSucc)) (a : V) (e : E), Incident G a e
    → Sum.inr e ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex)
    → Sum.inl a ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) := by
  classical
  intro V E _ _ _ G k rounds e0 input series v i gamma secondStable choice a e hae hem
  change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
      (Sum.inl a) = _
  have support : Sum.inr e ∈
      (TwoColorIncidenceGraph G secondStable gamma choice.color).support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := TwoColorIncidenceGraph G secondStable gamma choice.color)
      (u := Sum.inr e) (v := Sum.inl choice.vertex) (by simp)
    exact SimpleGraph.ConnectedComponent.eq.mp hem
  obtain ⟨r, hr⟩ := (TwoColorIncidenceGraph G secondStable gamma choice.color).mem_support.mp
      support
  have hcolors : secondStable e = some gamma ∨
      secondStable e = some choice.color := by
    cases r with
    | inl a => exact hr.2
    | inr r => simp [TwoColorIncidenceGraph] at hr
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (by simp [TwoColorIncidenceGraph, hae, hcolors])).trans hem

private theorem helper_branch_71.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (_ : V) (i : Fin
    rounds), ∀ x ∈ TreeSequenceVertexSet (series.data.tree i.succ.castSucc), ∀ (ci : Fin
    rounds), IsProperEdgeColoring G (series.data.coloring ci.castSucc) → IsOneEdgeUncolored
    (series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G (series.data.coloring
    ci.castSucc) (TreeSequenceVertexSet (series.data.tree ci.succ.castSucc)) →
    ¬ColoredVertexSetStronglyClosed G (series.data.coloring ci.castSucc)
    (TreeSequenceVertexSet (series.data.tree ci.succ.castSucc)) → ¬Nonempty
    (RevisitingExtensionCertificate series.data ci.castSucc) → ∀ (choice :
    MaximumDefectiveChoice G e0 (series.data.tree ci.succ.castSucc) (TashkinovStoredColors
    series.data ci.castSucc) (series.data.coloring ci.castSucc)), (∃ (rho :
    PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
    StableColoring (series.data.tree ci.succ.castSucc) (insert choice.color
    (TashkinovStoredColors series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
    (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (series.data.tree
    ci.succ.castSucc))) → ∀ (gamma : Fin k), ParallelExtensionColor series.data ci.castSucc
    choice.selected choice.vertex gamma → ∀ (secondStable : PartialEdgeColoring E k),
    IsProperEdgeColoring G secondStable → StableColoring (series.data.tree ci.succ.castSucc)
    (insert choice.color (TashkinovStoredColors series.data ci.castSucc)) choice.selected
    secondStable → TreeExit (series.data.tree ci.succ.castSucc) secondStable gamma
    choice.color choice.vertex → series.data.coloring ci.succ = TwoColorComponentSwap G
    secondStable gamma choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G
    (series.data.coloring ci.succ) → IsOneEdgeUncolored (series.data.coloring ci.succ) e0 →
    series.data.stored ci.succ = {choice.color, gamma} → series.data.connectingEdges ci.succ =
    {choice.edge} → series.data.kind ci.succ = some TashkinovExtensionKind.PE →
    series.data.chosenVertex ci.succ = some choice.vertex → series.data.outsideVertex ci.succ
    = some choice.otherEndpoint → series.data.delta ci.succ = some choice.color →
    series.data.gamma ci.succ = some gamma → TashkinovClosure (series.data.coloring ci.succ)
    (series.data.tree ci.succ.castSucc) (series.data.tree ci.succ.succ) →
    TreeSequenceInitialSegment (series.data.tree ci.succ.castSucc) (series.data.tree
    ci.succ.succ) → (series.data.tree ci.succ.castSucc).length < (series.data.tree
    ci.succ.succ).length → ci.succ = i.succ → ¬(series.data.kind ci.succ = some
    TashkinovExtensionKind.PE ∧ series.data.chosenVertex ci.succ = some x) → MissingColors G
    (series.data.coloring i.castSucc) x = MissingColors G (series.data.coloring ci.succ) x := by
  classical
  intro V E _ _ _ G k rounds e0 input series v i x hx ci previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
      gammaRule secondStable secondStableProper secondStableRelation exitWitness currentColoring
      currentProper currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension
      hj hno
  have hvals := congrArg Fin.val hj
  simp at hvals
  have hieq : ci = i := by apply Fin.ext; omega
  subst ci
  have hvneq : choice.vertex ≠ x := by
    intro he
    apply hno
    exact ⟨currentKind, currentVertex.trans (congrArg some he)⟩
  have hstable := (show StableColoring _ _ _ _ from
    secondStableRelation).2 x hx
  rw [currentColoring]
  rw [(choice.selectedStable.2 x hx).symm]
  rw [hstable.symm]
  have hmissing : gamma ∈ MissingColors G secondStable choice.vertex := by
    exact (secondStableRelation.2 choice.vertex choice.vertexDefective.1).symm ▸
      gammaRule.1
  have degree_one_of_missing := fun w hw ↦ TwoColorMissingVertexDegreeAtMostOne G secondStable
    secondStableProper gamma choice.color w hw
  have hdegree_one : (TwoColorIncidenceGraph G secondStable gamma choice.color).degree
      (Sum.inl choice.vertex) ≤ 1 :=
    degree_one_of_missing choice.vertex (Or.inl hmissing)
  have hcomponent := @helper_hcomponent_167 V E inferInstance inferInstance inferInstance G k rounds
      e0 input series i gamma secondStable secondStableProper choice exitWitness hmissing
      degree_one_of_missing hdegree_one
  have hyout : Sum.inl x ∉ TwoColorComponent G secondStable gamma choice.color
      (Sum.inl choice.vertex) := by
    intro hyC
    exact hvneq (hcomponent x hx hyC).symm
  unfold MissingColors
  have vertex_step := @helper_vertex_step_297 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series v i gamma secondStable choice
  have edge_out : ∀ e, Incident G x e →
      Sum.inr e ∉ TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    intro e he hec
    apply hyout
    exact vertex_step x e he hec
  ext c
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hc hec
    obtain ⟨e, he, hec⟩ := hec
    apply hc
    refine ⟨e, he, ?_⟩
    simpa [TwoColorComponentSwap, edge_out e he] using hec
  · intro hc hec
    obtain ⟨e, he, hec⟩ := hec
    apply hc
    refine ⟨e, he, ?_⟩
    simpa [TwoColorComponentSwap, edge_out e he] using hec

private theorem helper_one_step_55.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (_ _ : Fin rounds)
    (_ : V) (j : Fin (rounds + (1 : ℕ))) (i : Fin rounds), j = i.succ → ∀ x ∈
    TreeSequenceVertexSet (series.data.tree i.succ.castSucc), ¬(series.data.kind j = some
    TashkinovExtensionKind.PE ∧ series.data.chosenVertex j = some x) → MissingColors G
    (series.data.coloring i.castSucc) x = MissingColors G (series.data.coloring j) x := by
  classical
  intro V E _ _ _ G k rounds e0 input series q p v j i hj x hx hno
  cases series.certified j with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero i) hj.symm |>.elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    rw [currentColoring]
    exact ((show StableColoring _ _ _ _ from choice.selectedStable).2 x hx).symm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hvals := congrArg Fin.val hj
    simp at hvals
    have hieq : ci = i := by apply Fin.ext; omega
    subst ci
    rw [currentColoring]
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_71 V E inferInstance inferInstance inferInstance G k rounds e0
              input series v i x hx ci previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
              gammaRule secondStable secondStableProper secondStableRelation exitWitness
              currentColoring currentProper currentOneUncolored currentStored currentEdges
              currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
              orderedExtension strictExtension hj hno
private theorem helper_chain_383.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input :
    PartialEdgeColoring E k) (series : TashkinovSeries G k rounds e0 input) (_ _ : Fin
    rounds), (∀ (T T' : TreeSequence G e0), TreeSequenceInitialSegment T T' → ∀ x ∈
    TreeSequenceVertexSet T, x ∈ TreeSequenceVertexSet T') → (∀ (j : Fin (rounds + (1 : ℕ)))
    (i : Fin rounds), j = i.succ → ∀ x ∈ TreeSequenceVertexSet (series.data.tree
    i.succ.castSucc), ¬(series.data.kind j = some TashkinovExtensionKind.PE ∧
    series.data.chosenVertex j = some x) → MissingColors G (series.data.coloring i.castSucc) x
    = MissingColors G (series.data.coloring j) x) → (∀ (j : Fin (rounds + (1 : ℕ))) (i : Fin
    rounds), j = i.succ → TreeSequenceInitialSegment (series.data.tree i.succ.castSucc)
    (series.data.tree i.succ.succ)) → ∀ (a b : Fin rounds), (↑a : ℕ) ≤ (↑b : ℕ) → ∀ x ∈
    TreeSequenceVertexSet (series.data.tree a.succ.castSucc), (∀ (j : Fin rounds), (↑a : ℕ) ≤
    (↑j : ℕ) → (↑j : ℕ) ≤ (↑b : ℕ) → ¬(series.data.kind j.succ = some
    TashkinovExtensionKind.PE ∧ series.data.chosenVertex j.succ = some x)) → MissingColors G
    (series.data.coloring a.castSucc) x = MissingColors G (series.data.coloring b.succ) x := by
  classical
  intro V E _ _ _ G k rounds e0 input series q p vertex_transfer one_step next_segment a b hab x
      hxa hnu
  induction h : b.val - a.val using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases he : a.val = b.val
    · have habeq : a = b := Fin.ext he
      subst b
      exact one_step a.succ a rfl x hxa (by
        intro hh
        exact hnu a le_rfl le_rfl hh)
    · have halt : a.val + 1 ≤ b.val := by omega
      let mid : Fin rounds := ⟨a.val + 1, by omega⟩
      have hmidval : mid.val = a.val + 1 := rfl
      have hseg := next_segment a.succ a rfl
      have hmid : mid = ⟨a.val + 1, by omega⟩ := rfl
      have hxm : x ∈ TreeSequenceVertexSet (series.data.tree mid.succ.castSucc) := by
        apply vertex_transfer _ _ (show TreeSequenceInitialSegment
          (series.data.tree a.succ.castSucc)
          (series.data.tree mid.succ.castSucc) from ?_) x hxa
        have heq : mid.succ.castSucc = a.succ.succ := by
          apply Fin.ext
          simp [mid]
        rw [heq]
        exact hseg
      have hfirst := one_step a.succ a rfl x hxa (by
        intro hh
        exact hnu a le_rfl (by omega) hh)
      have hrest := ih (b.val - mid.val) (by omega) mid b (by omega) hxm (by
        intro j hj1 hj2
        exact hnu j (by omega) (by omega)) (by simp)
      exact hfirst.trans hrest

theorem HkuUnsupportedVertexColors {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input) (q p : Fin rounds)
    (v : V) (hpq : p.val ≤ q.val)
    (hv : v ∈ TreeSequenceVertexSet (series.data.tree p.succ.castSucc))
    (hunused : ∀ j : Fin rounds, p.val ≤ j.val → j.val ≤ q.val →
      ¬ (series.data.kind j.succ = some TashkinovExtensionKind.PE ∧
        series.data.chosenVertex j.succ = some v)) :
    MissingColors G (series.data.coloring p.castSucc) v =
      MissingColors G (series.data.coloring q.succ) v := by
  classical
  have vertex_transfer :
    ∀ (T T' : TreeSequence G e0), TreeSequenceInitialSegment T T' →
    ∀ x, x ∈ TreeSequenceVertexSet T → x ∈ TreeSequenceVertexSet T' := by
    intro T T' hseg x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    rcases hseg with ⟨hlen, hvertex, hedge⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, by
      simpa using (hvertex i)⟩
  have one_step := @helper_one_step_55 V E inferInstance inferInstance inferInstance G k rounds e0
      input series q p v
  have next_segment := @SharedFacts.UnsupportedVertexColors.next_segment V E inferInstance
      inferInstance inferInstance G k
      rounds e0 input series
  have chain := @helper_chain_383 V E inferInstance inferInstance inferInstance G k rounds e0 input
      series q p vertex_transfer one_step next_segment
  exact chain p q hpq v hv hunused

end GoldbergSeymour

end
