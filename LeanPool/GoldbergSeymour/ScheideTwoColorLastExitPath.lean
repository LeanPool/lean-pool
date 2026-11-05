/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideEnlargedClosed
public import LeanPool.GoldbergSeymour.ScheideLastExitPath

/-!
# Scheide Two Color Last Exit Path

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_continuation_207.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k),
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let X : Finset V := ScheideEnlargedVertexSet R;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 alpha;
    ∀ (_ : y0 ∈ X) (terminal : V) (p : H.Walk (Sum.inl y0) (Sum.inl terminal)) (_ : p.IsPath) (_ :
        {z : V ⊕ E | z ∈ p.support} = TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0)) (_ :
        terminal ∉ X),
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) := ({i : Fin (p.length + (1 : ℕ)) |
    ∃ v ∈ X, p.getVert (↑i : ℕ) = Sum.inl v} : Finset (Fin (p.length + (1 : ℕ))));
    ∀ (hinsideNonempty : insideIndices.Nonempty),
    let lastIndex : Fin (p.length + (1 : ℕ)) := insideIndices.max' hinsideNonempty;
    ∀ (lastInside : V) (_ : lastInside ∈ X) (_ : p.getVert (↑lastIndex : ℕ) = Sum.inl lastInside)
        (_ :
    ∀ (j : Fin (p.length + (1 : ℕ))), (↑lastIndex : ℕ) < (↑j : ℕ) →
    ∀ (v : V), p.getVert (↑j : ℕ) = Sum.inl v → v ∉ X) (_ : (↑lastIndex : ℕ) < p.length), Nonempty
        (ScheideLastExitPath G k e0 phi T C D R alpha) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha y0 X H hy0X terminal p hp hps hterminalOutside
      insideIndices hinsideNonempty lastIndex lastInside hlastInsideX hlastInsideAt hafter hlastLt
  let crossingIndex : Fin (p.length + 1) :=
    ⟨lastIndex.val + 1, by omega⟩
  have hcrossingAdj := p.adj_getVert_succ hlastLt
  rw [hlastInsideAt] at hcrossingAdj
  obtain ⟨crossing, hcrossingAt, hlastIncident, hcrossingColors⟩ :
      ∃ crossing : E,
        p.getVert crossingIndex.val = Sum.inr crossing ∧
        Incident G lastInside crossing ∧
        (phi crossing = some D.alpha0 ∨ phi crossing = some alpha) := by
    cases hnext : p.getVert crossingIndex.val with
    | inl v =>
        exfalso
        rw [hnext] at hcrossingAdj
        have hbad : H.Adj (Sum.inl lastInside) (Sum.inl v) := by
          simpa [crossingIndex] using hcrossingAdj
        simp [H, TwoColorIncidenceGraph] at hbad
    | inr crossing =>
        rw [hnext] at hcrossingAdj
        refine ⟨crossing, rfl, ?_⟩
        have hdata : H.Adj (Sum.inl lastInside) (Sum.inr crossing) := by
          simpa [crossingIndex] using hcrossingAdj
        simpa [H, TwoColorIncidenceGraph] using hdata
  have hcrossingLt : crossingIndex.val < p.length := by
    by_contra hn
    have heq : crossingIndex.val = p.length := by omega
    have hbad := hcrossingAt
    rw [heq, p.getVert_length] at hbad
    exact Sum.inl_ne_inr hbad
  let outsideIndex : Fin (p.length + 1) :=
    ⟨crossingIndex.val + 1, by omega⟩
  have houtsideAdj := p.adj_getVert_succ hcrossingLt
  rw [hcrossingAt] at houtsideAdj
  obtain ⟨firstOutside, hfirstOutsideAt, hfirstIncident⟩ :
      ∃ firstOutside : V,
        p.getVert outsideIndex.val = Sum.inl firstOutside ∧
        Incident G firstOutside crossing := by
    cases hnext : p.getVert outsideIndex.val with
    | inl v =>
        rw [hnext] at houtsideAdj
        refine ⟨v, rfl, ?_⟩
        have hdata : H.Adj (Sum.inr crossing) (Sum.inl v) := by
          simpa [outsideIndex] using houtsideAdj
        have hdata' : Incident G v crossing ∧
            (phi crossing = some D.alpha0 ∨ phi crossing = some alpha) := by
          simpa [H, TwoColorIncidenceGraph] using hdata
        exact hdata'.1
    | inr e =>
        exfalso
        rw [hnext] at houtsideAdj
        have hbad : H.Adj (Sum.inr crossing) (Sum.inr e) := by
          simpa [outsideIndex] using houtsideAdj
        simp [H, TwoColorIncidenceGraph] at hbad
  have hfirstOutsideX : firstOutside ∉ X := by
    apply hafter outsideIndex
    · dsimp [outsideIndex, crossingIndex]
      omega
    · exact hfirstOutsideAt
  have hverticesNe : lastInside ≠ firstOutside := by
    intro heq
    exact hfirstOutsideX (heq ▸ hlastInsideX)
  have hcrossingEnds : G.ends crossing = s(lastInside, firstOutside) :=
    (Sym2.mem_and_mem_iff hverticesNe).mp
      ⟨hlastIncident, hfirstIncident⟩
  have hcrossingBoundary : crossing ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨lastInside, hlastInsideX, firstOutside,
      hfirstOutsideX, hcrossingEnds⟩
  have hcrossingColor : phi crossing = some alpha := by
    rcases hcrossingColors with h0 | ha
    · have hclosed : ColoredVertexSetClosed G phi X := by
        unfold ColoredVertexSetClosed
        intro f c v hf hv hfc
        exact ScheideEnlargedClosed G k e0 phi T C D R
          (by simpa [X] using hf) (by simpa [X] using hv) hfc
      exact False.elim
        ((hclosed hcrossingBoundary hy0X h0) D.alpha0_missing_at_y0)
    · exact ha
  have hcrossingComponent : Sum.inr crossing ∈
      TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    rw [← hps]
    rw [← hcrossingAt]
    exact p.getVert_mem_support crossingIndex.val
  refine ⟨{
    terminal := terminal
    lastInside := lastInside
    firstOutside := firstOutside
    crossing := crossing
    path := p
    lastIndex := lastIndex
    pathSimple := hp
    pathSpans := hps
    terminalOutside := hterminalOutside
    lastInsideAt := hlastInsideAt
    lastInsideMem := hlastInsideX
    followingVertex := by
      change lastIndex.val + 2 ≤ p.length
      dsimp [crossingIndex] at hcrossingLt
      omega
    crossingAt := by
      simpa [crossingIndex] using hcrossingAt
    firstOutsideAt := by
      simpa [outsideIndex, crossingIndex] using hfirstOutsideAt
    firstOutsideNotMem := hfirstOutsideX
    afterLastOutside := hafter
    crossingBoundary := hcrossingBoundary
    crossingColor := hcrossingColor
    crossingComponent := hcrossingComponent
  }⟩

private theorem helper_continuation_273.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (R : (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) →
        ScheideReplacementData G k e0 phi T C D d) (alpha : Fin k) (_ :
    ∀ v ∈ ScheideEnlargedVertexSet R, alpha ∈ PresentColors G phi v),
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let X : Finset V := ScheideEnlargedVertexSet R;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 alpha;
    ∀ (_ : y0 ∈ X) (_ : D.alpha0 ≠ alpha) (terminalNode : V ⊕ E) (p : H.Walk (Sum.inl y0)
        terminalNode) (_ : p.IsPath) (_ : {z : V ⊕ E | z ∈ p.support} = TwoColorComponent G phi
        D.alpha0 alpha (Sum.inl y0)) (_ : (0 : ℕ) < p.length) (_ : terminalNode ≠ Sum.inl y0) (_ :
    ∀ (z : V ⊕ E), H.Adj terminalNode z → z = p.getVert (p.length - (1 : ℕ))), Nonempty
        (ScheideLastExitPath G k e0 phi T C D R alpha) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D R alpha hpresent y0 X H hy0X halphaNe terminalNode p hp hps
      hpPositive hterminalNe hterminalOnlyPrev
  have hterminalPrevAdj : H.Adj terminalNode
      (p.getVert (p.length - 1)) := by
    have hadj := p.adj_getVert_succ
      (show p.length - 1 < p.length by omega)
    rw [show p.length - 1 + 1 = p.length by omega,
      p.getVert_length] at hadj
    exact hadj.symm
  have hterminalDegree : @SimpleGraph.degree _ H terminalNode
      (Fintype.ofFinite _) = 1 := by
    apply (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H terminalNode
      (Fintype.ofFinite _)).mpr
    exact ⟨p.getVert (p.length - 1), hterminalPrevAdj,
      hterminalOnlyPrev⟩
  obtain ⟨terminal, hterminal⟩ : ∃ terminal : V,
      terminalNode = Sum.inl terminal := by
    cases hnode : terminalNode with
    | inl terminal => exact ⟨terminal, rfl⟩
    | inr e =>
        have hlastAdj : H.Adj (Sum.inr e)
            (p.getVert (p.length - 1)) := by
          simpa [hnode] using hterminalPrevAdj
        have heColor : phi e = some D.alpha0 ∨ phi e = some alpha := by
          cases hprev : p.getVert (p.length - 1) with
          | inl v =>
              rw [hprev] at hlastAdj
              have hdata : Incident G v e ∧
                  (phi e = some D.alpha0 ∨ phi e = some alpha) := by
                simpa [H, TwoColorIncidenceGraph] using hlastAdj
              exact hdata.2
          | inr f =>
              rw [hprev] at hlastAdj
              simp [H, TwoColorIncidenceGraph] at hlastAdj
        let v1 := (Quot.out (G.ends e)).1
        let v2 := (Quot.out (G.ends e)).2
        have hends : s(v1, v2) = G.ends e := Quot.out_eq _
        have hv1 : Incident G v1 e := by
          change v1 ∈ G.ends e
          rw [← hends]
          simp [v1, v2]
        have hv2 : Incident G v2 e := by
          change v2 ∈ G.ends e
          rw [← hends]
          simp [v1, v2]
        have hvne : v1 ≠ v2 := by
          intro heq
          apply G.loopless e v1
          rw [← hends, heq]
        have hadj1 : H.Adj (Sum.inr e) (Sum.inl v1) := by
          simpa [H, TwoColorIncidenceGraph] using
            (show Incident G v1 e ∧
              (phi e = some D.alpha0 ∨ phi e = some alpha) from
              ⟨hv1, heColor⟩)
        have hadj2 : H.Adj (Sum.inr e) (Sum.inl v2) := by
          simpa [H, TwoColorIncidenceGraph] using
            (show Incident G v2 e ∧
              (phi e = some D.alpha0 ∨ phi e = some alpha) from
              ⟨hv2, heColor⟩)
        have hdegreeTwo : 2 ≤ @SimpleGraph.degree _ H (Sum.inr e)
            (Fintype.ofFinite _) := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          let endpoints : Finset (Sum V E) := {Sum.inl v1, Sum.inl v2}
          have hsub : endpoints ⊆ @SimpleGraph.neighborFinset (Sum V E) H
              (Sum.inr e) (Fintype.ofFinite _) := by
            intro z hz
            simp only [endpoints, Finset.mem_insert,
              Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · simpa [SimpleGraph.mem_neighborFinset] using hadj1
            · simpa [SimpleGraph.mem_neighborFinset] using hadj2
          have hcard : 2 ≤ endpoints.card := by simp [endpoints, hvne]
          exact hcard.trans (Finset.card_le_card hsub)
        have hdegreeOne : @SimpleGraph.degree _ H (Sum.inr e)
            (Fintype.ofFinite _) = 1 := by
          rw [hnode] at hterminalDegree
          exact hterminalDegree
        omega
  subst terminalNode
  have hy0NeTerminal : y0 ≠ terminal := by
    intro heq
    apply hterminalNe
    simp [heq]
  have hterminalOutside : terminal ∉ X := by
    intro hterminalX
    have hterminalPresent : alpha ∈ PresentColors G phi terminal :=
      hpresent terminal hterminalX
    obtain ⟨et, het, hetColor⟩ : ∃ et : E,
        Incident G terminal et ∧ phi et = some alpha := by
      simpa [PresentColors] using hterminalPresent
    have hetAdj : H.Adj (Sum.inl terminal) (Sum.inr et) := by
      simpa [H, TwoColorIncidenceGraph] using
        (show Incident G terminal et ∧
          (phi et = some D.alpha0 ∨ phi et = some alpha) from
          ⟨het, Or.inr hetColor⟩)
    have hterminalUnique :=
      (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H
        (Sum.inl terminal) (Fintype.ofFinite _)).mp hterminalDegree
    have halpha0TerminalNotPresent :
        D.alpha0 ∉ PresentColors G phi terminal := by
      intro hpresent0
      obtain ⟨e0, he0, he0Color⟩ : ∃ e0' : E,
          Incident G terminal e0' ∧ phi e0' = some D.alpha0 := by
        simpa [PresentColors] using hpresent0
      have he0Adj : H.Adj (Sum.inl terminal) (Sum.inr e0) := by
        simpa [H, TwoColorIncidenceGraph] using
          (show Incident G terminal e0 ∧
            (phi e0 = some D.alpha0 ∨ phi e0 = some alpha) from
            ⟨he0, Or.inl he0Color⟩)
      have heq : (Sum.inr et : Sum V E) = Sum.inr e0 :=
        hterminalUnique.unique hetAdj he0Adj
      have hete0 : et = e0 := Sum.inr.inj heq
      have hcolors : (D.alpha0 : Fin k) = alpha := by
        exact Option.some.inj (he0Color.symm.trans (hete0 ▸ hetColor))
      exact halphaNe hcolors
    have halpha0TerminalMissing : D.alpha0 ∈
        MissingColors G phi terminal := by
      simpa [MissingColors] using halpha0TerminalNotPresent
    have hdisjoint := ScheideEnlargedElementary G k e0 phi T C D R
      hy0X hterminalX hy0NeTerminal
    exact (Finset.disjoint_left.mp hdisjoint)
      D.alpha0_missing_at_y0 halpha0TerminalMissing
  let insideIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun i => ∃ v ∈ X, p.getVert i.val = Sum.inl v
  have hinsideNonempty : insideIndices.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y0, hy0X, p.getVert_zero⟩
  let lastIndex : Fin (p.length + 1) :=
    insideIndices.max' hinsideNonempty
  have hlastMem : lastIndex ∈ insideIndices :=
    Finset.max'_mem insideIndices hinsideNonempty
  obtain ⟨lastInside, hlastInsideX, hlastInsideAt⟩ := by
    simpa only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using hlastMem
  have hafter : ∀ j : Fin (p.length + 1), lastIndex.val < j.val →
      ∀ v : V, p.getVert j.val = Sum.inl v → v ∉ X := by
    intro j hj v hjv hvX
    have hjMem : j ∈ insideIndices := by
      simp only [insideIndices, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨v, hvX, hjv⟩
    exact (not_le_of_gt hj) (Finset.le_max' insideIndices j hjMem)
  have hlastLt : lastIndex.val < p.length := by
    by_contra hn
    have heq : lastIndex.val = p.length := by omega
    have hvEq : lastInside = terminal := by
      apply Sum.inl.inj
      rw [← hlastInsideAt, heq, p.getVert_length]
    exact hterminalOutside (hvEq ▸ hlastInsideX)
  exact @helper_continuation_207 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@hy0X) (@terminal) (@p)
      (@hp) (@hps) (@hterminalOutside) (@hinsideNonempty) (@lastInside) (@hlastInsideX)
      (@hlastInsideAt) (@hafter) (@hlastLt)
private theorem helper_hterminalOnlyPrev_470.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (alpha : Fin k),
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 alpha;
    ∀ (_ : IsProperEdgeColoring G phi) (_ : @SimpleGraph.degree (Sum V E) H (@Sum.inl V E y0)
        (@Fintype.ofFinite (@Set.Elem (Sum V E) (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V
        E y0))) (@Subtype.finite (Sum V E) (@Finite.instSum V E (@Finite.of_fintype V inst)
        (@Finite.of_fintype E inst_1)) (@Membership.mem (Sum V E) (Set (Sum V E))
        (@Set.instMembership (Sum V E)) (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E
        y0))))) = (1 : ℕ)) (terminalNode : V ⊕ E) (p : H.Walk (Sum.inl y0) terminalNode) (_ :
        p.IsPath) (_ : {z : V ⊕ E | z ∈ p.support} = TwoColorComponent G phi D.alpha0 alpha
        (Sum.inl y0)) (_ : (0 : ℕ) < p.length) (_ : terminalNode ≠ Sum.inl y0) (z : V ⊕ E), H.Adj
        terminalNode z → z = p.getVert (p.length - (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T C D alpha y0 H hproper hy0Degree terminalNode p hp hps hpPositive
      hterminalNe z hz
  have hterminalComponent : terminalNode ∈
      TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    have hm : terminalNode ∈ {z | z ∈ p.support} := by
      change terminalNode ∈ p.support
      simpa only [p.getVert_length] using p.getVert_mem_support p.length
    rw [hps] at hm
    exact hm
  have hzComponent : z ∈
      TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    have hterminalMk :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
        hterminalComponent
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hz).symm.trans hterminalMk
  have hzSupport : z ∈ p.support := by
    change z ∈ {z | z ∈ p.support}
    rw [hps]
    exact hzComponent
  obtain ⟨j, hj, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzSupport
  have hjne : j ≠ p.length := by
    intro heq
    have hzterminal : z = terminalNode := by
      rw [← hj, heq, p.getVert_length]
    exact hz.ne hzterminal.symm
  have hjlt : j < p.length := Nat.lt_of_le_of_ne hjle hjne
  by_cases hjpenultimate : j + 1 = p.length
  · calc
      z = p.getVert j := hj.symm
      _ = p.getVert (p.length - 1) := by congr 1; omega
  by_cases hjzero : j = 0
  · by_cases hlengthOne : p.length = 1
    · rw [← hj, hjzero, hlengthOne]
    · have hfirstAdj : H.Adj (Sum.inl y0) (p.getVert 1) := by
        simpa only [p.getVert_zero] using
          p.adj_getVert_succ (by omega : 0 < p.length)
      have hrootTerminalAdj : H.Adj (Sum.inl y0) terminalNode := by
        have hz' := hz.symm
        rw [← hj, hjzero, p.getVert_zero] at hz'
        exact hz'
      have hunique := (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H
        (Sum.inl y0) (Fintype.ofFinite _)).mp hy0Degree
      have heq := hunique.unique hfirstAdj hrootTerminalAdj
      have hne : p.getVert 1 ≠ terminalNode := by
        intro hh
        have hidx := hp.getVert_injOn (by omega : 1 ≤ p.length)
          (le_rfl : p.length ≤ p.length)
          (hh.trans p.getVert_length.symm)
        omega
      exact (hne heq).elim
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hleft := p.adj_getVert_succ (show j - 1 < p.length by omega)
    rw [show j - 1 + 1 = j by omega] at hleft
    have hright := p.adj_getVert_succ hjlt
    have hthree : 3 ≤ @SimpleGraph.degree _ H (p.getVert j)
        (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset (Sum V E) :=
        {terminalNode, p.getVert (j - 1), p.getVert (j + 1)}
      have hs : s ⊆ @SimpleGraph.neighborFinset (Sum V E) H
          (p.getVert j) (Fintype.ofFinite _) := by
        intro w hw
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · have hz' := hz.symm
          rw [← hj] at hz'
          simpa [SimpleGraph.mem_neighborFinset] using hz'
        · simpa [SimpleGraph.mem_neighborFinset] using hleft.symm
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hterminalNotNeighbors : terminalNode ∉
          ({p.getVert (j - 1), p.getVert (j + 1)} : Finset (Sum V E)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        intro hh
        rcases hh with hh | hh
        · have hidx := hp.getVert_injOn
            (show j - 1 ≤ p.length by omega)
            (le_rfl : p.length ≤ p.length)
            (hh.symm.trans p.getVert_length.symm)
          omega
        · have hidx := hp.getVert_injOn
            (show j + 1 ≤ p.length by omega)
            (le_rfl : p.length ≤ p.length)
            (hh.symm.trans p.getVert_length.symm)
          exact hjpenultimate hidx
      have hneighborsNe : p.getVert (j - 1) ≠ p.getVert (j + 1) := by
        intro hh
        have hidx := hp.getVert_injOn
          (show j - 1 ≤ p.length by omega)
          (show j + 1 ≤ p.length by omega) hh
        omega
      have hcard : s.card = 3 := by
        simp [s, hterminalNotNeighbors, hneighborsNe]
      calc
        3 = s.card := hcard.symm
        _ ≤ _ := Finset.card_le_card hs
    have hdegree : @SimpleGraph.degree _ H (p.getVert j)
        (Fintype.ofFinite _) ≤ 2 := by
      simpa [H] using TwoColorIncidenceDegreeAtMostTwo G phi D.alpha0
        alpha hproper (p.getVert j)
    omega

theorem ScheideTwoColorLastExitPath {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (R : ∀ d : {delta // delta ∈ DefectiveColors G phi
      (TreeSequenceVertexSet T)}, ScheideReplacementData G k e0 phi T C D d)
    (alpha : Fin k)
    (hpresent : ∀ v ∈ ScheideEnlargedVertexSet R,
      alpha ∈ PresentColors G phi v) :
    Nonempty (ScheideLastExitPath G k e0 phi T C D R alpha) := by
  classical
  let y0 : V := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let X : Finset V := ScheideEnlargedVertexSet R
  let H := TwoColorIncidenceGraph G phi D.alpha0 alpha
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    refine ⟨⟨0, by omega⟩, ?_⟩
    change T.vertex ⟨0, by omega⟩ =
      C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
    exact C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  have hy0X : y0 ∈ X := by
    exact Finset.mem_union_left _ hy0T
  have halphaPresent : alpha ∈ PresentColors G phi y0 :=
    hpresent y0 hy0X
  have halpha0NotPresent : D.alpha0 ∉ PresentColors G phi y0 := by
    simpa [MissingColors] using D.alpha0_missing_at_y0
  have halphaNe : D.alpha0 ≠ alpha := by
    intro h
    exact halpha0NotPresent (h ▸ halphaPresent)
  obtain ⟨ea, hea, heaColor⟩ : ∃ ea : E,
      Incident G y0 ea ∧ phi ea = some alpha := by
    simpa [PresentColors] using halphaPresent
  have heaAdj : H.Adj (Sum.inl y0) (Sum.inr ea) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G y0 ea ∧
        (phi ea = some D.alpha0 ∨ phi ea = some alpha) from
        ⟨hea, Or.inr heaColor⟩)
  have hy0Degree : @SimpleGraph.degree _ H (Sum.inl y0)
      (Fintype.ofFinite _) = 1 := by
    apply (@SimpleGraph.degree_eq_one_iff_existsUnique_adj _ H
      (Sum.inl y0) (Fintype.ofFinite _)).mpr
    refine ⟨Sum.inr ea, heaAdj, ?_⟩
    intro z hz
    cases z with
    | inl v =>
        simp [H, TwoColorIncidenceGraph] at hz
    | inr f =>
        have hf : Incident G y0 f ∧
            (phi f = some D.alpha0 ∨ phi f = some alpha) := by
          simpa [H, TwoColorIncidenceGraph] using hz
        have hfColor : phi f = some alpha := by
          rcases hf.2 with hf0 | hfa
          · exfalso
            apply halpha0NotPresent
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
              true_and]
            exact ⟨f, hf.1, hf0⟩
          · exact hfa
        have hfeq : f = ea := by
          by_contra hne
          exact (hproper hne ⟨y0, hf.1, hea⟩ hfColor) heaColor
        exact congrArg Sum.inr hfeq
  obtain ⟨a, b, q, hq, hqs⟩ :=
    TwoColorComponentSpanningPath G phi D.alpha0 alpha hproper
      (Sum.inl y0)
  have hy0Component : Sum.inl y0 ∈
      TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hy0Support : Sum.inl y0 ∈ q.support := by
    change Sum.inl y0 ∈ {z | z ∈ q.support}
    rw [hqs]
    exact hy0Component
  have hy0Leaf : H.neighborSet (Sum.inl y0) |>.Subsingleton := by
    let : Fintype (H.neighborSet (Sum.inl y0)) := Fintype.ofFinite _
    intro z hz w hw
    have hc : Fintype.card (H.neighborSet (Sum.inl y0)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact hy0Degree.le
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hc ⟨z, hz⟩ ⟨w, hw⟩)
  have hy0End : (Sum.inl y0 : Sum V E) = a ∨ Sum.inl y0 = b := by
    by_contra hn
    push Not at hn
    exact (hq.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hy0Leaf) hy0Support
  obtain ⟨terminalNode, p, hp, hps⟩ :
      ∃ (w : Sum V E) (p : H.Walk (Sum.inl y0) w),
        p.IsPath ∧ {z | z ∈ p.support} =
          TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    rcases hy0End with ha | hb
    · subst a
      exact ⟨b, q, hq, hqs⟩
    · subst b
      refine ⟨a, q.reverse, hq.reverse, ?_⟩
      ext z
      rw [SimpleGraph.Walk.support_reverse]
      simpa using Set.ext_iff.mp hqs z
  have heaComponent : Sum.inr ea ∈
      TwoColorComponent G phi D.alpha0 alpha (Sum.inl y0) := by
    apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (by simpa [H] using heaAdj)).symm
  have hpPositive : 0 < p.length := by
    by_contra hn
    have hzero : p.length = 0 := Nat.eq_zero_of_not_pos hn
    have heaSupport : Sum.inr ea ∈ p.support := by
      change Sum.inr ea ∈ {z | z ∈ p.support}
      rw [hps]
      exact heaComponent
    obtain ⟨j, hj, hjle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp heaSupport
    have hjzero : j = 0 := by omega
    have : (Sum.inr ea : Sum V E) = Sum.inl y0 := by
      rw [← hj, hjzero, p.getVert_zero]
    exact Sum.inr_ne_inl this
  have hterminalNe : terminalNode ≠ Sum.inl y0 := by
    intro h
    have hverts : p.getVert 0 = p.getVert p.length := by
      rw [p.getVert_zero, p.getVert_length, h]
    have hidx := hp.getVert_injOn (by omega : 0 ≤ p.length)
      (le_rfl : p.length ≤ p.length) hverts
    omega
  have hterminalOnlyPrev := @helper_hterminalOnlyPrev_470 (@V) (@E) inferInstance inferInstance
       inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@alpha) (@hproper)
      (@hy0Degree) (@terminalNode) (@p) (@hp) (@hps) (@hpPositive) (@hterminalNe)
  exact @helper_continuation_273 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@R) (@alpha) (@hpresent) (@hy0X)
      (@halphaNe) (@terminalNode) (@p) (@hp) (@hps) (@hpPositive) (@hterminalNe)
      (@hterminalOnlyPrev)
end GoldbergSeymour

end
