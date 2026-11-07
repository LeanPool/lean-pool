/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesColoringProperties

public import LeanPool.GoldbergSeymour.SameColorSeriesPreserved
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TwoColorComponentCycle

/-!
# Stable Series Cycle Component Transport

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hpairControl_97.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon terminal : Fin rounds) (gamma
        delta : Fin k), series.data.kind t.succ = some TashkinovExtensionKind.PE →
        series.data.gamma t.succ = some gamma → series.data.delta t.succ = some delta →
    ∀ (_ : PartialEdgeColoring E k) (z : V ⊕ E), TwoColorComponentCycle G (series.data.coloring
        t.succ) gamma delta z → (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (series.data.coloring t.succ) gamma delta z → w ∈
        TreeSequenceVertexSet (series.data.tree epsilon.succ.castSucc)) →
    let _ : PartialEdgeColoring E k := series.data.coloring t.succ;
    let _ : PartialEdgeColoring E k := series.data.coloring terminal.succ; (
    ∀ (q : Fin rounds),
    ∀ c ∈ series.data.stored q.succ, c ∈ TreeMissingColors (series.data.coloring q.succ)
        (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.succ) →
    ∀ (c : Fin k), c = gamma ∨ c = delta → c ∈ TreeMissingColors (series.data.coloring t.succ)
        (series.data.tree t.succ.castSucc) ∪ TashkinovStoredColors series.data t.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal gamma delta htKind htGamma
      htDelta sigma z hcycle hcontained oldColoring terminalColoring currentStoredControl c hc
  have cert := series.certified t.succ
  generalize hslot : t.succ = slot at cert
  cases cert with
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
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      rw [currentKind] at htKind
      simp at htKind
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = t := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      have hgamma : actualGamma = gamma :=
        Option.some.inj (currentGamma.symm.trans htGamma)
      have hdelta : choice.color = delta :=
        Option.some.inj (currentDelta.symm.trans htDelta)
      apply currentStoredControl t c
      rw [currentStored]
      rcases hc with rfl | rfl
      · simp [hgamma]
      · simp [hdelta]
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = t := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      rw [currentKind] at htKind
      simp at htKind

private theorem helper_controlPrevious_161.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t _ terminal : Fin rounds),
    ∀ c ∈ TreeMissingColors (series.data.coloring t.succ) (series.data.tree t.succ.castSucc) ∪
        TashkinovStoredColors series.data t.succ,
    ∀ (n : ℕ), (↑t : ℕ) + (1 : ℕ) ≤ n → n ≤ (↑terminal : ℕ) →
    ∀ (q : Fin rounds), (↑q : ℕ) = n → c ∈ TreeMissingColors (series.data.coloring q.castSucc)
        (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal c hc n htn
  induction n, htn using Nat.le_induction with
  | base =>
      intro hn q hq
      have hcolor : q.castSucc = t.succ := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      have htree : q.succ.castSucc = t.succ.succ := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      simpa [hcolor, htree] using
        (HkuMissingStoredMonotone G k rounds e0 input series t).2 hc
  | succ n hn ih =>
      intro hnterminal q hq
      let r : Fin rounds := ⟨n, by omega⟩
      have hold := ih (by omega) r rfl
      have hcurrent :=
        (HkuMissingStoredMonotone G k rounds e0 input series r).1 hold
      have hnext :=
        (HkuMissingStoredMonotone G k rounds e0 input series r).2 hcurrent
      have hcolor : q.castSucc = r.succ := by
        apply Fin.ext
        simp [r, hq]
      have htree : q.succ.castSucc = r.succ.succ := by
        apply Fin.ext
        simp [r, hq]
      simpa [hcolor, htree] using hnext

private theorem helper_reColoring_228.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (_ _ _ r : Fin rounds),
    series.data.kind r.succ = some TashkinovExtensionKind.RE →
    series.data.coloring r.succ = series.data.coloring r.castSucc := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal r hr
  have cert := series.certified r.succ
  generalize hslot : r.succ = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      exact (Fin.succ_ne_zero r hslot).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      rw [currentKind] at hr
      simp at hr
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      rw [currentKind] at hr
      simp at hr
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa [hslot] using currentColoring

private theorem helper_stepSegment_310.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (_ _ _ r : Fin rounds),
    TreeSequenceInitialSegment (series.data.tree r.succ.castSucc)
      (series.data.tree r.succ.succ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal r
  have cert := series.certified r.succ
  generalize hslot : r.succ = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      exact (Fin.succ_ne_zero r hslot).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa [hslot] using orderedExtension
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa [hslot] using orderedExtension
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i = r := by
        apply Fin.ext
        have := congrArg Fin.val hslot
        simp only [Fin.val_succ] at this
        omega
      subst i
      simpa [hslot] using orderedExtension

private theorem helper_terminalClosed_552.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t terminal : Fin rounds) (gamma delta :
        Fin k) (z : V ⊕ E),
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G oldColoring gamma delta;
    let terminalGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G terminalColoring gamma
        delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G oldColoring gamma delta z; IsProperEdgeColoring G
        terminalColoring →
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ (x : V ⊕ E), x ∈ cycle.walk.support ↔ x ∈ TwoColorComponent G (series.data.coloring t.succ)
        gamma delta z) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → oldColoring f = some gamma ∨ oldColoring f = some
        delta) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → terminalColoring f = oldColoring f) →
    ∀ {a b : V ⊕ E}, a ∈ cycle.walk.support → terminalGraph.Adj a b → b ∈ cycle.walk.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta z oldColoring
      terminalColoring oldGraph terminalGraph oldComponent hterminalProper cycle hfull
      edgeOldActive edgeSeriesPreserved a b ha hab
  cases a with
  | inl v =>
      cases b with
      | inl w => simp [terminalGraph, TwoColorIncidenceGraph] at hab
      | inr f =>
          have hfData : Incident G v f ∧
              (terminalColoring f = some gamma ∨
                terminalColoring f = some delta) := by
            simpa [terminalGraph, TwoColorIncidenceGraph] using hab
          let rotated := cycle.walk.rotate (Sum.inl v) ha
          have hrotated : rotated.IsCycle := cycle.isCycle.rotate ha
          have hfirst : oldGraph.Adj (Sum.inl v) rotated.snd := by
            simpa [oldGraph] using rotated.adj_snd hrotated.not_nil
          have hlast : oldGraph.Adj (Sum.inl v) rotated.penultimate := by
            simpa [oldGraph] using
              (rotated.adj_penultimate hrotated.not_nil).symm
          cases hfirstNode : rotated.snd with
          | inl u =>
              rw [hfirstNode] at hfirst
              simp [oldGraph, TwoColorIncidenceGraph] at hfirst
          | inr e1 =>
              rw [hfirstNode] at hfirst
              cases hlastNode : rotated.penultimate with
              | inl u =>
                  rw [hlastNode] at hlast
                  simp [oldGraph, TwoColorIncidenceGraph] at hlast
              | inr e2 =>
                  rw [hlastNode] at hlast
                  have he1Data : Incident G v e1 ∧
                      (oldColoring e1 = some gamma ∨
                        oldColoring e1 = some delta) := by
                    simpa [oldGraph, TwoColorIncidenceGraph] using hfirst
                  have he2Data : Incident G v e2 ∧
                      (oldColoring e2 = some gamma ∨
                        oldColoring e2 = some delta) := by
                    simpa [oldGraph, TwoColorIncidenceGraph] using hlast
                  have hvComponent : Sum.inl v ∈ oldComponent :=
                    (hfull (Sum.inl v)).1 ha
                  have he1Component : Sum.inr e1 ∈ oldComponent := by
                    change oldGraph.connectedComponentMk (Sum.inr e1) =
                      oldGraph.connectedComponentMk z
                    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                      hfirst).symm.trans hvComponent
                  have he2Component : Sum.inr e2 ∈ oldComponent := by
                    change oldGraph.connectedComponentMk (Sum.inr e2) =
                      oldGraph.connectedComponentMk z
                    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                      hlast).symm.trans hvComponent
                  have he1Support := (hfull (Sum.inr e1)).2 he1Component
                  have he2Support := (hfull (Sum.inr e2)).2 he2Component
                  have he1Terminal : terminalColoring e1 = oldColoring e1 :=
                    edgeSeriesPreserved e1 he1Support
                  have he2Terminal : terminalColoring e2 = oldColoring e2 :=
                    edgeSeriesPreserved e2 he2Support
                  have he1Active : terminalColoring e1 = some gamma ∨
                      terminalColoring e1 = some delta := by
                    rw [he1Terminal]
                    exact he1Data.2
                  have he2Active : terminalColoring e2 = some gamma ∨
                      terminalColoring e2 = some delta := by
                    rw [he2Terminal]
                    exact he2Data.2
                  have he12 : e1 ≠ e2 := by
                    intro heq
                    apply hrotated.snd_ne_penultimate
                    rw [hfirstNode, hlastNode, heq]
                  have hmatch : f = e1 ∨ f = e2 := by
                    rcases hfData.2 with hfg | hfd
                    · rcases he1Active with he1g | he1d
                      · left
                        by_contra hne
                        exact (hterminalProper hne
                          ⟨v, hfData.1, he1Data.1⟩ hfg) he1g
                      · have he2g : terminalColoring e2 = some gamma :=
                          he2Active.resolve_right (by
                            intro he2d
                            exact (hterminalProper he12
                              ⟨v, he1Data.1, he2Data.1⟩ he1d) he2d)
                        right
                        by_contra hne
                        exact (hterminalProper hne
                          ⟨v, hfData.1, he2Data.1⟩ hfg) he2g
                    · rcases he1Active with he1g | he1d
                      · have he2d : terminalColoring e2 = some delta :=
                          he2Active.resolve_left (by
                            intro he2g
                            exact (hterminalProper he12
                              ⟨v, he1Data.1, he2Data.1⟩ he1g) he2g)
                        right
                        by_contra hne
                        exact (hterminalProper hne
                          ⟨v, hfData.1, he2Data.1⟩ hfd) he2d
                      · left
                        by_contra hne
                        exact (hterminalProper hne
                          ⟨v, hfData.1, he1Data.1⟩ hfd) he1d
                  rcases hmatch with rfl | rfl
                  · exact he1Support
                  · exact he2Support
  | inr e =>
      cases b with
      | inl v =>
          have hdata : Incident G v e ∧
              (terminalColoring e = some gamma ∨
                terminalColoring e = some delta) := by
            simpa [terminalGraph, TwoColorIncidenceGraph] using hab
          have heActive := edgeOldActive e ha
          have hadjOld : oldGraph.Adj (Sum.inr e) (Sum.inl v) := by
            simpa [oldGraph, TwoColorIncidenceGraph] using ⟨hdata.1, heActive⟩
          have heComponent : Sum.inr e ∈ oldComponent :=
            (hfull (Sum.inr e)).1 ha
          have hvComponent : Sum.inl v ∈ oldComponent := by
            change oldGraph.connectedComponentMk (Sum.inl v) =
              oldGraph.connectedComponentMk z
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hadjOld).symm.trans heComponent
          exact (hfull (Sum.inl v)).2 hvComponent
      | inr f => simp [terminalGraph, TwoColorIncidenceGraph] at hab

private theorem helper_sigmaClosed_817.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t terminal : Fin rounds) (gamma delta :
        Fin k) (sigma : PartialEdgeColoring E k),
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let terminalTree : TreeSequence G e0 := series.data.tree terminal.succ.castSucc;
    let terminalStored : Finset (Fin k) := TashkinovStoredColors series.data terminal.succ;
    let terminalGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G terminalColoring gamma
        delta;
    let sigmaGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma gamma delta;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ {a b : V ⊕ E}, a ∈ cycle.walk.support → terminalGraph.Adj a b → b ∈ cycle.walk.support) →
        gamma ∈ TreeMissingColors sigma terminalTree ∪ terminalStored → delta ∈ TreeMissingColors
        sigma terminalTree ∪ terminalStored → StableColoring terminalTree terminalStored sigma
        terminalColoring → (
    ∀ (v : V), Sum.inl v ∈ cycle.walk.support → v ∈ TreeSequenceVertexSet terminalTree) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → sigma f = terminalColoring f) →
    ∀ {a b : V ⊕ E}, a ∈ cycle.walk.support → sigmaGraph.Adj a b → b ∈ cycle.walk.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta sigma terminalColoring
      terminalTree terminalStored terminalGraph sigmaGraph cycle terminalClosed hgammaSigma
      hdeltaSigma hsigmaReverse cycleVertexTerminalTree edgeSigmaPreserved a b ha hab
  cases a with
  | inl v =>
      cases b with
      | inl w => simp [sigmaGraph, TwoColorIncidenceGraph] at hab
      | inr f =>
          have hdata : Incident G v f ∧
              (sigma f = some gamma ∨ sigma f = some delta) := by
            simpa [sigmaGraph, TwoColorIncidenceGraph] using hab
          have hvTree := cycleVertexTerminalTree v ha
          rcases hdata.2 with hgamma | hdelta
          · have hreverse := hsigmaReverse.1 f
              ⟨v, hvTree, hdata.1⟩
              ⟨gamma, hgammaSigma, hgamma⟩
            apply terminalClosed ha
            simpa [terminalGraph, TwoColorIncidenceGraph, hreverse, hgamma]
              using hdata.1
          · have hreverse := hsigmaReverse.1 f
              ⟨v, hvTree, hdata.1⟩
              ⟨delta, hdeltaSigma, hdelta⟩
            apply terminalClosed ha
            simpa [terminalGraph, TwoColorIncidenceGraph, hreverse, hdelta]
              using hdata.1
  | inr e =>
      cases b with
      | inl v =>
          have hdata : Incident G v e ∧
              (sigma e = some gamma ∨ sigma e = some delta) := by
            simpa [sigmaGraph, TwoColorIncidenceGraph] using hab
          have hsigma := edgeSigmaPreserved e ha
          apply terminalClosed ha
          simpa [terminalGraph, TwoColorIncidenceGraph, ← hsigma] using hdata
      | inr f => simp [sigmaGraph, TwoColorIncidenceGraph] at hab

private theorem helper_coloringAlong_644.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon _ : Fin rounds), (
    ∀ (r : Fin rounds), (↑t : ℕ) < (↑r : ℕ) → (↑r : ℕ) < (↑epsilon : ℕ) → series.data.kind r.succ
        = some TashkinovExtensionKind.RE) →
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ; (
    ∀ (r : Fin rounds), series.data.kind r.succ = some TashkinovExtensionKind.RE →
        series.data.coloring r.succ = series.data.coloring r.castSucc) →
    ∀ (n : ℕ), (↑t : ℕ) + (1 : ℕ) ≤ n → n ≤ (↑epsilon : ℕ) →
    ∀ (q : Fin (rounds + (1 : ℕ))), (↑q : ℕ) = n → series.data.coloring q = oldColoring := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal hintervening oldColoring
      reColoring n htn
  induction n, htn using Nat.le_induction with
  | base =>
      intro hn q hq
      have hqeq : q = t.succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      simp [oldColoring, hqeq]
  | succ n hn ih =>
      intro hnepsilon q hq
      have hnlt : n < epsilon.val := by omega
      have hnt : t.val < n := by omega
      let r : Fin rounds := ⟨n, by omega⟩
      have hrKind := hintervening r (by simpa [r]) (by simpa [r])
      have hrColor := reColoring r hrKind
      have hqeq : q = r.succ := by
        apply Fin.ext
        simp [r, hq]
      calc
        series.data.coloring q = series.data.coloring r.succ := by rw [hqeq]
        _ = series.data.coloring r.castSucc := hrColor
        _ = oldColoring := ih (by omega) r.castSucc rfl

private theorem helper_vertexToTerminal_689.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (_ epsilon terminal : Fin rounds),
        (↑epsilon : ℕ) ≤ (↑terminal : ℕ) →
    let epsilonTree : TreeSequence G e0 := series.data.tree epsilon.succ.castSucc;
    let terminalTree : TreeSequence G e0 := series.data.tree terminal.succ.castSucc; (
    ∀ (r : Fin rounds), TreeSequenceInitialSegment (series.data.tree r.succ.castSucc)
        (series.data.tree r.succ.succ)) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → TreeSequenceVertexSet epsilonTree ⊆ TreeSequenceVertexSet
        terminalTree := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal hepsilonTerminal epsilonTree
      terminalTree stepSegment vertexTransfer v hv
  have carry : ∀ n : ℕ, epsilon.val ≤ n → n ≤ terminal.val →
      ∀ q : Fin rounds, q.val = n →
        v ∈ TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
    intro n hen
    induction n, hen using Nat.le_induction with
    | base =>
        intro hn q hq
        have hqeq : q = epsilon := by apply Fin.ext; omega
        simpa [epsilonTree, hqeq] using hv
    | succ n hn ih =>
        intro hnterminal q hq
        let r : Fin rounds := ⟨n, by omega⟩
        have hold := ih (by omega) r rfl
        have hnext := vertexTransfer (stepSegment r) hold
        have htree : q.succ.castSucc = r.succ.succ := by
          apply Fin.ext
          simp [r, hq]
        simpa [htree] using hnext
  simpa [terminalTree] using carry terminal.val hepsilonTerminal le_rfl terminal rfl

private theorem helper_edgeSeriesPreserved_763.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon terminal : Fin rounds) (gamma
        delta : Fin k), (↑epsilon : ℕ) ≤ (↑terminal : ℕ) →
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let epsilonTree : TreeSequence G e0 := series.data.tree epsilon.succ.castSucc; gamma ∈
        TreeMissingColors (series.data.coloring epsilon.castSucc) epsilonTree ∪
        TashkinovStoredColors series.data epsilon.castSucc → delta ∈ TreeMissingColors
        (series.data.coloring epsilon.castSucc) epsilonTree ∪ TashkinovStoredColors series.data
        epsilon.castSucc → series.data.coloring epsilon.castSucc = oldColoring →
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → oldColoring f = some gamma ∨ oldColoring f = some
        delta) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → TreeIncidentEdge epsilonTree f) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → f ∈ InternalEdges G (TreeSequenceVertexSet
        epsilonTree)) →
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → terminalColoring f = oldColoring f := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal gamma delta hepsilonTerminal
      oldColoring terminalColoring epsilonTree hgammaEpsilon hdeltaEpsilon hepsilonColoring cycle
      edgeOldActive edgeIncidentEpsilon edgeInternalEpsilon f hf
  have hfIncident := edgeIncidentEpsilon f hf
  have hfInternal := edgeInternalEpsilon f hf
  rcases edgeOldActive f hf with hgamma | hdelta
  · have hepsilonGamma : series.data.coloring epsilon.castSucc f =
        some gamma := by
      rw [hepsilonColoring]
      exact hgamma
    have h := (SameColorSeriesPreserved G k rounds e0 input series
      epsilon terminal hepsilonTerminal f gamma hfIncident hepsilonGamma
      hgammaEpsilon).2 hfInternal
    have hterminal : terminalColoring f =
        series.data.coloring epsilon.castSucc f := by
      simpa [terminalColoring] using h
    exact hterminal.trans (congrFun hepsilonColoring f)
  · have hepsilonDelta : series.data.coloring epsilon.castSucc f =
        some delta := by
      rw [hepsilonColoring]
      exact hdelta
    have h := (SameColorSeriesPreserved G k rounds e0 input series
      epsilon terminal hepsilonTerminal f delta hfIncident hepsilonDelta
      hdeltaEpsilon).2 hfInternal
    have hterminal : terminalColoring f =
        series.data.coloring epsilon.castSucc f := by
      simpa [terminalColoring] using h
    exact hterminal.trans (congrFun hepsilonColoring f)

private theorem helper_terminalEdgeTransfer_791.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (t terminal : Fin rounds) (gamma delta : Fin k),
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G oldColoring gamma delta;
    let terminalGraph : SimpleGraph (V ⊕ E) :=
      TwoColorIncidenceGraph G terminalColoring gamma delta;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta),
    (∀ (f : E), Sum.inr f ∈ cycle.walk.support → terminalColoring f = oldColoring f) →
    ∀ edge ∈ cycle.walk.edges,
    edge ∈ terminalGraph.edgeSet := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta oldColoring terminalColoring
      oldGraph terminalGraph cycle edgeSeriesPreserved edge hedge
  induction edge using Sym2.inductionOn with
  | _ a b =>
      have haSupport := cycle.walk.fst_mem_support_of_mem_edges hedge
      have hbSupport := cycle.walk.snd_mem_support_of_mem_edges hedge
      have habOld : oldGraph.Adj a b := by
        simpa [oldGraph] using cycle.walk.edges_subset_edgeSet hedge
      cases a with
      | inl v =>
          cases b with
          | inl w => simp [oldGraph, TwoColorIncidenceGraph] at habOld
          | inr f =>
              have hdata : Incident G v f ∧
                  (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                simpa [oldGraph, TwoColorIncidenceGraph] using habOld
              have hcolor := edgeSeriesPreserved f hbSupport
              simpa [terminalGraph, TwoColorIncidenceGraph, hcolor] using hdata
      | inr f =>
          cases b with
          | inl v =>
              have hdata : Incident G v f ∧
                  (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                simpa [oldGraph, TwoColorIncidenceGraph] using habOld
              have hcolor := edgeSeriesPreserved f haSupport
              simpa [terminalGraph, TwoColorIncidenceGraph, hcolor] using hdata
          | inr g => simp [oldGraph, TwoColorIncidenceGraph] at habOld

private theorem helper_sigmaEdgeTransfer_936.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (t terminal : Fin rounds) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G oldColoring gamma delta;
    let sigmaGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma gamma delta;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta),
    (∀ (f : E), Sum.inr f ∈ cycle.walk.support → terminalColoring f = oldColoring f) →
    (∀ (f : E), Sum.inr f ∈ cycle.walk.support → sigma f = terminalColoring f) →
    ∀ edge ∈ cycle.walk.edges,
    edge ∈ sigmaGraph.edgeSet := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta sigma oldColoring
      terminalColoring oldGraph sigmaGraph cycle edgeSeriesPreserved edgeSigmaPreserved edge hedge
  induction edge using Sym2.inductionOn with
  | _ a b =>
      have haSupport := cycle.walk.fst_mem_support_of_mem_edges hedge
      have hbSupport := cycle.walk.snd_mem_support_of_mem_edges hedge
      have habOld : oldGraph.Adj a b := by
        simpa [oldGraph] using cycle.walk.edges_subset_edgeSet hedge
      cases a with
      | inl v =>
          cases b with
          | inl w => simp [oldGraph, TwoColorIncidenceGraph] at habOld
          | inr f =>
              have hdata : Incident G v f ∧
                  (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                simpa [oldGraph, TwoColorIncidenceGraph] using habOld
              have hseries := edgeSeriesPreserved f hbSupport
              have hsigma := edgeSigmaPreserved f hbSupport
              simpa [sigmaGraph, TwoColorIncidenceGraph, hsigma, hseries] using hdata
      | inr f =>
          cases b with
          | inl v =>
              have hdata : Incident G v f ∧
                  (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
                simpa [oldGraph, TwoColorIncidenceGraph] using habOld
              have hseries := edgeSeriesPreserved f haSupport
              have hsigma := edgeSigmaPreserved f haSupport
              simpa [sigmaGraph, TwoColorIncidenceGraph, hsigma, hseries] using hdata
          | inr g => simp [oldGraph, TwoColorIncidenceGraph] at habOld

private theorem helper_currentStoredControl_788.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (q : Fin rounds),
    ∀ c ∈ series.data.stored q.succ, c ∈ TreeMissingColors (series.data.coloring q.succ)
        (series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors series.data q.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series q c hc
  by_cases hm : c ∈ TreeMissingColors (series.data.coloring q.succ)
      (series.data.tree q.succ.castSucc)
  · exact Finset.mem_union.mpr (Or.inl hm)
  · apply Finset.mem_union.mpr
    right
    unfold TashkinovStoredColors
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Fin.castSucc_succ,
  Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨⟨q.succ, ?_⟩, ?_⟩
    · simpa using hc
    · simpa using hm

private theorem helper_edgeIncidentEpsilon_899.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon : Fin rounds) (gamma delta : Fin
        k) (z : V ⊕ E), (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (series.data.coloring t.succ) gamma delta z → w ∈
        TreeSequenceVertexSet (series.data.tree epsilon.succ.castSucc)) →
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let epsilonTree : TreeSequence G e0 := series.data.tree epsilon.succ.castSucc;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G oldColoring gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G oldColoring gamma delta z;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ (x : V ⊕ E), x ∈ cycle.walk.support ↔ x ∈ TwoColorComponent G (series.data.coloring t.succ)
        gamma delta z) →
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → TreeIncidentEdge epsilonTree f := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon gamma delta z hcontained oldColoring
      epsilonTree oldGraph oldComponent cycle hfull f hf
  obtain ⟨node, hnode, hadj⟩ :=
    SimpleGraph.adj_of_mem_walk_support cycle.walk cycle.isCycle.not_nil hf
  cases node with
  | inl v =>
      have hdata : Incident G v f ∧
          (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
        simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj
      have hvComponent : Sum.inl v ∈ oldComponent :=
        (hfull (Sum.inl v)).1 hnode
      exact ⟨v, hcontained v (by simpa [oldComponent, oldColoring] using hvComponent),
        hdata.1⟩
  | inr e =>
      simp [TwoColorIncidenceGraph] at hadj

private theorem helper_edgeInternalEpsilon_915.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon : Fin rounds) (gamma delta : Fin
        k) (z : V ⊕ E), (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (series.data.coloring t.succ) gamma delta z → w ∈
        TreeSequenceVertexSet (series.data.tree epsilon.succ.castSucc)) →
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let epsilonTree : TreeSequence G e0 := series.data.tree epsilon.succ.castSucc;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G oldColoring gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G oldColoring gamma delta z;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ (x : V ⊕ E), x ∈ cycle.walk.support ↔ x ∈ TwoColorComponent G (series.data.coloring t.succ)
        gamma delta z) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → oldColoring f = some gamma ∨ oldColoring f = some
        delta) →
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → f ∈ InternalEdges G (TreeSequenceVertexSet
        epsilonTree) := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon gamma delta z hcontained oldColoring
      epsilonTree oldGraph oldComponent cycle hfull edgeOldActive f hf
  have hfActive := edgeOldActive f hf
  simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro v hvf
  have hadj : oldGraph.Adj (Sum.inl v) (Sum.inr f) := by
    simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using ⟨hvf, hfActive⟩
  have hfComponent : Sum.inr f ∈ oldComponent := (hfull (Sum.inr f)).1 hf
  have hvComponent : Sum.inl v ∈ oldComponent := by
    change oldGraph.connectedComponentMk (Sum.inl v) =
      oldGraph.connectedComponentMk z
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).trans hfComponent
  exact hcontained v (by simpa [oldComponent, oldColoring] using hvComponent)

private theorem helper_terminalComponentSubset_946.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t terminal : Fin rounds) (gamma delta :
        Fin k) (z : V ⊕ E),
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let terminalGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G terminalColoring gamma
        delta;
    let terminalComponent : Set (V ⊕ E) := TwoColorComponent G terminalColoring gamma delta z;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ {a b : V ⊕ E}, a ∈ cycle.walk.support → terminalGraph.Adj a b → b ∈ cycle.walk.support) → z
        ∈ cycle.walk.support → terminalComponent ⊆ {x : V ⊕ E | x ∈ cycle.walk.support} := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta z terminalColoring
      terminalGraph terminalComponent cycle terminalClosed hzSupport x hx
  change terminalGraph.connectedComponentMk x =
    terminalGraph.connectedComponentMk z at hx
  obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact hx.symm
  have propagate : ∀ {a b : Sum V E}, terminalGraph.Walk a b →
      a ∈ cycle.walk.support → b ∈ cycle.walk.support := by
    intro a b walk ha
    induction walk with
    | nil => exact ha
    | @cons a c b hac rest ih => exact ih (terminalClosed ha hac)
  exact propagate walk hzSupport

private theorem helper_terminalSupportComponent_960.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t terminal : Fin rounds) (gamma delta :
        Fin k) (z : V ⊕ E),
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let terminalGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G terminalColoring gamma
        delta;
    let terminalComponent : Set (V ⊕ E) := TwoColorComponent G terminalColoring gamma delta z;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta) (terminalEdgeTransfer :
    ∀ edge ∈ cycle.walk.edges, edge ∈ terminalGraph.edgeSet),
    let _ : terminalGraph.Walk cycle.base cycle.base := cycle.walk.transfer terminalGraph
        terminalEdgeTransfer; z ∈ cycle.walk.support →
    ∀ x ∈ cycle.walk.support, x ∈ terminalComponent := by
  classical
  intro V E _ _ _ G k rounds e0 input series t terminal gamma delta z terminalColoring
      terminalGraph terminalComponent cycle terminalEdgeTransfer terminalWalk hzSupport x hx
  have hxWalk : x ∈ terminalWalk.support := by
    simpa [terminalWalk] using hx
  have hzWalk : z ∈ terminalWalk.support := by
    simpa [terminalWalk] using hzSupport
  have supportComponent : ∀ y : Sum V E, y ∈ terminalWalk.support →
      terminalGraph.connectedComponentMk y =
        terminalGraph.connectedComponentMk cycle.base := by
    intro y hy
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    rw [← hi]
    exact (SimpleGraph.ConnectedComponent.sound
      (terminalWalk.take i).reachable).symm
  change terminalGraph.connectedComponentMk x =
    terminalGraph.connectedComponentMk z
  exact (supportComponent x hxWalk).trans (supportComponent z hzWalk).symm

private theorem helper_terminalTreeMissingEq_985.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (terminal : Fin rounds) (sigma : PartialEdgeColoring E k),
    StableColoring (series.data.tree terminal.succ.castSucc)
        (TashkinovStoredColors series.data terminal.succ)
        (series.data.coloring terminal.succ) sigma →
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let terminalTree : TreeSequence G e0 := series.data.tree terminal.succ.castSucc;
    TreeMissingColors sigma terminalTree = TreeMissingColors terminalColoring terminalTree := by
  classical
  intro V E _ _ _ G k rounds e0 input series terminal sigma hsigmaStable terminalColoring
      terminalTree
  ext c
  simp only [TreeMissingColors, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hvc⟩
    exact ⟨v, hv, by
      rw [hsigmaStable.2 v (by simpa [terminalTree] using hv)] at hvc
      simpa [terminalColoring] using hvc⟩
  · rintro ⟨v, hv, hvc⟩
    exact ⟨v, hv, by
      rw [← hsigmaStable.2 v (by simpa [terminalTree] using hv)] at hvc
      simpa [terminalColoring] using hvc⟩

private theorem helper_sigmaSupportComponent_1076.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
      {input : PartialEdgeColoring E k} (series : TashkinovSeries G k rounds e0 input)
      (t : Fin rounds) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k) (z : V ⊕ E),
    let sigmaGraph : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma gamma delta;
    let sigmaComponent : Set (V ⊕ E) := TwoColorComponent G sigma gamma delta z;
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta),
    z ∈ cycle.walk.support →
    ∀ (sigmaEdgeTransfer : ∀ edge ∈ cycle.walk.edges, edge ∈ sigmaGraph.edgeSet),
    let _ : sigmaGraph.Walk cycle.base cycle.base :=
      cycle.walk.transfer sigmaGraph sigmaEdgeTransfer;
    ∀ x ∈ cycle.walk.support,
    x ∈ sigmaComponent := by
  classical
  intro V E _ _ _ G k rounds e0 input series t gamma delta sigma z sigmaGraph sigmaComponent
      cycle hzSupport sigmaEdgeTransfer sigmaWalk x hx
  have hxWalk : x ∈ sigmaWalk.support := by
    simpa [sigmaWalk] using hx
  have hzWalk : z ∈ sigmaWalk.support := by
    simpa [sigmaWalk] using hzSupport
  have supportComponent : ∀ y : Sum V E, y ∈ sigmaWalk.support →
      sigmaGraph.connectedComponentMk y =
        sigmaGraph.connectedComponentMk cycle.base := by
    intro y hy
    obtain ⟨i, hi, hiLe⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    rw [← hi]
    exact (SimpleGraph.ConnectedComponent.sound
      (sigmaWalk.take i).reachable).symm
  change sigmaGraph.connectedComponentMk x = sigmaGraph.connectedComponentMk z
  exact (supportComponent x hxWalk).trans (supportComponent z hzWalk).symm

private theorem helper_continuation_1088.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        (series : TashkinovSeries G k rounds e0 input) (t epsilon terminal : Fin rounds) (gamma
        delta : Fin k), (↑epsilon : ℕ) ≤ (↑terminal : ℕ) →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 → StableColoring (series.data.tree terminal.succ.castSucc) (TashkinovStoredColors
        series.data terminal.succ) (series.data.coloring terminal.succ) sigma →
    ∀ (z : V ⊕ E), (
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G (series.data.coloring t.succ) gamma delta z → w ∈
        TreeSequenceVertexSet (series.data.tree epsilon.succ.castSucc)) →
    let oldColoring : PartialEdgeColoring E k := series.data.coloring t.succ;
    let terminalColoring : PartialEdgeColoring E k := series.data.coloring terminal.succ;
    let epsilonTree : TreeSequence G e0 := series.data.tree epsilon.succ.castSucc;
    let terminalTree : TreeSequence G e0 := series.data.tree terminal.succ.castSucc;
    let terminalStored : Finset (Fin k) := TashkinovStoredColors series.data terminal.succ;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G terminalColoring gamma delta;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G oldColoring gamma delta z;
    let _ : Set (V ⊕ E) := TwoColorComponent G terminalColoring gamma delta z;
    let _ : Set (V ⊕ E) := TwoColorComponent G sigma gamma delta z; gamma ∈ TreeMissingColors
        (series.data.coloring epsilon.castSucc) epsilonTree ∪ TashkinovStoredColors series.data
        epsilon.castSucc → delta ∈ TreeMissingColors (series.data.coloring epsilon.castSucc)
        epsilonTree ∪ TashkinovStoredColors series.data epsilon.castSucc → gamma ∈
        TreeMissingColors terminalColoring terminalTree ∪ terminalStored → delta ∈
        TreeMissingColors terminalColoring terminalTree ∪ terminalStored → series.data.coloring
        epsilon.castSucc = oldColoring → TreeSequenceVertexSet epsilonTree ⊆ TreeSequenceVertexSet
        terminalTree → IsProperEdgeColoring G terminalColoring → IsOneEdgeUncolored
        terminalColoring e0 →
    ∀ (cycle : TwoColorCycle G (series.data.coloring t.succ) gamma delta), (
    ∀ (x : V ⊕ E), x ∈ cycle.walk.support ↔ x ∈ TwoColorComponent G (series.data.coloring t.succ)
        gamma delta z) → (
    ∀ (f : E), Sum.inr f ∈ cycle.walk.support → oldColoring f = some gamma ∨ oldColoring f = some
        delta) → TwoColorComponent G sigma gamma delta z = TwoColorComponent G
        (series.data.coloring t.succ) gamma delta z ∧ TwoColorComponentCycle G sigma gamma delta z
  := by
  classical
  intro V E _ _ _ G k rounds e0 input series t epsilon terminal gamma delta hepsilonTerminal
      sigma hsigmaProper hsigmaOne hsigmaStable z hcontained oldColoring terminalColoring
      epsilonTree terminalTree terminalStored terminalGraph sigmaGraph oldComponent
      terminalComponent sigmaComponent hgammaEpsilon hdeltaEpsilon hgammaTerminal hdeltaTerminal
      hepsilonColoring vertexToTerminal hterminalProper hterminalOne cycle hfull edgeOldActive
  have edgeIncidentEpsilon := @helper_edgeIncidentEpsilon_899 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t epsilon gamma delta z hcontained cycle hfull
  have edgeInternalEpsilon := @helper_edgeInternalEpsilon_915 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t epsilon gamma delta z hcontained cycle hfull
      edgeOldActive
  have edgeSeriesPreserved := @helper_edgeSeriesPreserved_763 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t epsilon terminal gamma delta hepsilonTerminal
      hgammaEpsilon hdeltaEpsilon hepsilonColoring cycle edgeOldActive edgeIncidentEpsilon
      edgeInternalEpsilon
  have terminalEdgeTransfer := @helper_terminalEdgeTransfer_791 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t terminal gamma delta cycle edgeSeriesPreserved
  let terminalWalk := cycle.walk.transfer terminalGraph terminalEdgeTransfer
  have hterminalCycle : terminalWalk.IsCycle :=
    cycle.isCycle.transfer terminalEdgeTransfer
  have terminalClosed := @helper_terminalClosed_552 V E inferInstance inferInstance inferInstance G
      k rounds e0 input series t terminal gamma delta z hterminalProper cycle hfull edgeOldActive
      edgeSeriesPreserved
  have hzSupport : z ∈ cycle.walk.support := (hfull z).2 (by rfl)
  have terminalComponentSubset := @helper_terminalComponentSubset_946 V E inferInstance
      inferInstance inferInstance G k rounds e0 input series t terminal gamma delta z cycle
      terminalClosed hzSupport
  have terminalSupportComponent := @helper_terminalSupportComponent_960 V E inferInstance
      inferInstance inferInstance G k rounds e0 input series t terminal gamma delta z cycle
      terminalEdgeTransfer hzSupport
  have hterminalFull : ∀ x : Sum V E,
      x ∈ cycle.walk.support ↔ x ∈ terminalComponent := by
    intro x
    exact ⟨terminalSupportComponent x, terminalComponentSubset (a := x)⟩
  have terminalTreeMissingEq := @helper_terminalTreeMissingEq_985 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series terminal sigma hsigmaStable
  have hgammaSigma : gamma ∈
      TreeMissingColors sigma terminalTree ∪ terminalStored := by
    rw [terminalTreeMissingEq]
    exact hgammaTerminal
  have hdeltaSigma : delta ∈
      TreeMissingColors sigma terminalTree ∪ terminalStored := by
    rw [terminalTreeMissingEq]
    exact hdeltaTerminal
  let terminalSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨terminalColoring, hterminalProper, hterminalOne⟩
  let sigmaSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨sigma, hsigmaProper, hsigmaOne⟩
  have hsigmaReverse : StableColoring terminalTree terminalStored
      sigma terminalColoring := by
    have hforward : StableColoring terminalTree terminalStored
        terminalColoring sigma := by
      simpa [terminalTree, terminalStored, terminalColoring] using hsigmaStable
    have hforwardSubtype : StableColoring terminalTree terminalStored
        terminalSubtype.1 sigmaSubtype.1 := by
      simpa [terminalSubtype, sigmaSubtype] using hforward
    have hreverseSubtype :=
      (sc2 G e0 terminalTree terminalStored).symm hforwardSubtype
    simpa [terminalSubtype, sigmaSubtype] using hreverseSubtype
  have cycleVertexTerminalTree (v : V)
      (hv : Sum.inl v ∈ cycle.walk.support) :
      v ∈ TreeSequenceVertexSet terminalTree := by
    apply vertexToTerminal
    apply hcontained v
    exact (hfull (Sum.inl v)).1 hv
  have edgeIncidentTerminal (f : E)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      TreeIncidentEdge terminalTree f := by
    rcases edgeIncidentEpsilon f hf with ⟨v, hv, hvf⟩
    exact ⟨v, vertexToTerminal hv, hvf⟩
  have edgeSigmaPreserved (f : E)
      (hf : Sum.inr f ∈ cycle.walk.support) :
      sigma f = terminalColoring f := by
    have hfIncident := edgeIncidentTerminal f hf
    have hfSeries := edgeSeriesPreserved f hf
    rcases edgeOldActive f hf with hgamma | hdelta
    · apply hsigmaStable.1 f (by simpa [terminalTree] using hfIncident)
      exact ⟨gamma, by simpa [terminalColoring, terminalTree, terminalStored]
        using hgammaTerminal, hfSeries.trans hgamma⟩
    · apply hsigmaStable.1 f (by simpa [terminalTree] using hfIncident)
      exact ⟨delta, by simpa [terminalColoring, terminalTree, terminalStored]
        using hdeltaTerminal, hfSeries.trans hdelta⟩
  have sigmaEdgeTransfer := @helper_sigmaEdgeTransfer_936 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t terminal gamma delta sigma cycle
      edgeSeriesPreserved edgeSigmaPreserved
  let sigmaWalk := cycle.walk.transfer sigmaGraph sigmaEdgeTransfer
  have hsigmaCycle : sigmaWalk.IsCycle := cycle.isCycle.transfer sigmaEdgeTransfer
  have sigmaClosed := @helper_sigmaClosed_817 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series t terminal gamma delta sigma cycle terminalClosed hgammaSigma
      hdeltaSigma hsigmaReverse cycleVertexTerminalTree edgeSigmaPreserved
  have sigmaComponentSubset : sigmaComponent ⊆
      {x | x ∈ cycle.walk.support} := by
    intro x hx
    change sigmaGraph.connectedComponentMk x = sigmaGraph.connectedComponentMk z at hx
    obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact hx.symm
    have propagate : ∀ {a b : Sum V E}, sigmaGraph.Walk a b →
        a ∈ cycle.walk.support → b ∈ cycle.walk.support := by
      intro a b walk ha
      induction walk with
      | nil => exact ha
      | @cons a c b hac rest ih => exact ih (sigmaClosed ha hac)
    exact propagate walk hzSupport
  have sigmaSupportComponent := @helper_sigmaSupportComponent_1076 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t gamma delta sigma z cycle hzSupport
      sigmaEdgeTransfer
  have hsigmaFull : ∀ x : Sum V E,
      x ∈ cycle.walk.support ↔ x ∈ sigmaComponent := by
    intro x
    exact ⟨sigmaSupportComponent x, sigmaComponentSubset (a := x)⟩
  have hcomponent : sigmaComponent = oldComponent := by
    ext x
    exact (hsigmaFull x).symm.trans (hfull x)
  refine ⟨by simpa [sigmaComponent, oldComponent, oldColoring] using hcomponent, ?_⟩
  refine ⟨⟨cycle.base, sigmaWalk, hsigmaCycle⟩, ?_⟩
  intro x
  change x ∈ sigmaWalk.support ↔ x ∈ TwoColorComponent G sigma gamma delta z
  rw [SimpleGraph.Walk.support_transfer]
  simpa [sigmaComponent] using hsigmaFull x

theorem StableSeriesCycleComponentTransport {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k}
    (series : TashkinovSeries G k rounds e0 input)
    (t epsilon terminal : Fin rounds) (gamma delta : Fin k)
    (htEpsilon : t.val < epsilon.val)
    (hepsilonTerminal : epsilon.val ≤ terminal.val)
    (htKind : series.data.kind t.succ =
      some TashkinovExtensionKind.PE)
    (htGamma : series.data.gamma t.succ = some gamma)
    (htDelta : series.data.delta t.succ = some delta)
    (hintervening : ∀ r : Fin rounds,
      t.val < r.val → r.val < epsilon.val →
      series.data.kind r.succ = some TashkinovExtensionKind.RE)
    (_ : series.data.kind terminal.succ =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (series.data.tree terminal.succ.castSucc)
      (TashkinovStoredColors series.data terminal.succ)
      (series.data.coloring terminal.succ) sigma)
    (z : Sum V E)
    (hcycle : TwoColorComponentCycle G
      (series.data.coloring t.succ) gamma delta z)
    (hcontained : ∀ w : V,
      Sum.inl w ∈ TwoColorComponent G
        (series.data.coloring t.succ) gamma delta z →
      w ∈ TreeSequenceVertexSet
        (series.data.tree epsilon.succ.castSucc)) :
    TwoColorComponent G sigma gamma delta z =
        TwoColorComponent G (series.data.coloring t.succ) gamma delta z ∧
      TwoColorComponentCycle G sigma gamma delta z := by
  classical
  let oldColoring := series.data.coloring t.succ
  let terminalColoring := series.data.coloring terminal.succ
  let epsilonTree := series.data.tree epsilon.succ.castSucc
  let terminalTree := series.data.tree terminal.succ.castSucc
  let terminalStored := TashkinovStoredColors series.data terminal.succ
  let oldGraph := TwoColorIncidenceGraph G oldColoring gamma delta
  let terminalGraph := TwoColorIncidenceGraph G terminalColoring gamma delta
  let sigmaGraph := TwoColorIncidenceGraph G sigma gamma delta
  let oldComponent := TwoColorComponent G oldColoring gamma delta z
  let terminalComponent := TwoColorComponent G terminalColoring gamma delta z
  let sigmaComponent := TwoColorComponent G sigma gamma delta z
  have currentStoredControl := @helper_currentStoredControl_788 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series
  have hpairControl := @helper_hpairControl_97 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series t epsilon terminal gamma delta htKind htGamma htDelta sigma z hcycle
      hcontained currentStoredControl
  have hgammaStart := hpairControl gamma (Or.inl rfl)
  have hdeltaStart := hpairControl delta (Or.inr rfl)
  have controlPrevious := @helper_controlPrevious_161 V E inferInstance inferInstance inferInstance
      G k rounds e0 input series t epsilon terminal
  have htTerminal : t.val < terminal.val := by omega
  have hgammaEpsilon : gamma ∈
      TreeMissingColors (series.data.coloring epsilon.castSucc) epsilonTree ∪
        TashkinovStoredColors series.data epsilon.castSucc := by
    simpa [epsilonTree] using
      controlPrevious gamma hgammaStart epsilon.val (by omega)
        hepsilonTerminal epsilon rfl
  have hdeltaEpsilon : delta ∈
      TreeMissingColors (series.data.coloring epsilon.castSucc) epsilonTree ∪
        TashkinovStoredColors series.data epsilon.castSucc := by
    simpa [epsilonTree] using
      controlPrevious delta hdeltaStart epsilon.val (by omega)
        hepsilonTerminal epsilon rfl
  have hgammaTerminalPrevious :=
    controlPrevious gamma hgammaStart terminal.val (by omega) le_rfl terminal rfl
  have hdeltaTerminalPrevious :=
    controlPrevious delta hdeltaStart terminal.val (by omega) le_rfl terminal rfl
  have hgammaTerminal : gamma ∈
      TreeMissingColors terminalColoring terminalTree ∪ terminalStored := by
    simpa [terminalColoring, terminalTree, terminalStored] using
      (HkuMissingStoredMonotone G k rounds e0 input series terminal).1
        hgammaTerminalPrevious
  have hdeltaTerminal : delta ∈
      TreeMissingColors terminalColoring terminalTree ∪ terminalStored := by
    simpa [terminalColoring, terminalTree, terminalStored] using
      (HkuMissingStoredMonotone G k rounds e0 input series terminal).1
        hdeltaTerminalPrevious
  have reColoring := @helper_reColoring_228 V E inferInstance inferInstance inferInstance G k rounds
      e0 input series t epsilon terminal
  have coloringAlong := @helper_coloringAlong_644 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series t epsilon terminal hintervening reColoring
  have hepsilonColoring :
      series.data.coloring epsilon.castSucc = oldColoring :=
    coloringAlong epsilon.val (by omega) le_rfl epsilon.castSucc rfl
  have stepSegment := @helper_stepSegment_310 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series t epsilon terminal
  have vertexTransfer {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    rcases hv with ⟨i, -, rfl⟩
    rcases hAB with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i
  have vertexToTerminal := @helper_vertexToTerminal_689 V E inferInstance inferInstance
      inferInstance G k rounds e0 input series t epsilon terminal hepsilonTerminal stepSegment
      vertexTransfer
  have hterminalData := series.coloringProperties terminal.succ
  rcases hterminalData with ⟨hterminalProper, hterminalOne⟩
  rcases hcycle with ⟨cycle, hfull⟩
  have edgeOldActive (f : E) (hf : Sum.inr f ∈ cycle.walk.support) :
      oldColoring f = some gamma ∨ oldColoring f = some delta := by
    obtain ⟨node, -, hadj⟩ :=
      SimpleGraph.adj_of_mem_walk_support cycle.walk cycle.isCycle.not_nil hf
    cases node with
    | inl v =>
        have hdata : Incident G v f ∧
            (oldColoring f = some gamma ∨ oldColoring f = some delta) := by
          simpa [oldGraph, oldColoring, TwoColorIncidenceGraph] using hadj
        exact hdata.2
    | inr e =>
        simp [TwoColorIncidenceGraph] at hadj
  exact @helper_continuation_1088 V E inferInstance inferInstance inferInstance G k
      rounds e0 input series t epsilon terminal gamma delta hepsilonTerminal sigma hsigmaProper
      hsigmaOne hsigmaStable z hcontained hgammaEpsilon hdeltaEpsilon hgammaTerminal
      hdeltaTerminal hepsilonColoring vertexToTerminal hterminalProper hterminalOne cycle hfull
      edgeOldActive
end GoldbergSeymour

end
