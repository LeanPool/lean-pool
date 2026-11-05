/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmB
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBInvariant
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBTrace
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseOneIndices
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass
public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeVerticesBefore
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Extension Base Claim44

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hmissingFixedInternal_357.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (
    ∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring
        a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) →
        Sum.inr f ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
        a) (Sum.inl u)) → (
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
        (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) →
    ∀ (a : Fin trace.steps) (v : V), Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) → trace.gamma a ∈ PresentColors G
        (trace.coloring a.castSucc) v → trace.delta a ∈ PresentColors G (trace.coloring
        a.castSucc) v → MissingColors G (trace.coloring a.succ) v = MissingColors G
        (trace.coloring a.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace htraceColorsNe hcomponentEdgeOfVertex hunaffectedValue a v hvComponent hgammaPresent
      hdeltaPresent
  have hgammaNew : trace.gamma a ∈
      PresentColors G (trace.coloring a.succ) v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hdeltaPresent ⊢
    obtain ⟨f, hvf, hfdelta⟩ := hdeltaPresent
    have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf (Or.inr hfdelta)
    refine ⟨f, hvf, ?_⟩
    rw [trace.transition]
    simp [TwoColorComponentSwap, hfComponent, hfdelta,
      (htraceColorsNe a).symm]
  have hdeltaNew : trace.delta a ∈
      PresentColors G (trace.coloring a.succ) v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hgammaPresent ⊢
    obtain ⟨f, hvf, hfgamma⟩ := hgammaPresent
    have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf (Or.inl hfgamma)
    refine ⟨f, hvf, ?_⟩
    rw [trace.transition]
    simp [TwoColorComponentSwap, hfComponent, hfgamma]
  apply Finset.ext
  intro c
  by_cases hcg : c = trace.gamma a
  · subst c
    have hold : trace.gamma a ∉
        MissingColors G (trace.coloring a.castSucc) v := by
      simpa [MissingColors] using hgammaPresent
    have hnew : trace.gamma a ∉
        MissingColors G (trace.coloring a.succ) v := by
      simpa [MissingColors] using hgammaNew
    simp [hold, hnew]
  · by_cases hcd : c = trace.delta a
    · subst c
      have hold : trace.delta a ∉
          MissingColors G (trace.coloring a.castSucc) v := by
        simpa [MissingColors] using hdeltaPresent
      have hnew : trace.delta a ∉
          MissingColors G (trace.coloring a.succ) v := by
        simpa [MissingColors] using hdeltaNew
      simp [hold, hnew]
    · simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ,
        true_and, PresentColors, Finset.mem_filter]
      constructor
      · intro hc hold
        rcases hold with ⟨f, hvf, hfc⟩
        exact hc ⟨f, hvf, (hunaffectedValue a f c hcg hcd).mpr hfc⟩
      · intro hc hnew
        rcases hnew with ⟨f, hvf, hfc⟩
        exact hc ⟨f, hvf, (hunaffectedValue a f c hcg hcd).mp hfc⟩

private theorem helper_hswapMakesGammaMissing_415.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (jSlot : Fin
        ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (
    ∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
        (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
        terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (
    ∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring
        a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) →
        Sum.inr f ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
        a) (Sum.inl u)) →
    ∀ (a : Fin trace.steps), trace.gamma a ∈ MissingColors G (trace.coloring a.succ) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport jSlot rho1 u p indices gamma
      delta b trace htraceColorsNe hstepData hcomponentEdgeOfVertex a
  have hdeltaMissing := hstepData a |>.2.1
  have huComponent : Sum.inl u ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) := rfl
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hgammaNew
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    at hgammaNew
  obtain ⟨f, huf, hfnew⟩ := hgammaNew
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u)
  · have hfold : trace.coloring a.castSucc f = some (trace.delta a) := by
      by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
      · rw [trace.transition] at hfnew
        have : trace.delta a = trace.gamma a := by
          simpa [TwoColorComponentSwap, hfComponent, hfg] using hfnew
        exact False.elim ((htraceColorsNe a) this.symm)
      · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
        · exact hfd
        · rw [trace.transition] at hfnew
          have : trace.coloring a.castSucc f = some (trace.gamma a) := by
            simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfnew
          exact False.elim (hfg this)
    have hdeltaNotPresent : trace.delta a ∉
        PresentColors G (trace.coloring a.castSucc) u := by
      simpa [MissingColors] using hdeltaMissing
    exact hdeltaNotPresent (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨f, huf, hfold⟩)
  · have hfold : trace.coloring a.castSucc f = some (trace.gamma a) := by
      rw [trace.transition] at hfnew
      simpa [TwoColorComponentSwap, hfComponent] using hfnew
    exact hfComponent
      (hcomponentEdgeOfVertex a huComponent huf (Or.inl hfold))

private theorem helper_hpresentOfNonSubsingleton_453.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (
    ∀ (n : Fin (trace.steps + (1 : ℕ))), IsProperEdgeColoring G (trace.coloring n)) →
    ∀ (a : Fin trace.steps) (v : V), ¬((TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl v)).Subsingleton → trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) v ∧ trace.delta a ∈ PresentColors G
        (trace.coloring a.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace htraceColorsNe htraceProper a v hnontrivial
  have colorPresent (c d : Fin k) (hcd : c ≠ d)
      (hc : c = trace.gamma a ∧ d = trace.delta a ∨
        c = trace.delta a ∧ d = trace.gamma a) :
      c ∈ PresentColors G (trace.coloring a.castSucc) v := by
    by_contra hcMissing
    apply hnontrivial
    intro x hx y hy
    cases x with
    | inl w =>
        simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hx
    | inr f =>
        cases y with
        | inl w =>
            simp [SimpleGraph.mem_neighborSet, TwoColorIncidenceGraph] at hy
        | inr g =>
            have hxf := hx
            have hyg := hy
            simp only [TwoColorIncidenceGraph, SimpleGraph.mem_neighborSet] at hxf hyg
            rcases hxf with ⟨hvf, hfc⟩
            rcases hyg with ⟨hvg, hgc⟩
            have hnotC (e : E) (hve : Incident G v e) :
                trace.coloring a.castSucc e ≠ some c := by
              intro hec
              apply hcMissing
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨e, hve, hec⟩
            have hfd : trace.coloring a.castSucc f = some d := by
              rcases hc with hc | hc
              · rcases hc with ⟨rfl, rfl⟩
                exact hfc.resolve_left (hnotC f hvf)
              · rcases hc with ⟨rfl, rfl⟩
                exact hfc.resolve_right (hnotC f hvf)
            have hgd : trace.coloring a.castSucc g = some d := by
              rcases hc with hc | hc
              · rcases hc with ⟨rfl, rfl⟩
                exact hgc.resolve_left (hnotC g hvg)
              · rcases hc with ⟨rfl, rfl⟩
                exact hgc.resolve_right (hnotC g hvg)
            by_cases hfg : f = g
            · subst g
              rfl
            · exact False.elim
                ((htraceProper a.castSucc) hfg ⟨v, hvf, hvg⟩ hfd hgd)
  refine ⟨?_, ?_⟩
  · exact colorPresent (trace.gamma a) (trace.delta a)
      (htraceColorsNe a) (Or.inl ⟨rfl, rfl⟩)
  · exact colorPresent (trace.delta a) (trace.gamma a)
      (htraceColorsNe a).symm (Or.inr ⟨rfl, rfl⟩)

private theorem helper_hmissingPreserved_558.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (jSlot : Fin
        ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (TjPrime : TreeSequence G e0)
        (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
        (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
        terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (
    ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) → MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v) → (
    ∀ (a : Fin trace.steps) (v : V), Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) → trace.gamma a ∈ PresentColors G
        (trace.coloring a.castSucc) v → trace.delta a ∈ PresentColors G (trace.coloring
        a.castSucc) v → MissingColors G (trace.coloring a.succ) v = MissingColors G
        (trace.coloring a.castSucc) v) → (
    ∀ (a : Fin trace.steps) (v : V), ¬((TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl v)).Subsingleton → trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) v ∧ trace.delta a ∈ PresentColors G
        (trace.coloring a.castSucc) v) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) → (
    ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeVerticesBefore TjPrime u huPrime → trace.gamma a ∉
        MissingColors G rho1 v ∧ trace.delta a ∉ MissingColors G rho1 v) →
    ∀ (n : Fin (trace.steps + (1 : ℕ))),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (trace.coloring n) v = MissingColors G rho1 v := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport jSlot rho1 u TjPrime huPrime p
      indices gamma delta b trace hstepData hmissingFixedOutside hmissingFixedInternal
      hpresentOfNonSubsingleton hvertexInitialSegment hprefixColorsNotMissing n
  induction n using Fin.induction with
  | zero =>
      intro v hv
      rw [trace.initialColoring]
  | succ a ih =>
      intro v hv
      rcases Finset.mem_union.mp hv with hvTj | hvPrefix
      · by_cases hvTerminal : v = terminalSupport
        · subst v
          by_cases hvComponent : Sum.inl terminalSupport ∈
              TwoColorComponent G (trace.coloring a.castSucc)
                (trace.gamma a) (trace.delta a) (Sum.inl u)
          · have hnontrivial := (hstepData a).2.2.2.2.1 hvComponent
            obtain ⟨hgammaPresent, hdeltaPresent⟩ :=
              hpresentOfNonSubsingleton a terminalSupport hnontrivial
            exact (hmissingFixedInternal a terminalSupport hvComponent
              hgammaPresent hdeltaPresent).trans
                (ih terminalSupport (Finset.mem_union_left _ hvTj))
          · exact (hmissingFixedOutside a hvComponent).trans
              (ih terminalSupport (Finset.mem_union_left _ hvTj))
        · have hvOutside : Sum.inl v ∉
              TwoColorComponent G (trace.coloring a.castSucc)
                (trace.gamma a) (trace.delta a) (Sum.inl u) := by
            intro hvComponent
            have hvSlot := hvertexInitialSegment (hstepData a).1 hvTj
            exact hvTerminal ((hstepData a).2.2.2.1 v hvSlot hvComponent)
          exact (hmissingFixedOutside a hvOutside).trans
            (ih v (Finset.mem_union_left _ hvTj))
      · by_cases hvComponent : Sum.inl v ∈
            TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u)
        · obtain ⟨hgammaRho1, hdeltaRho1⟩ :=
            hprefixColorsNotMissing a hvPrefix
          have hcurrent := ih v (Finset.mem_union_right _ hvPrefix)
          have hgammaCurrent : trace.gamma a ∉
              MissingColors G (trace.coloring a.castSucc) v := by
            rw [hcurrent]
            exact hgammaRho1
          have hdeltaCurrent : trace.delta a ∉
              MissingColors G (trace.coloring a.castSucc) v := by
            rw [hcurrent]
            exact hdeltaRho1
          have hgammaPresent : trace.gamma a ∈
              PresentColors G (trace.coloring a.castSucc) v := by
            simpa [MissingColors] using hgammaCurrent
          have hdeltaPresent : trace.delta a ∈
              PresentColors G (trace.coloring a.castSucc) v := by
            simpa [MissingColors] using hdeltaCurrent
          exact (hmissingFixedInternal a v hvComponent hgammaPresent
            hdeltaPresent).trans hcurrent
        · exact (hmissingFixedOutside a hvComponent).trans
            (ih v (Finset.mem_union_right _ hvPrefix))

private theorem helper_hstageEdgeFixedStep_665.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ)))
        (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
        (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
        terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (
    ∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring
        a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) →
        Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
        a) (Sum.inl u)) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) →
    ∀ (a : Fin trace.steps) (q : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
        trace.coloring a.succ ((ett.series.data.tree jSlot.succ.castSucc).edge q) = trace.coloring
        a.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge q) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices gamma delta b trace hstepData hvertexOfComponentEdge
      hvertexInitialSegment a q
  let S := ett.series.data.tree jSlot.succ.castSucc
  change trace.coloring a.succ (S.edge q) =
    trace.coloring a.castSucc (S.edge q)
  obtain ⟨i, hi⟩ := S.attaches q
  let r : Fin (S.length + 1) := Fin.castLT i
    (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))
  have hnewIncident : Incident G (S.vertex q.succ) (S.edge q) := by
    unfold Incident
    rw [hi]
    simp
  have holdIncident : Incident G (S.vertex r) (S.edge q) := by
    unfold Incident
    rw [hi]
    simp [r]
  have hverticesNe : S.vertex q.succ ≠ S.vertex r := by
    intro heq
    have hindexEq := S.vertex_injective heq
    have hvalEq := congrArg (fun x => x.val) hindexEq
    simp [r] at hvalEq
    omega
  have hnewS : S.vertex q.succ ∈ TreeSequenceVertexSet S := by
    simp [TreeSequenceVertexSet]
  have holdS : S.vertex r ∈ TreeSequenceVertexSet S := by
    simp [TreeSequenceVertexSet]
  have hnewSlot := hvertexInitialSegment (hstepData a).1 hnewS
  have holdSlot := hvertexInitialSegment (hstepData a).1 holdS
  rw [trace.transition]
  by_cases hfComponent : Sum.inr (S.edge q) ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u)
  · by_cases hfg : trace.coloring a.castSucc (S.edge q) =
        some (trace.gamma a)
    · have hnewComponent := hvertexOfComponentEdge a hfComponent
        hnewIncident (Or.inl hfg)
      have holdComponent := hvertexOfComponentEdge a hfComponent
        holdIncident (Or.inl hfg)
      have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
      have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
      exact False.elim (hverticesNe (hnewTerminal.trans holdTerminal.symm))
    · by_cases hfd : trace.coloring a.castSucc (S.edge q) =
          some (trace.delta a)
      · have hnewComponent := hvertexOfComponentEdge a hfComponent
          hnewIncident (Or.inr hfd)
        have holdComponent := hvertexOfComponentEdge a hfComponent
          holdIncident (Or.inr hfd)
        have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
        have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
        exact False.elim (hverticesNe (hnewTerminal.trans holdTerminal.symm))
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
  · simp [TwoColorComponentSwap, hfComponent]

private theorem helper_hfinalGammaMissing_734.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (gamma : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ)))
        (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), gamma b ∈
        MissingColors G rho1 u → trace.steps = (↑b : ℕ) → (
    ∀ (a : Fin trace.steps), (↑(trace.position a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = (↑b : ℕ)) → (
    ∀ (a : Fin trace.steps), trace.gamma a = gamma (trace.position a)) → (
    ∀ (a : Fin trace.steps), trace.gamma a ∈ MissingColors G (trace.coloring a.succ) u) → gamma (0
        : Fin (p + (1 : ℕ))) ∈ MissingColors G (trace.coloring (Fin.last trace.steps)) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices gamma b trace hselected hsteps hpositionReverse htraceGamma
      hswapMakesGammaMissing
  by_cases hzero : trace.steps = 0
  · have hbzero : b.val = 0 := by omega
    have hb : b = 0 := Fin.ext hbzero
    have hlastZero : (Fin.last trace.steps : Fin (trace.steps + 1)) = 0 := by
      apply Fin.ext
      simp [hzero]
    rw [hlastZero, trace.initialColoring, ← hb]
    exact hselected
  · have hpositive : 0 < trace.steps := Nat.pos_of_ne_zero hzero
    let a : Fin trace.steps := ⟨trace.steps - 1, by omega⟩
    have hpositionZero : trace.position a = 0 := by
      apply Fin.ext
      change (trace.position a).val = 0
      have hreverse := hpositionReverse a
      have haSucc : a.val + 1 = trace.steps := by
        simp [a]
        omega
      have hsum : (trace.position a).val + trace.steps = b.val := by
        omega
      have hbval : b.val = trace.steps := hsteps.symm
      apply Nat.add_right_cancel (m := trace.steps)
      simpa using hsum.trans hbval
    have hgammaA : trace.gamma a = gamma 0 := by
      rw [htraceGamma, hpositionZero]
    have hlast : a.succ = (Fin.last trace.steps : Fin (trace.steps + 1)) := by
      apply Fin.ext
      simp [a]
      omega
    rw [← hgammaA, ← hlast]
    exact hswapMakesGammaMissing a

private theorem helper_haugmentationEdgeMissing_799.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (seed : TreeSequence G e0)
        (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices :
        Fin (p + (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ))) (_ :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b)
        {B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 seed B →
    ∀ (a : Fin B.length), seed.length ≤ (↑a : ℕ) →
    ∃ (i : Fin (B.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑a : ℕ) ∧
    ∃ (c : Fin k), rho1 (B.edge a) = some c ∧ c ∈ MissingColors G rho1 (B.vertex i) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      seed terminalPosition p indices b trace B hreach
  unfold TashkinovAugmentationSequence at hreach
  induction hreach with
  | refl =>
      intro a ha
      omega
  | @tail A B hprior ih hstep =>
      intro a ha
      rcases ih with ⟨hlen, hinit, cnew, hcolor, hmissing⟩
      by_cases hold : a.val < A.length
      · let old : Fin A.length := ⟨a.val, hold⟩
        obtain ⟨i, hi, c, hcol, hmiss⟩ :=
          hstep old (by simpa [old] using ha)
        refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, c, ?_, ?_⟩
        · simpa using hi
        · have haold : Fin.castLE hinit.1 old = a := by
            apply Fin.ext
            rfl
          rw [← haold, hinit.2.2]
          simpa [old] using hcol
        · simpa [hinit.2.1] using hmiss
      · have hnew : a.val = A.length := by omega
        let last : Fin B.length := ⟨a.val, by omega⟩
        have hlast : a = last := by
          apply Fin.ext
          simp [last]
        rw [hlast]
        rw [show B.edge last =
            B.edge (Fin.cast hlen.symm (Fin.last A.length)) by
          congr 1
          apply Fin.ext
          simpa [last] using hnew]
        rw [hcolor]
        rw [TreeMissingColors] at hmissing
        obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp hmissing
        simp only [TreeSequenceVertexSet, Finset.mem_image] at hw
        obtain ⟨i, -, hwi⟩ := hw
        refine ⟨Fin.castLE (Nat.succ_le_succ hinit.1) i, ?_, cnew,
          rfl, ?_⟩
        · change i.val ≤ a.val
          omega
        · rw [hinit.2.1, hwi]
          exact hwm

private theorem helper_branch_851.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (TjPrime seed :
        TreeSequence G e0) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)), seed = TreeSequencePrefix (ett.series.data.tree
        jSlot.succ.castSucc) (↑terminalPosition : ℕ) hterminalPositionPositive (Nat.le_of_lt_succ
        terminalPosition.isLt) →
    ∀ (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), TashkinovClosure
        rho1 seed TjPrime → (
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
        (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) → (
    ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeVerticesBefore TjPrime u huPrime → trace.gamma a ∉
        MissingColors G rho1 v ∧ trace.delta a ∉ MissingColors G rho1 v) → (
    ∀ (n : Fin (trace.steps + (1 : ℕ))) (q : Fin (ett.series.data.tree
        jSlot.succ.castSucc).length), trace.coloring n ((ett.series.data.tree
        jSlot.succ.castSucc).edge q) = rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge q)) →
        (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 A B →
        TreeSequenceInitialSegment A B) → (
    ∀ {B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 seed B →
    ∀ (a : Fin B.length), seed.length ≤ (↑a : ℕ) →
    ∃ (i : Fin (B.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑a : ℕ) ∧
    ∃ (c : Fin k), rho1 (B.edge a) = some c ∧ c ∈ MissingColors G rho1 (B.vertex i)) →
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → trace.coloring (Fin.last trace.steps) f = rho1 f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      TjPrime seed terminalPosition hterminalPositionPositive hseed huPrime p indices gamma delta
      b trace hclosure hunaffectedValue hprefixColorsNotMissing hstageEdgesPreserved
      hsequenceInitialSegment haugmentationEdgeMissing f hf
  rcases hf with hfStage | hfPrefix
  · obtain ⟨q, hq⟩ := hfStage
    rw [← hq]
    exact hstageEdgesPreserved (Fin.last trace.steps) q
  · obtain ⟨q, z, hzu, hqz, hqf⟩ := hfPrefix
    subst f
    by_cases hqSeed : q.val < seed.length
    · have hsegment := hsequenceInitialSegment hclosure.1
      let qSeed : Fin seed.length := ⟨q.val, hqSeed⟩
      have hqCast : Fin.castLE hsegment.1 qSeed = q := by
        apply Fin.ext
        rfl
      have hinherited : TjPrime.edge q = seed.edge qSeed := by
        rw [← hqCast, hsegment.2.2]
      have hseedLength : seed.length = terminalPosition.val := by
        rw [hseed]
        rfl
      have hqStageLt : q.val <
          (ett.series.data.tree jSlot.succ.castSucc).length := by
        have hterminalLe : terminalPosition.val ≤
            (ett.series.data.tree jSlot.succ.castSucc).length :=
          Nat.le_of_lt_succ terminalPosition.isLt
        omega
      let qStage : Fin
          (ett.series.data.tree jSlot.succ.castSucc).length :=
        ⟨q.val, hqStageLt⟩
      subst seed
      have hedgeEq : TjPrime.edge q =
          (ett.series.data.tree jSlot.succ.castSucc).edge qStage :=
        hinherited.trans (by rfl)
      rw [hedgeEq]
      exact hstageEdgesPreserved (Fin.last trace.steps) qStage
    · have hqAfterSeed : seed.length ≤ q.val := Nat.le_of_not_gt hqSeed
      obtain ⟨i, hiq, c, hcolor, hmissing⟩ :=
        haugmentationEdgeMissing hclosure.1 q hqAfterSeed
      have hiBefore : TjPrime.vertex i ∈
          TreeVerticesBefore TjPrime u huPrime := by
        unfold TreeVerticesBefore
        apply Finset.mem_filter.mpr
        constructor
        · simp [TreeSequenceVertexSet]
        · exact ⟨i, z, rfl, hzu, lt_of_le_of_lt hiq hqz⟩
      have hcAvoids (a : Fin trace.steps) :
          c ≠ trace.gamma a ∧ c ≠ trace.delta a := by
        obtain ⟨hgammaNotMissing, hdeltaNotMissing⟩ :=
          hprefixColorsNotMissing a hiBefore
        constructor
        · intro hcg
          apply hgammaNotMissing
          rw [← hcg]
          exact hmissing
        · intro hcd
          apply hdeltaNotMissing
          rw [← hcd]
          exact hmissing
      have hcolorPreserved : ∀ n : Fin (trace.steps + 1),
          trace.coloring n (TjPrime.edge q) = some c := by
        intro n
        induction n using Fin.induction with
        | zero =>
            rw [trace.initialColoring]
            exact hcolor
        | succ a ih =>
            exact (hunaffectedValue a (TjPrime.edge q) c
              (hcAvoids a).1 (hcAvoids a).2).mpr ih
      exact (hcolorPreserved (Fin.last trace.steps)).trans hcolor.symm

private theorem helper_hsteps_791.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace
        ett terminalSupport rho1 u p indices b), Function.Injective indices → Function.Injective
        trace.slot → trace.steps = (↑b : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices b trace hindicesInjective hslotInjective
  have hleft : (Finset.univ.image trace.slot).card = trace.steps := by
    rw [Finset.card_image_of_injective Finset.univ hslotInjective]
    simp
  have hright :
      (ExtensionBaseCaseOneIndices ett p indices b).card = b.val := by
    unfold ExtensionBaseCaseOneIndices
    rw [Finset.card_image_of_injective _ hindicesInjective]
    let s := Finset.univ.filter fun a : Fin (p + 1) => a.val < b.val
    change s.card = b.val
    calc
      s.card = Fintype.card s := (Fintype.card_coe s).symm
      _ = Fintype.card (Fin b.val) := Fintype.card_congr {
        toFun := fun a => ⟨a.val.val, (Finset.mem_filter.mp a.property).2⟩
        invFun := fun a =>
          ⟨⟨a.val, by omega⟩, Finset.mem_filter.mpr ⟨by simp, a.isLt⟩⟩
        left_inv := by intro a; apply Subtype.ext; apply Fin.ext; rfl
        right_inv := by intro a; apply Fin.ext; rfl
      }
      _ = b.val := Fintype.card_fin b.val
  rw [← hleft, trace.enumerates, hright]

private theorem helper_hbeforeEdgesPreserved_1075.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (jSlot : Fin
        ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalAt :
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = terminalSupport) (p :
        ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b :
        Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p
        indices b), (
    ∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
        (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
        terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (
    ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) →
    ∀ {f : E}, Incident G v f → trace.coloring a.succ f = trace.coloring a.castSucc f) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B) → (
    ∀ {A : TreeSequence G e0} {v w : V} (hv : v ∈ TreeSequenceVertexSet A), w ∈ TreeVerticesBefore
        A v hv → w ∈ TreeSequenceVertexSet A ∧ w ≠ v) →
    ∀ (n : Fin (trace.steps + (1 : ℕ))) (f : E), (
    ∃ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) terminalSupport (Eq.mpr
        (id (congrArg (fun (_a : V) ↦ _a ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) (Eq.symm hterminalAt))) (of_eq_true (Eq.trans (propext
        Finset.mem_image) (Eq.trans (congrArg Exists (funext fun (a : Fin ((ett.series.data.tree
        jSlot.castSucc.succ).length + (1 : ℕ))) ↦ Eq.trans (congrFun' (congrArg And ((fun x =>
        eq_true (Finset.mem_univ x)) a)) ((ett.series.data.tree jSlot.castSucc.succ).vertex a =
        (ett.series.data.tree jSlot.castSucc.succ).vertex terminalPosition)) (true_and
        ((ett.series.data.tree jSlot.castSucc.succ).vertex a = (ett.series.data.tree
        jSlot.castSucc.succ).vertex terminalPosition)))) ((fun f a => eq_true
        (exists_apply_eq_apply f a)) (ett.series.data.tree jSlot.castSucc.succ).vertex
        terminalPosition))))), Incident G w f) → trace.coloring n f = rho1 f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport jSlot rho1 u terminalPosition
      hterminalAt p indices gamma delta b trace hstepData hfixedOutsideComponent
      hvertexInitialSegment hbeforeMemberAndNe n
  induction n using Fin.induction with
  | zero =>
      intro f hf
      rw [trace.initialColoring]
  | succ a ih =>
      intro f hf
      obtain ⟨w, hwBefore, hwf⟩ := hf
      have hwData := hbeforeMemberAndNe
        (v := terminalSupport)
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet]) hwBefore
      have hwOutside : Sum.inl w ∉
          TwoColorComponent G (trace.coloring a.castSucc)
            (trace.gamma a) (trace.delta a) (Sum.inl u) := by
        intro hwComponent
        have hwSlot := hvertexInitialSegment (hstepData a).1 hwData.1
        exact hwData.2 ((hstepData a).2.2.2.1 w hwSlot hwComponent)
      exact (hfixedOutsideComponent a hwOutside hwf).trans
        (ih f ⟨w, hwBefore, hwf⟩)

private theorem helper_hindicesInjective_829.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds),
    (∀ (a c : Fin (p + (1 : ℕ))),
        (↑a : ℕ) < (↑c : ℕ) → (↑(indices a) : ℕ) < (↑(indices c) : ℕ)) →
    Function.Injective indices := by
  classical
  intro V E _ _ _ G k e0 input T generating ett p indices hincreasing a c hac
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hincreasing a c hlt
    rw [hac] at hstrict
    exact (Nat.lt_irrefl _ hstrict)
  · have hstrict := hincreasing c a hgt
    rw [hac] at hstrict
    exact (Nat.lt_irrefl _ hstrict)

private theorem helper_hslotInjective_840.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (rho1 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ)))
      (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b),
    Function.Injective trace.slot := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices b trace a c hac
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := trace.strictlyDescending a c hlt
    rw [hac] at hstrict
    exact (Nat.lt_irrefl _ hstrict)
  · have hstrict := trace.strictlyDescending c a hgt
    rw [hac] at hstrict
    exact (Nat.lt_irrefl _ hstrict)

private theorem helper_hpositionSurjectiveBelow_859.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (b
        : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p
        indices b), Function.Injective indices →
    ∀ (q : Fin (p + (1 : ℕ))), (↑q : ℕ) < (↑b : ℕ) →
    ∃ (a : Fin trace.steps), trace.position a = q := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices b trace
      hindicesInjective q hqb
  have hmem : indices q ∈ Finset.univ.image trace.slot := by
    rw [trace.enumerates]
    unfold ExtensionBaseCaseOneIndices
    exact Finset.mem_image.mpr ⟨q, by simpa using hqb, rfl⟩
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
  refine ⟨a, hindicesInjective ?_⟩
  rw [← trace.slotIdentity a]
  exact ha

private theorem helper_hgammaDeltaNe_915 :
    open scoped Classical in
    ∀ {k : ℕ} (p : ℕ) (gamma delta : Fin (p + (1 : ℕ)) → Fin k),
    (∀ (a : Fin p), gamma a.succ = delta a.castSucc) →
    Function.Injective (Fin.cons (gamma (0 : Fin (p + (1 : ℕ)))) delta) →
    ∀ (q : Fin (p + (1 : ℕ))),
    gamma q ≠ delta q := by
  classical
  intro k p gamma delta hchain hdistinct q
  have hconsGamma :
      (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) q.castSucc =
        gamma q := by
    refine Fin.cases ?_ (fun r => ?_) q
    · simp
    · rw [show (Fin.succ r).castSucc = r.castSucc.succ by
        apply Fin.ext
        rfl]
      rw [Fin.cons_succ]
      exact (hchain r).symm
  have hconsDelta :
      (Fin.cons (gamma 0) delta : Fin (p + 2) → Fin k) q.succ =
        delta q := by simp
  intro heq
  have hindexEq : q.castSucc = q.succ :=
    hdistinct (hconsGamma.trans (heq.trans hconsDelta.symm))
  exact (ne_of_lt Fin.castSucc_lt_succ) hindexEq

private theorem helper_hvertexOfComponentEdge_941.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b) (a : Fin trace.steps)
        {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma
        a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f = some
        (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inl v ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace a v f hfComponent hvf hfColor
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk
        (Sum.inr f) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    at hfComponent
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk
        (Sum.inl v) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
  have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).Adj (Sum.inl v) (Sum.inr f) := by
    simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    hadj).trans hfComponent

private theorem helper_hcomponentEdgeOfVertex_966.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b) (a : Fin trace.steps)
        {v : V} {f : E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma
        a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f = some
        (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inr f ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace a v f hvComponent hvf hfColor
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk
        (Sum.inl v) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    at hvComponent
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk
        (Sum.inr f) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
  have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).Adj (Sum.inr f) (Sum.inl v) := by
    simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    hadj).trans hvComponent

private theorem helper_hfixedOutsideComponent_991.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring
        a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) →
        Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
        a) (Sum.inl u)) →
    ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) →
    ∀ {f : E}, Incident G v f → trace.coloring a.succ f = trace.coloring a.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace hvertexOfComponentEdge a v hvOutside f hvf
  rw [trace.transition]
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u)
  · by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
    · exact False.elim (hvOutside
        (hvertexOfComponentEdge a hfComponent hvf (Or.inl hfg)))
    · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
      · exact False.elim (hvOutside
          (hvertexOfComponentEdge a hfComponent hvf (Or.inr hfd)))
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
  · simp [TwoColorComponentSwap, hfComponent]

private theorem helper_hmissingFixedOutside_1009.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (b
        : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p
        indices b), (
    ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) →
    ∀ {f : E}, Incident G v f → trace.coloring a.succ f = trace.coloring a.castSucc f) →
    ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u) → MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices b trace
      hfixedOutsideComponent a v hvOutside
  apply Finset.ext
  intro c
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
    PresentColors, Finset.mem_filter]
  constructor
  · intro hc hold
    rcases hold with ⟨f, hvf, hfc⟩
    exact hc ⟨f, hvf, (hfixedOutsideComponent a hvOutside hvf).trans hfc⟩
  · intro hc hnew
    rcases hnew with ⟨f, hvf, hfc⟩
    exact hc ⟨f, hvf, (hfixedOutsideComponent a hvOutside hvf).symm.trans hfc⟩

private theorem helper_hunaffectedValue_1026.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) →
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
        (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace htraceColorsNe a f c hcg hcd
  rw [trace.transition]
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u)
  · by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
    · simp [TwoColorComponentSwap, hfComponent, hfg, hcg.symm, hcd.symm]
    · by_cases hfd : trace.coloring a.castSucc f = some (trace.delta a)
      · simp [TwoColorComponentSwap, hfComponent, hfd,
          (htraceColorsNe a).symm, hcg.symm, hcd.symm]
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
  · simp [TwoColorComponentSwap, hfComponent]

private theorem helper_hvertexInitialSegment_1077.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E}
        {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
  classical
  intro V E G e0 A B hAB v hv
  simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
  obtain ⟨i, -, hi⟩ := hv
  obtain ⟨hlen, hvertices, -⟩ := hAB
  refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
  exact (hvertices i).trans hi

private theorem helper_hbeforeMemberAndNe_1086.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ))) (_ : ExtensionBaseAlgorithmBTrace ett
        terminalSupport rho1 u p indices b) {A : TreeSequence G e0} {v w : V} (hv : v ∈
        TreeSequenceVertexSet A), w ∈ TreeVerticesBefore A v hv → w ∈ TreeSequenceVertexSet A ∧ w
        ≠ v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices b trace A v w hv hw
  unfold TreeVerticesBefore at hw
  obtain ⟨hwA, i, j, hiw, hjv, hij⟩ := Finset.mem_filter.mp hw
  refine ⟨hwA, ?_⟩
  intro hwv
  have hijEq : i = j := A.vertex_injective
    (hiw.trans (hwv.trans hjv.symm))
  omega

private theorem helper_hprefixColorsNotMissing_1097.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (TjPrime : TreeSequence G e0) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_ _
        : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace
        ett terminalSupport rho1 u p indices b), (((TreeVerticesBefore TjPrime u huPrime).biUnion
        fun (v : V) ↦ MissingColors G rho1 v) ∩ (ExtensionBaseCaseOneIndices ett p indices
        b).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ : Finset (Fin k)) = ∅
        → (
    ∀ (a : Fin trace.steps), ett.series.data.stored (trace.slot a).succ = (insert (trace.gamma a)
        ({trace.delta a} : Finset (Fin k)) : Finset (Fin k))) → (
    ∀ (a : Fin trace.steps), trace.slot a ∈ ExtensionBaseCaseOneIndices ett p indices b) →
    ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeVerticesBefore TjPrime u huPrime → trace.gamma a ∉
        MissingColors G rho1 v ∧ trace.delta a ∉ MissingColors G rho1 v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u TjPrime huPrime p indices
      gamma delta b trace hprefixAvoids htraceStored hslotProcessed a v hv
  have exclude (c : Fin k) (hc : c ∈
      ett.series.data.stored (trace.slot a).succ) :
      c ∉ MissingColors G rho1 v := by
    intro hmissing
    have hleft : c ∈
        (TreeVerticesBefore TjPrime u huPrime).biUnion
          (fun w => MissingColors G rho1 w) :=
      Finset.mem_biUnion.mpr ⟨v, hv, hmissing⟩
    have hright : c ∈
        (ExtensionBaseCaseOneIndices ett p indices b).biUnion
          (fun t => ett.series.data.stored t.succ) :=
      Finset.mem_biUnion.mpr ⟨trace.slot a, hslotProcessed a, hc⟩
    have hinter := Finset.mem_inter.mpr ⟨hleft, hright⟩
    rw [hprefixAvoids] at hinter
    simp at hinter
  rw [htraceStored] at exclude
  exact ⟨exclude (trace.gamma a) (by simp),
    exclude (trace.delta a) (by simp)⟩

private theorem helper_hstageEdgesPreserved_1169.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (p : ℕ)
      (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ)))
      (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b),
    (∀ (a : Fin trace.steps) (q : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
        trace.coloring a.succ ((ett.series.data.tree jSlot.succ.castSucc).edge q) =
          trace.coloring a.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge q)) →
    ∀ (n : Fin (trace.steps + (1 : ℕ)))
      (q : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
    trace.coloring n ((ett.series.data.tree jSlot.succ.castSucc).edge q) =
      rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge q) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport jSlot rho1 u p indices b trace
      hstageEdgeFixedStep n
  induction n using Fin.induction with
  | zero =>
      intro q
      rw [trace.initialColoring]
  | succ a ih =>
      intro q
      exact (hstageEdgeFixedStep a q).trans (ih q)

private theorem helper_hinitialSegmentTrans_1187.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E}
        {A B D : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        D → TreeSequenceInitialSegment A D := by
  classical
  intro V E G e0 A B D hAB hBD
  obtain ⟨hlenAB, hverticesAB, hedgesAB⟩ := hAB
  obtain ⟨hlenBD, hverticesBD, hedgesBD⟩ := hBD
  refine ⟨hlenAB.trans hlenBD, ?_, ?_⟩
  · intro i
    rw [show Fin.castLE (Nat.succ_le_succ (hlenAB.trans hlenBD)) i =
        Fin.castLE (Nat.succ_le_succ hlenBD)
          (Fin.castLE (Nat.succ_le_succ hlenAB) i) by
      apply Fin.ext
      rfl]
    rw [hverticesBD, hverticesAB]
  · intro q
    rw [show Fin.castLE (hlenAB.trans hlenBD) q =
        Fin.castLE hlenBD (Fin.castLE hlenAB q) by
      apply Fin.ext
      rfl]
    rw [hedgesBD, hedgesAB]

private theorem helper_hsequenceInitialSegment_1207.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (rho1 : PartialEdgeColoring E k), (
    ∀ {A B D : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B D
        → TreeSequenceInitialSegment A D) →
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 A B →
        TreeSequenceInitialSegment A B := by
  classical
  intro V E _ _ G k e0 rho1 hinitialSegmentTrans A B hreach
  let _ := Fintype.ofFinite V
  unfold TashkinovAugmentationSequence at hreach
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨Nat.le_refl _, ?_, ?_⟩
      · intro i
        rfl
      · intro q
        rfl
  | @head A D hstep htail ih =>
      exact hinitialSegmentTrans hstep.2.1 ih

private theorem helper_branch_1233.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (TjPrime seed :
        TreeSequence G e0) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)), seed = TreeSequencePrefix (ett.series.data.tree
        jSlot.succ.castSucc) (↑terminalPosition : ℕ) hterminalPositionPositive (
    by omega
    ) →
    ∀ (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), TashkinovClosure
        rho1 seed TjPrime → (
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
        (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) → (
    ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeVerticesBefore TjPrime u huPrime → trace.gamma a ∉
        MissingColors G rho1 v ∧ trace.delta a ∉ MissingColors G rho1 v) → (
    ∀ (n : Fin (trace.steps + (1 : ℕ))) (q : Fin (ett.series.data.tree
        jSlot.succ.castSucc).length), trace.coloring n ((ett.series.data.tree
        jSlot.succ.castSucc).edge q) = rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge q)) →
        (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 A B →
        TreeSequenceInitialSegment A B) → (
    ∀ {B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 seed B →
    ∀ (a : Fin B.length), seed.length ≤ (↑a : ℕ) →
    ∃ (i : Fin (B.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑a : ℕ) ∧
    ∃ (c : Fin k), rho1 (B.edge a) = some c ∧ c ∈ MissingColors G rho1 (B.vertex i)) →
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → trace.coloring (Fin.last trace.steps) f = rho1 f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      TjPrime seed terminalPosition hterminalPositionPositive hseed huPrime p indices gamma delta
      b trace hclosure hunaffectedValue hprefixColorsNotMissing hstageEdgesPreserved
      hsequenceInitialSegment haugmentationEdgeMissing
  exact @helper_branch_851 V E inferInstance inferInstance inferInstance G k e0 input T
    generating ett terminalSupport hterminalSupport jSlot rho1 u TjPrime seed terminalPosition
    hterminalPositionPositive hseed huPrime p indices gamma delta b trace hclosure
    hunaffectedValue hprefixColorsNotMissing hstageEdgesPreserved hsequenceInitialSegment
    haugmentationEdgeMissing

private theorem helper_branch_1767.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (TjPrime seed :
        TreeSequence G e0) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)), seed = TreeSequencePrefix (ett.series.data.tree
        jSlot.succ.castSucc) (↑terminalPosition : ℕ) hterminalPositionPositive (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) →
    ∀ (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), TashkinovClosure
        rho1 seed TjPrime → (
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
        (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) → (
    ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeVerticesBefore TjPrime u huPrime → trace.gamma a ∉
        MissingColors G rho1 v ∧ trace.delta a ∉ MissingColors G rho1 v) → (
    ∀ (n : Fin (trace.steps + (1 : ℕ))) (q : Fin (ett.series.data.tree
        jSlot.succ.castSucc).length), trace.coloring n ((ett.series.data.tree
        jSlot.succ.castSucc).edge q) = rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge q)) →
        (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 A B →
        TreeSequenceInitialSegment A B) → (
    ∀ {B : TreeSequence G e0}, TashkinovAugmentationSequence rho1 seed B →
    ∀ (a : Fin B.length), seed.length ≤ (↑a : ℕ) →
    ∃ (i : Fin (B.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑a : ℕ) ∧
    ∃ (c : Fin k), rho1 (B.edge a) = some c ∧ c ∈ MissingColors G rho1 (B.vertex i)) →
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → trace.coloring (Fin.last trace.steps) f = rho1 f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      TjPrime seed terminalPosition hterminalPositionPositive hseed huPrime p indices gamma delta
      b trace hclosure hunaffectedValue hprefixColorsNotMissing hstageEdgesPreserved
      hsequenceInitialSegment haugmentationEdgeMissing
  exact @helper_branch_1233 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
    (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport) (@jSlot) (@rho1)
    (@u) (@TjPrime) (@seed) (@terminalPosition) (@hterminalPositionPositive) (@hseed)
    (@huPrime) (@p) (@indices) (@gamma) (@delta) (@b) (@trace) (@hclosure) (@hunaffectedValue)
    (@hprefixColorsNotMissing) (@hstageEdgesPreserved) (@hsequenceInitialSegment)
    (@haugmentationEdgeMissing)

private theorem helper_hpositionBelowAnti_1591.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (gamma : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))), (
    ∀ (a c : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑c : ℕ) → (↑(indices a) : ℕ) < (↑(indices c) : ℕ)) →
    ∀ (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → gamma a ∉ MissingColors G rho1 u) →
    ∀ (hsteps : trace.steps = (↑b : ℕ)), Function.Injective trace.position →
    let positionBelow : Fin (↑b : ℕ) → Fin (↑b : ℕ) := fun (a : Fin (↑b : ℕ)) ↦
        (⟨(↑(trace.position (Fin.cast (
    by
                    omega
    ) a)) : ℕ), trace.positionBefore (Fin.cast (
    by
                omega
    ) a)⟩ : Fin (↑b : ℕ)); StrictAnti positionBelow := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices gamma b hincreasing trace _ hsteps hpositionInjective
      positionBelow a c hac
  have hdesc := trace.strictlyDescending
    (Fin.cast hsteps.symm a) (Fin.cast hsteps.symm c) (by simpa using hac)
  rw [trace.slotIdentity, trace.slotIdentity] at hdesc
  by_contra hnot
  have hle : (trace.position (Fin.cast hsteps.symm a)).val ≤
      (trace.position (Fin.cast hsteps.symm c)).val := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hinc := hincreasing _ _ hlt
    omega
  · have hposEq : trace.position (Fin.cast hsteps.symm a) =
        trace.position (Fin.cast hsteps.symm c) := Fin.ext heq
    exact (ne_of_lt hac) (by
      have hcastEq := hpositionInjective hposEq
      apply Fin.ext
      simpa using congrArg (fun x => x.val) hcastEq)

private theorem helper_hpositionBelowRev_1608.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (b
        : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p
        indices b) (hsteps : trace.steps = (↑b : ℕ)),
    let positionBelow : Fin (↑b : ℕ) → Fin (↑b : ℕ) := fun (a : Fin (↑b : ℕ)) ↦
        (⟨(↑(trace.position (Fin.cast (
    by
                    omega
    ) a)) : ℕ), trace.positionBefore (Fin.cast (
    by
                omega
    ) a)⟩ : Fin (↑b : ℕ)); StrictAnti positionBelow →
    ∀ (a : Fin (↑b : ℕ)), positionBelow a = a.rev := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices b trace hsteps
      positionBelow hpositionBelowAnti a
  have hmono : StrictMono (fun q : Fin b.val => (positionBelow q).rev) := by
    intro q r hqr
    exact Fin.rev_lt_rev.mpr (hpositionBelowAnti hqr)
  have hid := congrFun hmono.eq_id a
  exact Fin.rev_eq_iff.mp hid

private theorem helper_hpositionReverse_1614.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    ∀ terminalSupport ∈ TreeSequenceVertexSet T,
    ∀ (jSlot : Fin ett.rounds) (rho1 : PartialEdgeColoring E k) (u : V) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (p : ℕ) (indices : Fin (p +
        (1 : ℕ)) → Fin ett.rounds) (b : Fin (p + (1 : ℕ))) (trace : ExtensionBaseAlgorithmBTrace
        ett terminalSupport rho1 u p indices b) (hsteps : trace.steps = (↑b : ℕ)),
    let positionBelow : Fin (↑b : ℕ) → Fin (↑b : ℕ) := fun (a : Fin (↑b : ℕ)) ↦
        (⟨(↑(trace.position (Fin.cast (
    by
                    omega
    ) a)) : ℕ), trace.positionBefore (Fin.cast (
    by
                omega
    ) a)⟩ : Fin (↑b : ℕ)); (
    ∀ (a : Fin (↑b : ℕ)), positionBelow a = a.rev) →
    ∀ (a : Fin trace.steps), (↑(trace.position a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = (↑b : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices b trace hsteps positionBelow hpositionBelowRev a
  have hrev := hpositionBelowRev (Fin.cast hsteps a)
  have hval := congrArg Fin.val hrev
  simp [positionBelow] at hval
  omega

private theorem helper_continuation_1854.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (_ :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot : Fin ett.rounds) (rho1 :
        PartialEdgeColoring E k) (C : Finset (Fin k)) (u : V) (TjPrime seed : TreeSequence G e0)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalAt : (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport) (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ : seed
        = TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive (Nat.le_of_lt_succ terminalPosition.isLt)) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
        (gamma _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b) (_ :
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) terminalSupport (
    by
            classical
            simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨terminalPosition, hterminalAt⟩
    ) C (ett.series.data.coloring jSlot.castSucc) rho1) (_ : TashkinovClosure rho1 seed TjPrime)
        (_ : (((TreeVerticesBefore TjPrime u huPrime).biUnion fun (v : V) ↦ MissingColors G rho1
        v) ∩ (ExtensionBaseCaseOneIndices ett p indices b).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ : Finset (Fin k)) = ∅) (_ : gamma b ∈ MissingColors G rho1
        u) (_ : trace.steps = (↑b : ℕ)) (_ :
    ∀ (a : Fin trace.steps), (↑(trace.position a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = (↑b : ℕ)) (_ :
    ∀ (a : Fin trace.steps), trace.gamma a = gamma (trace.position a)) (_ :
    ∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
        (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
        TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
        u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
        (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
        terminalSupport)).Subsingleton) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS) (_ :
    ∀ (a : Fin trace.steps) {v : V} {f : E} (_ : Sum.inr f ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) (_ : Incident G v f) (_ :
        trace.coloring a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some
        (trace.delta a)), Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma
        a) (trace.delta a) (Sum.inl u)) (_ :
    ∀ (a : Fin trace.steps) {v : V} (_ : Sum.inl v ∉ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) {f : E} (_ : Incident G v f),
        trace.coloring a.succ f = trace.coloring a.castSucc f) (_ :
    ∀ (a : Fin trace.steps) {v : V} (_ : Sum.inl v ∉ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)), MissingColors G (trace.coloring
        a.succ) v = MissingColors G (trace.coloring a.castSucc) v) (_ :
    ∀ (a : Fin trace.steps) (f : E) (c : Fin k) (_ : c ≠ trace.gamma a) (_ : c ≠ trace.delta a),
        trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c) (_ :
    ∀ (a : Fin trace.steps) (v : V) (_ : Sum.inl v ∈ TwoColorComponent G (trace.coloring
        a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) (_ : trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) v) (_ : trace.delta a ∈ PresentColors G
        (trace.coloring a.castSucc) v), MissingColors G (trace.coloring a.succ) v = MissingColors
        G (trace.coloring a.castSucc) v) (_ :
    ∀ (a : Fin trace.steps), trace.gamma a ∈ MissingColors G (trace.coloring a.succ) u) (_ :
    ∀ (a : Fin trace.steps) (v : V) (_ : ¬((TwoColorIncidenceGraph G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl v)).Subsingleton), trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) v ∧ trace.delta a ∈ PresentColors G
        (trace.coloring a.castSucc) v) (_ :
    ∀ (a : Fin trace.steps), ett.series.data.stored (trace.slot a).succ = (insert (trace.gamma a)
        ({trace.delta a} : Finset (Fin k)) : Finset (Fin k))) (_ :
    ∀ (a : Fin trace.steps), trace.slot a ∈ ExtensionBaseCaseOneIndices ett p indices b) (_ :
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) {v : V} (_ : v ∈
        TreeSequenceVertexSet A), v ∈ TreeSequenceVertexSet B) (_ :
    ∀ {A : TreeSequence G e0} {v w : V} (hv : v ∈ TreeSequenceVertexSet A) (_ : w ∈
        TreeVerticesBefore A v hv), w ∈ TreeSequenceVertexSet A ∧ w ≠ v),
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) terminalSupport (
    by
          classical
          simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨terminalPosition, hterminalAt⟩
    ) C (ett.series.data.coloring jSlot.castSucc) (trace.coloring (Fin.last trace.steps)) ∧ ((
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G rho1 v) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → trace.coloring (Fin.last trace.steps) f = rho1 f) ∧
        gamma (0 : Fin (p + (1 : ℕ))) ∈ MissingColors G (trace.coloring (Fin.last trace.steps)) u
  := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 C u
      TjPrime seed terminalPosition hterminalAt hterminalPositionPositive hseed huPrime p indices
      gamma delta b trace hbaseStable hclosure hprefixAvoids hselected hsteps hpositionReverse
      htraceGamma hstepData hvertexOfComponentEdge hfixedOutsideComponent hmissingFixedOutside
      hunaffectedValue hmissingFixedInternal hswapMakesGammaMissing hpresentOfNonSubsingleton
      htraceStored hslotProcessed hvertexInitialSegment hbeforeMemberAndNe
  have hprefixColorsNotMissing := @helper_hprefixColorsNotMissing_1097 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@terminalSupport) (@rho1) (@u) (@TjPrime) (@huPrime) (@p) (@indices) (@gamma) (@delta) (@b)
      (@trace) (@hprefixAvoids) (@htraceStored) (@hslotProcessed)
  have hmissingPreserved :=
    @helper_hmissingPreserved_558 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T generating ett terminalSupport jSlot rho1 u TjPrime huPrime
        p indices gamma delta b trace hstepData hmissingFixedOutside hmissingFixedInternal
        hpresentOfNonSubsingleton hvertexInitialSegment hprefixColorsNotMissing
  have hbeforeEdgesPreserved :=
    @helper_hbeforeEdgesPreserved_1075 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett terminalSupport jSlot rho1 u terminalPosition hterminalAt p
        indices gamma delta b trace hstepData hfixedOutsideComponent hvertexInitialSegment
        hbeforeMemberAndNe
  have hstableOutput : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
      (by
        rw [← hterminalAt]
        simp [TreeSequenceVertexSet])
      C (ett.series.data.coloring jSlot.castSucc)
        (trace.coloring (Fin.last trace.steps)) := by
    unfold StableColoringBeforeVertex at hbaseStable ⊢
    constructor
    · intro f hfIncident hfControlled
      exact (hbeforeEdgesPreserved (Fin.last trace.steps) f hfIncident).trans
        (hbaseStable.1 f hfIncident hfControlled)
    · intro w hwBefore
      have hwTj := (hbeforeMemberAndNe
        (v := terminalSupport)
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet]) hwBefore).1
      exact (hmissingPreserved (Fin.last trace.steps) w
        (Finset.mem_union_left _ hwTj)).trans (hbaseStable.2 w hwBefore)
  have hstageEdgeFixedStep := @helper_hstageEdgeFixedStep_665 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSupport hterminalSupport jSlot rho1 u
      terminalPosition p indices gamma delta b trace hstepData hvertexOfComponentEdge
      hvertexInitialSegment
  have hstageEdgesPreserved :=
    @helper_hstageEdgesPreserved_1169 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@jSlot) (@rho1) (@u)
        (@p) (@indices) (@b) (@trace) (@hstageEdgeFixedStep)
  have hfinalGammaMissing :=
    @helper_hfinalGammaMissing_734 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett terminalSupport hterminalSupport jSlot rho1 u terminalPosition p
        indices gamma b trace hselected hsteps hpositionReverse htraceGamma hswapMakesGammaMissing
  have hinitialSegmentTrans := @helper_hinitialSegmentTrans_1187 (@V) (@E) (@G) (@e0)
  have hsequenceInitialSegment := @helper_hsequenceInitialSegment_1207 (@V) (@E) inferInstance
      inferInstance (@G) (@k) (@e0) (@rho1) (@hinitialSegmentTrans)
  have haugmentationEdgeMissing := @helper_haugmentationEdgeMissing_799 V E inferInstance
      inferInstance inferInstance G k e0 input T generating ett terminalSupport hterminalSupport
      jSlot rho1 u seed terminalPosition p indices b trace
  refine ⟨hstableOutput, ?_, hfinalGammaMissing⟩
  constructor
  · intro v hv
    exact hmissingPreserved (Fin.last trace.steps) v hv
  · exact @helper_branch_1767 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport) (@jSlot) (@rho1)
      (@u) (@TjPrime) (@seed) (@terminalPosition) (@hterminalPositionPositive) (@hseed)
      (@huPrime) (@p) (@indices) (@gamma) (@delta) (@b) (@trace) (@hclosure) (@hunaffectedValue)
      (@hprefixColorsNotMissing) (@hstageEdgesPreserved) (@hsequenceInitialSegment)
      (@haugmentationEdgeMissing)

theorem ExtensionBaseClaim44 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot : Fin ett.rounds)
    (_ : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (rho1 : PartialEdgeColoring E k)
    (C : Finset (Fin k)) (u : V)
    (TjPrime seed : TreeSequence G e0)
    (terminalPosition : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1))
    (hterminalAt :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition =
        terminalSupport)
    (hterminalPositionPositive : 1 ≤ terminalPosition.val)
    (hseed : seed = TreeSequencePrefix
      (ett.series.data.tree jSlot.succ.castSucc) terminalPosition.val
      hterminalPositionPositive
      (Nat.le_of_lt_succ terminalPosition.isLt))
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (_ : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport ↔
        ∃ a : Fin (p + 1), indices a = r)
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (hinvariant : ExtensionBaseAlgorithmBInvariant ett terminalSupport
      jSlot rho1 u p indices b trace)
    (hbaseStable : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
      (by
        rw [← hterminalAt]
        simp [TreeSequenceVertexSet])
      C (ett.series.data.coloring jSlot.castSucc) rho1)
    (_ : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprefixAvoids :
      (TreeVerticesBefore TjPrime u huPrime).biUnion
          (fun v => MissingColors G rho1 v) ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (_ : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    let rho2 := trace.coloring (Fin.last trace.steps)
    StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) terminalSupport
        (by
          rw [← hterminalAt]
          simp [TreeSequenceVertexSet])
        C (ett.series.data.coloring jSlot.castSucc) rho2 ∧
      ((∀ v : V,
        v ∈ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc) ∪
            TreeVerticesBefore TjPrime u huPrime →
        MissingColors G rho2 v = MissingColors G rho1 v) ∧
       ∀ f : E,
        ((∃ a : Fin (ett.series.data.tree
              jSlot.succ.castSucc).length,
            (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
          ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + 1)),
            TjPrime.vertex z = u ∧ a.val < z.val ∧
              TjPrime.edge a = f) →
        rho2 f = rho1 f) ∧
      gamma 0 ∈ MissingColors G rho2 u := by
  classical
  dsimp only
  have hindicesInjective :=
    @helper_hindicesInjective_829 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@p) (@indices) (@hincreasing)
  have hslotInjective :=
    @helper_hslotInjective_840 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@rho1) (@u) (@p) (@indices)
        (@b) (@trace)
  have hsteps :=
    @helper_hsteps_791 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSupport hterminalSupport jSlot rho1 u terminalPosition p indices b
        trace hindicesInjective hslotInjective
  have hpositionInjective : Function.Injective trace.position := by
    intro a c hac
    apply hslotInjective
    rw [trace.slotIdentity, trace.slotIdentity, hac]
  have hpositionSurjectiveBelow :=
    @helper_hpositionSurjectiveBelow_859 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@rho1) (@u) (@p)
        (@indices) (@b) (@trace) (@hindicesInjective)
  let positionBelow : Fin b.val → Fin b.val := fun a =>
    ⟨(trace.position (Fin.cast hsteps.symm a)).val,
      trace.positionBefore (Fin.cast hsteps.symm a)⟩
  have hpositionBelowAnti : StrictAnti positionBelow := by
    exact @helper_hpositionBelowAnti_1591 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@hterminalSupport)
        (@jSlot) (@rho1) (@u) (@terminalPosition) (@p) (@indices) (@gamma) (@b) (@hincreasing)
        (@trace) (by assumption) (@hsteps) (@hpositionInjective)
  have hpositionBelowRev := @helper_hpositionBelowRev_1608 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@rho1)
      (@u) (@p) (@indices) (@b) (@trace) (@hsteps) (@hpositionBelowAnti)
  have hpositionReverse := @helper_hpositionReverse_1614 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport)
      (@hterminalSupport) (@jSlot) (@rho1) (@u) (@terminalPosition) (@p) (@indices) (@b) (@trace)
      (@hsteps) (@hpositionBelowRev)
  have htraceGamma (a : Fin trace.steps) :
      trace.gamma a = gamma (trace.position a) := by
    apply Option.some.inj
    exact (trace.gammaField a).symm.trans (by
      rw [trace.slotIdentity]
      exact hgamma (trace.position a))
  have htraceDelta (a : Fin trace.steps) :
      trace.delta a = delta (trace.position a) := by
    apply Option.some.inj
    exact (trace.deltaField a).symm.trans (by
      rw [trace.slotIdentity]
      exact hdelta (trace.position a))
  have hgammaDeltaNe := @helper_hgammaDeltaNe_915 (@k) (@p) (@gamma) (@delta) (@hchain) (@hdistinct)
  have htraceColorsNe (a : Fin trace.steps) :
      trace.gamma a ≠ trace.delta a := by
    rw [htraceGamma, htraceDelta]
    exact hgammaDeltaNe (trace.position a)
  have htraceProper (n : Fin (trace.steps + 1)) :
      IsProperEdgeColoring G (trace.coloring n) :=
    (hinvariant.1 n).1
  have hstepData (a : Fin trace.steps) := hinvariant.2.1 a
  have hvertexOfComponentEdge := @helper_hvertexOfComponentEdge_941 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@terminalSupport) (@rho1) (@u) (@p) (@indices) (@gamma) (@delta) (@b) (@trace)
  have hcomponentEdgeOfVertex := @helper_hcomponentEdgeOfVertex_966 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@terminalSupport) (@rho1) (@u) (@p) (@indices) (@gamma) (@delta) (@b) (@trace)
  have hfixedOutsideComponent := @helper_hfixedOutsideComponent_991 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@terminalSupport) (@rho1) (@u) (@p) (@indices) (@gamma) (@delta) (@b) (@trace)
      (@hvertexOfComponentEdge)
  have hmissingFixedOutside := @helper_hmissingFixedOutside_1009 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@terminalSupport) (@rho1) (@u) (@p) (@indices) (@b) (@trace) (@hfixedOutsideComponent)
  have hunaffectedValue := @helper_hunaffectedValue_1026 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@rho1)
      (@u) (@p) (@indices) (@gamma) (@delta) (@b) (@trace) (@htraceColorsNe)
  have hmissingFixedInternal := @helper_hmissingFixedInternal_357 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace htraceColorsNe hcomponentEdgeOfVertex hunaffectedValue
  have hswapMakesGammaMissing := @helper_hswapMakesGammaMissing_415 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSupport jSlot rho1 u p indices gamma delta
      b trace htraceColorsNe hstepData hcomponentEdgeOfVertex
  have hpresentOfNonSubsingleton := @helper_hpresentOfNonSubsingleton_453 V E inferInstance
      inferInstance inferInstance G k e0 input T generating ett terminalSupport rho1 u p indices
      gamma delta b trace htraceColorsNe htraceProper
  have htraceStored (a : Fin trace.steps) :
      ett.series.data.stored (trace.slot a).succ =
        {trace.gamma a, trace.delta a} := by
    rw [trace.slotIdentity, hstored, htraceGamma, htraceDelta]
  have hslotProcessed (a : Fin trace.steps) :
      trace.slot a ∈ ExtensionBaseCaseOneIndices ett p indices b := by
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hvertexInitialSegment := @helper_hvertexInitialSegment_1077 (@V) (@E) (@G) (@e0)
  have hbeforeMemberAndNe := @helper_hbeforeMemberAndNe_1086 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport)
      (@hterminalSupport) (@jSlot) (@rho1) (@u) (@terminalPosition) (@p) (@indices) (@b) (@trace)
  exact @helper_continuation_1854 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport)
      (@hterminalSupport) (@jSlot) (@rho1) (@C) (@u) (@TjPrime) (@seed) (@terminalPosition)
      (@hterminalAt) (@hterminalPositionPositive) (@hseed) (@huPrime) (@p) (@indices) (@gamma)
      (@delta) (@b) (@trace) (@hbaseStable) (@hclosure) (@hprefixAvoids) (@hselected) (@hsteps)
      (@hpositionReverse) (@htraceGamma) (@hstepData) (@hvertexOfComponentEdge)
      (@hfixedOutsideComponent) (@hmissingFixedOutside) (@hunaffectedValue)
      (@hmissingFixedInternal) (@hswapMakesGammaMissing) (@hpresentOfNonSubsingleton)
      (@htraceStored) (@hslotProcessed) (@hvertexInitialSegment) (@hbeforeMemberAndNe)
end GoldbergSeymour

end
