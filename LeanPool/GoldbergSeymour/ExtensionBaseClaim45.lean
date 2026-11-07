/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmC

public import LeanPool.GoldbergSeymour.ExtensionBaseClaim46

/-!
# Extension Base Claim45

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hmissingFixedInternal_549.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k) (u : V) (beta : Fin k),
    ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a :
    Fin trace.steps), trace.gamma a ≠ trace.delta a) → (∀ (a : Fin trace.steps) {v : V} {f :
    E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a)
    (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f = some
    (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inr f ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u)) → (∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a
    → (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) → ∀ (a : Fin
    trace.steps) (v : V), Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
    (trace.gamma a) (trace.delta a) (Sum.inl u) → trace.gamma a ∈ PresentColors G
    (trace.coloring a.castSucc) v → trace.delta a ∈ PresentColors G (trace.coloring
    a.castSucc) v → MissingColors G (trace.coloring a.succ) v = MissingColors G
    (trace.coloring a.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace htraceColorsNe hcomponentEdgeOfVertex hunaffectedValue a v hvComponent
      hgammaPresent hdeltaPresent
  have hgammaNew : trace.gamma a ∈
      PresentColors G (trace.coloring a.succ) v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hdeltaPresent ⊢
    obtain ⟨f, hvf, hfdelta⟩ := hdeltaPresent
    have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf
      (Or.inr hfdelta)
    refine ⟨f, hvf, ?_⟩
    rw [trace.transition]
    simp [TwoColorComponentSwap, hfComponent, hfdelta,
      (htraceColorsNe a).symm]
  have hdeltaNew : trace.delta a ∈
      PresentColors G (trace.coloring a.succ) v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      at hgammaPresent ⊢
    obtain ⟨f, hvf, hfgamma⟩ := hgammaPresent
    have hfComponent := hcomponentEdgeOfVertex a hvComponent hvf
      (Or.inl hfgamma)
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

private theorem helper_hmissingPreserved_685.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSlot jSlot : Fin
    ett.rounds) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
    (gammaN deltaN : Fin k) (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k),
    ett.series.data.tree jSlot.succ.castSucc = Tj → ∀ (u : V) (beta : Fin k), ∀ (trace :
    ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a :
    Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
    (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
    (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈ TreeSequenceVertexSet
    (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → w =
    terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈
    TreeSequenceVertexSet B) → (∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent
    G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → MissingColors
    G (trace.coloring a.succ) v = MissingColors G (trace.coloring a.castSucc) v) → (∀ (a : Fin
    trace.steps) (v : V), Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
    (trace.gamma a) (trace.delta a) (Sum.inl u) → trace.gamma a ∈ PresentColors G
    (trace.coloring a.castSucc) v → trace.delta a ∈ PresentColors G (trace.coloring
    a.castSucc) v → MissingColors G (trace.coloring a.succ) v = MissingColors G
    (trace.coloring a.castSucc) v) → terminalSupport ∈ TreeSequenceVertexSet TjPrime →
    terminalSupport ≠ u → (∀ (a : Fin trace.steps) {v : V}, v ∈ TreeSequenceVertexSet TjPrime
    → v ≠ u → trace.gamma a ∉ MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap
    TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) :
    PartialEdgeColoring E k) v ∧ trace.delta a ∉ MissingColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) v) → ∀ (n : Fin (trace.steps + (1 : ℕ))), ∀ v ∈
    TreeSequenceVertexSet Tj ∪ (TreeSequenceVertexSet TjPrime).erase u, MissingColors G
    (trace.coloring n) v = MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap
    TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) :
    PartialEdgeColoring E k) v := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot jSlot terminalSupport
      hterminalSupport Tj TjPrime rho1 gammaN deltaN supportLength gamma delta hTjStored u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hstepData hvertexInitialSegment hmissingFixedOutside hmissingFixedInternal
      hterminalPrime hterminalNeU hprefixColorsNotMissing n
  induction n using Fin.induction with
  | zero =>
      intro v hv
      rw [trace.initialColoring]
  | succ a ih =>
      intro v hv
      rcases Finset.mem_union.mp hv with hvTj | hvPrime
      · by_cases hvTerminal : v = terminalSupport
        · subst v
          have hprimeErased : terminalSupport ∈
              (TreeSequenceVertexSet TjPrime).erase u :=
            Finset.mem_erase.mpr ⟨hterminalNeU, hterminalPrime⟩
          have hcurrent := ih terminalSupport
            (Finset.mem_union_right _ hprimeErased)
          obtain ⟨hgMu, hdMu⟩ :=
            hprefixColorsNotMissing a hterminalPrime hterminalNeU
          have hgCurrent : trace.gamma a ∉
              MissingColors G (trace.coloring a.castSucc) terminalSupport := by
            rw [hcurrent]
            exact hgMu
          have hdCurrent : trace.delta a ∉
              MissingColors G (trace.coloring a.castSucc) terminalSupport := by
            rw [hcurrent]
            exact hdMu
          by_cases hvComponent : Sum.inl terminalSupport ∈
              TwoColorComponent G (trace.coloring a.castSucc)
                (trace.gamma a) (trace.delta a) (Sum.inl u)
          · have hgPresent : trace.gamma a ∈
                PresentColors G (trace.coloring a.castSucc)
                  terminalSupport := by
              simpa [MissingColors] using hgCurrent
            have hdPresent : trace.delta a ∈
                PresentColors G (trace.coloring a.castSucc)
                  terminalSupport := by
              simpa [MissingColors] using hdCurrent
            exact (hmissingFixedInternal a terminalSupport hvComponent
              hgPresent hdPresent).trans hcurrent
          · exact (hmissingFixedOutside a hvComponent).trans hcurrent
        · have hsegment := (hstepData a).1
          rw [hTjStored] at hsegment
          have hvSlot := hvertexInitialSegment hsegment hvTj
          have hvOutside : Sum.inl v ∉
              TwoColorComponent G (trace.coloring a.castSucc)
                (trace.gamma a) (trace.delta a) (Sum.inl u) := by
            intro hvComponent
            exact hvTerminal ((hstepData a).2.2.2.1 v hvSlot hvComponent)
          exact (hmissingFixedOutside a hvOutside).trans
            (ih v (Finset.mem_union_left _ hvTj))
      · have hvPrimeData := Finset.mem_erase.mp hvPrime
        have hcurrent := ih v (Finset.mem_union_right _ hvPrime)
        obtain ⟨hgMu, hdMu⟩ := hprefixColorsNotMissing a
          hvPrimeData.2 hvPrimeData.1
        have hgCurrent : trace.gamma a ∉
            MissingColors G (trace.coloring a.castSucc) v := by
          rw [hcurrent]
          exact hgMu
        have hdCurrent : trace.delta a ∉
            MissingColors G (trace.coloring a.castSucc) v := by
          rw [hcurrent]
          exact hdMu
        by_cases hvComponent : Sum.inl v ∈
            TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u)
        · have hgPresent : trace.gamma a ∈
              PresentColors G (trace.coloring a.castSucc) v := by
            simpa [MissingColors] using hgCurrent
          have hdPresent : trace.delta a ∈
              PresentColors G (trace.coloring a.castSucc) v := by
            simpa [MissingColors] using hdCurrent
          exact (hmissingFixedInternal a v hvComponent hgPresent
            hdPresent).trans hcurrent
        · exact (hmissingFixedOutside a hvComponent).trans hcurrent

private theorem helper_hstageEdgeFixedStep_762.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot _ jSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tj _
    TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (_ gammaN deltaN : Fin k) (x
    : V) (supportLength : ℕ) (_ : Fin (supportLength + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin
    (supportLength + (1 : ℕ)) → Fin k), ett.series.data.tree jSlot.succ.castSucc = Tj → ∀ (u :
    V) (_ : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (beta
    : Fin k) (_ : Fin (Tj.length + (1 : ℕ))), ∀ (trace : ExtensionBaseAlgorithmCTrace ett
    terminalSupport hterminalSupport terminalSlot (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a : Fin trace.steps),
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
    (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
    (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈ TreeSequenceVertexSet
    (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → w =
    terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈
    TreeSequenceVertexSet B) → (∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inr f ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → Incident G v f → trace.coloring a.castSucc f = some (trace.gamma a) ∨ trace.coloring
    a.castSucc f = some (trace.delta a) → Sum.inl v ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) → ∀ (a : Fin trace.steps) (q :
    Fin Tj.length), trace.coloring a.succ (Tj.edge q) = trace.coloring a.castSucc (Tj.edge q) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot jSlot
      terminalSupport hterminalSupport Tj seed TjPrime rho1 gammaFirst gammaN deltaN x
      supportLength indices gamma delta hTjStored u exitPath beta zPosition
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hstepData hvertexInitialSegment hvertexOfComponentEdge a q
  obtain ⟨i, hi⟩ := Tj.attaches q
  let r : Fin (Tj.length + 1) := Fin.castLT i
    (Nat.lt_trans i.isLt (Nat.succ_lt_succ q.isLt))
  have hnewIncident : Incident G (Tj.vertex q.succ) (Tj.edge q) := by
    unfold Incident
    rw [hi]
    simp
  have holdIncident : Incident G (Tj.vertex r) (Tj.edge q) := by
    unfold Incident
    rw [hi]
    simp [r]
  have hverticesNe : Tj.vertex q.succ ≠ Tj.vertex r := by
    intro heq
    have hindexEq := Tj.vertex_injective heq
    have hvalEq := congrArg Fin.val hindexEq
    simp [r] at hvalEq
    omega
  have hnewTj : Tj.vertex q.succ ∈ TreeSequenceVertexSet Tj := by
    simp [TreeSequenceVertexSet]
  have holdTj : Tj.vertex r ∈ TreeSequenceVertexSet Tj := by
    simp [TreeSequenceVertexSet]
  have hsegment := (hstepData a).1
  rw [hTjStored] at hsegment
  have hnewSlot := hvertexInitialSegment hsegment hnewTj
  have holdSlot := hvertexInitialSegment hsegment holdTj
  rw [trace.transition]
  by_cases hfComponent : Sum.inr (Tj.edge q) ∈
      TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl u)
  · by_cases hfg : trace.coloring a.castSucc (Tj.edge q) =
        some (trace.gamma a)
    · have hnewComponent := hvertexOfComponentEdge a hfComponent
        hnewIncident (Or.inl hfg)
      have holdComponent := hvertexOfComponentEdge a hfComponent
        holdIncident (Or.inl hfg)
      have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
      have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
      exact False.elim (hverticesNe (hnewTerminal.trans holdTerminal.symm))
    · by_cases hfd : trace.coloring a.castSucc (Tj.edge q) =
          some (trace.delta a)
      · have hnewComponent := hvertexOfComponentEdge a hfComponent
          hnewIncident (Or.inr hfd)
        have holdComponent := hvertexOfComponentEdge a hfComponent
          holdIncident (Or.inr hfd)
        have hnewTerminal := (hstepData a).2.2.2.1 _ hnewSlot hnewComponent
        have holdTerminal := (hstepData a).2.2.2.1 _ holdSlot holdComponent
        exact False.elim
          (hverticesNe (hnewTerminal.trans holdTerminal.symm))
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd]
  · simp [TwoColorComponentSwap, hfComponent]

private theorem helper_hprimeEdgesPreserved_837.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tj
    seed TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (supportColors : Finset
    (Fin k)) (gammaN deltaN : Fin k) (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ))
    → Fin k) (u : V) (beta : Fin k), (∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) → ∀ c
    ∈ supportColors \ {deltaN}, (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    (TjPrime.edge a) ≠ some c) → ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
    hterminalSupport terminalSlot (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    u), (∀ (a : Fin trace.steps), trace.gamma a ∈ supportColors ∧ trace.delta a ∈
    supportColors) → (∀ (a : Fin trace.steps), deltaN ≠ trace.gamma a ∧ deltaN ≠ trace.delta
    a) → (∀ (n : Fin (trace.steps + (1 : ℕ))) (q : Fin Tj.length), trace.coloring n (Tj.edge
    q) = (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) (Tj.edge q)) →
    (∀ (q : Fin TjPrime.length), (↑q : ℕ) < seed.length → ∃ (r : Fin Tj.length), TjPrime.edge
    q = Tj.edge r) → ∀ (n : Fin (trace.steps + (1 : ℕ))) (q : Fin TjPrime.length),
    trace.coloring n (TjPrime.edge q) = (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime
    rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring
    E k) (TjPrime.edge q) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport Tj
      seed TjPrime rho1 supportColors gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro hmuAppendedEdges trace htraceSupportColors htraceDeltaNNe hstageEdgesPreserved
      hseedEdgeCommon n
  induction n using Fin.induction with
  | zero =>
      intro q
      rw [trace.initialColoring]
  | succ a ih =>
      intro q
      by_cases hqSeed : q.val < seed.length
      · obtain ⟨r, hr⟩ := hseedEdgeCommon q hqSeed
        rw [hr]
        exact hstageEdgesPreserved a.succ r
      · have hqAfter : seed.length ≤ q.val := Nat.le_of_not_gt hqSeed
        have hfg : trace.coloring a.castSucc (TjPrime.edge q) ≠
            some (trace.gamma a) := by
          rw [ih q]
          apply hmuAppendedEdges q hqAfter (trace.gamma a)
          exact Finset.mem_sdiff.mpr
            ⟨(htraceSupportColors a).1,
              by simpa using (htraceDeltaNNe a).1.symm⟩
        have hfd : trace.coloring a.castSucc (TjPrime.edge q) ≠
            some (trace.delta a) := by
          rw [ih q]
          apply hmuAppendedEdges q hqAfter (trace.delta a)
          exact Finset.mem_sdiff.mpr
            ⟨(htraceSupportColors a).2,
              by simpa using (htraceDeltaNNe a).2.symm⟩
        have hfgMu : mu0 (TjPrime.edge q) ≠ some (trace.gamma a) := by
          intro h
          exact hfg ((ih q).trans h)
        have hfdMu : mu0 (TjPrime.edge q) ≠ some (trace.delta a) := by
          intro h
          exact hfd ((ih q).trans h)
        rw [trace.transition]
        by_cases hfComponent : Sum.inr (TjPrime.edge q) ∈
            TwoColorComponent G (trace.coloring a.castSucc)
              (trace.gamma a) (trace.delta a) (Sum.inl u)
        · simp [TwoColorComponentSwap, hfComponent, hfgMu, hfdMu, ih q]
        · simp [TwoColorComponentSwap, hfComponent, ih q]

private theorem helper_hswapMakesGammaMissing_658.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot jSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k) (u : V) (beta : Fin k),
    ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a :
    Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
    (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
    (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈ TreeSequenceVertexSet
    (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → w =
    terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ (a : Fin trace.steps),
    trace.gamma a ≠ trace.delta a) → (∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inl v ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → Incident G v f → trace.coloring a.castSucc f = some (trace.gamma a) ∨ trace.coloring
    a.castSucc f = some (trace.delta a) → Sum.inr f ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) → ∀ (a : Fin trace.steps),
    trace.gamma a ∈ MissingColors G (trace.coloring a.succ) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot jSlot terminalSupport
      hterminalSupport TjPrime rho1 gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hstepData htraceColorsNe hcomponentEdgeOfVertex a
  have hdeltaMissingStep := (hstepData a).2.1
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
  · have hfold : trace.coloring a.castSucc f =
        some (trace.delta a) := by
      by_cases hfg : trace.coloring a.castSucc f = some (trace.gamma a)
      · rw [trace.transition] at hfnew
        have : trace.delta a = trace.gamma a := by
          simpa [TwoColorComponentSwap, hfComponent, hfg] using hfnew
        exact False.elim ((htraceColorsNe a) this.symm)
      · by_cases hfd : trace.coloring a.castSucc f =
            some (trace.delta a)
        · exact hfd
        · rw [trace.transition] at hfnew
          have : trace.coloring a.castSucc f =
              some (trace.gamma a) := by
            simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfnew
          exact False.elim (hfg this)
    have hdeltaNotPresent : trace.delta a ∉
        PresentColors G (trace.coloring a.castSucc) u := by
      simpa [MissingColors] using hdeltaMissingStep
    exact hdeltaNotPresent (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨f, huf, hfold⟩)
  · have hfold : trace.coloring a.castSucc f =
        some (trace.gamma a) := by
      rw [trace.transition] at hfnew
      simpa [TwoColorComponentSwap, hfComponent] using hfnew
    exact hfComponent
      (hcomponentEdgeOfVertex a huComponent huf (Or.inl hfold))

private theorem helper_branch_945.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot jSlot : Fin
    ett.rounds), (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds → (↑preterminalSlot : ℕ) <
    (↑terminalSlot : ℕ) → ∀ (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (Tj Tn _ TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring
    E k) (gammaFirst gammaN deltaN : Fin k) (x : V), preterminalSlot ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → ∀ (supportLength : ℕ) (indices : Fin (supportLength + (1 : ℕ)) → Fin
    ett.rounds) (gamma delta : Fin (supportLength + (1 : ℕ)) → Fin k), (∀ (a c : Fin
    (supportLength + (1 : ℕ))), (↑a : ℕ) < (↑c : ℕ) → (↑(indices a) : ℕ) < (↑(indices c) : ℕ))
    → (∀ (s : Fin ett.rounds), s ∈ ExtensionBaseSupportClass ett terminalSupport
    hterminalSupport terminalSupport ↔ ∃ (a : Fin (supportLength + (1 : ℕ))), indices a = s) →
    indices (Fin.last supportLength) = terminalSlot → (∀ (a : Fin (supportLength + (1 : ℕ))),
    ett.series.data.chosenVertex (indices a).succ = some terminalSupport) → (∀ (a : Fin
    (supportLength + (1 : ℕ))), ett.series.data.kind (indices a).succ = some
    TashkinovExtensionKind.PE) → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.gamma
    (indices a).succ = some (gamma a)) → (∀ (a : Fin (supportLength + (1 : ℕ))),
    ett.series.data.delta (indices a).succ = some (delta a)) → (∀ (a : Fin (supportLength + (1
    : ℕ))), ett.series.data.stored (indices a).succ = {gamma a, delta a}) → (∀ (a : Fin
    supportLength), gamma a.succ = delta a.castSucc) → Function.Injective (Fin.cons (gamma (0
    : Fin (supportLength + (1 : ℕ)))) delta) → gamma (0 : Fin (supportLength + (1 : ℕ))) =
    gammaFirst → (∀ (u : V) (beta : Fin k), u ∈ TreeSequenceVertexSet TjPrime → u ∉
    TreeSequenceVertexSet Tn → beta ∈ MissingColors G rho1 u → ∀ (a : Fin supportLength),
    gamma a.castSucc ∈ PresentColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime
    rho1 beta deltaN) gammaN beta (Sum.inl u)) u) → ∀ (u : V) (_ : (TwoColorIncidenceGraph G
    rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (beta : Fin k) (_ : Fin (Tj.length + (1
    : ℕ))), gamma (Fin.last supportLength) = gammaN → ∀ (trace : ExtensionBaseAlgorithmCTrace
    ett terminalSupport hterminalSupport terminalSlot (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a : Fin trace.steps),
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
    (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
    (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈ TreeSequenceVertexSet
    (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → w =
    terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ (q : Fin (supportLength + (1
    : ℕ))), gamma q ≠ delta q) → (∀ (a : Fin trace.steps), ∃ (q : Fin (supportLength + (1 :
    ℕ))), indices q = trace.slot a) → (∀ (a : Fin trace.steps) (q : Fin (supportLength + (1 :
    ℕ))), indices q = trace.slot a → trace.gamma a = gamma q) → (∀ (a : Fin trace.steps) (q :
    Fin (supportLength + (1 : ℕ))), indices q = trace.slot a → trace.delta a = delta q) → (∀
    (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (∀ (a : Fin trace.steps) {v : V}
    {f : E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a)
    (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f = some
    (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inr f ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u)) → gammaFirst ∈ MissingColors G (trace.coloring (Fin.last trace.steps) :
    PartialEdgeColoring E k) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot jSlot hterminalAtEnd
      hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime rho1 gammaFirst
      gammaN deltaN x hpreterminalClass supportLength indices gamma delta hincreasing hclass
      hterminalIndex hsupport hkind hgamma hdelta hstored hchain hdistinct hfirstGamma
      hpreterminalGammaPresent u exitPath beta zPosition
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro hgammaLast trace
  set rho3 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps)
  intro hstepData hgammaDeltaNe htraceIndex htraceGamma htraceDelta htraceColorsNe
      hcomponentEdgeOfVertex
  have hswapMakesGammaMissing := @helper_hswapMakesGammaMissing_658 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@terminalSlot)
      (@jSlot) (@terminalSupport) (@hterminalSupport) (@TjPrime) (@rho1) (@gammaN) (@deltaN)
      (@supportLength) (@gamma) (@delta) (@u) (@beta) (@trace) (@hstepData) (@htraceColorsNe)
      (@hcomponentEdgeOfVertex)
  have hsupportLengthPositive : 0 < supportLength := by
    obtain ⟨q, hq⟩ :=
      (hclass preterminalSlot).mp (Finset.mem_erase.mp hpreterminalClass).2
    have hqNeLast : q ≠ Fin.last supportLength := by
      intro h
      have hslots : preterminalSlot = terminalSlot := by
        rw [← hq, h, hterminalIndex]
      omega
    by_contra hnot
    have hzero : supportLength = 0 := Nat.eq_zero_of_not_pos hnot
    subst supportLength
    apply hqNeLast
    apply Fin.ext
    omega
  have hstepsPositive : 0 < trace.steps := by
    by_contra hnot
    have hzero : trace.steps = 0 := Nat.eq_zero_of_not_pos hnot
    have hmem := hpreterminalClass
    rw [← trace.enumerates] at hmem
    obtain ⟨a, -, -⟩ := Finset.mem_image.mp hmem
    exact Fin.elim0 (Fin.cast hzero a)
  let lastStep : Fin trace.steps := ⟨trace.steps - 1, by omega⟩
  have hzeroInErased : (indices 0) ∈
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
        terminalSupport).erase terminalSlot := by
    apply Finset.mem_erase.mpr
    constructor
    · intro hzeroTerminal
      have hstrict := hincreasing (0 : Fin (supportLength + 1))
        (Fin.last supportLength) (by simpa using hsupportLengthPositive)
      rw [hzeroTerminal, hterminalIndex] at hstrict
      exact (Nat.lt_irrefl _ hstrict)
    · exact (hclass (indices 0)).mpr ⟨0, rfl⟩
  have hindexZeroLe (q : Fin (supportLength + 1)) :
      (indices 0).val ≤ (indices q).val := by
    by_cases hq : q = 0
    · subst q
      exact Nat.le_refl _
    · have hqPositive : (0 : Fin (supportLength + 1)).val < q.val := by
        simp only [Fin.val_zero]
        exact Nat.pos_of_ne_zero (by
          intro hval
          apply hq
          apply Fin.ext
          simpa using hval)
      exact Nat.le_of_lt (hincreasing 0 q hqPositive)
  have hlastSlot : trace.slot lastStep = indices 0 := by
    have hmem : indices 0 ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hzeroInErased
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hmem
    have hble : b.val ≤ lastStep.val := by
      simp [lastStep]
      omega
    rcases lt_or_eq_of_le hble with hlt | heq
    · have hdesc := trace.strictlyDescending b lastStep hlt
      rw [hb] at hdesc
      obtain ⟨q, hq⟩ := htraceIndex lastStep
      rw [← hq] at hdesc
      exact False.elim ((Nat.not_lt_of_ge (hindexZeroLe q)) hdesc)
    · have hbeq : b = lastStep := Fin.ext heq
      rwa [← hbeq]
  have hlastGamma : trace.gamma lastStep = gamma 0 :=
    htraceGamma lastStep 0 hlastSlot.symm
  have hlastIndex : lastStep.succ =
      (Fin.last trace.steps : Fin (trace.steps + 1)) := by
    apply Fin.ext
    simp [lastStep]
    omega
  change gammaFirst ∈
    MissingColors G (trace.coloring (Fin.last trace.steps)) u
  rw [← hfirstGamma, ← hlastGamma, ← hlastIndex]
  exact hswapMakesGammaMissing lastStep

private theorem helper_hterminalNoMissing_940.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (supportColors : Finset
    (Fin k)) (gammaN deltaN : Fin k), (supportColors = (ExtensionBaseSupportClass ett
    terminalSupport hterminalSupport terminalSupport).biUnion fun (s : Fin ett.rounds) ↦
    ett.series.data.stored s.succ) → (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
    some deltaS → deltaN ≠ gammaS ∧ deltaN ≠ deltaS) → ∀ (supportLength : ℕ) (indices : Fin
    (supportLength + (1 : ℕ)) → Fin ett.rounds) (gamma delta : Fin (supportLength + (1 : ℕ)) →
    Fin k), (∀ (s : Fin ett.rounds), s ∈ ExtensionBaseSupportClass ett terminalSupport
    hterminalSupport terminalSupport ↔ ∃ (a : Fin (supportLength + (1 : ℕ))), indices a = s) →
    (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some
    (gamma a)) → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.delta (indices
    a).succ = some (delta a)) → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.stored
    (indices a).succ = {gamma a, delta a}) → ∀ (u : V) (beta : Fin k), MissingColors G
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    terminalSupport ∩ supportColors = {deltaN} → (MissingColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) terminalSupport ∩ ((ExtensionBaseSupportClass ett
    terminalSupport hterminalSupport terminalSupport).erase terminalSlot).biUnion fun (s : Fin
    ett.rounds) ↦ ett.series.data.stored s.succ) = ∅ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 supportColors gammaN deltaN hsupportSet hdeltaEarlier supportLength indices
      gamma delta hclass hgamma hdelta hstored u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1
                          beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN
                          beta (Sum.inl u)
  intro hmuTerminalMissing
  apply Finset.eq_empty_of_forall_notMem
  intro c hc
  have hcMissing := (Finset.mem_inter.mp hc).1
  have hcUnion := (Finset.mem_inter.mp hc).2
  have hcSupport : c ∈ supportColors := by
    rw [hsupportSet]
    obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp hcUnion
    exact Finset.mem_biUnion.mpr ⟨s, (Finset.mem_erase.mp hs).2, hcs⟩
  have hcDelta : c = deltaN := by
    have hcTerminal : c ∈
        MissingColors G mu0 terminalSupport ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hcMissing, hcSupport⟩
    rw [hmuTerminalMissing] at hcTerminal
    simpa using hcTerminal
  obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp hcUnion
  obtain ⟨a, ha⟩ := (hclass s).mp (Finset.mem_erase.mp hs).2
  have hgs : ett.series.data.gamma s.succ = some (gamma a) := by
    rw [← ha]
    exact hgamma a
  have hds : ett.series.data.delta s.succ = some (delta a) := by
    rw [← ha]
    exact hdelta a
  have hne := hdeltaEarlier s (gamma a) (delta a) hs hgs hds
  rw [← ha, hstored a] at hcs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcs
  rcases hcs with hca | hca
  · exact hne.1 (hcDelta.symm.trans hca)
  · exact hne.2 (hcDelta.symm.trans hca)

private theorem helper_hstableOutput_1191.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tj
    TjPrime : TreeSequence G e0) (phiJ rho1 : PartialEdgeColoring E k) (Dprev : Finset (Fin
    k)) (gammaN deltaN : Fin k) (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj) (u
    : V) (beta : Fin k), StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) → ∀ (trace :
    ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (n :
    Fin (trace.steps + (1 : ℕ))) (f : E), (∃ w ∈ TreeVerticesBefore Tj terminalSupport
    hterminalTj, Incident G w f) → trace.coloring n f = (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) f) → StableColoringBeforeVertex Tj terminalSupport
    hterminalTj Dprev phiJ (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport Tj
      TjPrime phiJ rho1 Dprev gammaN deltaN hterminalTj u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro hmuStable trace
  set rho3 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps)
  intro hbeforeEdgesPreserved
  unfold StableColoringBeforeVertex at hmuStable ⊢
  constructor
  · intro f hfIncident hfControlled
    exact (hbeforeEdgesPreserved (Fin.last trace.steps) f hfIncident).trans
      (hmuStable.1 f hfIncident hfControlled)
  · intro w hw
    have hmissingFinal : MissingColors G rho3 w = MissingColors G mu0 w := by
      apply Finset.ext
      intro c
      simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
        PresentColors, Finset.mem_filter]
      constructor
      · intro hc hold
        obtain ⟨f, hwf, hfc⟩ := hold
        apply hc
        exact ⟨f, hwf, (hbeforeEdgesPreserved (Fin.last trace.steps) f
          ⟨w, hw, hwf⟩).trans hfc⟩
      · intro hc hnew
        obtain ⟨f, hwf, hfc⟩ := hnew
        apply hc
        exact ⟨f, hwf, (hbeforeEdgesPreserved (Fin.last trace.steps) f
          ⟨w, hw, hwf⟩).symm.trans hfc⟩
    exact hmissingFinal.trans (hmuStable.2 w hw)

private theorem helper_hdeltaNMissingPreserved_1280.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (u
    : V) (beta : Fin k) (z : V), ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
    hterminalSupport terminalSlot (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    u), (∀ (a : Fin trace.steps), deltaN ≠ trace.gamma a ∧ deltaN ≠ trace.delta a) → (∀ (a :
    Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠ trace.delta a →
    (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c)) → deltaN ∈
    MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) z → deltaN ∈
    MissingColors G (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) z := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN u beta z
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace
  set rho3 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps)
  intro htraceDeltaNNe hunaffectedValue hdeltaMu
  have hpreserved : ∀ n : Fin (trace.steps + 1),
      deltaN ∈ MissingColors G (trace.coloring n) z := by
    intro n
    induction n using Fin.induction with
    | zero => simpa [trace.initialColoring] using hdeltaMu
    | succ a ih =>
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hpresent
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] at hpresent
        obtain ⟨f, hzf, hfcolor⟩ := hpresent
        have hold : trace.coloring a.castSucc f = some deltaN :=
          (hunaffectedValue a f deltaN (htraceDeltaNNe a).1
            (htraceDeltaNNe a).2).mp hfcolor
        have hnotPresent : deltaN ∉
            PresentColors G (trace.coloring a.castSucc) z := by
          simpa [MissingColors] using ih
        exact hnotPresent (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨f, hzf, hold⟩)
  exact hpreserved (Fin.last trace.steps)

private theorem helper_branch_1307.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tj
    TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (u :
    V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (beta : Fin k) (z : V) (hz : z ∈
    TreeSequenceVertexSet Tj), (∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ {z} ∪ (TreeVerticesBefore
    TjPrime u huPrime ∪ {u})).erase u).erase z, MissingColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) v = MissingColors G rho1 v) → ∀ (trace :
    ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ {A :
    TreeSequence G e0} {v w : V} (hv : v ∈ TreeSequenceVertexSet A), w ∈ TreeVerticesBefore A
    v hv → w ∈ TreeSequenceVertexSet A ∧ w ≠ v) → (∀ (n : Fin (trace.steps + (1 : ℕ))), ∀ v ∈
    TreeSequenceVertexSet Tj ∪ (TreeSequenceVertexSet TjPrime).erase u, MissingColors G
    (trace.coloring n) v = MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap
    TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) :
    PartialEdgeColoring E k) v) → ∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ {z} ∪
    (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z, MissingColors G
    (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) v = MissingColors G rho1
    v := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      Tj TjPrime rho1 gammaN deltaN u huPrime beta z hz
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro hmuMissing trace
  set rho3 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps)
  intro hbeforeMemberAndNe hmissingPreserved v hv
  have hvOuter := Finset.mem_erase.mp hv
  have hvInner := Finset.mem_erase.mp hvOuter.2
  have hvTrace : v ∈ TreeSequenceVertexSet Tj ∪
      (TreeSequenceVertexSet TjPrime).erase u := by
    rcases Finset.mem_union.mp hvInner.2 with hvLeft | hvRight
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hvLeft with hvBefore | hvZ
      · exact (hbeforeMemberAndNe hz hvBefore).1
      · have hvz : v = z := Finset.mem_singleton.mp hvZ
        subst v
        exact hz
    · apply Finset.mem_union_right
      apply Finset.mem_erase.mpr
      refine ⟨hvInner.1, ?_⟩
      rcases Finset.mem_union.mp hvRight with hvBefore | hvU
      · exact (hbeforeMemberAndNe huPrime hvBefore).1
      · have hvu : v = u := Finset.mem_singleton.mp hvU
        subst v
        exact huPrime
  exact (hmissingPreserved (Fin.last trace.steps) v hvTrace).trans
    (hmuMissing v hv)

private theorem helper_hgammaDeltaNe_1160 :
    open scoped Classical in ∀ {k : ℕ} (supportLength : ℕ) (gamma delta : Fin (supportLength +
    (1 : ℕ)) → Fin k), (∀ (a : Fin supportLength), gamma a.succ = delta a.castSucc) →
    Function.Injective (Fin.cons (gamma (0 : Fin (supportLength + (1 : ℕ)))) delta) → ∀ (q :
    Fin (supportLength + (1 : ℕ))), gamma q ≠ delta q := by
  classical
  intro k supportLength gamma delta hchain hdistinct q
  have hconsGamma :
      (Fin.cons (gamma 0) delta : Fin (supportLength + 2) → Fin k)
          q.castSucc = gamma q := by
    refine Fin.cases ?_ (fun r => ?_) q
    · simp
    · rw [show (Fin.succ r).castSucc = r.castSucc.succ by
        apply Fin.ext
        rfl]
      rw [Fin.cons_succ]
      exact (hchain r).symm
  have hconsDelta :
      (Fin.cons (gamma 0) delta : Fin (supportLength + 2) → Fin k)
          q.succ = delta q := by simp
  intro heq
  have hindexEq : q.castSucc = q.succ :=
    hdistinct (hconsGamma.trans (heq.trans hconsDelta.symm))
  exact (ne_of_lt Fin.castSucc_lt_succ) hindexEq

private theorem helper_hvertexOfComponentEdge_1229.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k) (u : V) (beta : Fin k),
    ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u) (a : Fin
    trace.steps) {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G (trace.coloring a.castSucc)
    (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f
    = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inl v ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace a v f hfComponent hvf hfColor
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inr f) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    at hfComponent
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl v) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
  have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).Adj (Sum.inl v) (Sum.inr f) := by
    simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    hadj).trans hfComponent

private theorem helper_hcomponentEdgeOfVertex_1252.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k) (u : V) (beta : Fin k),
    ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u) (a : Fin
    trace.steps) {v : V} {f : E}, Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc)
    (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring a.castSucc f
    = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) → Sum.inr f ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace a v f hvComponent hvf hfColor
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl v) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
    at hvComponent
  change (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inr f) =
    (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).connectedComponentMk (Sum.inl u)
  have hadj : (TwoColorIncidenceGraph G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a)).Adj (Sum.inr f) (Sum.inl v) := by
    simpa [TwoColorIncidenceGraph] using And.intro hvf hfColor
  exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    hadj).trans hvComponent

private theorem helper_hfixedOutsideComponent_1275.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ)) → Fin k) (u : V) (beta : Fin k),
    ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a :
    Fin trace.steps) {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f → trace.coloring
    a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some (trace.delta a) →
    Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
    a) (Sum.inl u)) → ∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ∀ {f : E},
    Incident G v f → trace.coloring a.succ f = trace.coloring a.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hvertexOfComponentEdge a v hvOutside f hvf
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

private theorem helper_hmissingFixedOutside_1293.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (u
    : V) (beta : Fin k), ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
    hterminalSupport terminalSlot (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    u), (∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ∀ {f : E}, Incident G v f →
    trace.coloring a.succ f = trace.coloring a.castSucc f) → ∀ (a : Fin trace.steps) {v : V},
    Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta
    a) (Sum.inl u) → MissingColors G (trace.coloring a.succ) v = MissingColors G
    (trace.coloring a.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hfixedOutsideComponent a v hvOutside
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
    exact hc ⟨f, hvf,
      (hfixedOutsideComponent a hvOutside hvf).symm.trans hfc⟩

private theorem helper_hbeforeEdgesPreserved_1337.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring
    E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
    ExtendedTashkinovTree G k e0 input T generating) (terminalSlot jSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tj
    TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj) (supportLength : ℕ) (_ _ : Fin
    (supportLength + (1 : ℕ)) → Fin k), ett.series.data.tree jSlot.succ.castSucc = Tj → ∀ (u :
    V) (beta : Fin k), ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
    hterminalSupport terminalSlot (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    u), (∀ (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree
    jSlot.succ.castSucc) (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈
    MissingColors G (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈
    TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈
    TreeSequenceVertexSet B) → (∀ {A : TreeSequence G e0} {v w : V} (hv : v ∈
    TreeSequenceVertexSet A), w ∈ TreeVerticesBefore A v hv → w ∈ TreeSequenceVertexSet A ∧ w
    ≠ v) → (∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ∀ {f : E}, Incident G v f →
    trace.coloring a.succ f = trace.coloring a.castSucc f) → ∀ (n : Fin (trace.steps + (1 :
    ℕ))) (f : E), (∃ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, Incident G w f) →
    trace.coloring n f = (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta
    deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot jSlot terminalSupport
      hterminalSupport Tj TjPrime rho1 gammaN deltaN hterminalTj supportLength gamma delta
      hTjStored u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro trace hstepData hvertexInitialSegment hbeforeMemberAndNe hfixedOutsideComponent n
  induction n using Fin.induction with
  | zero =>
      intro f hf
      simpa using congrFun trace.initialColoring f
  | succ a ih =>
      intro f hf
      obtain ⟨w, hw, hwf⟩ := hf
      have hwData := hbeforeMemberAndNe hterminalTj hw
      have hsegment := (hstepData a).1
      rw [hTjStored] at hsegment
      have hwSlot := hvertexInitialSegment hsegment hwData.1
      have hwOutside : Sum.inl w ∉
          TwoColorComponent G (trace.coloring a.castSucc)
            (trace.gamma a) (trace.delta a) (Sum.inl u) := by
        intro hwComponent
        exact hwData.2 ((hstepData a).2.2.2.1 w hwSlot hwComponent)
      exact (hfixedOutsideComponent a hwOutside hwf).trans
        (ih f ⟨w, hw, hwf⟩)

private theorem helper_hprefixColorsNotMissing_1371.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
    (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (supportColors : Finset
    (Fin k)) (gammaN deltaN : Fin k) (supportLength : ℕ) (_ _ : Fin (supportLength + (1 : ℕ))
    → Fin k) (u : V) (beta : Fin k), (((TreeSequenceVertexSet TjPrime).erase u).biUnion fun (v
    : V) ↦ MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta
    deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) v) ∩
    supportColors = {deltaN} → ∀ (trace : ExtensionBaseAlgorithmCTrace ett terminalSupport
    hterminalSupport terminalSlot (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    u), (∀ (a : Fin trace.steps), trace.gamma a ∈ supportColors ∧ trace.delta a ∈
    supportColors) → (∀ (a : Fin trace.steps), deltaN ≠ trace.gamma a ∧ deltaN ≠ trace.delta
    a) → ∀ (a : Fin trace.steps) {v : V}, v ∈ TreeSequenceVertexSet TjPrime → v ≠ u →
    trace.gamma a ∉ MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime
    rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring
    E k) v ∧ trace.delta a ∉ MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap
    TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) :
    PartialEdgeColoring E k) v := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 supportColors gammaN deltaN supportLength gamma delta u beta
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  intro hmuPrimeMissing trace htraceSupportColors htraceDeltaNNe a v hvPrime hvU
  have exclude (c : Fin k) (hcSupport : c ∈ supportColors)
      (hcDelta : deltaN ≠ c) : c ∉ MissingColors G mu0 v := by
    intro hcMissing
    have hcUnion : c ∈
        ((TreeSequenceVertexSet TjPrime).erase u).biUnion
          (fun w => MissingColors G mu0 w) :=
      Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_erase.mpr ⟨hvU, hvPrime⟩, hcMissing⟩
    have hcInter := Finset.mem_inter.mpr ⟨hcUnion, hcSupport⟩
    rw [hmuPrimeMissing] at hcInter
    have : c = deltaN := by simpa using hcInter
    exact hcDelta this.symm
  exact ⟨exclude (trace.gamma a) (htraceSupportColors a).1
      (htraceDeltaNNe a).1,
    exclude (trace.delta a) (htraceSupportColors a).2
      (htraceDeltaNNe a).2⟩

private theorem helper_continuation_1506.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot
    jSlot : Fin ett.rounds), (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds → (↑preterminalSlot :
    ℕ) < (↑terminalSlot : ℕ) → ∀ (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (Tj Tn seed TjPrime : TreeSequence G e0) (phiJ rho1 :
    PartialEdgeColoring E k) (Dprev supportColors : Finset (Fin k)) (gammaFirst gammaN deltaN
    : Fin k) (x : V), TreeSequenceInitialSegment Tj Tn → TreeSequenceInitialSegment seed Tj →
    TreeSequenceInitialSegment seed TjPrime → ∀ (hterminalTj : terminalSupport ∈
    TreeSequenceVertexSet Tj), terminalSupport ∈ TreeSequenceVertexSet seed → preterminalSlot
    ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → ∀ (supportLength : ℕ) (indices : Fin (supportLength + (1 : ℕ)) → Fin
    ett.rounds) (gamma delta : Fin (supportLength + (1 : ℕ)) → Fin k), (∀ (a c : Fin
    (supportLength + (1 : ℕ))), (↑a : ℕ) < (↑c : ℕ) → (↑(indices a) : ℕ) < (↑(indices c) : ℕ))
    → (∀ (s : Fin ett.rounds), s ∈ ExtensionBaseSupportClass ett terminalSupport
    hterminalSupport terminalSupport ↔ ∃ (a : Fin (supportLength + (1 : ℕ))), indices a = s) →
    indices (Fin.last supportLength) = terminalSlot → (∀ (a : Fin (supportLength + (1 : ℕ))),
    ett.series.data.chosenVertex (indices a).succ = some terminalSupport) → (∀ (a : Fin
    (supportLength + (1 : ℕ))), ett.series.data.kind (indices a).succ = some
    TashkinovExtensionKind.PE) → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.gamma
    (indices a).succ = some (gamma a)) → (∀ (a : Fin (supportLength + (1 : ℕ))),
    ett.series.data.delta (indices a).succ = some (delta a)) → (∀ (a : Fin (supportLength + (1
    : ℕ))), ett.series.data.stored (indices a).succ = {gamma a, delta a}) → (∀ (a : Fin
    supportLength), gamma a.succ = delta a.castSucc) → Function.Injective (Fin.cons (gamma (0
    : Fin (supportLength + (1 : ℕ)))) delta) → ett.series.data.tree jSlot.succ.castSucc = Tj →
    gamma (0 : Fin (supportLength + (1 : ℕ))) = gammaFirst → (∀ (u : V) (beta : Fin k), u ∈
    TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet Tn → beta ∈ MissingColors G rho1
    u → ∀ (a : Fin supportLength), gamma a.castSucc ∈ PresentColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) u) → ∀ (u : V)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime), u ∉ TreeSequenceVertexSet Tn → ∀ (_ :
    (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (beta : Fin k)
    (z : V) (hz : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin (Tj.length + (1 : ℕ))),
    StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) → (∀ v ∈
    ((TreeVerticesBefore Tj z hz ∪ {z} ∪ (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase
    u).erase z, MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    v = MissingColors G rho1 v) → (∀ (f : E), ((∃ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ)
    ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨ ∃ (a : Fin TjPrime.length) (uPosition :
    Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u ∧ (↑a : ℕ) < (↑uPosition :
    ℕ) ∧ TjPrime.edge a = f) → (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    f = rho1 f) → (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) z) → (z ∈
    TreeVerticesBefore TjPrime u huPrime → MissingColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) z = MissingColors G rho1 z) →
    (((TreeSequenceVertexSet TjPrime).erase u).biUnion fun (v : V) ↦ MissingColors G
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) v) ∩
    supportColors = {deltaN} → (∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) → ∀ c ∈
    supportColors \ {deltaN}, (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta
    deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    (TjPrime.edge a) ≠ some c) → gamma (Fin.last supportLength) = gammaN → ∀ (trace :
    ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u), (∀ (a :
    Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
    (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈ MissingColors G
    (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈ TreeSequenceVertexSet
    (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → w =
    terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ (q : Fin (supportLength + (1
    : ℕ))), gamma q ≠ delta q) → (∀ (a : Fin trace.steps), ∃ (q : Fin (supportLength + (1 :
    ℕ))), indices q = trace.slot a) → (∀ (a : Fin trace.steps) (q : Fin (supportLength + (1 :
    ℕ))), indices q = trace.slot a → trace.gamma a = gamma q) → (∀ (a : Fin trace.steps) (q :
    Fin (supportLength + (1 : ℕ))), indices q = trace.slot a → trace.delta a = delta q) → (∀
    (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (∀ (a : Fin trace.steps),
    trace.gamma a ∈ supportColors ∧ trace.delta a ∈ supportColors) → (∀ (a : Fin trace.steps),
    deltaN ≠ trace.gamma a ∧ deltaN ≠ trace.delta a) → (∀ {A B : TreeSequence G e0},
    TreeSequenceInitialSegment A B → ∀ {v : V}, v ∈ TreeSequenceVertexSet A → v ∈
    TreeSequenceVertexSet B) → (∀ {A : TreeSequence G e0} {v w : V} (hv : v ∈
    TreeSequenceVertexSet A), w ∈ TreeVerticesBefore A v hv → w ∈ TreeSequenceVertexSet A ∧ w
    ≠ v) → (∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inr f ∈ TwoColorComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → Incident G v f →
    trace.coloring a.castSucc f = some (trace.gamma a) ∨ trace.coloring a.castSucc f = some
    (trace.delta a) → Sum.inl v ∈ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma
    a) (trace.delta a) (Sum.inl u)) → (∀ (a : Fin trace.steps) {v : V} {f : E}, Sum.inl v ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → Incident G v f → trace.coloring a.castSucc f = some (trace.gamma a) ∨ trace.coloring
    a.castSucc f = some (trace.delta a) → Sum.inr f ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u)) → (∀ (a : Fin trace.steps) {v :
    V}, Sum.inl v ∉ TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a)
    (trace.delta a) (Sum.inl u) → ∀ {f : E}, Incident G v f → trace.coloring a.succ f =
    trace.coloring a.castSucc f) → (∀ (a : Fin trace.steps) {v : V}, Sum.inl v ∉
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → MissingColors G (trace.coloring a.succ) v = MissingColors G (trace.coloring
    a.castSucc) v) → (∀ (a : Fin trace.steps) (f : E) (c : Fin k), c ≠ trace.gamma a → c ≠
    trace.delta a → (trace.coloring a.succ f = some c ↔ trace.coloring a.castSucc f = some c))
    → (∀ (a : Fin trace.steps) (v : V), Sum.inl v ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → trace.gamma a ∈ PresentColors G
    (trace.coloring a.castSucc) v → trace.delta a ∈ PresentColors G (trace.coloring
    a.castSucc) v → MissingColors G (trace.coloring a.succ) v = MissingColors G
    (trace.coloring a.castSucc) v) → StableColoringBeforeVertex Tj terminalSupport hterminalTj
    Dprev phiJ (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) ∧ (∀ v ∈
    ((TreeVerticesBefore Tj z hz ∪ {z} ∪ (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase
    u).erase z, MissingColors G (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E
    k) v = MissingColors G rho1 v) ∧ (∀ (f : E), ((∃ (a : Fin Tj.length), seed.length ≤ (↑a :
    ℕ) ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨ ∃ (a : Fin TjPrime.length) (uPosition
    : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u ∧ (↑a : ℕ) < (↑uPosition :
    ℕ) ∧ TjPrime.edge a = f) → (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E
    k) f = rho1 f) ∧ (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G (trace.coloring
    (Fin.last trace.steps) : PartialEdgeColoring E k) z) ∧ (z ∈ TreeVerticesBefore TjPrime u
    huPrime → MissingColors G (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E
    k) z = MissingColors G rho1 z) ∧ gammaFirst ∈ MissingColors G (trace.coloring (Fin.last
    trace.steps) : PartialEdgeColoring E k) u := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot jSlot
      hterminalAtEnd hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ
      rho1 Dprev supportColors gammaFirst gammaN deltaN x hTjN hseedJ hseedPrime hterminalTj
      hterminalSeed hpreterminalClass supportLength indices gamma delta hincreasing hclass
      hterminalIndex hsupport hkind hgamma hdelta hstored hchain hdistinct hTjStored hfirstGamma
      hpreterminalGammaPresent u huPrime huOutside exitPath beta z hz zPosition
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1
                                                                beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN
                                                                beta (Sum.inl u)
  intro hmuStable hmuMissing hmuEdges hmuBeta hmuZ hmuPrimeMissing hmuAppendedEdges hgammaLast trace
  set rho3 : PartialEdgeColoring E k := trace.coloring
                                                                                  (Fin.last
                                                                                  trace.steps)
  intro hstepData hgammaDeltaNe htraceIndex htraceGamma htraceDelta htraceColorsNe
      htraceSupportColors htraceDeltaNNe hvertexInitialSegment hbeforeMemberAndNe
      hvertexOfComponentEdge hcomponentEdgeOfVertex hfixedOutsideComponent hmissingFixedOutside
      hunaffectedValue hmissingFixedInternal
  have hbeforeEdgesPreserved := @helper_hbeforeEdgesPreserved_1337 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot jSlot terminalSupport
      hterminalSupport Tj TjPrime rho1 gammaN deltaN hterminalTj supportLength gamma delta hTjStored
      u beta trace hstepData hvertexInitialSegment hbeforeMemberAndNe hfixedOutsideComponent
  have hstableOutput := @helper_hstableOutput_1191 V E inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSlot terminalSupport hterminalSupport Tj TjPrime phiJ rho1
      Dprev gammaN deltaN hterminalTj u beta hmuStable trace hbeforeEdgesPreserved
  refine ⟨hstableOutput, ?_⟩
  have hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn :=
    hvertexInitialSegment hTjN hterminalTj
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    hvertexInitialSegment hseedPrime hterminalSeed
  have hterminalNeU : terminalSupport ≠ u := by
    intro h
    apply huOutside
    rwa [← h]
  have hprefixColorsNotMissing := @helper_hprefixColorsNotMissing_1371 V E inferInstance
      inferInstance inferInstance inferInstance G k e0 input T generating ett terminalSlot
      terminalSupport hterminalSupport TjPrime rho1 supportColors gammaN deltaN supportLength gamma
      delta u beta hmuPrimeMissing trace htraceSupportColors htraceDeltaNNe
  have hmissingPreserved := @helper_hmissingPreserved_685 V E inferInstance inferInstance
      inferInstance inferInstance G k e0 input T generating ett terminalSlot jSlot terminalSupport
      hterminalSupport Tj TjPrime rho1 gammaN deltaN supportLength gamma delta hTjStored u beta
      trace hstepData hvertexInitialSegment hmissingFixedOutside hmissingFixedInternal
      hterminalPrime hterminalNeU hprefixColorsNotMissing
  have hstageEdgeFixedStep := @helper_hstageEdgeFixedStep_762 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot preterminalSlot jSlot terminalSupport
      hterminalSupport Tj seed TjPrime rho1 gammaFirst gammaN deltaN x supportLength indices gamma
      delta hTjStored u exitPath beta zPosition trace hstepData hvertexInitialSegment
      hvertexOfComponentEdge
  have hstageEdgesPreserved : ∀ n : Fin (trace.steps + 1),
      ∀ q : Fin Tj.length, trace.coloring n (Tj.edge q) = mu0 (Tj.edge q) := by
    intro n
    induction n using Fin.induction with
    | zero =>
        intro q
        rw [trace.initialColoring]
    | succ a ih =>
        intro q
        exact (hstageEdgeFixedStep a q).trans (ih q)
  have hseedEdgeCommon (q : Fin TjPrime.length) (hq : q.val < seed.length) :
      ∃ r : Fin Tj.length, TjPrime.edge q = Tj.edge r := by
    let s : Fin seed.length := ⟨q.val, hq⟩
    obtain ⟨hseedJLength, -, hseedJEdges⟩ := hseedJ
    obtain ⟨hseedPrimeLength, -, hseedPrimeEdges⟩ := hseedPrime
    let r : Fin Tj.length := Fin.castLE hseedJLength s
    have hqCast : Fin.castLE hseedPrimeLength s = q := by
      apply Fin.ext
      rfl
    refine ⟨r, ?_⟩
    rw [← hqCast, hseedPrimeEdges]
    exact (hseedJEdges s).symm
  have hprimeEdgesPreserved := @helper_hprimeEdgesPreserved_837 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport Tj
      seed TjPrime rho1 supportColors gammaN deltaN supportLength gamma delta u beta
      hmuAppendedEdges trace htraceSupportColors htraceDeltaNNe hstageEdgesPreserved hseedEdgeCommon
  have hdeltaNMissingPreserved := @helper_hdeltaNMissingPreserved_1280 V E inferInstance
      inferInstance inferInstance G k e0 input T generating ett terminalSlot terminalSupport
      hterminalSupport TjPrime rho1 gammaN deltaN u beta z trace htraceDeltaNNe hunaffectedValue
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact @helper_branch_1307 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSlot terminalSupport hterminalSupport Tj TjPrime rho1 gammaN
      deltaN u huPrime beta z hz hmuMissing trace hbeforeMemberAndNe hmissingPreserved
  · intro f hf
    rcases hf with hfTj | hfPrime
    · obtain ⟨a, haSeed, haPosition, rfl⟩ := hfTj
      exact (hstageEdgesPreserved (Fin.last trace.steps) a).trans
        (hmuEdges (Tj.edge a) (Or.inl ⟨a, haSeed, haPosition, rfl⟩))
    · obtain ⟨a, uPosition, huPosition, haPosition, rfl⟩ := hfPrime
      exact (hprimeEdgesPreserved (Fin.last trace.steps) a).trans
        (hmuEdges (TjPrime.edge a)
          (Or.inr ⟨a, uPosition, huPosition, haPosition, rfl⟩))
  · intro hbetaZ
    exact hdeltaNMissingPreserved (hmuBeta hbetaZ)
  · intro hzBefore
    have hzData := hbeforeMemberAndNe huPrime hzBefore
    have hzTrace : z ∈ TreeSequenceVertexSet Tj ∪
        (TreeSequenceVertexSet TjPrime).erase u :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzData.2, hzData.1⟩)
    exact (hmissingPreserved (Fin.last trace.steps) z hzTrace).trans
      (hmuZ hzBefore)
  · exact @helper_branch_945 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSlot preterminalSlot jSlot hterminalAtEnd hpreterminalOrder
      terminalSupport hterminalSupport Tj Tn seed TjPrime rho1 gammaFirst gammaN deltaN x
      hpreterminalClass supportLength indices gamma delta hincreasing hclass hterminalIndex
      hsupport hkind hgamma hdelta hstored hchain hdistinct hfirstGamma hpreterminalGammaPresent
      u exitPath beta zPosition hgammaLast trace hstepData hgammaDeltaNe htraceIndex htraceGamma
      htraceDelta htraceColorsNe hcomponentEdgeOfVertex

private theorem helper_continuation_1438.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input :
    PartialEdgeColoring E k} {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot
    jSlot : Fin ett.rounds), (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds → (↑preterminalSlot :
    ℕ) < (↑terminalSlot : ℕ) → ∀ (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (Tj Tn seed TjPrime : TreeSequence G e0) (phiJ rho1 :
    PartialEdgeColoring E k) (Dprev supportColors : Finset (Fin k)) (gammaFirst gammaN deltaN
    : Fin k) (x : V), TreeSequenceInitialSegment Tj Tn → TreeSequenceInitialSegment seed Tj →
    TreeSequenceInitialSegment seed TjPrime → ∀ (hterminalTj : terminalSupport ∈
    TreeSequenceVertexSet Tj), terminalSupport ∈ TreeSequenceVertexSet seed → preterminalSlot
    ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
    some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) → (∀ (s : Fin ett.rounds)
    (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett terminalSupport
    hterminalSupport terminalSupport).erase terminalSlot → ett.series.data.gamma s.succ = some
    gammaS → ett.series.data.delta s.succ = some deltaS → deltaN ≠ gammaS ∧ deltaN ≠ deltaS) →
    ∀ (supportLength : ℕ) (indices : Fin (supportLength + (1 : ℕ)) → Fin ett.rounds) (gamma
    delta : Fin (supportLength + (1 : ℕ)) → Fin k), (∀ (a c : Fin (supportLength + (1 : ℕ))),
    (↑a : ℕ) < (↑c : ℕ) → (↑(indices a) : ℕ) < (↑(indices c) : ℕ)) → (∀ (s : Fin ett.rounds),
    s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport ↔ ∃ (a
    : Fin (supportLength + (1 : ℕ))), indices a = s) → indices (Fin.last supportLength) =
    terminalSlot → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.chosenVertex
    (indices a).succ = some terminalSupport) → (∀ (a : Fin (supportLength + (1 : ℕ))),
    ett.series.data.kind (indices a).succ = some TashkinovExtensionKind.PE) → (∀ (a : Fin
    (supportLength + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a)) → (∀
    (a : Fin (supportLength + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta
    a)) → (∀ (a : Fin (supportLength + (1 : ℕ))), ett.series.data.stored (indices a).succ =
    {gamma a, delta a}) → (∀ (a : Fin supportLength), gamma a.succ = delta a.castSucc) →
    Function.Injective (Fin.cons (gamma (0 : Fin (supportLength + (1 : ℕ)))) delta) →
    ett.series.data.tree jSlot.succ.castSucc = Tj → gamma (0 : Fin (supportLength + (1 : ℕ)))
    = gammaFirst → (∀ (u : V) (beta : Fin k), u ∈ TreeSequenceVertexSet TjPrime → u ∉
    TreeSequenceVertexSet Tn → beta ∈ MissingColors G rho1 u → ∀ (a : Fin supportLength),
    gamma a.castSucc ∈ PresentColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime
    rho1 beta deltaN) gammaN beta (Sum.inl u)) u) → ∀ (u : V) (huPrime : u ∈
    TreeSequenceVertexSet TjPrime), u ∉ TreeSequenceVertexSet Tn → ∀ (_ :
    (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (beta : Fin k)
    (z : V) (hz : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin (Tj.length + (1 : ℕ))),
    StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) → (∀ v ∈
    ((TreeVerticesBefore Tj z hz ∪ {z} ∪ (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase
    u).erase z, MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    v = MissingColors G rho1 v) → (∀ (f : E), ((∃ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ)
    ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨ ∃ (a : Fin TjPrime.length) (uPosition :
    Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u ∧ (↑a : ℕ) < (↑uPosition :
    ℕ) ∧ TjPrime.edge a = f) → (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
    beta deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    f = rho1 f) → (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) z) → (z ∈
    TreeVerticesBefore TjPrime u huPrime → MissingColors G (TwoColorComponentSwap G
    (OutsideTreeColorSwap TjPrime rho1 beta deltaN : PartialEdgeColoring E k) gammaN beta
    (Sum.inl u) : PartialEdgeColoring E k) z = MissingColors G rho1 z) →
    (((TreeSequenceVertexSet TjPrime).erase u).biUnion fun (v : V) ↦ MissingColors G
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) v) ∩
    supportColors = {deltaN} → (∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) → ∀ c ∈
    supportColors \ {deltaN}, (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta
    deltaN : PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k)
    (TjPrime.edge a) ≠ some c) → gamma (Fin.last supportLength) = gammaN → ∀ (trace :
    ExtensionBaseAlgorithmCTrace ett terminalSupport hterminalSupport terminalSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u),
    ExtensionBaseAlgorithmCInvariant ett terminalSupport hterminalSupport terminalSlot jSlot
    (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN :
    PartialEdgeColoring E k) gammaN beta (Sum.inl u) : PartialEdgeColoring E k) u trace → (∀
    (a : Fin trace.steps), TreeSequenceInitialSegment (ett.series.data.tree
    jSlot.succ.castSucc) (ett.series.data.tree (trace.slot a).succ.castSucc) ∧ trace.delta a ∈
    MissingColors G (trace.coloring a.castSucc) u ∧ TwoColorNontrivialPathComponent G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) ∧ (∀ w ∈
    TreeSequenceVertexSet (ett.series.data.tree (trace.slot a).succ.castSucc), Sum.inl w ∈
    TwoColorComponent G (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl
    u) → w = terminalSupport) ∧ (Sum.inl terminalSupport ∈ TwoColorComponent G (trace.coloring
    a.castSucc) (trace.gamma a) (trace.delta a) (Sum.inl u) → ¬((TwoColorIncidenceGraph G
    (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)).neighborSet (Sum.inl
    terminalSupport)).Subsingleton) ∧ ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈
    (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
    terminalSlot → (∀ (b : Fin trace.steps), (↑b : ℕ) ≤ (↑a : ℕ) → trace.slot b ≠ s) →
    ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
    = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
    s terminalSupport (trace.coloring a.succ) gammaS deltaS) → (∀ (a : Fin trace.steps),
    trace.slot a ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
    terminalSupport).erase terminalSlot) → (∀ (q : Fin (supportLength + (1 : ℕ))), gamma q ≠
    delta q) → (∀ (a : Fin trace.steps), ∃ (q : Fin (supportLength + (1 : ℕ))), indices q =
    trace.slot a) → (∀ (a : Fin trace.steps) (q : Fin (supportLength + (1 : ℕ))), indices q =
    trace.slot a → trace.gamma a = gamma q) → StableColoringBeforeVertex Tj terminalSupport
    hterminalTj Dprev phiJ (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) ∧
    (∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ {z} ∪ (TreeVerticesBefore TjPrime u huPrime ∪
    {u})).erase u).erase z, MissingColors G (trace.coloring (Fin.last trace.steps) :
    PartialEdgeColoring E k) v = MissingColors G rho1 v) ∧ (∀ (f : E), ((∃ (a : Fin
    Tj.length), seed.length ≤ (↑a : ℕ) ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨ ∃ (a :
    Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition
    = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → (trace.coloring (Fin.last
    trace.steps) : PartialEdgeColoring E k) f = rho1 f) ∧ (beta ∈ MissingColors G rho1 z →
    deltaN ∈ MissingColors G (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k)
    z) ∧ (z ∈ TreeVerticesBefore TjPrime u huPrime → MissingColors G (trace.coloring (Fin.last
    trace.steps) : PartialEdgeColoring E k) z = MissingColors G rho1 z) ∧ gammaFirst ∈
    MissingColors G (trace.coloring (Fin.last trace.steps) : PartialEdgeColoring E k) u := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot jSlot
      hterminalAtEnd hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ
      rho1 Dprev supportColors gammaFirst gammaN deltaN x hTjN hseedJ hseedPrime hterminalTj
      hterminalSeed hpreterminalClass hsupportColors hdeltaEarlier supportLength indices gamma
      delta hincreasing hclass hterminalIndex hsupport hkind hgamma hdelta hstored hchain
      hdistinct hTjStored hfirstGamma hpreterminalGammaPresent u huPrime huOutside exitPath beta
      z hz zPosition
  set rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1
                                                                    beta deltaN
  set mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0
                                                                    gammaN beta (Sum.inl u)
  intro hmuStable hmuMissing hmuEdges hmuBeta hmuZ hmuPrimeMissing hmuAppendedEdges hgammaLast
      trace hinvariant
  set rho3 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps)
  intro hstepData hslotMem hgammaDeltaNe htraceIndex htraceGamma
  have htraceDelta (a : Fin trace.steps) (q : Fin (supportLength + 1))
      (hq : indices q = trace.slot a) : trace.delta a = delta q := by
    apply Option.some.inj
    exact (trace.deltaField a).symm.trans (by
      rw [← hq]
      exact hdelta q)
  have htraceColorsNe (a : Fin trace.steps) :
      trace.gamma a ≠ trace.delta a := by
    obtain ⟨q, hq⟩ := htraceIndex a
    rw [htraceGamma a q hq, htraceDelta a q hq]
    exact hgammaDeltaNe q
  have htraceSupportColors (a : Fin trace.steps) :
      trace.gamma a ∈ supportColors ∧ trace.delta a ∈ supportColors :=
    hsupportColors (trace.slot a) (trace.gamma a) (trace.delta a)
      (hslotMem a) (trace.gammaField a) (trace.deltaField a)
  have htraceDeltaNNe (a : Fin trace.steps) :
      deltaN ≠ trace.gamma a ∧ deltaN ≠ trace.delta a :=
    hdeltaEarlier (trace.slot a) (trace.gamma a) (trace.delta a)
      (hslotMem a) (trace.gammaField a) (trace.deltaField a)
  have htraceProper (n : Fin (trace.steps + 1)) :
      IsProperEdgeColoring G (trace.coloring n) := (hinvariant.1 n).1
  have hvertexInitialSegment {A B : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, -, hi⟩ := hv
    obtain ⟨hlen, hvertices, -⟩ := hAB
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hi⟩
  have hbeforeMemberAndNe {A : TreeSequence G e0} {v w : V}
      (hv : v ∈ TreeSequenceVertexSet A)
      (hw : w ∈ TreeVerticesBefore A v hv) :
      w ∈ TreeSequenceVertexSet A ∧ w ≠ v := by
    unfold TreeVerticesBefore at hw
    obtain ⟨hwA, i, j, hiw, hjv, hij⟩ := Finset.mem_filter.mp hw
    refine ⟨hwA, ?_⟩
    intro hwv
    have hijEq : i = j := A.vertex_injective
      (hiw.trans (hwv.trans hjv.symm))
    omega
  have hvertexOfComponentEdge := @helper_hvertexOfComponentEdge_1229 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta trace
  have hcomponentEdgeOfVertex := @helper_hcomponentEdgeOfVertex_1252 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta trace
  have hfixedOutsideComponent := @helper_hfixedOutsideComponent_1275 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta trace hvertexOfComponentEdge
  have hmissingFixedOutside := @helper_hmissingFixedOutside_1293 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN u beta trace hfixedOutsideComponent
  have hunaffectedValue (a : Fin trace.steps) (f : E) (c : Fin k)
      (hcg : c ≠ trace.gamma a) (hcd : c ≠ trace.delta a) :
      trace.coloring a.succ f = some c ↔
        trace.coloring a.castSucc f = some c := by
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
  have hmissingFixedInternal := @helper_hmissingFixedInternal_549 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 gammaN deltaN supportLength gamma delta u beta trace htraceColorsNe
      hcomponentEdgeOfVertex hunaffectedValue
  exact @helper_continuation_1506 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSlot preterminalSlot jSlot hterminalAtEnd
      hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ rho1 Dprev
      supportColors gammaFirst gammaN deltaN x hTjN hseedJ hseedPrime hterminalTj hterminalSeed
      hpreterminalClass supportLength indices gamma delta hincreasing hclass hterminalIndex
      hsupport hkind hgamma hdelta hstored hchain hdistinct hTjStored hfirstGamma
      hpreterminalGammaPresent u huPrime huOutside exitPath beta z hz zPosition hmuStable
      hmuMissing hmuEdges hmuBeta hmuZ hmuPrimeMissing hmuAppendedEdges hgammaLast trace
      hstepData hgammaDeltaNe htraceIndex htraceGamma htraceDelta htraceColorsNe
      htraceSupportColors htraceDeltaNNe hvertexInitialSegment hbeforeMemberAndNe
      hvertexOfComponentEdge hcomponentEdgeOfVertex hfixedOutsideComponent hmissingFixedOutside
      hunaffectedValue hmissingFixedInternal
theorem ExtensionBaseClaim45 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSlot preterminalSlot jSlot : Fin ett.rounds)
    (hterminalAtEnd : terminalSlot.val + 1 = ett.rounds)
    (hpreterminalOrder : preterminalSlot.val < terminalSlot.val)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (Tj Tn seed TjPrime : TreeSequence G e0)
    (phiJ phiN sigmaN rho1 : PartialEdgeColoring E k)
    (Dprev controlled restorationColors supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN : Fin k) (fN : E) (x : V)
    (componentPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hphiNProper : IsProperEdgeColoring G phiN)
    (hphiNOne : IsOneEdgeUncolored phiN e0)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hterminalColors :
      MissingColors G rho1 terminalSupport ∩ supportColors = {deltaN})
    (hgammaSupport : gammaN ∈ supportColors)
    (hdeltaSupport : deltaN ∈ supportColors)
    (hgammaFirstSupport : gammaFirst ∈ supportColors)
    (hgammaDelta : gammaN ≠ deltaN)
    (hsigmaStable : StableColoring Tn controlled phiN sigmaN)
    (hgammaControlled : gammaN ∈ controlled)
    (hdeltaControlled : deltaN ∈ controlled)
    (hb3 : ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G (TreeSequenceVertexSet Tj) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors)
    (hgammaRestored : gammaN ∉ restorationColors)
    (hdeltaRestored : deltaN ∉ restorationColors)
    (hgammaBoundary :
      BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaLocation : ∀ f ∈ BoundaryColorEdges G phiN
        (TreeSequenceVertexSet Tn) deltaN,
      ∃ w ∈ TreeSequenceVertexSet seed, Incident G w f)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : componentPath.IsPath)
    (hcomponent : {y : Sum V E | y ∈ componentPath.support} =
      TwoColorComponent G rho1 gammaN deltaN
        (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ componentPath.support)
    (hfNterminal : Incident G terminalSupport fN)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hsupportSet : supportColors =
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).biUnion
          (fun s => ett.series.data.stored s.succ))
    (hterminalClass : terminalSlot ∈ ExtensionBaseSupportClass ett
      terminalSupport hterminalSupport terminalSupport)
    (hpreterminalClass : preterminalSlot ∈
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).erase terminalSlot)
    (hgammaIdentity : ett.series.data.delta preterminalSlot.succ =
      some gammaN)
    (hterminalGamma : ett.series.data.gamma terminalSlot.succ = some gammaN)
    (hterminalDelta : ett.series.data.delta terminalSlot.succ = some deltaN)
    (hb4 : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS)
    (hsupportColors : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      gammaS ∈ supportColors ∧ deltaS ∈ supportColors)
    (hdeltaEarlier : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      deltaN ≠ gammaS ∧ deltaN ≠ deltaS)
    (hsupportOrder : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ∀ v : V,
        v ∈ TreeSequenceVertexSet
            (ett.series.data.tree s.succ.castSucc) →
        v ≠ terminalSupport →
        ∀ w : V, Sum.inl w ∈
          TwoColorComponent G rho1 gammaS deltaS (Sum.inl v) →
          w ∈ TreeSequenceVertexSet Tn)
    (supportLength : ℕ)
    (indices : Fin (supportLength + 1) → Fin ett.rounds)
    (gamma delta : Fin (supportLength + 1) → Fin k)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hclass : ∀ s : Fin ett.rounds,
      s ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport ↔
        ∃ a : Fin (supportLength + 1), indices a = s)
    (hterminalIndex : indices (Fin.last supportLength) = terminalSlot)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a})
    (hchain : ∀ a : Fin supportLength,
      gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hTjStored : ett.series.data.tree jSlot.succ.castSucc = Tj)
    (hTjInitial : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport).erase terminalSlot →
        TreeSequenceInitialSegment Tj
          (ett.series.data.tree s.succ.castSucc))
    (hfirstGamma : gamma 0 = gammaFirst)
    (hpreterminalGammaPresent : ∀ (u : V) (beta : Fin k),
      u ∈ TreeSequenceVertexSet TjPrime →
      u ∉ TreeSequenceVertexSet Tn →
      beta ∈ MissingColors G rho1 u →
      ∀ a : Fin supportLength,
        gamma a.castSucc ∈ PresentColors G
          (TwoColorComponentSwap G
            (OutsideTreeColorSwap TjPrime rho1 beta deltaN)
            gammaN beta (Sum.inl u)) u) :
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
      (_ : u ∉ TreeSequenceVertexSet Tn)
      (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
      exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
      (∀ y : Sum V E, y ∈ exitPath.support → y ∈ componentPath.support) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
        (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
      (∃ g ∈ BoundaryColorEdges G rho1
          (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
        Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
      ¬ Incident G u fN ∧
      ∀ beta : Fin k, beta ∈ MissingColors G rho1 u →
      ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj)
        (zPosition : Fin (Tj.length + 1)),
        Tj.vertex zPosition = z ∧ seed.length ≤ zPosition.val ∧
        ((seed.length < zPosition.val ∧
            beta ∈ MissingColors G rho1 z ∧
            ∀ r : Fin (Tj.length + 1),
              seed.length < r.val → r.val < zPosition.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
          (zPosition = Fin.last Tj.length ∧
            ∀ r : Fin (Tj.length + 1), seed.length < r.val →
              beta ∉ MissingColors G rho1 (Tj.vertex r))) ∧
        (∀ w ∈ TreeVerticesBefore Tj z hz,
          beta ∉ MissingColors G rho1 w) ∧
        (∀ a : Fin Tj.length, seed.length ≤ a.val →
          a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) ∧
        ∃ rho3 : PartialEdgeColoring E k,
          IsProperEdgeColoring G rho3 ∧
          IsOneEdgeUncolored rho3 e0 ∧
          StableColoringBeforeVertex Tj terminalSupport hterminalTj
            Dprev phiJ rho3 ∧
          (∀ v : V,
            v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
                (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
            MissingColors G rho3 v = MissingColors G rho1 v) ∧
          (∀ f : E,
            ((∃ a : Fin Tj.length,
                seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                  Tj.edge a = f) ∨
              (∃ (a : Fin TjPrime.length)
                (uPosition : Fin (TjPrime.length + 1)),
                TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                  TjPrime.edge a = f)) →
            rho3 f = rho1 f) ∧
          (beta ∈ MissingColors G rho1 z →
            deltaN ∈ MissingColors G rho3 z) ∧
          (z ∈ TreeVerticesBefore TjPrime u huPrime →
            MissingColors G rho3 z = MissingColors G rho1 z) ∧
          gammaFirst ∈ MissingColors G rho3 u := by
  classical
  obtain ⟨u, huPrime, huOutside, exitPath, hExitPath, hExitLength,
      hExitSupport, hExitIntersection, hExitBoundary, huNotFN, hbeta⟩ :=
    ExtensionBaseClaim46 ett terminalSlot preterminalSlot hterminalAtEnd
      hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime
      phiJ phiN sigmaN rho1 Dprev controlled restorationColors supportColors
      gammaFirst gammaN deltaN fN x componentPath hphiNProper hphiNOne
      hsigmaProper hsigmaOne hrhoProper hrhoOne hTjN hseedJ hseedPrime
      hseedTerminal hterminalTj hterminalSeed hclosure hprimeElementary
      hcaseTwo hterminalColors hgammaSupport hdeltaSupport hgammaFirstSupport
      hgammaDelta hsigmaStable hgammaControlled hdeltaControlled hb3
      hgammaRestored hdeltaRestored hgammaBoundary hdeltaLocation
      hdeltaMissing hpath hcomponent hxOutside htwoN hfNterminal hb1
      hb2Missing hterminalInclusion haugmentation hb2Edges hdeltaPhiJ
      hsupportSet hterminalClass hpreterminalClass hgammaIdentity
      hterminalGamma hterminalDelta hb4 hsupportColors hdeltaEarlier
      hsupportOrder
  refine ⟨u, huPrime, huOutside, exitPath, hExitPath, hExitLength,
    hExitSupport, hExitIntersection, hExitBoundary, huNotFN, ?_⟩
  intro beta hbetaMissing
  obtain ⟨z, hz, zPosition, hzPosition, hseedPosition, hpositionCases,
      hbetaBefore, hbetaEdges, hmu⟩ := hbeta beta hbetaMissing
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let mu0 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  change IsProperEdgeColoring G mu0 ∧ IsOneEdgeUncolored mu0 e0 ∧
      StableColoringBeforeVertex Tj terminalSupport hterminalTj
        Dprev phiJ mu0 ∧
      ((∀ v : V,
        v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
            (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G mu0 v = MissingColors G rho1 v) ∧
        (∀ f : E,
          ((∃ a : Fin Tj.length,
              seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                Tj.edge a = f) ∨
            (∃ (a : Fin TjPrime.length)
              (uPosition : Fin (TjPrime.length + 1)),
              TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                TjPrime.edge a = f)) →
          mu0 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z →
          deltaN ∈ MissingColors G mu0 z) ∧
        (z ∈ TreeVerticesBefore TjPrime u huPrime →
          MissingColors G mu0 z = MissingColors G rho1 z)) ∧
      (ett.series.data.delta preterminalSlot.succ = some gammaN ∧
        gammaN ∈ MissingColors G mu0 u ∧
        beta ∉ MissingColors G mu0 u) ∧
      (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
        s ∈ (ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport terminalSupport).erase terminalSlot →
        ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS) ∧
      (((TreeSequenceVertexSet TjPrime).erase u).biUnion
          (fun v => MissingColors G mu0 v) ∩ supportColors = {deltaN} ∧
        MissingColors G mu0 terminalSupport ∩ supportColors = {deltaN} ∧
        ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
          ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
            mu0 (TjPrime.edge a) ≠ some c) at hmu
  rcases hmu with ⟨hmuProper, hmuOne, hmuStable,
    ⟨hmuMissing, hmuEdges, hmuBeta, hmuZ⟩,
    ⟨-, hgammaNMissing, -⟩, hmuSI,
    ⟨hmuPrimeMissing, hmuTerminalMissing, hmuAppendedEdges⟩⟩
  have hgammaLast : gamma (Fin.last supportLength) = gammaN := by
    apply Option.some.inj
    exact (hgamma (Fin.last supportLength)).symm.trans (by
      rw [hterminalIndex]
      exact hterminalGamma)
  have hterminalNoMissing := @helper_hterminalNoMissing_940 V E inferInstance inferInstance
      inferInstance G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      TjPrime rho1 supportColors gammaN deltaN hsupportSet hdeltaEarlier supportLength indices gamma
      delta hclass hgamma hdelta hstored u beta hmuTerminalMissing
  obtain ⟨trace, hinvariant⟩ := ExtensionBaseAlgorithmC ett terminalSupport
    hterminalSupport terminalSlot jSlot mu0 u supportLength indices gamma delta
    hmuProper hmuOne hterminalAtEnd hincreasing hclass hterminalIndex hsupport
    hkind hgamma hdelta hstored hchain hdistinct (by
      intro s hs
      rw [hTjStored]
      exact hTjInitial s hs)
    (by simpa [hgammaLast] using hgammaNMissing)
    (hpreterminalGammaPresent u beta huPrime huOutside hbetaMissing)
    hmuSI hterminalNoMissing
  let rho3 := trace.coloring (Fin.last trace.steps)
  refine ⟨z, hz, zPosition, hzPosition, hseedPosition, hpositionCases,
    hbetaBefore, hbetaEdges, rho3, (hinvariant.1 _).1, (hinvariant.1 _).2, ?_⟩
  have hstepData (a : Fin trace.steps) := hinvariant.2.1 a
  have hslotMem (a : Fin trace.steps) :
      trace.slot a ∈ (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).erase terminalSlot := by
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hgammaDeltaNe := @helper_hgammaDeltaNe_1160 k supportLength gamma delta hchain hdistinct
  have htraceIndex (a : Fin trace.steps) :
      ∃ q : Fin (supportLength + 1), indices q = trace.slot a := by
    exact (hclass (trace.slot a)).mp (Finset.mem_erase.mp (hslotMem a)).2
  have htraceGamma (a : Fin trace.steps) (q : Fin (supportLength + 1))
      (hq : indices q = trace.slot a) : trace.gamma a = gamma q := by
    apply Option.some.inj
    exact (trace.gammaField a).symm.trans (by
      rw [← hq]
      exact hgamma q)
  exact @helper_continuation_1438 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSlot preterminalSlot jSlot hterminalAtEnd
      hpreterminalOrder terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ rho1 Dprev
      supportColors gammaFirst gammaN deltaN x hTjN hseedJ hseedPrime hterminalTj hterminalSeed
      hpreterminalClass hsupportColors hdeltaEarlier supportLength indices gamma delta
      hincreasing hclass hterminalIndex hsupport hkind hgamma hdelta hstored hchain hdistinct
      hTjStored hfirstGamma hpreterminalGammaPresent u huPrime huOutside exitPath beta z hz
      zPosition hmuStable hmuMissing hmuEdges hmuBeta hmuZ hmuPrimeMissing hmuAppendedEdges
      hgammaLast trace hinvariant hstepData hslotMem hgammaDeltaNe htraceIndex htraceGamma
end GoldbergSeymour

end
