/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationInvariant

/-!
# Extension Base Claim43Missing Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_edgeOutside_99.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace → (
    ∀ (A B : TreeSequence G e0), TreeSequenceInitialSegment A B →
    ∀ v ∈ TreeSequenceVertexSet A, v ∈ TreeSequenceVertexSet B) →
    ∀ (a : Fin trace.steps),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ trace.support a →
    ∀ (f : E), Incident G v f → Sum.inr f ∉ TwoColorComponent G (trace.coloring a.castSucc)
        (trace.gamma a) (trace.delta a) (Sum.inl (trace.support a)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant vertexTransfer a v hv hvSupport f hvf hf
  have stepInvariant := hinvariant.2.1 a
  rcases stepInvariant.2.2 with
    ⟨segment, supportInTree, deltaMissing, pathComponent,
      exactIntersection, remaining⟩
  have hvCurrent : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree (trace.slot a).succ.castSucc) :=
    vertexTransfer _ _ segment v hv
  have endpoint : Sum.inl v ∈ TwoColorComponent G
      (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
      (Sum.inl (trace.support a)) := by
    exact TwoColorComponent.vertex_mem_of_incident hf hvf
  exact hvSupport ((exactIntersection v hvCurrent).mp endpoint)

private theorem helper_rootExchange_162.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace →
    ∀ (a : Fin trace.steps), MissingColors G (trace.coloring a.succ) (trace.support a) =
        MissingColors G (trace.coloring a.castSucc) (trace.support a) \ {trace.delta a} ∪
        {trace.gamma a} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant a
  have stepInvariant := hinvariant.2.1 a
  rcases stepInvariant.2.2 with
    ⟨segment, supportInTree, deltaMissing, pathComponent,
      exactIntersection, remaining⟩
  let phi := trace.coloring a.castSucc
  let gamma := trace.gamma a
  let delta := trace.delta a
  let v := trace.support a
  have deltaNotPresent : delta ∉ PresentColors G phi v := by
    simpa [MissingColors] using deltaMissing
  have gammaPresent : gamma ∈ PresentColors G phi v := by
    obtain ⟨f, hf⟩ := pathComponent.2
    obtain ⟨e, hve, hcolor | hcolor⟩ :=
      TwoColorComponent.exists_colored_incident hf
    · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hve, hcolor⟩
    · exact (deltaNotPresent (by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hve, hcolor⟩)).elim
  have gammaNeDelta : gamma ≠ delta := by
    intro h
    apply deltaNotPresent
    simpa [h] using gammaPresent
  have edgeMember : ∀ e : E, Incident G v e →
      (phi e = some gamma ∨ phi e = some delta) →
      Sum.inr e ∈ TwoColorComponent G phi gamma delta (Sum.inl v) := by
    intro e hve hcolor
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, hve, hcolor]
  have presentStep :
    ∀ c : Fin k, c ∈ PresentColors G (TwoColorComponentSwap G phi gamma delta (Sum.inl v)) v ↔ c =
        delta ∨ (c ≠ gamma ∧ c ∈ PresentColors G phi v) := by
    intro c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, hve, hec⟩
      by_cases hcomp : Sum.inr e ∈
          TwoColorComponent G phi gamma delta (Sum.inl v)
      · by_cases hgamma : phi e = some gamma
        · have value := hec
          simp [TwoColorComponentSwap, hcomp, hgamma] at value
          exact Or.inl value.symm
        · by_cases hdelta : phi e = some delta
          · exact (deltaNotPresent (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨e, hve, hdelta⟩)).elim
          · right
            have value := hec
            simp only [TwoColorComponentSwap, hcomp, ↓reduceIte, hgamma, hdelta] at value
            refine ⟨?_, ⟨e, hve, value⟩⟩
            intro hc
            apply hgamma
            simpa [hc] using value
      · right
        have value := hec
        simp only [TwoColorComponentSwap, hcomp, ↓reduceIte] at value
        refine ⟨?_, ⟨e, hve, value⟩⟩
        intro hc
        apply hcomp
        apply edgeMember e hve
        left
        simpa [hc] using value
    · rintro (rfl | ⟨hcGamma, ⟨e, hve, hec⟩⟩)
      · obtain ⟨e, hve, heGamma⟩ := by
          simpa [PresentColors] using gammaPresent
        refine ⟨e, hve, ?_⟩
        simp [TwoColorComponentSwap,
          edgeMember e hve (Or.inl heGamma), heGamma]
      · refine ⟨e, hve, ?_⟩
        by_cases hgamma : phi e = some gamma
        · exact False.elim (hcGamma (Option.some.inj (hec.symm.trans hgamma)))
        · by_cases hdelta : phi e = some delta
          · exact False.elim (deltaNotPresent (by
              simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              exact ⟨e, hve, hdelta⟩))
          · simp only [TwoColorComponentSwap, hgamma, ↓reduceIte, hdelta, ite_self]
            exact hec
  have exchange : MissingColors G
      (TwoColorComponentSwap G phi gamma delta (Sum.inl v)) v =
        (MissingColors G phi v \ {delta}) ∪ {gamma} := by
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_univ, true_and]
    rw [presentStep]
    by_cases hcDelta : c = delta <;>
      by_cases hcGamma : c = gamma <;>
        simp [hcDelta, hcGamma, gammaNeDelta, gammaNeDelta.symm]
  rw [trace.transition]
  exact exchange

private theorem helper_hposReverse_329.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (sigmaN : PartialEdgeColoring E k) (trace :
        ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN) (p : ℕ)
        (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_ : (
    ∀ (a b : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) < (↑b : ℕ)), (↑(indices a) : ℕ) < (↑(indices b) :
        ℕ))) (hpositionExists :
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (s : Fin trace.steps), trace.slot s = indices a),
    let pos : Fin (p + (1 : ℕ)) → Fin trace.steps := fun (a : Fin (p + (1 : ℕ))) =>
        Classical.choose (hpositionExists a);
    ∀ (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.slot (pos a) = indices a)) (a b : Fin (p + (1 : ℕ))) (_ : (↑a
        : ℕ) < (↑b : ℕ)), (↑(pos b) : ℕ) < (↑(pos a) : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport sigmaN trace p
      indices hincreasing hpositionExists pos hposSlot a b hab
  have hindices := hincreasing a b hab
  by_contra hnot
  have hle : (pos a).val ≤ (pos b).val := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hdesc := trace.strictlyDescending (pos a) (pos b) hlt
    rw [hposSlot, hposSlot] at hdesc
    omega
  · have hposEq : pos a = pos b := Fin.ext heq
    have hindexEq : indices a = indices b := by
      rw [← hposSlot a, ← hposSlot b, hposEq]
    have hvalEq := congrArg Fin.val hindexEq
    omega

private theorem helper_hsupportPosition_356.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN) (_ : ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace) (v : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin
        ett.rounds) (_ : (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport v ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r)) (hpositionExists :
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (s : Fin trace.steps), trace.slot s = indices a),
    let pos : Fin (p + (1 : ℕ)) → Fin trace.steps := fun (a : Fin (p + (1 : ℕ))) =>
        Classical.choose (hpositionExists a);
    ∀ (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.slot (pos a) = indices a)) (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.support (pos a) = v)) (_ : Function.Injective trace.slot) (s
        : Fin trace.steps), trace.support s = v ↔
    ∃ (a : Fin (p + (1 : ℕ))), pos a = s := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant v p indices hclass hpositionExists pos hposSlot hposSupport hslotInjective s
  constructor
  · intro hs
    have hsRestoration := (hinvariant.2.1 s).1
    have hsActive := (Finset.mem_sdiff.mp hsRestoration).1
    have hsClass : trace.slot s ∈
        ExtensionBaseSupportClass ett terminalSupport hterminalSupport v := by
      simp only [ExtensionBaseSupportClass, Finset.mem_filter]
      exact ⟨hsActive, by simpa [hs] using trace.chosenVertex s⟩
    obtain ⟨a, ha⟩ := (hclass (trace.slot s)).mp hsClass
    refine ⟨a, hslotInjective ?_⟩
    exact (hposSlot a).trans ha
  · rintro ⟨a, rfl⟩
    exact hposSupport a

private theorem helper_rootGammaPresent_371.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
      {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
      (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
      (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
      (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
      (trace : ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN),
    ExtensionBaseRestorationInvariant ett terminalSupport hterminalSupport jSlot q sigmaN
        trace →
    ∀ (_ : V) (p : ℕ) (_ _ : Fin (p + (1 : ℕ)) → Fin k) (s : Fin trace.steps),
    trace.gamma s ∈ PresentColors G (trace.coloring s.castSucc) (trace.support s) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant v p gamma delta s
  have stepInvariant := hinvariant.2.1 s
  rcases stepInvariant.2.2 with
    ⟨segment, supportInTree, deltaMissing, pathComponent,
      exactIntersection, remaining⟩
  have deltaNotPresent : trace.delta s ∉
      PresentColors G (trace.coloring s.castSucc) (trace.support s) := by
    simpa [MissingColors] using deltaMissing
  obtain ⟨f, hf⟩ := pathComponent.2
  obtain ⟨e, hse, hcolor | hcolor⟩ :=
    TwoColorComponent.exists_colored_incident hf
  · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hse, hcolor⟩
  · exact (deltaNotPresent (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hse, hcolor⟩)).elim

private theorem helper_offSupportInterval_409.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), (
    ∀ (a : Fin trace.steps),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ trace.support a →
        MissingColors G (trace.coloring a.succ) v = MissingColors G (trace.coloring a.castSucc) v)
        →
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc),
    ∀ (n m : ℕ) (hn : n ≤ trace.steps) (hm : m ≤ n), (
    ∀ (s : Fin trace.steps), m ≤ (↑s : ℕ) → (↑s : ℕ) < n → trace.support s ≠ v) → MissingColors G
        (trace.coloring (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + (1 : ℕ)))) v =
        MissingColors G (trace.coloring (⟨m, Nat.lt_succ_of_le (LE.le.trans hm hn)⟩ : Fin
        (trace.steps + (1 : ℕ)))) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot sigmaN
      trace offSupportStep v hv n
  induction n with
  | zero =>
      intro m hn hm hOff
      have hmZero : m = 0 := by omega
      subst m
      rfl
  | succ n ih =>
      intro m hn hm hOff
      by_cases hmTop : m = n + 1
      · subst m
        rfl
      · have hmPrev : m ≤ n := by omega
        let s : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
        have hsOff : trace.support s ≠ v :=
          hOff s hmPrev (Nat.lt_succ_self n)
        have hstep := offSupportStep s v hv (Ne.symm hsOff)
        have hprevious := ih m (Nat.le_of_succ_le hn) hmPrev (by
          intro t hmt htn
          exact hOff t hmt (Nat.lt_succ_of_lt htn))
        have hstep' :
            MissingColors G
                (trace.coloring
                  ⟨n + 1, Nat.lt_succ_of_le hn⟩) v =
              MissingColors G
                (trace.coloring
                  ⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩) v := by
          simpa [s] using hstep
        exact hstep'.trans hprevious

private theorem helper_intermediateInitiallyPresent_477.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN) (_ : (
    ∀ (a : Fin trace.steps),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ trace.support a →
        MissingColors G (trace.coloring a.succ) v = MissingColors G (trace.coloring a.castSucc)
        v)) (_ : (
    ∀ (a : Fin trace.steps), MissingColors G (trace.coloring a.succ) (trace.support a) =
        MissingColors G (trace.coloring a.castSucc) (trace.support a) \ {trace.delta a} ∪
        {trace.gamma a})),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc),
    ∀ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma delta : Fin (p + (1 : ℕ)) →
        Fin k), (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) →
    ∀ (hpositionExists :
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (s : Fin trace.steps), trace.slot s = indices a),
    let pos : Fin (p + (1 : ℕ)) → Fin trace.steps := fun (a : Fin (p + (1 : ℕ))) =>
        Classical.choose (hpositionExists a); (
    ∀ (a : Fin (p + (1 : ℕ))), trace.support (pos a) = v) → (
    ∀ (a : Fin (p + (1 : ℕ))), trace.gamma (pos a) = gamma a) → (
    ∀ (a : Fin (p + (1 : ℕ))), trace.delta (pos a) = delta a) → (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑(pos b) : ℕ) < (↑(pos a) : ℕ) ↔ (↑a : ℕ) < (↑b : ℕ)) → (
    ∀ (s : Fin trace.steps), trace.support s = v ↔
    ∃ (a : Fin (p + (1 : ℕ))), pos a = s) → (
    ∀ (s : Fin trace.steps), trace.gamma s ∉ MissingColors G (trace.coloring s.castSucc)
        (trace.support s)) → (
    ∀ (a : Fin p) (b : Fin (p + (1 : ℕ))), (↑a.succ : ℕ) < (↑b : ℕ) → delta a.castSucc ≠ delta b)
        → (
    ∀ (a : Fin p) (b : Fin (p + (1 : ℕ))), (↑a.succ : ℕ) < (↑b : ℕ) → delta a.castSucc ≠ gamma b)
        →
    ∀ (a : Fin p), delta a.castSucc ∉ MissingColors G sigmaN v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot sigmaN
      trace offSupportStep rootExchange v hv p indices gamma delta hchain hpositionExists pos
      hposSupport hposGamma hposDelta hposOrder hsupportPosition rootGammaNotMissing
      deltaNeLaterDelta deltaNeLaterGamma a
  let target : Fin (p + 1) := a.succ
  let c : Fin k := delta a.castSucc
  have membershipPreserved :
    ∀ (n : ℕ) (hn : n ≤ (pos target).val), (c ∈ MissingColors G (trace.coloring ⟨n,
    by omega
    ⟩) v ↔ c ∈ MissingColors G sigmaN v) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [c] using (Finset.ext_iff.mp
          (congrArg (fun phi => MissingColors G phi v)
            trace.initialColoring) c)
    | succ n ih =>
        intro hn
        have hnPrev : n ≤ (pos target).val := by omega
        have hprevious := ih hnPrev
        let s : Fin trace.steps := ⟨n, by omega⟩
        have hstep :
            (c ∈ MissingColors G (trace.coloring s.succ) v ↔
              c ∈ MissingColors G (trace.coloring s.castSucc) v) := by
          by_cases hs : trace.support s = v
          · obtain ⟨b, hb⟩ := (hsupportPosition s).mp hs
            have hpositionLt : (pos b).val < (pos target).val := by
              rw [hb]
              exact Nat.lt_of_succ_le hn
            have htargetB : target.val < b.val :=
              (hposOrder target b).mp hpositionLt
            have hcDelta : c ≠ delta b := by
              exact deltaNeLaterDelta a b (by simpa [target] using htargetB)
            have hcGamma : c ≠ gamma b := by
              exact deltaNeLaterGamma a b (by simpa [target] using htargetB)
            rw [← hs, rootExchange s, ← hb, hposDelta, hposGamma]
            simp [hcDelta, hcGamma]
          · have hoff := offSupportStep s v hv (Ne.symm hs)
            rw [hoff]
        have hstep' :
            (c ∈ MissingColors G
                (trace.coloring ⟨n + 1, by omega⟩) v ↔
              c ∈ MissingColors G
                (trace.coloring ⟨n, by omega⟩) v) := by
          simpa [s] using hstep
        exact hstep'.trans hprevious
  have hroot : c ∉ MissingColors G
      (trace.coloring (pos target).castSucc) v := by
    have h := rootGammaNotMissing (pos target)
    rw [hposSupport, hposGamma] at h
    change gamma a.succ ∉
      MissingColors G (trace.coloring (pos target).castSucc) v at h
    rw [hchain a] at h
    exact h
  intro hc
  apply hroot
  have hm := (membershipPreserved (pos target).val le_rfl).2 hc
  have hcast :
      (⟨(pos target).val, by omega⟩ : Fin (trace.steps + 1)) =
        (pos target).castSucc := Fin.ext rfl
  rw [hcast] at hm
  exact hm

private theorem helper_processed_541.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (sigmaN : PartialEdgeColoring E k) (trace :
        ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN) (_ : (
    ∀ (a : Fin trace.steps), MissingColors G (trace.coloring a.succ) (trace.support a) =
        MissingColors G (trace.coloring a.castSucc) (trace.support a) \ {trace.delta a} ∪
        {trace.gamma a})) (v : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma
        delta : Fin (p + (1 : ℕ)) → Fin k) (_ : (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc)) (hpositionExists :
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (s : Fin trace.steps), trace.slot s = indices a),
    let pos : Fin (p + (1 : ℕ)) → Fin trace.steps := fun (a : Fin (p + (1 : ℕ))) =>
        Classical.choose (hpositionExists a);
    ∀ (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.support (pos a) = v)) (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.gamma (pos a) = gamma a)) (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), trace.delta (pos a) = delta a)) (_ : (
    ∀ (a b : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) < (↑b : ℕ)), (↑(pos b) : ℕ) < (↑(pos a) : ℕ))) (_ :
        (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑(pos b) : ℕ) < (↑(pos a) : ℕ) ↔ (↑a : ℕ) < (↑b : ℕ))) (_ : (
    ∀ (s : Fin trace.steps), trace.support s = v ↔
    ∃ (a : Fin (p + (1 : ℕ))), pos a = s)) (_ : (
    ∀ (n m : ℕ) (hn : n ≤ trace.steps) (hm : m ≤ n) (_ : (
    ∀ (s : Fin trace.steps) (_ : m ≤ (↑s : ℕ)) (_ : (↑s : ℕ) < n), trace.support s ≠ v)),
        MissingColors G (trace.coloring (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + (1 : ℕ))))
        v = MissingColors G (trace.coloring (⟨m, Nat.lt_succ_of_le (LE.le.trans hm hn)⟩ : Fin
        (trace.steps + (1 : ℕ)))) v)) (_ : (
    ∀ (a : Fin p), delta a.castSucc ∉ MissingColors G sigmaN v)),
    let baseMissing : Finset (Fin k) := MissingColors G sigmaN v \ {delta (Fin.last p)};
    ∀ (a : Fin (p + (1 : ℕ))), MissingColors G (trace.coloring (pos a).succ) v = baseMissing ∪
        {gamma a} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport sigmaN trace
      rootExchange v p indices gamma delta hchain hpositionExists pos hposSupport hposGamma
      hposDelta hposReverse hposOrder hsupportPosition offSupportInterval
      intermediateInitiallyPresent baseMissing a
  exact Fin.reverseInduction (motive := fun a =>
      MissingColors G (trace.coloring (pos a).succ) v =
        baseMissing ∪ {gamma a}) (by
    have hbefore : MissingColors G
        (trace.coloring (pos (Fin.last p)).castSucc) v =
          MissingColors G sigmaN v := by
      have hinterval := offSupportInterval
        (pos (Fin.last p)).val 0 (Nat.le_of_lt (pos (Fin.last p)).isLt)
        (Nat.zero_le _) (by
          intro s hsZero hsBefore hsupport
          obtain ⟨b, hb⟩ := (hsupportPosition s).mp hsupport
          have hbad : (pos b).val < (pos (Fin.last p)).val := by
            simpa [hb] using hsBefore
          have := (hposOrder (Fin.last p) b).mp hbad
          have hbLt := b.isLt
          simp only [Fin.last, Fin.val_mk] at this
          omega)
      have hcast :
          (⟨(pos (Fin.last p)).val,
              Nat.lt_succ_of_le (Nat.le_of_lt (pos (Fin.last p)).isLt)⟩ :
            Fin (trace.steps + 1)) =
            (pos (Fin.last p)).castSucc := Fin.ext rfl
      rw [hcast] at hinterval
      exact hinterval.trans (congrArg
        (fun phi => MissingColors G phi v) trace.initialColoring)
    have hexchange := rootExchange (pos (Fin.last p))
    rw [hposSupport, hposGamma, hposDelta, hbefore] at hexchange
    simpa [baseMissing] using hexchange) (by
    intro a ha
    have hbetween : MissingColors G
        (trace.coloring (pos a.castSucc).castSucc) v =
          MissingColors G (trace.coloring (pos a.succ).succ) v := by
      have hposition := hposReverse a.castSucc a.succ (by simp)
      have hinterval := offSupportInterval
        (pos a.castSucc).val ((pos a.succ).val + 1)
        (Nat.le_of_lt (pos a.castSucc).isLt) (by omega) (by
          intro s hsAfter hsBefore hsupport
          obtain ⟨b, hb⟩ := (hsupportPosition s).mp hsupport
          have hlower : (pos a.succ).val < (pos b).val := by
            rw [hb]
            omega
          have hupper : (pos b).val < (pos a.castSucc).val := by
            rw [hb]
            exact hsBefore
          have hbUpper : b.val < a.succ.val :=
            (hposOrder b a.succ).mp hlower
          have hbLower : a.castSucc.val < b.val :=
            (hposOrder a.castSucc b).mp hupper
          change b.val < a.val + 1 at hbUpper
          change a.val < b.val at hbLower
          omega)
      have hnCast :
          (⟨(pos a.castSucc).val,
              Nat.lt_succ_of_le (Nat.le_of_lt (pos a.castSucc).isLt)⟩ :
            Fin (trace.steps + 1)) =
            (pos a.castSucc).castSucc := Fin.ext rfl
      have hmSucc :
          (⟨(pos a.succ).val + 1, by omega⟩ :
            Fin (trace.steps + 1)) = (pos a.succ).succ := Fin.ext rfl
      rw [hnCast, hmSucc] at hinterval
      exact hinterval
    have hexchange := rootExchange (pos a.castSucc)
    rw [hposSupport, hposGamma, hposDelta, hbetween, ha, hchain a]
      at hexchange
    have hnotBase : delta a.castSucc ∉ baseMissing := by
      exact fun hmem => intermediateInitiallyPresent a
        (Finset.mem_sdiff.mp hmem).1
    apply hexchange.trans
    ext c
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_singleton]
    by_cases hc : c = delta a.castSucc
    · subst c
      simp [hnotBase]
    · simp [hc]) a

private theorem helper_hafter_619.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (sigmaN : PartialEdgeColoring E k) (trace :
        ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN) (v : V) (p : ℕ)
        (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (hpositionExists :
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (s : Fin trace.steps), trace.slot s = indices a),
    let pos : Fin (p + (1 : ℕ)) → Fin trace.steps := fun (a : Fin (p + (1 : ℕ))) =>
        Classical.choose (hpositionExists a);
    ∀ (_ : (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑(pos b) : ℕ) < (↑(pos a) : ℕ) ↔ (↑a : ℕ) < (↑b : ℕ))) (_ : (
    ∀ (s : Fin trace.steps), trace.support s = v ↔
    ∃ (a : Fin (p + (1 : ℕ))), pos a = s)) (_ : (
    ∀ (n m : ℕ) (hn : n ≤ trace.steps) (hm : m ≤ n) (_ : (
    ∀ (s : Fin trace.steps) (_ : m ≤ (↑s : ℕ)) (_ : (↑s : ℕ) < n), trace.support s ≠ v)),
        MissingColors G (trace.coloring (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + (1 : ℕ))))
        v = MissingColors G (trace.coloring (⟨m, Nat.lt_succ_of_le (LE.le.trans hm hn)⟩ : Fin
        (trace.steps + (1 : ℕ)))) v)), MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G (trace.coloring (pos (0 : Fin (p + (1 : ℕ)))).succ) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport sigmaN trace v p
      indices hpositionExists pos hposOrder hsupportPosition offSupportInterval
  have hinterval := offSupportInterval trace.steps ((pos 0).val + 1)
    le_rfl (by omega) (by
      intro s hsAfter hsFinal hsupport
      obtain ⟨b, hb⟩ := (hsupportPosition s).mp hsupport
      have hbad : (pos 0).val < (pos b).val := by
        rw [hb]
        omega
      have hbNeg : b.val < 0 := by
        simpa using (hposOrder b 0).mp hbad
      omega)
  have hnLast :
      (⟨trace.steps, Nat.lt_succ_of_le le_rfl⟩ :
        Fin (trace.steps + 1)) = Fin.last trace.steps := Fin.ext rfl
  have hmSucc :
      (⟨(pos 0).val + 1, by omega⟩ : Fin (trace.steps + 1)) =
        (pos 0).succ := Fin.ext rfl
  rw [hnLast, hmSucc] at hinterval
  exact hinterval

private theorem helper_branch_261.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN phiJ :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), w ≠ terminalSupport →
        (
    ∃ t ∈ ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport,
        ett.series.data.chosenVertex t.succ = some w) →
    ∃ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma : Fin (p + (1 : ℕ)) → Fin k)
        (delta : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) ∧
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a)) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a)) ∧ (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) ∧ Function.Injective (Fin.cons (gamma (0 : Fin
        (p + (1 : ℕ)))) delta) ∧ MissingColors G phiJ w = MissingColors G sigmaN w \
        {delta (Fin.last p)} ∪ {gamma (0 : Fin (p + (1 : ℕ)))}) → (
    ∀ (a : Fin trace.steps),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ trace.support a →
        MissingColors G (trace.coloring a.succ) v = MissingColors G (trace.coloring a.castSucc) v)
        → (
    ∀ (a : Fin trace.steps), MissingColors G (trace.coloring a.succ) (trace.support a) =
        MissingColors G (trace.coloring a.castSucc) (trace.support a) \ {trace.delta a} ∪
        {trace.gamma a}) →
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ terminalSupport →
        (
    ∃ r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport,
        ett.series.data.chosenVertex r.succ = some v) → MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G phiJ v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN phiJ
      trace hinvariant hclassPrepared offSupportStep rootExchange v hv hvTerminal hsupported
  obtain ⟨r, hrActive, hrVertex⟩ := hsupported
  have hrRestoration : r ∈ ExtensionBaseRestorationIndices ett
      terminalSupport hterminalSupport := by
    unfold ExtensionBaseRestorationIndices
    apply Finset.mem_sdiff.mpr
    refine ⟨hrActive, ?_⟩
    unfold ExtensionBaseSupportClass
    simp only [Finset.mem_filter, hrActive, true_and]
    intro hterminalVertex
    have : v = terminalSupport := by
      apply Option.some.inj
      exact hrVertex.symm.trans hterminalVertex
    exact hvTerminal this
  obtain ⟨p, indices, gamma, delta, hincreasing, hclass,
      hgamma, hdelta, hchain, hinjective, hprepared⟩ :=
    hclassPrepared v hv hvTerminal ⟨r, hrRestoration, hrVertex⟩
  have hindexClass (a : Fin (p + 1)) :
      indices a ∈ ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport v :=
    (hclass (indices a)).2 ⟨a, rfl⟩
  have hindexActive (a : Fin (p + 1)) :
      indices a ∈ ExtensionBaseActiveIndices ett terminalSupport
        hterminalSupport := by
    have h := hindexClass a
    simp only [ExtensionBaseSupportClass, Finset.mem_filter] at h
    exact h.1
  have hindexVertex (a : Fin (p + 1)) :
      ett.series.data.chosenVertex (indices a).succ = some v := by
    have h := hindexClass a
    simp only [ExtensionBaseSupportClass, Finset.mem_filter] at h
    exact h.2
  have hindexRestoration (a : Fin (p + 1)) :
      indices a ∈ ExtensionBaseRestorationIndices ett terminalSupport
        hterminalSupport := by
    unfold ExtensionBaseRestorationIndices
    apply Finset.mem_sdiff.mpr
    refine ⟨hindexActive a, ?_⟩
    intro haTerminal
    have h := haTerminal
    simp only [ExtensionBaseSupportClass, Finset.mem_filter] at h
    have haVertex := h.2
    apply hvTerminal
    exact Option.some.inj ((hindexVertex a).symm.trans haVertex)
  have hpositionExists (a : Fin (p + 1)) :
      ∃ s : Fin trace.steps, trace.slot s = indices a := by
    have hmem : indices a ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hindexRestoration a
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hmem
  let pos : Fin (p + 1) → Fin trace.steps := fun a =>
    Classical.choose (hpositionExists a)
  have hposSlot (a : Fin (p + 1)) : trace.slot (pos a) = indices a :=
    Classical.choose_spec (hpositionExists a)
  have hposSupport (a : Fin (p + 1)) : trace.support (pos a) = v := by
    apply Option.some.inj
    exact (trace.chosenVertex (pos a)).symm.trans (by
      rw [hposSlot]
      exact hindexVertex a)
  have hposGamma (a : Fin (p + 1)) : trace.gamma (pos a) = gamma a := by
    apply Option.some.inj
    exact (trace.gammaField (pos a)).symm.trans (by
      rw [hposSlot]
      exact hgamma a)
  have hposDelta (a : Fin (p + 1)) : trace.delta (pos a) = delta a := by
    apply Option.some.inj
    exact (trace.deltaField (pos a)).symm.trans (by
      rw [hposSlot]
      exact hdelta a)
  have hslotInjective : Function.Injective trace.slot := by
    intro a b hab
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hdesc := trace.strictlyDescending a b hlt
      rw [hab] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
    · have hdesc := trace.strictlyDescending b a hgt
      rw [hab] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
  have hposReverse (a b : Fin (p + 1)) (hab : a.val < b.val) :
      (pos b).val < (pos a).val := by
    exact @helper_hposReverse_329 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSupport hterminalSupport sigmaN trace p indices hincreasing
        hpositionExists hposSlot a b hab
  have hposOrder (a b : Fin (p + 1)) :
      (pos b).val < (pos a).val ↔ a.val < b.val := by
    constructor
    · intro hba
      by_contra hnot
      have hle : b.val ≤ a.val := Nat.le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hrev := hposReverse b a hlt
        omega
      · have hab : a = b := Fin.ext heq.symm
        subst b
        exact (Nat.lt_irrefl _ hba)
    · exact hposReverse a b
  have hsupportPosition (s : Fin trace.steps) :
      trace.support s = v ↔ ∃ a : Fin (p + 1), pos a = s := by
    exact @helper_hsupportPosition_356 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett terminalSupport hterminalSupport jSlot q
        sigmaN trace hinvariant v p indices hclass hpositionExists hposSlot hposSupport
        hslotInjective s
  have rootGammaPresent (s : Fin trace.steps) :
      trace.gamma s ∈ PresentColors G (trace.coloring s.castSucc)
        (trace.support s) := by
    exact @helper_rootGammaPresent_371 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett terminalSupport hterminalSupport jSlot q
        sigmaN trace hinvariant v p gamma delta s
  have rootGammaNotMissing (s : Fin trace.steps) :
      trace.gamma s ∉ MissingColors G (trace.coloring s.castSucc)
        (trace.support s) := by
    simpa [MissingColors] using rootGammaPresent s
  have offSupportInterval :=
    @helper_offSupportInterval_409 V E inferInstance inferInstance inferInstance G k e0
        input T generating ett terminalSupport hterminalSupport jSlot sigmaN trace offSupportStep
        v hv
  let colorChain : Fin (p + 2) → Fin k := Fin.cons (gamma 0) delta
  have gammaEqChain (a : Fin (p + 1)) :
      gamma a = colorChain a.castSucc := by
    cases a using Fin.cases with
    | zero => simp [colorChain]
    | succ a => simpa [colorChain] using hchain a
  have deltaEqChain (a : Fin (p + 1)) :
      delta a = colorChain a.succ := by
    simp [colorChain]
  have deltaNeLaterDelta (a : Fin p) (b : Fin (p + 1))
      (hab : a.succ.val < b.val) : delta a.castSucc ≠ delta b := by
    intro heq
    have hcolor : colorChain a.castSucc.succ = colorChain b.succ := by
      rw [← deltaEqChain, ← deltaEqChain]
      exact heq
    have hi : a.castSucc.succ = b.succ := hinjective hcolor
    have hbase : a.castSucc = b := Fin.succ_inj.mp hi
    have hv : a.val = b.val := congrArg Fin.val hbase
    have hab' : a.val + 1 < b.val := by simpa using hab
    omega
  have deltaNeLaterGamma (a : Fin p) (b : Fin (p + 1))
      (hab : a.succ.val < b.val) : delta a.castSucc ≠ gamma b := by
    intro heq
    have hcolor : colorChain a.castSucc.succ = colorChain b.castSucc := by
      rw [← deltaEqChain, ← gammaEqChain]
      exact heq
    have hi : a.castSucc.succ = b.castSucc := hinjective hcolor
    have hv : a.val + 1 = b.val := by
      simpa using congrArg Fin.val hi
    have hab' : a.val + 1 < b.val := by simpa using hab
    exact (Nat.ne_of_lt hab') hv
  have intermediateInitiallyPresent (a : Fin p) :
      delta a.castSucc ∉ MissingColors G sigmaN v := by
    exact @helper_intermediateInitiallyPresent_477 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett terminalSupport hterminalSupport jSlot sigmaN
        trace offSupportStep rootExchange v hv p indices gamma delta hchain hpositionExists
        hposSupport hposGamma hposDelta hposOrder hsupportPosition rootGammaNotMissing
        deltaNeLaterDelta deltaNeLaterGamma a
  let baseMissing :=
    MissingColors G sigmaN v \ {delta (Fin.last p)}
  have processed (a : Fin (p + 1)) :
      MissingColors G (trace.coloring (pos a).succ) v =
        baseMissing ∪ {gamma a} := by
    exact @helper_processed_541 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSupport hterminalSupport sigmaN trace rootExchange v p indices
        gamma delta hchain hpositionExists hposSupport hposGamma hposDelta hposReverse hposOrder
        hsupportPosition offSupportInterval intermediateInitiallyPresent a
  have hafter :=
    @helper_hafter_619 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSupport hterminalSupport sigmaN trace v p indices hpositionExists
        hposOrder hsupportPosition offSupportInterval
  have hfinal := hafter.trans (processed 0)
  exact hfinal.trans (by simpa [baseMissing] using hprepared.symm)

private theorem helper_branch_318.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN phiJ :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), (
    ∀ r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport,
        ett.series.data.chosenVertex r.succ ≠ some v) → MissingColors G sigmaN v = MissingColors G
        phiJ v) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), w ≠ terminalSupport →
        (
    ∃ t ∈ ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport,
        ett.series.data.chosenVertex t.succ = some w) →
    ∃ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gamma : Fin (p + (1 : ℕ)) → Fin k)
        (delta : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) ∧
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gamma a)) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (delta a)) ∧ (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) ∧ Function.Injective (Fin.cons (gamma (0 : Fin
        (p + (1 : ℕ)))) delta) ∧ MissingColors G phiJ w = MissingColors G sigmaN w \
        {delta (Fin.last p)} ∪ {gamma (0 : Fin (p + (1 : ℕ)))}) → (
    ∀ (a : Fin trace.steps),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), v ≠ trace.support a →
        MissingColors G (trace.coloring a.succ) v = MissingColors G (trace.coloring a.castSucc) v)
        → (
    ∀ (a : Fin trace.steps), MissingColors G (trace.coloring a.succ) (trace.support a) =
        MissingColors G (trace.coloring a.castSucc) (trace.support a) \ {trace.delta a} ∪
        {trace.gamma a}) → (
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), (
    ∀ (a : Fin trace.steps), trace.support a ≠ v) → MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigmaN v) →
    ∀ v ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase
        terminalSupport, MissingColors G (trace.coloring (Fin.last trace.steps)) v = MissingColors
        G phiJ v := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      phiJ trace hinvariant hunsupported hclassPrepared offSupportStep rootExchange
      preservedWhenOff v hvErase
  have hv := (Finset.mem_erase.mp hvErase).2
  have hvTerminal : v ≠ terminalSupport := by
    exact (Finset.mem_erase.mp hvErase).1
  by_cases hsupported : ∃ r : Fin ett.rounds,
      r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport ∧
        ett.series.data.chosenVertex r.succ = some v
  · exact @helper_branch_261 V E inferInstance inferInstance  inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport jSlot q sigmaN phiJ trace
      hinvariant hclassPrepared offSupportStep rootExchange v hv hvTerminal hsupported
  · have hOff : ∀ a : Fin trace.steps, trace.support a ≠ v := by
      intro a hsupport
      have hrestoration := (hinvariant.2.1 a).1
      have hactive := (Finset.mem_sdiff.mp hrestoration).1
      apply hsupported
      refine ⟨trace.slot a, hactive, ?_⟩
      simpa [hsupport] using trace.chosenVertex a
    exact (preservedWhenOff v hv hOff).trans
      (hunsupported v hv (by
        intro r hrActive hrVertex
        exact hsupported ⟨r, hrActive, hrVertex⟩))

theorem ExtensionBaseClaim43MissingColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN phiJ : PartialEdgeColoring E k)
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace)
    (hunsupported : ∀ v : V,
      v ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      (∀ r : Fin ett.rounds,
        r ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
        ett.series.data.chosenVertex r.succ ≠ some v) →
      MissingColors G sigmaN v = MissingColors G phiJ v)
    (hclassPrepared : ∀ w : V,
      w ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      w ≠ terminalSupport →
      (∃ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport ∧
        ett.series.data.chosenVertex t.succ = some w) →
      ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
        ∃ gamma delta : Fin (p + 1) → Fin k,
          (∀ a b, a.val < b.val →
            (indices a).val < (indices b).val) ∧
          (∀ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport w ↔
              ∃ a : Fin (p + 1), indices a = r) ∧
          (∀ a, ett.series.data.gamma (indices a).succ = some (gamma a)) ∧
          (∀ a, ett.series.data.delta (indices a).succ = some (delta a)) ∧
          (∀ a : Fin p, gamma a.succ = delta a.castSucc) ∧
          Function.Injective (Fin.cons (gamma 0) delta) ∧
          MissingColors G phiJ w =
            (MissingColors G sigmaN w \ {delta (Fin.last p)}) ∪
              {gamma 0}) :
    (∀ v : V,
      v ∈ (TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc)).erase
            terminalSupport →
      MissingColors G (trace.coloring (Fin.last trace.steps)) v =
        MissingColors G phiJ v) ∧
    MissingColors G (trace.coloring (Fin.last trace.steps))
        terminalSupport =
      MissingColors G sigmaN terminalSupport := by
  classical
  have vertexTransfer : ∀ (A B : TreeSequence G e0),
      TreeSequenceInitialSegment A B → ∀ v,
        v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
    intro A B hAB v hv
    rcases hAB with ⟨hlen, hvertex, hedge⟩
    unfold TreeSequenceVertexSet at hv ⊢
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertex i⟩
  have edgeOutside :=
    @helper_edgeOutside_99 V E inferInstance inferInstance  inferInstance G k
        e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN trace
        hinvariant vertexTransfer
  have offSupportStep :
    ∀ (a : Fin trace.steps) (v : V), v ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc) → v ≠ trace.support a → MissingColors G (trace.coloring a.succ) v =
        MissingColors G (trace.coloring a.castSucc) v := by
    intro a v hv hvSupport
    have fixed : ∀ f : E, Incident G v f →
        trace.coloring a.succ f = trace.coloring a.castSucc f := by
      intro f hvf
      rw [trace.transition]
      simp [TwoColorComponentSwap, edgeOutside a v hv hvSupport f hvf]
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and]
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and,
      not_exists, not_and]
    constructor
    · intro hc f hvf hcolor
      apply hc f hvf
      rw [fixed f hvf]
      exact hcolor
    · intro hc f hvf hcolor
      apply hc f hvf
      rw [← fixed f hvf]
      exact hcolor
  have rootExchange :=
    @helper_rootExchange_162 V E inferInstance inferInstance  inferInstance G
        k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN trace hinvariant
  have preservedWhenOff :
    ∀ (v : V), v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ a : Fin trace.steps, trace.support a ≠ v) → MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigmaN v := by
    intro v hv hOff
    have inductionClaim :
    ∀ n : ℕ, (hn : n ≤ trace.steps) → MissingColors G (trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩) v
        = MissingColors G sigmaN v := by
      intro n hn
      induction n with
      | zero =>
          simpa using (congrArg (fun phi => MissingColors G phi v)
            trace.initialColoring)
      | succ n ih =>
          let a : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
          have hprevious := ih (Nat.le_of_succ_le hn)
          have hstep := offSupportStep a v hv (Ne.symm (hOff a))
          have hcast : a.castSucc =
              (⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ :
                Fin (trace.steps + 1)) := by
            apply Fin.ext
            rfl
          have hsucc : a.succ =
              (⟨n + 1, Nat.lt_succ_of_le hn⟩ :
                Fin (trace.steps + 1)) := by
            apply Fin.ext
            rfl
          rw [hcast, hsucc] at hstep
          exact hstep.trans hprevious
    simpa [Fin.last] using inductionClaim trace.steps le_rfl
  have terminalOff : ∀ a : Fin trace.steps,
      trace.support a ≠ terminalSupport := by
    intro a hsupport
    have hrestoration := (hinvariant.2.1 a).1
    have hparts := Finset.mem_sdiff.mp hrestoration
    apply hparts.2
    unfold ExtensionBaseSupportClass
    simp only [Finset.mem_filter]
    refine ⟨hparts.1, ?_⟩
    simpa [hsupport] using trace.chosenVertex a
  constructor
  · exact @helper_branch_318 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSupport hterminalSupport jSlot q sigmaN phiJ trace
      hinvariant hunsupported hclassPrepared offSupportStep rootExchange preservedWhenOff
  · exact preservedWhenOff terminalSupport hterminalJ terminalOff

end GoldbergSeymour

end
