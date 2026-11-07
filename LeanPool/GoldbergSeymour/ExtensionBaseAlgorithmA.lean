/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmAInduction
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmATraceExists
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmAColorState

/-!
# Extension Base Algorithm A

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmA {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (_ : q.val + 1 = ett.rounds)
    (_ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ =
      some terminalSupport)
    (_ : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hterminalBefore : ∀ (t : Fin ett.rounds) (vt : V),
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ett.series.data.chosenVertex t.succ = some vt →
      TreeVertexOrder T terminalSupport vt)
    (hjInitial : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree t.succ.castSucc))
    (hslotData : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett terminalSupport
          hterminalSupport →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT)
    (hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigmaN gammaT deltaT)
    (hclassMissing : ∀ (w : V) (t : Fin ett.rounds) (deltaT : Fin k),
      ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ⊆
          ExtensionBaseRestorationIndices ett terminalSupport
            hterminalSupport →
      t ∈ ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport w →
      (∀ s : Fin ett.rounds,
        s ∈ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport w →
        s.val ≤ t.val) →
      ett.series.data.delta t.succ = some deltaT →
      MissingColors G sigmaN w ∩
          (ExtensionBaseSupportClass ett terminalSupport hterminalSupport w).biUnion
            (fun s => ett.series.data.stored s.succ) = {deltaT})
    (hpairOverlap : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      t ∈ ExtensionBaseActiveIndices ett terminalSupport
          hterminalSupport →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
          vs = vt ∧
          ¬ ∃ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett terminalSupport
                hterminalSupport vs ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty →
        ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {gammaT} ∧
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {deltaS})) :
    ∃ trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN,
      ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace := by
  classical
  obtain ⟨trace⟩ := ExtensionBaseAlgorithmATraceExists ett terminalSupport
    hterminalSupport sigmaN hslotData
  have hcolorState := ExtensionBaseAlgorithmAColorState ett terminalSupport
    hterminalSupport q sigmaN hqVertex trace hinitialSI hclassMissing
      hpairOverlap
  refine ⟨trace, ?_⟩
  exact ExtensionBaseAlgorithmAInduction ett terminalSupport hterminalSupport
    jSlot q sigmaN hqVertex hsigmaProper hsigmaOne hterminalBefore hjInitial
      hinitialSI hpairOverlap trace hcolorState

end GoldbergSeymour

end
