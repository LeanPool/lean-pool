/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseClaim43EdgeEffects
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim43MissingColors
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim43Stability
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim43TreeEdges
public import LeanPool.GoldbergSeymour.ExtensionRules

/-!
# Extension Base Claim43

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseClaim43 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (_ : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (_ : ett.series.data.chosenVertex q.succ =
      some terminalSupport)
    (_ : jSlot.val + 1 =
      ETTFirstAppearanceIndex ett terminalSupport hterminalSupport)
    (sigmaN : PartialEdgeColoring E k) (C : Finset (Fin k))
    (hterminalJ : terminalSupport ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc))
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigmaN)
    (hsigmaBefore : StableColoringBeforeVertex T terminalSupport
      hterminalSupport C (ett.series.data.coloring jSlot.castSucc) sigmaN)
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
      MissingColors G sigmaN v =
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v)
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
          MissingColors G (ett.series.data.coloring jSlot.castSucc) w =
            (MissingColors G sigmaN w \ {delta (Fin.last p)}) ∪
              {gamma 0}) :
    let rho1 := trace.coloring (Fin.last trace.steps)
    let restorationColors :=
      (ExtensionBaseRestorationIndices ett terminalSupport
        hterminalSupport).biUnion fun t => ett.series.data.stored t.succ
    StableColoringBeforeVertex T terminalSupport hterminalSupport C
        (ett.series.data.coloring jSlot.castSucc) rho1 ∧
      ((∀ v : V,
        v ∈ (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)).erase
              terminalSupport →
        MissingColors G rho1 v =
          MissingColors G (ett.series.data.coloring jSlot.castSucc) v) ∧
       MissingColors G rho1 terminalSupport =
          MissingColors G sigmaN terminalSupport) ∧
      (∀ a : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
        rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            sigmaN ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
          sigmaN ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            ett.series.data.coloring jSlot.castSucc
              ((ett.series.data.tree jSlot.succ.castSucc).edge a)) ∧
      (∀ f : E, rho1 f ≠ sigmaN f →
        f ∉ InternalEdges G
            (TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc)) ∧
          ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
            c ∈ restorationColors ∧ d ∈ restorationColors) ∧
      ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
        s ∈ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport terminalSupport →
        s ≠ q →
        ett.series.data.chosenVertex s.succ = some terminalSupport →
        ett.series.data.gamma s.succ = some gammaS →
        ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ExtensionBaseClaim43Stability ett terminalSupport hterminalSupport
      jSlot q sigmaN (ett.series.data.coloring jSlot.castSucc) C hterminalJ trace hinvariant
      hsigmaBefore
  · exact ExtensionBaseClaim43MissingColors ett terminalSupport hterminalSupport
      jSlot q sigmaN (ett.series.data.coloring jSlot.castSucc) hterminalJ trace
      hinvariant hunsupported hclassPrepared
  · exact ExtensionBaseClaim43TreeEdges ett terminalSupport hterminalSupport
      jSlot q hjle hqTerminal sigmaN hsigmaProper hsigmaOne hsigmaStable trace
      hinvariant
  · exact ExtensionBaseClaim43EdgeEffects ett terminalSupport hterminalSupport
      jSlot q sigmaN trace hinvariant
  · intro s gammaS deltaS hs hneq hchosen hgamma hdelta
    have hactive : s ∈ ExtensionBaseActiveIndices ett terminalSupport
        hterminalSupport := by
      simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hs
      exact hs.1
    have hnoTrace : ∀ a : Fin trace.steps, trace.slot a ≠ s := by
      intro a ha
      have hrest : trace.slot a ∈
          ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport := by
        rw [← trace.enumerates]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      have hdiff : trace.slot a ∈
          ExtensionBaseActiveIndices ett terminalSupport hterminalSupport ∧
          trace.slot a ∉ ExtensionBaseSupportClass ett terminalSupport
            hterminalSupport terminalSupport := by
        simpa [ExtensionBaseRestorationIndices] using hrest
      exact hdiff.2 (by simpa [ha])
    exact hinvariant.2.2 s terminalSupport gammaS deltaS hactive hneq hnoTrace
      hchosen hgamma hdelta

end GoldbergSeymour

end
