/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass

/-!
# Extension Base Algorithm CTrace

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A descending enumeration of the terminal support class excluding the terminal slot, with its
color swaps.
-/
structure ExtensionBaseAlgorithmCTrace {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (terminalSlot : Fin ett.rounds)
    (mu0 : PartialEdgeColoring E k) (u : V) where
  /-- The number of component swaps in the trace. -/
  steps : ℕ
  /-- The extension-series slot processed by each swap. -/
  slot : Fin steps → Fin ett.rounds
  /-- The auxiliary color or color family used by this configuration. -/
  gamma : Fin steps → Fin k
  /-- The companion color used for the component swap at each stage. -/
  delta : Fin steps → Fin k
  /-- The partial coloring or sequence of partial colorings recorded by this certificate. -/
  coloring : Fin (steps + 1) → PartialEdgeColoring E k
  initialColoring : coloring 0 = mu0
  terminalAtEnd : terminalSlot.val + 1 = ett.rounds
  terminalInClass :
    terminalSlot ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport
  enumerates :
    Finset.univ.image slot =
      (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
        terminalSlot
  strictlyDescending : ∀ a b, a.val < b.val → (slot b).val < (slot a).val
  chosenSupport : ∀ a, ett.series.data.chosenVertex (slot a).succ = some terminalSupport
  extensionKind : ∀ a, ett.series.data.kind (slot a).succ = some TashkinovExtensionKind.PE
  gammaField : ∀ a, ett.series.data.gamma (slot a).succ = some (gamma a)
  deltaField : ∀ a, ett.series.data.delta (slot a).succ = some (delta a)
  transition :
    ∀ a,
      coloring a.succ =
        TwoColorComponentSwap G (coloring a.castSucc) (gamma a) (delta a) (Sum.inl u)

end GoldbergSeymour

end
