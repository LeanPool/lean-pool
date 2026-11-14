/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.MaximumProperty

/-!
# Rutgers Closed Presentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A closed replacement-tree presentation with a corresponding maximum-property extended tree. -/
structure RutgersClosedPresentation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E) {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
    (original : ExtendedTashkinovTree G k e0 input T generating) where
  /-- The replacement coloring constrained by this certificate. -/
  sigma : PartialEdgeColoring E k
  /-- The replacement tree under the new coloring. -/
  U : TreeSequence G e0
  /-- The replacement extended tree with its ladder and coloring agreement certificates. -/
  corresponding : CorrespondingExtendedTashkinovTree G k e0 original sigma U
  maximum : MaximumProperty corresponding.replacementETT
  terminalRoute :
    let replacement := corresponding.replacementETT
    let n : Fin (replacement.rounds + 1) := Fin.last replacement.rounds
    let Tn : TreeSequence G e0 := replacement.series.data.tree n.castSucc
    (replacement.series.data.kind n = some TashkinovExtensionKind.PE ∧
        TashkinovClosure sigma Tn U) ∨
      ((replacement.series.data.kind n = some TashkinovExtensionKind.SE ∨
          replacement.series.data.kind n = some TashkinovExtensionKind.RE) ∧
        exists (f : E) (seed : TreeSequence G e0),
          replacement.series.data.connectingEdges n = { f } ∧
            TreeSequenceAdjoinEdge Tn f seed ∧ TashkinovClosure sigma seed U)

end GoldbergSeymour

end
