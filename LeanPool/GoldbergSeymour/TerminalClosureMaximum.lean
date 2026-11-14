/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtendedTashkinovTree

/-!
# Terminal Closure Maximum

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Maximality of terminal closures under the stable recolorings and seeds allowed by the terminal
extension kind.
-/
def TerminalClosureMaximum {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
  {G : LooplessMultigraph V E} {k : Nat} {e0 : E} {input : PartialEdgeColoring E k}
  {T : TreeSequence G e0} {generating : PartialEdgeColoring E k}
  (ett : ExtendedTashkinovTree G k e0 input T generating) : Prop :=
 let idx : Fin (ett.rounds + 1) := Fin.last ett.rounds
 let Ti : TreeSequence G e0 := ett.series.data.tree idx.castSucc
 ∀ (pi : PartialEdgeColoring E k) (seed candidate : TreeSequence G e0),
  IsProperEdgeColoring G pi →
   IsOneEdgeUncolored pi e0 →
    StableColoring Ti (TashkinovStoredColors ett.series.data idx) (ett.series.data.coloring idx)
      pi →
     ((ett.series.data.kind idx = some TashkinovExtensionKind.PE ∧ seed = Ti) ∨
       ((ett.series.data.kind idx = some TashkinovExtensionKind.SE ∨
         ett.series.data.kind idx = some TashkinovExtensionKind.RE) ∧
        exists f : E,
         ett.series.data.connectingEdges idx = { f } ∧ TreeSequenceAdjoinEdge Ti f seed)) →
      TashkinovClosure pi seed candidate →
       (TreeSequenceVertexSet candidate).card ≤
        (TreeSequenceVertexSet (ett.series.data.tree (Fin.last (ett.rounds + 1)))).card

end GoldbergSeymour

end
