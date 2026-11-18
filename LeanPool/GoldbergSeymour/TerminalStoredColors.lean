/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTerminalData

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# P2752_T2_Terminal Stored Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2752_T2_TerminalStoredColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input phi sigma : PartialEdgeColoring E k} {T U : TreeSequence G e0}
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma U) :
    TashkinovStoredColors corr.replacementETT.series.data
        (Fin.last corr.replacementETT.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
  exact corr.terminalData.2.2

end GoldbergSeymour

end
