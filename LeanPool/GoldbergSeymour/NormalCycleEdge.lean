/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple

/-!
# Normal Cycle Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- The distinguished cycle edge at a position, using the uncolored edge first and the closing edge
last.
-/
noncomputable def NormalCycleEdge {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {phi : PartialEdgeColoring E k}
    {T : TreeSequence G e0} (N : NormalGlobalMaximumTriple G k e0 phi T) (i : Fin N.height) : E
        := by
  classical
  if hzero : i.val = 0 then
    exact e0
  else if hlast : i.val + 1 = N.height then
    exact N.closingEdge
  else
    exact T.edge ⟨i.val, by
      have hi := i.isLt
      have hu := N.height_upper
      omega⟩

end GoldbergSeymour

end
