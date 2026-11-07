/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTreeTransTrees

/-!
# Corresponding Extended Tashkinov Tree Trans

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma CorrespondingExtendedTashkinovTreeTrans
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma tau : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (first : CorrespondingExtendedTashkinovTree G k e0 ett sigma T)
    (second : CorrespondingExtendedTashkinovTree
      G k e0 first.replacementETT tau T) :
    exists composite : CorrespondingExtendedTashkinovTree G k e0 ett tau T,
      composite.replacementInput = second.replacementInput /\
        HEq composite.replacementSeries second.replacementSeries /\
        HEq composite.replacementETT second.replacementETT := by
  classical
  exact CorrespondingExtendedTashkinovTreeTransTrees G k e0 input
    T T T phi sigma tau ett first second

end GoldbergSeymour

end
