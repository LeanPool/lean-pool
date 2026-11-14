/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext

public import LeanPool.GoldbergSeymour.SameGoodHierarchy

/-!
# Hierarchy Replacement Presentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A stable replacement coloring and corresponding minimum-counterexample hierarchy with the same
good-hierarchy data.
-/
structure HierarchyReplacementPresentation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi) (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C) where
  /-- The partial coloring or sequence of partial colorings recorded by this certificate. -/
  coloring : PartialEdgeColoring E k
  /-- The replacement extended tree with its ladder and coloring agreement certificates. -/
  corresponding : CorrespondingExtendedTashkinovTree G k e0 ett coloring T
  maximum : MaximumProperty corresponding.replacementETT
  /-- The hierarchy base for the replacement extended tree. -/
  replacementBase : HierarchyBase corresponding.replacementETT coloring
  /-- The replacement hierarchy retaining the non-elementarity condition. -/
  counterexample : HierarchyCounterexample replacementBase
  sameGood : SameGoodHierarchy C.good counterexample.good
  minimumContext :
    HierarchyMinimumCounterexampleContext G k e0 corresponding.replacementInput T coloring
      corresponding.replacementETT replacementBase counterexample

end GoldbergSeymour

end
