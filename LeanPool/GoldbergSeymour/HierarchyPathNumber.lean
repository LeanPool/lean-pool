/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import LeanPool.GoldbergSeymour.HierarchyStarredStage

/-!
# Hierarchy Path Number

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- The first position after the starred stage at which the remaining tail is a path, defaulting to
the tail length.
-/
noncomputable def HierarchyPathNumber {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
    {T : TreeSequence G e0} {generating phi : PartialEdgeColoring E k}
    {ett : ExtendedTashkinovTree G k e0 input T generating} {base : HierarchyBase ett phi}
    (H : TashkinovHierarchy ett base) : ℕ := by
  classical
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let tailLength := T.length - A.length
  let candidates := (Finset.Icc 1 tailLength).filter fun i =>
    ∀ r : Fin T.length, A.length + i ≤ r.val →
      G.ends (T.edge r) = s(T.vertex r.castSucc, T.vertex r.succ)
  exact if h : candidates.Nonempty then candidates.min' h else tailLength

end GoldbergSeymour

end
