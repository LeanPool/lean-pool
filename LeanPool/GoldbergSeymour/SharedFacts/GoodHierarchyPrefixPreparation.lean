/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Bound.Init

/-!
# Shared facts for GoodHierarchyPrefixPreparation

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.GoodHierarchyPrefixPreparation

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev segmentTransStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
          C → TreeSequenceInitialSegment A C

/-- A common proof used by the branches of this transport or construction argument. -/
theorem segmentTrans.{u_1, u_2} : segmentTransStatement.{u_1, u_2} := by
  intro V E G e0 A B C hAB hBC
  exact hAB.trans hBC

end GoldbergSeymour.SharedFacts.GoodHierarchyPrefixPreparation

end
