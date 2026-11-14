/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Bound.Init

/-!
# Shared facts for ChangeLemmaMixedZeroNonclosed

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ZeroNonclosedTransport

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {X Y Z : TreeSequence G e0}, TreeSequenceInitialSegment X Z → TreeSequenceInitialSegment Y
          Z → X.length ≤ Y.length → TreeSequenceInitialSegment X Y

/-- A common proof used by the branches of this transport or construction argument. -/
theorem comparableInitialSegments.{u_1, u_2} : comparableInitialSegmentsStatement.{u_1, u_2} := by
  intro V E G e0 X Y Z hXZ hYZ hXY
  exact hYZ.of_common_extension hXZ hXY

end GoldbergSeymour.SharedFacts.ZeroNonclosedTransport

end
