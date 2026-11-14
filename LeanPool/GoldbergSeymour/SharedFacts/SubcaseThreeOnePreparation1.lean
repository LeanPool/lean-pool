/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceColoringFacts

public import LeanPool.GoldbergSeymour.SharedFacts.ShorteningTransport


/-!
# Shared facts for Preparation1

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.SubcaseThreeOnePreparation1

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionUpperBoundStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0) (c : Fin k)
    (i : Fin (X.length + (1 : ℕ))),
    c ∈ MissingColors G phi (X.vertex i) →
    (↑(HierarchyFirstMissingPosition phi X c) : ℕ) ≤ (↑i : ℕ)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev firstMissingPositionWitnessStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E)
    (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : TreeSequence G e0),
    ∀ c ∈ TreeMissingColors phi X,
    c ∈ MissingColors G phi (X.vertex (HierarchyFirstMissingPosition phi X c))

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev initialSegmentTransitiveStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
    {X Y Z : TreeSequence G e0},
    TreeSequenceInitialSegment X Y →
    TreeSequenceInitialSegment Y Z →
    TreeSequenceInitialSegment X Z

alias initialSegmentTransitive :=
  SharedFacts.ShorteningTransport.trans

/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstMissingPositionUpperBound.{u_1, u_2} :
    firstMissingPositionUpperBoundStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 phi X c i hi
  exact TreeSequenceFirstMissingPositionLe hi


/-- A common proof used by the branches of this transport or construction argument. -/
theorem firstMissingPositionWitness.{u_1, u_2} : firstMissingPositionWitnessStatement.{u_1,
    u_2} := by
  classical
  intro V E _ _ G k e0 phi X c hc
  exact TreeSequenceFirstMissingPositionMemOfMissing hc

end GoldbergSeymour.SharedFacts.SubcaseThreeOnePreparation1

end
