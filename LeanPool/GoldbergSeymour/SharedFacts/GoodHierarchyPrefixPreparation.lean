/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
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
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hab, hvab, heab⟩
  rcases hBC with ⟨hbc, hvbc, hebc⟩
  refine ⟨le_trans hab hbc, ?_, ?_⟩
  · intro i
    have hmid := hvbc (Fin.castLE (Nat.succ_le_succ hab) i)
    simpa using hmid.trans (hvab i)
  · intro i
    have hmid := hebc (Fin.castLE hab i)
    simpa using hmid.trans (heab i)

end GoldbergSeymour.SharedFacts.GoodHierarchyPrefixPreparation

end
