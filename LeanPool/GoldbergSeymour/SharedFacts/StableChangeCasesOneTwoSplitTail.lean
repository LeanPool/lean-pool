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
# Shared facts for StableChangeCasesOneTwoSplitTail

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.StableChangeCasesOneTwoSplitTail

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev equalTreesStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {S U : TreeSequence G e0},
      TreeSequenceInitialSegment S U →
      S.length = U.length →
      S = U

/-- A common proof used by the branches of this transport or construction argument. -/
theorem equalTrees.{u_1, u_2} : equalTreesStatement.{u_1, u_2} := by
  classical
  intro V E G e0 S U hSU hlen
  cases S with
  | mk ls ps vs es vis eis fs aas =>
    cases U with
    | mk lu pu vu eu viu eiu fu aau =>
      simp only at hlen
      subst lu
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.1 i).symm
      · apply heq_of_eq
        funext i
        simpa only [Fin.castLE] using (hSU.2.2 i).symm

end GoldbergSeymour.SharedFacts.StableChangeCasesOneTwoSplitTail

end
