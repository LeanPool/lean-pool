/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Bound.Init

/-!
# Shared facts for ExtensionBaseStepLemmas

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ExtensionBaseStepLemmas

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev uPrimeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (TjPrime : TreeSequence
          G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤
          (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
      let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
          huPositionBound; TreeSequenceInitialSegment U TjPrime

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev prefixSelfStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
    (A : TreeSequence G e0),
    TreeSequencePrefix A A.length A.positive le_rfl = A

/-- A common proof used by the branches of this transport or construction argument. -/
theorem uPrime.{u_1, u_2} : uPrimeStatement.{u_1, u_2} := by
  classical
  intro V E G e0 TjPrime uPosition huPositionPositive huPositionBound U
  refine ⟨huPositionBound, ?_, ?_⟩
  · intro i
    simp [U, TreeSequencePrefix]
  · intro i
    simp [U, TreeSequencePrefix]

/-- A common proof used by the branches of this transport or construction argument. -/
theorem prefixSelf.{u_1, u_2} : prefixSelfStatement.{u_1, u_2} := by
  classical
  intro V E G e0 A
  cases A with
  | mk len pos vertex edge vinj einj first attach =>
    rw [TreeSequence.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · apply heq_of_eq
      funext i
      rfl
    · apply heq_of_eq
      funext i
      rfl

end GoldbergSeymour.SharedFacts.ExtensionBaseStepLemmas

end
