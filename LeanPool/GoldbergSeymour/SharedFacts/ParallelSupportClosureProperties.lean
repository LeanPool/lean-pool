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
# Shared facts for ParallelSupportClosureProperties

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ParallelSupportClosureProperties

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev comparableInitialSegmentsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B
          C → A.length ≤ B.length → TreeSequenceInitialSegment A B

/-- A common proof used by the branches of this transport or construction argument. -/
theorem comparableInitialSegments.{u_1, u_2} : comparableInitialSegmentsStatement.{u_1, u_2} := by
  classical
  intro V E G e0 A B C hAC hBC hlen
  rcases hAC with ⟨hACLen, hACVertices, hACEdges⟩
  rcases hBC with ⟨hBCLen, hBCVertices, hBCEdges⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    calc
      B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
          C.vertex (Fin.castLE (Nat.succ_le_succ hBCLen)
            (Fin.castLE (Nat.succ_le_succ hlen) i)) :=
        (hBCVertices _).symm
      _ = C.vertex (Fin.castLE (Nat.succ_le_succ hACLen) i) := by
        congr 1
      _ = A.vertex i := hACVertices i
  · intro i
    calc
      B.edge (Fin.castLE hlen i) =
          C.edge (Fin.castLE hBCLen (Fin.castLE hlen i)) :=
        (hBCEdges _).symm
      _ = C.edge (Fin.castLE hACLen i) := by congr 1
      _ = A.edge i := hACEdges i

end GoldbergSeymour.SharedFacts.ParallelSupportClosureProperties

end
