/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Bound.Init

/-!
# Shared facts for ScheideDefectiveNoCross

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ScheideDefectiveNoCross

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev treeEdgeIncidentStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E]
        (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0) (q : Fin T.length),
      TreeIncidentEdge T (T.edge q)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem tree_edge_incident.{u_1, u_2} : treeEdgeIncidentStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G e0 T q
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨a, ha⟩ := T.attaches q
  refine ⟨T.vertex q.succ, ?_, ?_⟩
  · simp [TreeSequenceVertexSet]
  · simp [Incident, ha]

end GoldbergSeymour.SharedFacts.ScheideDefectiveNoCross

end
