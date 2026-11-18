/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeColorSetClosed
public import LeanPool.GoldbergSeymour.TreeExitPath

/-!
# Closed Color Exit Path Boundary Edge

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

/-- With the first color closed, the actual last boundary edge has the other color. -/
theorem TreeExitPath.closedLastBoundaryEdge {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {T : TreeSequence G e0} {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {u v : V}
    {P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)}
    (exit : TreeExitPath T phi alpha beta u v P)
    (closed : TreeColorSetClosed G phi T {alpha}) :
    ∃ edge : E, P.getVert (P.length - 1) = Sum.inr edge ∧
      edge ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta ∧
      Incident G v edge ∧ Sum.inr edge ∈ P.support := by
  classical
  obtain ⟨edge, other, last, member, incident, _, _, boundary, colors⟩ := exit.lastBoundaryEdge
  have color : phi edge = some beta := by
    rcases colors with first | second
    · have forbidden : edge ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha := by
        simp [BoundaryColorEdges, boundary, first]
      rw [closed alpha (by simp)] at forbidden
      exact (Finset.notMem_empty edge forbidden).elim
    · exact second
  exact ⟨edge, last, by simp [BoundaryColorEdges, boundary, color], incident, member⟩

/-- A first entry into a tree closed in the first color ends on a boundary edge of the other
color. -/
theorem TreeExitPath.firstEntryClosed {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {u v : V}
    (P : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v))
    (path : P.IsPath)
    (missing : alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u)
    (outside : u ∉ TreeSequenceVertexSet T)
    (meets : ∃ x ∈ TreeSequenceVertexSet T, Sum.inl x ∈ P.support)
    (closed : TreeColorSetClosed G phi T {alpha}) :
    ∃ (c : V) (_ : c ∈ TreeSequenceVertexSet T) (member : Sum.inl c ∈ P.support),
      let Q := P.takeUntil (Sum.inl c) member
      TreeExitPath T phi alpha beta u c Q ∧
      ∃ edge : E, Q.getVert (Q.length - 1) = Sum.inr edge ∧ Incident G c edge ∧
        edge ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi edge = some beta := by
  obtain ⟨c, inside, member, exit⟩ := TreeExitPath.firstEntry T P path missing outside meets
  obtain ⟨edge, last, boundary, incident, _⟩ := exit.closedLastBoundaryEdge closed
  have data : edge ∈ BoundaryEdges G (TreeSequenceVertexSet T) ∧ phi edge = some beta := by
    simpa only [BoundaryColorEdges, Finset.mem_filter] using boundary
  exact ⟨c, inside, member, exit, edge, last, incident, data.1, data.2⟩

lemma ClosedColorExitPathBoundaryEdge {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} {e0 : E}
    (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
    (a b : Fin k)
    (hclosed : TreeColorSetClosed G phi T {a})
    (u v : V)
    (P : (TwoColorIncidenceGraph G phi a b).Walk
      (Sum.inl u) (Sum.inl v))
    (hP : TreeExitPath T phi a b u v P) :
    ∃ f : E,
      f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) b ∧
      Incident G v f ∧ Sum.inr f ∈ P.support := by
  obtain ⟨edge, _, boundary, incident, member⟩ := hP.closedLastBoundaryEdge hclosed
  exact ⟨edge, boundary, incident, member⟩

end GoldbergSeymour

end
