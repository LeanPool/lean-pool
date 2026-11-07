/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Restriction and symmetry of tree interchangeability

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A missing color makes the vertex an endpoint of its two-color component. -/
theorem TwoColorPathComponent.of_missing {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {a b : Fin k}
    (proper : IsProperEdgeColoring G phi) (different : a ≠ b) {v : V}
    (missing : a ∈ MissingColors G phi v) : TwoColorPathComponent G phi a b (Sum.inl v) := by
  classical
  have absent : a ∉ PresentColors G phi v := by simpa [MissingColors] using missing
  have notFirst {f : E} (incident : Incident G v f) : phi f ≠ some a := by
    intro color
    exact absent (by simpa [PresentColors] using
      (show ∃ f, Incident G v f ∧ phi f = some a from ⟨f, incident, color⟩))
  refine ⟨different, Sum.inl v, rfl, ?_⟩
  intro x first y second
  cases x with
  | inl w => exact first.elim
  | inr f =>
    cases y with
    | inl w => exact second.elim
    | inr g =>
      have firstColor := first.2.resolve_left (notFirst first.1)
      have secondColor := second.2.resolve_left (notFirst second.1)
      have equal : f = g := by
        by_contra differentEdges
        exact proper differentEdges ⟨v, first.1, second.1⟩ firstColor secondColor
      exact congrArg Sum.inr equal

/-- Reversing the two selected colors preserves their incidence graph. -/
theorem TwoColorIncidenceGraph.swap {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k) :
    TwoColorIncidenceGraph G phi alpha beta = TwoColorIncidenceGraph G phi beta alpha := by
  ext x y
  cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]

/-- Reversing the selected colors preserves every connected component. -/
theorem TwoColorComponent.swap {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : V ⊕ E) :
    TwoColorComponent G phi alpha beta z = TwoColorComponent G phi beta alpha z := by
  unfold TwoColorComponent
  rw [TwoColorIncidenceGraph.swap G phi alpha beta]

/-- Path components are invariant under reversal of the two colors. -/
theorem TwoColorPathComponent.swap {V E : Type*} (G : LooplessMultigraph V E)
    {k : ℕ} (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (z : V ⊕ E)
    (path : TwoColorPathComponent G phi alpha beta z) :
    TwoColorPathComponent G phi beta alpha z := by
  rcases path with ⟨different, x, member, singleton⟩
  refine ⟨different.symm, x, ?_, ?_⟩
  · exact (congrArg (fun s : Set (V ⊕ E) => x ∈ s)
      (TwoColorComponent.swap G phi alpha beta z)).mp member
  · exact (congrArg (fun graph : SimpleGraph (V ⊕ E) =>
      Set.Subsingleton (graph.neighborSet x))
      (TwoColorIncidenceGraph.swap G phi alpha beta)).mp singleton

/-- Interchangeability is inherited by trees with fewer vertices. -/
theorem TreeInterchangeable.mono {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {firstEdge secondEdge : E} {small : TreeSequence G firstEdge}
    {large : TreeSequence G secondEdge} {phi : PartialEdgeColoring E k} {alpha beta : Fin k}
    (interchange : TreeInterchangeable G large phi alpha beta)
    (subset : TreeSequenceVertexSet small ⊆ TreeSequenceVertexSet large) :
    TreeInterchangeable G small phi alpha beta := by
  intro z w hz hw hzTree hwTree
  apply interchange z w hz hw
  · obtain ⟨v, member, component⟩ := hzTree
    exact ⟨v, subset member, component⟩
  · obtain ⟨v, member, component⟩ := hwTree
    exact ⟨v, subset member, component⟩

/-- Tree interchangeability is symmetric in the two selected colors. -/
theorem TreeInterchangeable.symm {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {e0 : E} {tree : TreeSequence G e0} {phi : PartialEdgeColoring E k}
    {alpha beta : Fin k} (interchange : TreeInterchangeable G tree phi alpha beta) :
    TreeInterchangeable G tree phi beta alpha := by
  intro z w hz hw hzTree hwTree
  have components := TwoColorComponent.swap G phi beta alpha
  have hz' : ∃ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta z := by
    obtain ⟨v, member, component⟩ := hzTree
    exact ⟨v, member, components z ▸ component⟩
  have hw' : ∃ v ∈ TreeSequenceVertexSet tree,
      Sum.inl v ∈ TwoColorComponent G phi alpha beta w := by
    obtain ⟨v, member, component⟩ := hwTree
    exact ⟨v, member, components w ▸ component⟩
  exact (components z).trans
    ((interchange z w (TwoColorPathComponent.swap G phi beta alpha z hz)
      (TwoColorPathComponent.swap G phi beta alpha w hw) hz' hw').trans (components w).symm)

end GoldbergSeymour

end
