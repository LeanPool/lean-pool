/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeable
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Restriction and symmetry of tree interchangeability

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Missing either selected color leaves at most one neighbor at the vertex. -/
theorem TwoColorIncidenceGraph.neighborSet_subsingleton_of_missing {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {a b : Fin k}
    (proper : IsProperEdgeColoring G phi) {v : V}
    (missing : a ∈ MissingColors G phi v ∨ b ∈ MissingColors G phi v) :
    ((TwoColorIncidenceGraph G phi a b).neighborSet (Sum.inl v)).Subsingleton := by
  classical
  have absent {c : Fin k} (missing : c ∈ MissingColors G phi v) {f : E}
      (incident : Incident G v f) : phi f ≠ some c := by
    intro color
    exact (Finset.mem_sdiff.mp missing).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, incident, color⟩)
  intro x first y second
  cases x with
  | inl w => exact first.elim
  | inr f =>
    cases y with
    | inl w => exact second.elim
    | inr g =>
      apply congrArg Sum.inr
      by_contra differentEdges
      rcases missing with missing | missing
      · exact proper differentEdges ⟨v, first.1, second.1⟩
          (first.2.resolve_left (absent missing first.1))
          (second.2.resolve_left (absent missing second.1))
      · exact proper differentEdges ⟨v, first.1, second.1⟩
          (first.2.resolve_right (absent missing first.1))
          (second.2.resolve_right (absent missing second.1))

/-- A missing color makes the vertex an endpoint of its two-color component. -/
theorem TwoColorPathComponent.of_missing {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {a b : Fin k}
    (proper : IsProperEdgeColoring G phi) (different : a ≠ b) {v : V}
    (missing : a ∈ MissingColors G phi v) : TwoColorPathComponent G phi a b (Sum.inl v) := by
  exact ⟨different, Sum.inl v, rfl,
    TwoColorIncidenceGraph.neighborSet_subsingleton_of_missing proper (Or.inl missing)⟩


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
