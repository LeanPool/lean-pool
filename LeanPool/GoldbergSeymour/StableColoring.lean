/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.TreeIncidentEdge
public import LeanPool.GoldbergSeymour.TreeMissingColors

/-!
# Stable Coloring

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Preservation of relevant incident-edge colors and every missing-color set on the tree. -/
def StableColoring {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {e0 : E} (T : TreeSequence G e0) (C : Finset (Fin k)) (phi pi : PartialEdgeColoring E k) : Prop :=
 (∀ f, TreeIncidentEdge T f → (∃ c ∈ TreeMissingColors phi T ∪ C, phi f = some c) → pi f = phi f) ∧
  ∀ v ∈ TreeSequenceVertexSet T, MissingColors G pi v = MissingColors G phi v

/-- Preservation of controlled incident-edge colors and missing colors on a finite vertex set. -/
def StableColoringOn {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
    (vertices : Finset V) (colors : Finset (Fin k)) (phi pi : PartialEdgeColoring E k) : Prop :=
  (∀ edge, (∃ vertex ∈ vertices, Incident G vertex edge) →
    (∃ color ∈ (vertices.biUnion fun vertex => MissingColors G phi vertex) ∪ colors,
      phi edge = some color) → pi edge = phi edge) ∧
    ∀ vertex ∈ vertices, MissingColors G pi vertex = MissingColors G phi vertex

namespace StableColoringOn

variable {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
  {smaller larger : Finset V} {smallerColors largerColors : Finset (Fin k)}
  {phi pi : PartialEdgeColoring E k}

/-- Stability restricts to a smaller vertex set when its controlled colors remain controlled. -/
theorem restrict (stable : StableColoringOn (G := G) larger largerColors phi pi)
    (vertices : smaller ⊆ larger)
    (colors : smallerColors ⊆
      (larger.biUnion fun vertex => MissingColors G phi vertex) ∪ largerColors) :
    StableColoringOn (G := G) smaller smallerColors phi pi := by
  classical
  constructor
  · rintro edge ⟨vertex, membership, incident⟩ ⟨color, control, equality⟩
    apply stable.1 edge ⟨vertex, vertices membership, incident⟩
    refine ⟨color, ?_, equality⟩
    rcases Finset.mem_union.mp control with missing | controlled
    · apply Finset.mem_union.mpr
      left
      rcases Finset.mem_biUnion.mp missing with ⟨vertex, membership, missingAt⟩
      exact Finset.mem_biUnion.mpr ⟨vertex, vertices membership, missingAt⟩
    · exact colors controlled
  · intro vertex membership
    exact stable.2 vertex (vertices membership)

/-- Stability is monotone in both the vertex set and the additional controlled colors. -/
theorem mono (stable : StableColoringOn (G := G) larger largerColors phi pi)
    (vertices : smaller ⊆ larger) (colors : smallerColors ⊆ largerColors) :
    StableColoringOn (G := G) smaller smallerColors phi pi :=
  stable.restrict vertices (fun _ membership => Finset.mem_union_right _ (colors membership))

end StableColoringOn

namespace StableColoring

variable {V E : Type*} [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
  {smaller larger : TreeSequence G e0} {smallerColors largerColors : Finset (Fin k)}
  {phi pi : PartialEdgeColoring E k}

/-- Tree stability restricts along vertex-set inclusion and controlled-color containment. -/
theorem restrict (stable : StableColoring larger largerColors phi pi)
    (vertices : TreeSequenceVertexSet smaller ⊆ TreeSequenceVertexSet larger)
    (colors : smallerColors ⊆ TreeMissingColors phi larger ∪ largerColors) :
    StableColoring smaller smallerColors phi pi :=
  StableColoringOn.restrict stable vertices colors

/-- Tree stability is monotone in the vertex set and the additional controlled colors. -/
theorem mono (stable : StableColoring larger largerColors phi pi)
    (vertices : TreeSequenceVertexSet smaller ⊆ TreeSequenceVertexSet larger)
    (colors : smallerColors ⊆ largerColors) : StableColoring smaller smallerColors phi pi :=
  StableColoringOn.mono stable vertices colors

end StableColoring

end GoldbergSeymour

end
