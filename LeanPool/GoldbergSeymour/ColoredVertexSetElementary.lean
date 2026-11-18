/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors

/-!
# Colored Vertex Set Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Distinct vertices of the set have disjoint sets of missing colors. -/
def ColoredVertexSetElementary {V E : Type*} [Fintype E] (G : LooplessMultigraph V E)
  {k : ℕ} (phi : PartialEdgeColoring E k) (X : Finset V) : Prop :=
 ∀ {u}, u ∈ X → ∀ {v}, v ∈ X → u ≠ v → Disjoint (MissingColors G phi u) (MissingColors G phi v)

/-- Elementarity is inherited by subsets of the vertex set. -/
theorem ColoredVertexSetElementary.mono {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {X Y : Finset V}
    (elementary : ColoredVertexSetElementary G phi Y) (subset : X ⊆ Y) :
    ColoredVertexSetElementary G phi X :=
  fun {_} hu {_} hv different => elementary (subset hu) (subset hv) different

/-- A color missing at one vertex of an elementary set is present at every other vertex. -/
theorem ColoredVertexSetElementary.presentColor_of_missing {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {X : Finset V}
    (elementary : ColoredVertexSetElementary G phi X) {u v : V} {c : Fin k}
    (root : u ∈ X) (missing : c ∈ MissingColors G phi u)
    (inside : v ∈ X) (different : v ≠ u) : c ∈ PresentColors G phi v := by
  classical
  have absent : c ∉ MissingColors G phi v := by
    intro shared
    exact Finset.disjoint_left.mp (elementary inside root different) shared missing
  simpa [MissingColors] using absent

/-- A missing color at an outside vertex of an elementary set is absent from an inside subset. -/
theorem ColoredVertexSetElementary.missing_not_mem_biUnion {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {X Y : Finset V}
    (elementary : ColoredVertexSetElementary G phi Y) (subset : X ⊆ Y)
    {v : V} (member : v ∈ Y) (outside : v ∉ X) {c : Fin k}
    (missing : c ∈ MissingColors G phi v) : c ∉ X.biUnion (MissingColors G phi) := by
  classical
  intro shared
  obtain ⟨u, inside, color⟩ := Finset.mem_biUnion.mp shared
  have different : u ≠ v := by intro equal; exact outside (equal ▸ inside)
  exact (Finset.disjoint_left.mp (elementary (subset inside) member different)) color missing

end GoldbergSeymour

end
