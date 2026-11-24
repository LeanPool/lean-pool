/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section5Connections
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Components containing two marked vertices

In XVI (6.3), pages 59–60, `Y₁` consists of the marked vertices in
components containing at least two marked vertices. Outside these
components, connected hair graphs with different marked near ends are
disjoint. We express the components by walks to avoid choosing names for
the individual components.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
universe u v

/-- The marked vertices in components containing at least two marked
vertices, as in the definition of `Y₁` in XVI (6.3), page 59. -/
def activeMarkedVertices {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α) : Set α :=
  {y | y ∈ Z ∧ ∃ z ∈ Z, z ≠ y ∧ Nonempty (GraphWalk G y z)}

/-- Every active marked vertex is a vertex of the graph. -/
theorem activeMarkedVertices_subset_vertexSet
    {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α) :
    activeMarkedVertices G Z ⊆ V(G) := by
  rintro y ⟨_, z, _, _, ⟨W⟩⟩
  exact W.mem_vertexSet_of_mem_support W.start_mem_support

/-- No component contains exactly one active marked vertex. A walk to
another marked vertex also makes that other vertex active. -/
theorem activeMarkedVertices_component_hyp
    {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α) :
    ∀ y ∈ activeMarkedVertices G Z, ∃ z ∈ activeMarkedVertices G Z,
      z ≠ y ∧ Relation.ReflTransGen G.Adj y z := by
  rintro y ⟨hy, z, hz, hzy, ⟨W⟩⟩
  exact ⟨z, ⟨hz, y, hy, hzy.symm, ⟨W.reverse⟩⟩, hzy, graphWalk_adj_reachable W⟩

/-- Any marked vertex joined to an active marked vertex is active. -/
theorem activeMarkedVertices_of_walk
    {α : Type u} {β : Type v} {G : Graph α β} {Z : Set α} {a b : α}
    (ha : a ∈ activeMarkedVertices G Z) (hb : b ∈ Z) (W : GraphWalk G a b) :
    b ∈ activeMarkedVertices G Z := by
  by_cases hab : a = b
  · exact hab ▸ ha
  · exact ⟨hb, a, ha.1, hab, ⟨W.reverse⟩⟩

/-- Connected subgraphs with different marked near ends are disjoint
if the first near end is outside the active components. Otherwise their
meeting would join the two marked ends. This is the assertion about the
`Q_y` outside `Y₁` in XVI (6.3), page 60. -/
theorem disjoint_connected_hairs_of_not_active
    {α : Type u} {β : Type v} {G P Q : Graph α β} {Z : Set α} {a b : α}
    (hPG : P ≤ G) (hQG : Q ≤ G)
    (hP : IsGraphConnected P) (hQ : IsGraphConnected Q)
    (haP : a ∈ V(P)) (hbQ : b ∈ V(Q))
    (haZ : a ∈ Z) (hbZ : b ∈ Z) (hab : a ≠ b)
    (ha : a ∉ activeMarkedVertices G Z) : Disjoint V(P) V(Q) := by
  apply Set.disjoint_left.mpr
  intro w hwP hwQ
  obtain ⟨W₁⟩ := hP.2 a haP w hwP
  obtain ⟨W₂⟩ := hQ.2 w hwQ b hbQ
  obtain ⟨W₁', _, _⟩ := exists_walk_up_of_le hPG W₁
  obtain ⟨W₂', _, _⟩ := exists_walk_up_of_le hQG W₂
  exact ha ⟨haZ, b, hbZ, hab.symm, ⟨W₁'.append W₂'⟩⟩

end GraphMinor.GM16
