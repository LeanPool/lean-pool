/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Hypergraphs, separations and rooted hypergraphs

This file gives the basic definitions of Graph Minors IV, Section 3 (page 233), which Graph Minors
XVIII and XX repeat:

> A hypergraph `G` consists of a finite set `V(G)` of vertices, a finite set `E(G)` of edges with
> `E(G) ∩ V(G) = ∅`, and an incidence relation, a subset of `V(G) × E(G)`. The vertices incident
> with an edge `e` are its *ends*, and the set of ends of `e` in `G` is denoted by `V(e)`. If `G`,
> `G'` are hypergraphs and `V(G') ⊆ V(G)` and `E(G') ⊆ E(G)`, and `V_G(e) = V_{G'}(e)` for every
> `e ∈ E(G')`, then we call `G'` a *subhypergraph* of `G` and write `G' ⊆ G`. If `G₁, G₂ ⊆ G` we
> define `G₁ ∩ G₂`, `G₁ ∪ G₂` in the natural way. A *separation* of `G` is a pair `(G₁, G₂)` of
> subhypergraphs of `G` with `G₁ ∪ G₂ = G` and `E(G₁ ∩ G₂) = ∅`; its *order* is
> `|V(G₁ ∩ G₂)|`.
>
> A march in a set `V` is a finite sequence of distinct elements of `V`. ... A *rooted
> hypergraph* `G = (G⁻, π(G))` consists of a hypergraph `G⁻` and a march `π(G)` in `V(G⁻)`. ...
> A separation of a rooted hypergraph `G` is a pair `(G₁, G₂)` of rooted hypergraphs such that
> `(G₁⁻, G₂⁻)` is a separation of `G⁻`, and `π(G₂) = π(G)`, and `πBar(G₁) = V(G₁⁻ ∩ G₂⁻)`.

Vertices lie in a type `α` and edges in a type `β`, so the condition `E(G) ∩ V(G) = ∅` is
automatic. A march is a `List` without duplicates.

It also defines paths, which the papers use in Menger's theorem: a hypergraph `G` has the simple
graph `G.skeleton` on its vertices, in which two distinct vertices are adjacent when some edge is
incident with both (the *1-skeleton* of Graph Minors XX, Section 10, and the graph `K` in the proof
of Graph Minors IV, (6.1)). For a graph, the paths of `G` and of `G.skeleton` have the same vertex
sequences, so disjoint paths of `G` are disjoint paths of `G.skeleton`. `MengerStatement` is
Menger's theorem in the form that Graph Minors IV uses in the proof of (6.1).
-/

@[expose] public section

namespace GraphMinor

variable {α β : Type*}

/-- A hypergraph (Graph Minors IV, Section 3): a finite set of vertices, a finite set of edges, and
an incidence relation between them. `G.Inc e v` says that the vertex `v` is an end of the edge `e`.
An edge may have any number of ends. -/
@[ext]
structure Hypergraph (α β : Type*) where
  /-- The vertex set `V(G)`. -/
  vertexSet : Set α
  /-- The edge set `E(G)`. -/
  edgeSet : Set β
  /-- The incidence relation: `Inc e v` when `v` is an end of `e`. -/
  Inc : β → α → Prop
  /-- Incidence is a relation between vertices of `G` and edges of `G`. -/
  vertex_mem_of_inc : ∀ ⦃e : β⦄ ⦃v : α⦄, Inc e v → v ∈ vertexSet
  /-- Incidence is a relation between vertices of `G` and edges of `G`. -/
  edge_mem_of_inc : ∀ ⦃e : β⦄ ⦃v : α⦄, Inc e v → e ∈ edgeSet
  /-- The vertex set is finite. -/
  vertexSet_finite : vertexSet.Finite
  /-- The edge set is finite. -/
  edgeSet_finite : edgeSet.Finite

namespace Hypergraph

/-- `V(e)`, the set of ends of the edge `e`. -/
def ends (G : Hypergraph α β) (e : β) : Set α := {v | G.Inc e v}

/-- `H ⊆ G`: `H` is a subhypergraph of `G`. That is, `V(H) ⊆ V(G)`, `E(H) ⊆ E(G)`, and every edge of
`H` has the same ends in `H` as in `G`. -/
structure IsSubhypergraph (H G : Hypergraph α β) : Prop where
  vertexSet_subset : H.vertexSet ⊆ G.vertexSet
  edgeSet_subset : H.edgeSet ⊆ G.edgeSet
  ends_eq : ∀ e ∈ H.edgeSet, G.ends e = H.ends e

/-- Subhypergraphs, written `H ≤ G` (the paper writes `H ⊆ G`). -/
instance : PartialOrder (Hypergraph α β) where
  le H G := IsSubhypergraph H G
  le_refl G := ⟨subset_rfl, subset_rfl, fun _ _ ↦ rfl⟩
  le_trans G₁ G₂ G₃ h₁₂ h₂₃ :=
    ⟨h₁₂.vertexSet_subset.trans h₂₃.vertexSet_subset,
      h₁₂.edgeSet_subset.trans h₂₃.edgeSet_subset,
      fun e he ↦ (h₂₃.ends_eq e (h₁₂.edgeSet_subset he)).trans (h₁₂.ends_eq e he)⟩
  le_antisymm G H hGH hHG := by
    have hE : G.edgeSet = H.edgeSet := hGH.edgeSet_subset.antisymm hHG.edgeSet_subset
    refine Hypergraph.ext (hGH.vertexSet_subset.antisymm hHG.vertexSet_subset) hE ?_
    funext e v
    apply propext
    by_cases he : e ∈ G.edgeSet
    · have h := congrArg (v ∈ ·) (hGH.ends_eq e he)
      exact h.to_iff.symm
    · constructor
      · intro h
        exact absurd (G.edge_mem_of_inc h) he
      · intro h
        exact absurd (hE ▸ H.edge_mem_of_inc h) he

/-- The union `G₁ ∪ G₂`. For subhypergraphs `G₁, G₂` of a hypergraph `G` it is the subhypergraph of
`G` with vertex set `V(G₁) ∪ V(G₂)` and edge set `E(G₁) ∪ E(G₂)`. -/
instance : Union (Hypergraph α β) where
  union G₁ G₂ :=
    { vertexSet := G₁.vertexSet ∪ G₂.vertexSet
      edgeSet := G₁.edgeSet ∪ G₂.edgeSet
      Inc := fun e v ↦ G₁.Inc e v ∨ G₂.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦
        h.elim (fun h ↦ Or.inl (G₁.vertex_mem_of_inc h)) (fun h ↦ Or.inr (G₂.vertex_mem_of_inc h))
      edge_mem_of_inc := fun _ _ h ↦
        h.elim (fun h ↦ Or.inl (G₁.edge_mem_of_inc h)) (fun h ↦ Or.inr (G₂.edge_mem_of_inc h))
      vertexSet_finite := G₁.vertexSet_finite.union G₂.vertexSet_finite
      edgeSet_finite := G₁.edgeSet_finite.union G₂.edgeSet_finite }

/-- The intersection `G₁ ∩ G₂`. For subhypergraphs `G₁, G₂` of a hypergraph `G` it is the
subhypergraph of `G` with vertex set `V(G₁) ∩ V(G₂)` and edge set `E(G₁) ∩ E(G₂)`. -/
instance : Inter (Hypergraph α β) where
  inter G₁ G₂ :=
    { vertexSet := G₁.vertexSet ∩ G₂.vertexSet
      edgeSet := G₁.edgeSet ∩ G₂.edgeSet
      Inc := fun e v ↦ G₁.Inc e v ∧ G₂.Inc e v
      vertex_mem_of_inc := fun _ _ h ↦ ⟨G₁.vertex_mem_of_inc h.1, G₂.vertex_mem_of_inc h.2⟩
      edge_mem_of_inc := fun _ _ h ↦ ⟨G₁.edge_mem_of_inc h.1, G₂.edge_mem_of_inc h.2⟩
      vertexSet_finite := G₁.vertexSet_finite.subset Set.inter_subset_left
      edgeSet_finite := G₁.edgeSet_finite.subset Set.inter_subset_left }

theorem union_vertexSet_eq (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).vertexSet = G₁.vertexSet ∪ G₂.vertexSet := rfl

theorem union_edgeSet_eq (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := rfl

theorem union_inc_iff (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∪ G₂).Inc e v ↔ G₁.Inc e v ∨ G₂.Inc e v := Iff.rfl

theorem inter_vertexSet_eq (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).vertexSet = G₁.vertexSet ∩ G₂.vertexSet := rfl

theorem inter_edgeSet_eq (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := rfl

theorem inter_inc_iff (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∩ G₂).Inc e v ↔ G₁.Inc e v ∧ G₂.Inc e v := Iff.rfl

/-- The union `⋃ (G i : i ∈ s)` of finitely many hypergraphs. For subhypergraphs of a hypergraph
`G` it is the subhypergraph of `G` whose vertices and edges are those of the `G i`. -/
def biUnion {ι : Type*} (s : Finset ι) (G : ι → Hypergraph α β) : Hypergraph α β where
  vertexSet := ⋃ i ∈ s, (G i).vertexSet
  edgeSet := ⋃ i ∈ s, (G i).edgeSet
  Inc e v := ∃ i ∈ s, (G i).Inc e v
  vertex_mem_of_inc _ _ h := by
    obtain ⟨i, hi, h⟩ := h
    exact Set.mem_biUnion hi ((G i).vertex_mem_of_inc h)
  edge_mem_of_inc _ _ h := by
    obtain ⟨i, hi, h⟩ := h
    exact Set.mem_biUnion hi ((G i).edge_mem_of_inc h)
  vertexSet_finite := Set.Finite.biUnion s.finite_toSet fun i _ ↦ (G i).vertexSet_finite
  edgeSet_finite := Set.Finite.biUnion s.finite_toSet fun i _ ↦ (G i).edgeSet_finite

/-- `G \ F`: the subhypergraph of `G` with the same vertex set and edge set `E(G) - F`. -/
def deleteEdges (G : Hypergraph α β) (F : Set β) : Hypergraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ F
  Inc e v := G.Inc e v ∧ e ∉ F
  vertex_mem_of_inc _ _ h := G.vertex_mem_of_inc h.1
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.subset Set.sdiff_subset

/-- `G` is a graph: every edge has one or two ends. -/
def IsGraph (G : Hypergraph α β) : Prop :=
  ∀ e ∈ G.edgeSet, (G.ends e).Nonempty ∧ (G.ends e).ncard ≤ 2

/-- `(G₁, G₂)` is a separation of `G`: `G₁` and `G₂` are subhypergraphs of `G`, `G₁ ∪ G₂ = G`, and
`E(G₁ ∩ G₂) = ∅`. -/
structure IsSeparation (G G₁ G₂ : Hypergraph α β) : Prop where
  left_le : G₁ ≤ G
  right_le : G₂ ≤ G
  union_eq : G₁ ∪ G₂ = G
  edgeSet_inter_eq : (G₁ ∩ G₂).edgeSet = ∅

/-- The order `|V(G₁ ∩ G₂)|` of a separation `(G₁, G₂)`. -/
noncomputable def separationOrder (G₁ G₂ : Hypergraph α β) : ℕ := (G₁ ∩ G₂).vertexSet.ncard

/-- The 1-skeleton of `G`: the simple graph on `α` in which distinct vertices are adjacent when
some edge of `G` is incident with both. Its edges join vertices of `G` only. -/
def skeleton (G : Hypergraph α β) : SimpleGraph α where
  Adj x y := x ≠ y ∧ ∃ e, G.Inc e x ∧ G.Inc e y
  symm := ⟨fun _ _ ⟨hxy, e, hx, hy⟩ ↦ ⟨hxy.symm, e, hy, hx⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A skeleton walk with initial vertex in the hypergraph stays in its vertex set. -/
theorem skeleton_walk_support_subset_vertexSet {G : Hypergraph α β} {u v : α}
    (w : G.skeleton.Walk u v) (hu : u ∈ G.vertexSet) :
    ∀ z ∈ w.support, z ∈ G.vertexSet := by
  induction w with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
    exact hz ▸ hu
  | @cons u u' v hadj rest ih =>
    obtain ⟨_, e, _, heu'⟩ := id hadj
    have hu' : u' ∈ G.vertexSet := G.vertex_mem_of_inc heu'
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih hu' z hz

/-- The vertices incident with edges on both sides of an edge subset. -/
abbrev edgeBoundary (G : Hypergraph α β) (X : Set β) : Set α :=
  {v ∈ G.vertexSet | (∃ e ∈ X, G.Inc e v) ∧ (∃ e ∈ G.edgeSet \ X, G.Inc e v)}

end Hypergraph

/-- A path of the simple graph `K` from `X` to `Y`: a path of `K` whose first vertex is in `X` and
whose last vertex is in `Y`. It may have a single vertex, in `X ∩ Y`. -/
structure PathFromTo (K : SimpleGraph α) (X Y : Set α) where
  /-- The first vertex. -/
  first : α
  /-- The last vertex. -/
  last : α
  /-- The path. -/
  walk : K.Walk first last
  isPath : walk.IsPath
  first_mem : first ∈ X
  last_mem : last ∈ Y

/-- There are `k` mutually vertex-disjoint paths of `K` from `X` to `Y`. -/
def HasDisjointPaths (K : SimpleGraph α) (X Y : Set α) (k : ℕ) : Prop :=
  ∃ P : Fin k → PathFromTo K X Y,
    Pairwise fun i j ↦ Disjoint {x | x ∈ (P i).walk.support} {x | x ∈ (P j).walk.support}

/-- **Menger's theorem**, in the form used in the proof of Graph Minors IV, (6.1): for sets `X, Y`
of vertices of a hypergraph `G` and `k ≥ 0`, every separation `(G₁, G₂)` of `G` with `X ⊆ V(G₁)`
and `Y ⊆ V(G₂)` has order at least `k` if and only if there are `k` mutually vertex-disjoint paths
of the 1-skeleton of `G` from `X` to `Y`. -/
def MengerStatement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β) (X Y : Set α), X ⊆ G.vertexSet → Y ⊆ G.vertexSet →
    ∀ k : ℕ,
      (∀ G₁ G₂ : Hypergraph α β, G.IsSeparation G₁ G₂ → X ⊆ G₁.vertexSet → Y ⊆ G₂.vertexSet →
          k ≤ Hypergraph.separationOrder G₁ G₂) ↔
        HasDisjointPaths G.skeleton X Y k

/-- A rooted hypergraph `G = (G⁻, π(G))` (Graph Minors IV, Section 3): a hypergraph `G⁻`, here
`G.toHypergraph`, and a march `π(G)` in `V(G⁻)`, here `G.roots`, a list of distinct vertices.
`V(G) = V(G⁻)` and `E(G) = E(G⁻)`. -/
structure RootedHypergraph (α β : Type*) extends Hypergraph α β where
  /-- The march `π(G)`. -/
  roots : List α
  roots_nodup : roots.Nodup
  roots_subset : ∀ v ∈ roots, v ∈ vertexSet

namespace RootedHypergraph

/-- `πBar(G)`, the set of terms of the march `π(G)`. -/
def rootSet (G : RootedHypergraph α β) : Set α := {v | v ∈ G.roots}

/-- `(G₁, G₂)` is a separation of the rooted hypergraph `G`: `(G₁⁻, G₂⁻)` is a separation of `G⁻`,
`π(G₂) = π(G)` and `πBar(G₁) = V(G₁⁻ ∩ G₂⁻)`. Its order is
`Hypergraph.separationOrder G₁.toHypergraph G₂.toHypergraph`. -/
structure IsSeparation (G G₁ G₂ : RootedHypergraph α β) : Prop where
  isSeparation : G.toHypergraph.IsSeparation G₁.toHypergraph G₂.toHypergraph
  roots_right : G₂.roots = G.roots
  rootSet_left : G₁.rootSet = (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet

end RootedHypergraph

/-- The rooted hypergraph `(G, 0)`, where `0` is the null march. -/
def Hypergraph.toRooted (G : Hypergraph α β) : RootedHypergraph α β where
  toHypergraph := G
  roots := []
  roots_nodup := List.nodup_nil
  roots_subset _ h := absurd h List.not_mem_nil

end GraphMinor
