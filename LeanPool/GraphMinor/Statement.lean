/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps

/-!
# The graph minor theorem: the statement

This file defines the relation "is isomorphic to a minor of" that appears in the graph minor
theorem. Robertson and Seymour state the theorem as a conjecture of Wagner in

> N. Robertson and P. D. Seymour, *Graph Minors. IV. Tree-width and well-quasi-ordering*,
> J. Combin. Theory Ser. B **48** (1990), 227–254,

> **(1.1) Conjecture.** If `G₁, G₂, …` is any countable sequence of graphs then there exist
> `j > i ≥ 1` such that `Gᵢ` is isomorphic to a minor of `Gⱼ`.

and they prove it in

> N. Robertson and P. D. Seymour, *Graph Minors. XX. Wagner's conjecture*, J. Combin. Theory
> Ser. B **92** (2004), 325–357.

The definitions follow Section 1 of Graph Minors IV (page 227): "By a 'graph' we shall mean ... a
finite, undirected graph which may have loops and multiple edges. A graph is a *minor* of another
if the first can be obtained from a subgraph of the second by edge-contraction."

* A graph is Mathlib's multigraph `Graph α β`, with vertex set `V(G) : Set α` and edge set
  `E(G) : Set β`. Each edge has one or two ends, so loops and multiple edges are allowed. The
  theorem assumes that `V(G)` and `E(G)` are finite.
* A subgraph is Mathlib's subgraph order `G' ≤ G`: `V(G') ⊆ V(G)`, and each edge of `G'` is an edge
  of `G` with the same ends.
* `GraphMinor.contract G C` is the graph obtained from `G` by contracting the edges in `C`. Its
  vertices are the vertex sets of the components of the graph with vertex set `V(G)` and edge set
  `C`. Its edges are the edges of `G` not in `C`, each with the components of its ends as ends.
  Contracting the edges of `C` one at a time gives the same graph, up to isomorphism.
* `GraphMinor.Iso H G` is an isomorphism: a bijection between the vertex sets and a bijection
  between the edge sets that preserve the ends of every edge.
* `GraphMinor.IsIsoMinor H G` says that `H` is isomorphic to a minor of `G`: there are a subgraph
  `G'` of `G` and a set `C` of edges of `G'` with `H` isomorphic to `contract G' C`.

The theorem is available as `GraphMinor.graph_minor_theorem` from `LeanPool.GraphMinor`.
-/

@[expose] public section

namespace GraphMinor

open Graph

variable {α β α' β' : Type*}

/-- The graph obtained from `G` by contracting the edges in `C`.

A vertex `v` of `G` becomes the set of vertices that `v` can reach in `G` along edges in `C`, that
is, the vertex set of the component containing `v` of the graph with vertex set `V(G)` and edge set
`C`. The edges are those of `G` that are not in `C`. An edge of `G` with ends `x` and `y` gets the
components of `x` and `y` as ends, so it becomes a loop if `x` and `y` are in the same component.
-/
def contract (G : Graph α β) (C : Set β) : Graph (Set α) β :=
  (G.map fun v ↦ {w | Relation.ReflTransGen (fun x y ↦ ∃ e ∈ C, G.IsLink e x y) v w}).deleteEdges C

/-- An isomorphism from `H` to `G`: a bijection between the vertex sets and a bijection between
the edge sets such that an edge `e` of `H` has ends `x` and `y` exactly when the edge of `G` that
corresponds to `e` has as ends the vertices that correspond to `x` and `y`. -/
structure Iso (H : Graph α' β') (G : Graph α β) where
  /-- The bijection between the vertex sets. -/
  vertexEquiv : V(H) ≃ V(G)
  /-- The bijection between the edge sets. -/
  edgeEquiv : E(H) ≃ E(G)
  /-- The bijections preserve the ends of every edge. -/
  isLink_iff (e : E(H)) (x y : V(H)) :
    H.IsLink e x y ↔ G.IsLink (edgeEquiv e) (vertexEquiv x) (vertexEquiv y)

/-- `H` is isomorphic to a minor of `G`: there are a subgraph `G'` of `G` and a set `C` of edges of
`G'` such that `H` is isomorphic to the graph obtained from `G'` by contracting the edges in `C`. -/
def IsIsoMinor (H : Graph α' β') (G : Graph α β) : Prop :=
  ∃ G' ≤ G, ∃ C ⊆ E(G'), Nonempty (Iso H (contract G' C))

end GraphMinor
