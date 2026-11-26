/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
public import LeanPool.GraphMinor.Hypergraph.Basic

/-!
# Models of minors, and graphs as hypergraphs

Graph Minors IV, Section 7 (pages 242–243), describes when a graph `G` is isomorphic to a minor of
a graph `G'`: "each edge $e$ of $G$ is represented by an edge $\eta(e)$ of $G'$, and each vertex $v$
of $G$ is “formed” by identifying under contraction a nonempty subset $\eta(v)$ of the vertex set of
$G'$. Moreover, there is a connected subgraph of $G'$ with vertex set $\eta(v)$ all edges of which
are
to be contracted in producing this minor. Thus, in summary:

(i) $\eta$ is a function with domain $V(G) \cup E(G)$; for each $v \in V(G)$, $\eta(v)$ is a
non-empty subset
of $V(G')$ and for each $e \in E(G)$, $\eta(e) \in E(G')$ ...
(ii) $\eta(v_1) \cap \eta(v_2) = \emptyset$ for distinct $v_1, v_2 \in V(G)$, and $\eta(e_1) \neq
\eta(e_2)$ for distinct
$e_1, e_2 \in E(G)$
(iii) for each $v \in V(G)$ and $e \in E(G)$, $e$ is incident with $v$ in $G$ if and only if
$\eta(v)$
contains an end of $\eta(e)$ in $G'$, and $e$ is a loop of $G$ with end $v$ if and only if $\eta(v)$
contains every end of $\eta(e)$ in $G'$
(iv) for each $v \in V(G)$ there is a connected subgraph of $G' \setminus \eta(E(G))$ with vertex
set $\eta(v)$."

`IsMinorModel H G ηv ηe` says that `ηv` (on vertices) and `ηe` (on edges) satisfy (i)–(iv), with
`H` in the role of the paper's `G` and `G` in the role of `G'`. `MinorModelStatement` says that a
model gives a minor; Graph Minors IV uses it to deduce (1.5) from (9.1), and Graph Minors XX uses
it for (10.5).

`Hypergraph.ofGraph` views a finite graph (Mathlib's `Graph`) as a hypergraph whose edges have one
or two ends.
-/

@[expose] public section

namespace GraphMinor

open Graph

variable {α β α' β' : Type*}

/-- The graph `K` is connected: it has a vertex, and any two of its vertices are joined by a walk
of `K`. -/
def GraphConnected (K : Graph α β) : Prop :=
  V(K).Nonempty ∧ ∀ x ∈ V(K), ∀ y ∈ V(K), Relation.ReflTransGen K.Adj x y

/-- `ηv` and `ηe` form a model of `H` in `G`: conditions (i)–(iv) of Graph Minors IV, Section 7,
with `H` in the role of the paper's `G` and `G` in the role of `G'`. -/
structure IsMinorModel (H : Graph α' β') (G : Graph α β) (ηv : α' → Set α) (ηe : β' → β) :
    Prop where
  /-- (i) -/
  vertex_nonempty : ∀ v ∈ V(H), (ηv v).Nonempty
  /-- (i) -/
  vertex_subset : ∀ v ∈ V(H), ηv v ⊆ V(G)
  /-- (i) -/
  edge_mem : ∀ e ∈ E(H), ηe e ∈ E(G)
  /-- (ii) -/
  vertex_disjoint : ∀ v₁ ∈ V(H), ∀ v₂ ∈ V(H), v₁ ≠ v₂ → Disjoint (ηv v₁) (ηv v₂)
  /-- (ii) -/
  edge_injOn : Set.InjOn ηe E(H)
  /-- (iii), first part. -/
  inc_iff : ∀ v ∈ V(H), ∀ e ∈ E(H), H.Inc e v ↔ ∃ x ∈ ηv v, G.Inc (ηe e) x
  /-- (iii), second part. -/
  isLoopAt_iff : ∀ v ∈ V(H), ∀ e ∈ E(H), H.IsLoopAt e v ↔ ∀ x, G.Inc (ηe e) x → x ∈ ηv v
  /-- (iv) -/
  connected : ∀ v ∈ V(H), ∃ K ≤ G.deleteEdges (ηe '' E(H)), V(K) = ηv v ∧ GraphConnected K

/-- A model of `H` in `G` makes `H` isomorphic to a minor of `G`, for finite graphs. -/
def MinorModelStatement : Prop :=
  ∀ {α β α' β' : Type*} (H : Graph α' β') (G : Graph α β), V(H).Finite → E(H).Finite →
    V(G).Finite → E(G).Finite → ∀ (ηv : α' → Set α) (ηe : β' → β), IsMinorModel H G ηv ηe →
      IsIsoMinor H G

/-- A finite graph as a hypergraph: the same vertices and edges, with `v` incident with `e` when
`v` is an end of `e`. -/
def Hypergraph.ofGraph (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    Hypergraph α β where
  vertexSet := V(G)
  edgeSet := E(G)
  Inc := G.Inc
  vertex_mem_of_inc _ _ h := h.vertex_mem
  edge_mem_of_inc _ _ h := h.edge_mem
  vertexSet_finite := hV
  edgeSet_finite := hE

end GraphMinor
