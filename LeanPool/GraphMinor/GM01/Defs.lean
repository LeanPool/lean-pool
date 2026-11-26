/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Set.Card

/-!
# Definitions for Graph Minors I, Section 2 (Grids)

This file gives the definitions used in Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. I. Excluding a forest*,
J. Combin. Theory Ser. B **35** (1983), 39–61 (pages 41–50).

## Representation

A finite graph in Section 2 is represented as a subgraph `G : (⊤ : SimpleGraph α).Subgraph` with
`G.verts.Finite`. All results (2.1)–(2.9) of Section 2 concern grid minors, paths, connected
subgraphs, connected components, and vertex separators, which depend only on the underlying simple
graph; representing subgraphs of `G` (paths, stars, and the `Bⱼ`) as `H ≤ G` retains their edge sets
so that the proofs can delete and contract edges as in the paper.

* `toGraph G`: the Mathlib multigraph `Graph α (Sym2 α)` with vertex set `G.verts` and edge set
  `G.edgeSet`.
* `gridGraph θ`: the `θ`-grid `Graph.ofSimpleGraph (pathGraph θ □ pathGraph θ)`, whose vertex
  `(i, j)` corresponds to the paper's `v_{i+1, j+1}`.
* `𝓕 θ` (with notation `𝓕_θ`): the set of graphs `G` with no minor isomorphic to `gridGraph θ`.
* `Path α`: a path in `α`, given by its initial vertex `first`, its terminal vertex `last`, and a
  walk `walk : (⊤ : SimpleGraph α).Walk first last` with `walk.IsPath`. Its subgraph is
  `P.toSubgraph`, its vertex set is `P.verts`, its ends are `P.ends = {P.first, P.last}`, and its
  internal vertices are `P.internalVerts = P.verts \ P.ends`.
* `Path.Precedes`: the order of vertices along a path.
* `Path.IsIn`, `Path.IsFromTo`, `Path.Avoids`, `Separates`: paths in `G`, paths from `A₁` to `A₂`,
  paths avoiding `X`, and vertex sets `X` separating `Y` and `Z` in `G`.
* `IsDisjointPathFamily`: families of disjoint paths from `A₁` to `A₂`.
* `IsStarWithCenter`, `IsStar`, `IsTreeSubgraph`, `IsLeafOf`, `numComponents`: stars, trees,
  end-vertices, and the number of connected components of a subgraph.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

variable {α : Type*}

/-- The Mathlib `Graph α (Sym2 α)` underlying a subgraph `G : (⊤ : SimpleGraph α).Subgraph`, with
vertex set `G.verts` and edge set `G.edgeSet`. -/
def toGraph (G : (⊤ : SimpleGraph α).Subgraph) : Graph α (Sym2 α) where
  vertexSet := G.verts
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ G.Adj x y
  isLink_symm _ _ := ⟨fun _ _ ↦ by simp [Sym2.eq_swap, G.adj_comm]⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ he hf := by grind
  edge_mem_iff_exists_isLink e := by
    induction e with
    | h u v =>
      simp only [Subgraph.mem_edgeSet]
      exact ⟨fun h ↦ ⟨u, v, rfl, h⟩, fun ⟨x, y, heq, hadj⟩ ↦ by
        rw [G.adj_congr_of_sym2 heq]
        exact hadj⟩
  left_mem_of_isLink _ _ _ h := h.2.fst_mem

/-- The `θ`-grid (Graph Minors I, Section 2, page 42): "If $\theta \ge 2$, the $\theta$-grid is the
simple graph with vertices $v_{ij}$ ($1 \le i, j \le \theta$) in which $v_{ij}$ and $v_{i'j'}$ are
adjacent if $|i - i'| + |j - j'| = 1$." Here vertex `(i, j)` in `Fin θ × Fin θ` is the paper's
`v_{i+1, j+1}`. -/
def gridGraph (θ : ℕ) : Graph (Fin θ × Fin θ) (Sym2 (Fin θ × Fin θ)) :=
  Graph.ofSimpleGraph (pathGraph θ □ pathGraph θ)

/-- `𝓕_θ` denotes the set of all graphs with no minor isomorphic to the `θ`-grid
(Graph Minors I, Section 2, page 42). -/
def 𝓕 (θ : ℕ) : Set (⊤ : SimpleGraph α).Subgraph :=
  {G | ¬ IsIsoMinor (gridGraph θ) (toGraph G)}

/-- Notation `𝓕_θ` for `𝓕 θ`, the set of graphs with no minor isomorphic to the `θ`-grid. -/
scoped notation "𝓕_" θ:max => 𝓕 θ

/-- A path (Graph Minors I, Section 1, page 41): "Every *path* has at least one vertex, and no
... vertices. It has an *initial* and a *terminal* vertex (which are equal for a one-vertex
path) called its *ends*, and any other vertices are called *internal* vertices." -/
@[ext]
structure Path (α : Type*) where
  /-- The initial vertex of the path. -/
  first : α
  /-- The terminal vertex of the path. -/
  last : α
  /-- The walk from `first` to `last`. -/
  walk : (⊤ : SimpleGraph α).Walk first last
  /-- The walk has no repeated vertices. -/
  isPath : walk.IsPath

namespace Path

variable (P : Path α)

/-- The subgraph consisting of the vertices and edges of `P`. -/
def toSubgraph : (⊤ : SimpleGraph α).Subgraph := P.walk.toSubgraph

/-- The vertex set `V(P)` of the path `P`. -/
def verts : Set α := P.toSubgraph.verts

/-- The edge set `E(P)` of the path `P`. -/
def edgeSet : Set (Sym2 α) := P.toSubgraph.edgeSet

/-- The ends `{P.first, P.last}` of the path `P` (Graph Minors I, Section 1, page 41). -/
def ends : Set α := {P.first, P.last}

/-- The internal vertices of `P` (its vertices other than its ends): "called its *ends*, and any
other vertices are called *internal* vertices." (Graph Minors I, Section 1, page 41). -/
def internalVerts : Set α := P.verts \ P.ends

/-- `P` is a path of `G`: its subgraph `P.toSubgraph` is a subgraph of `G`. -/
def IsIn (G : (⊤ : SimpleGraph α).Subgraph) : Prop := P.toSubgraph ≤ G

/-- `P` is a path in `G` from `A₁` to `A₂`: `P` is a path of `G` with initial vertex in `A₁` and
terminal vertex in `A₂` (Graph Minors I, Section 1, page 41). -/
def IsFromTo (G : (⊤ : SimpleGraph α).Subgraph) (A₁ A₂ : Set α) : Prop :=
  P.toSubgraph ≤ G ∧ P.first ∈ A₁ ∧ P.last ∈ A₂

/-- "A path *avoids* $X \subseteq V(G)$ if it has no vertex in $X$."
(Graph Minors I, Section 1, page 41). -/
def Avoids (X : Set α) : Prop := Disjoint P.verts X

/-- `u` occurs before `v` on `P` (equivalently, `v` is after `u` on `P`, Graph Minors I,
Section 2, pages 42–44): `u` appears at an earlier position than `v` in `P.walk.support`. -/
def Precedes (u v : α) : Prop :=
  ∃ (i j : ℕ) (hi : i < P.walk.support.length) (hj : j < P.walk.support.length),
    i < j ∧ P.walk.support[i] = u ∧ P.walk.support[j] = v

end Path

/-- `H` is a path subgraph: there is a path `P : Path α` with `P.toSubgraph = H`. -/
def IsPathSubgraph (H : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  ∃ P : Path α, P.toSubgraph = H

/-- "$X \subseteq V(G)$ *separates* $Y, Z \subseteq V(G)$ if no path in $G$ from $Y$ to $Z$ avoids
$X$."
(Graph Minors I, Section 1, page 41). -/
def Separates (G : (⊤ : SimpleGraph α).Subgraph) (X Y Z : Set α) : Prop :=
  ∀ P : Path α, P.IsFromTo G Y Z → ¬ P.Avoids X

/-- `P₁, …, Pₘ` are disjoint paths in `G` from `A₁` to `A₂` (Graph Minors I, Section 1, page 41,
and Section 2, (2.5)–(2.8), pages 44–48). -/
def IsDisjointPathFamily (G : (⊤ : SimpleGraph α).Subgraph) (A₁ A₂ : Set α)
    {m : ℕ} (P : Fin m → Path α) : Prop :=
  (∀ i, (P i).IsFromTo G A₁ A₂) ∧ Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts

/-- "A star is a tree in which one vertex, called the *centre*, is adjacent to all others"
(Graph Minors I, Section 2, (2.2), page 42). Here `B` is a star with centre `c`. -/
def IsStarWithCenter (B : (⊤ : SimpleGraph α).Subgraph) (c : α) : Prop :=
  c ∈ B.verts ∧ (∀ v ∈ B.verts, v ≠ c → B.Adj c v) ∧ ∀ u v, B.Adj u v → u = c ∨ v = c

/-- `B` is a star: a tree in which one vertex (a centre) is adjacent to all others
(Graph Minors I, Section 2, (2.2), page 42). -/
def IsStar (B : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  ∃ c, IsStarWithCenter B c

/-- `T` is a tree subgraph: a connected acyclic subgraph (`T.coe.IsTree`). -/
def IsTreeSubgraph (T : (⊤ : SimpleGraph α).Subgraph) : Prop :=
  T.coe.IsTree

/-- `v` is an end-vertex (a vertex of valency `1`) of the subgraph `T`
(Graph Minors I, Section 2, (2.3), page 43). -/
def IsLeafOf (T : (⊤ : SimpleGraph α).Subgraph) (v : α) : Prop :=
  v ∈ T.verts ∧ (T.neighborSet v).ncard = 1

/-- The number of connected components of a subgraph `H`, or `⊤` if there are infinitely many.
For finite graphs this is the count in Graph Minors I, Section 2, (2.8), page 48. -/
noncomputable def numComponents (H : (⊤ : SimpleGraph α).Subgraph) : ℕ∞ :=
  ENat.card H.coe.ConnectedComponent

end GraphMinor.GM01
