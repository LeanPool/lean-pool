/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Hypergraph.Basic
public import LeanPool.GraphMinor.GM04.Tree

/-!
# Tree-decompositions of rooted hypergraphs (Graph Minors IV, Sections 3 and 5)

Graph Minors IV, Section 3 (page 234): "A *tree-decomposition* $(T, \tau)$ of a rooted hypergraph
$G$ consists of a tree $T$ and a function $\tau$ which assigns to each $t \in V(T)$ a rooted
hypergraph $\tau(t)$, such that

(i) for each $t \in V(T)$, $\tau(t)^- \subseteq G^-$

(ii) $\bigcup_{t \in V(T)} \tau(t)^- = G^-$

(iii) for distinct $t_1, t_2 \in V(T)$, $E(\tau(t_1)^- \cap \tau(t_2)^-) = \emptyset$

(iv) for $t_1, t_2, t_3 \in V(T)$, if $t_2$ lies on the path of $T$ between $t_1$ and $t_3$ then
$\tau(t_1)^- \cap \tau(t_3)^- \subseteq \tau(t_2)^-$

(v) $\pi(\tau(o(T))) = \pi(G)$

(vi) for each edge $f \in E(T)$ with head $t_1$ and tail $t_2$, $\bar{\pi}(\tau(t_1)) =
V(\tau(t_1)^- \cap \tau(t_2)^-)$."

"If $T'$ is a subtree of $T$ we denote by $\tau \times T'$ the rooted hypergraph $G'$ defined by
$$
G'^- = \bigcup_{t \in V(T')} \tau(t)^-
$$
$$
\pi(G') = \pi(\tau(o(T'))).
$$" Here `cross τ S r` is `τ × T'` for the
subtree `T'` with vertex set `S` and root `r`.

(3.1) says that for an edge `f` of `T`, `(τ × T^f, τ × T_f)` is a separation of `G`; "The order of
the separation in (3.1) is called the *order* of $f$ in $(T, \tau)$." (`edgeOrder`).

Section 5 (page 238): "The width of a tree-decomposition $(T, \tau)$ of a rooted hypergraph $G$ is

$$\max(|V(\tau(t))| - 1 : t \in V(T))$$

and the *tree-width* of $G$ is the minimum $w \ge 0$ such that $G$ has a tree-decomposition of width
$\le w$." `WidthLE T τ w` says that the width is at most `w`, and
`TreeWidthLE G w` that the tree-width is at most `w`. In `TreeWidthLE` the tree has vertices in
`ℕ`; every finite tree is isomorphic to one with vertices in `ℕ`, so this loses nothing.

`ThomasStatement` is the lemma of R. Thomas that Graph Minors IV quotes as (5.1).
-/

@[expose] public section

namespace GraphMinor.GM04

open Hypergraph

variable {α β ι : Type*}

open Classical in
/-- `τ × T'`, for the subtree `T'` of `T` with vertex set `S` and root `r ∈ S`: the union of the
`τ(t)⁻` for `t ∈ S`, with the march `π(τ(r))`. (The union is taken over `insert r S`, which is `S`
since `r ∈ S`; this makes the march a march in the union also when `r ∉ S`.) -/
noncomputable def cross (τ : ι → RootedHypergraph α β) (S : Finset ι) (r : ι) :
    RootedHypergraph α β where
  toHypergraph := Hypergraph.biUnion (insert r S) fun t ↦ (τ t).toHypergraph
  roots := (τ r).roots
  roots_nodup := (τ r).roots_nodup
  roots_subset v hv :=
    Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self r S)) ((τ r).roots_subset v hv)

/-- `(T, τ)` is a tree-decomposition of the rooted hypergraph `G` (Graph Minors IV, Section 3,
conditions (i)–(vi)). Only the values of `τ` on `V(T)` matter. -/
structure IsTreeDecomposition (G : RootedHypergraph α β) (T : RootedTree ι)
    (τ : ι → RootedHypergraph α β) : Prop where
  /-- (i) -/
  le : ∀ t ∈ T.verts, (τ t).toHypergraph ≤ G.toHypergraph
  /-- (ii) -/
  biUnion_eq : Hypergraph.biUnion T.verts (fun t ↦ (τ t).toHypergraph) = G.toHypergraph
  /-- (iii) -/
  edgeSet_inter_eq : ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ →
    ((τ t₁).toHypergraph ∩ (τ t₂).toHypergraph).edgeSet = ∅
  /-- (iv) -/
  inter_le : ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, ∀ t₃ ∈ T.verts, T.OnPath t₁ t₃ t₂ →
    (τ t₁).toHypergraph ∩ (τ t₃).toHypergraph ≤ (τ t₂).toHypergraph
  /-- (v) -/
  roots_root : (τ T.root).roots = G.roots
  /-- (vi), for the edge with head `f` and tail `T.parent f`. -/
  rootSet_edge : ∀ f ∈ T.edges,
    (τ f).rootSet = ((τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph).vertexSet

/-- The order of the edge `f` in `(T, τ)`: the order of the separation `(τ × T^f, τ × T_f)`, that
is, `|V((τ × T^f)⁻ ∩ (τ × T_f)⁻)|`. -/
noncomputable def edgeOrder (T : RootedTree ι) (τ : ι → RootedHypergraph α β) (f : ι) : ℕ :=
  separationOrder (cross τ (T.subtreeAt f) f).toHypergraph
    (cross τ (T.rootSide f) T.root).toHypergraph

/-- The width of `(T, τ)` is at most `w`: `|V(τ(t))| - 1 ≤ w` for every `t ∈ V(T)`. -/
def WidthLE (T : RootedTree ι) (τ : ι → RootedHypergraph α β) (w : ℕ) : Prop :=
  ∀ t ∈ T.verts, (τ t).vertexSet.ncard ≤ w + 1

/-- The tree-width of the rooted hypergraph `G` is at most `w`: `G` has a tree-decomposition of
width at most `w`. -/
def TreeWidthLE (G : RootedHypergraph α β) (w : ℕ) : Prop :=
  ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β), IsTreeDecomposition G T τ ∧ WidthLE T τ w

/-- The lemma of R. Thomas (*A Menger-like property of tree-width. The finite case*, J. Combin.
Theory Ser. B 48 (1990) 67–76), as Graph Minors IV states it in (5.1) (page 238): "Let $G$ be a
graph. If $(G, 0)$ has a tree-decomposition of width $\le w$, then it has a
tree-decomposition $(T, \tau)$ of width $\le w$ such that for all distinct $t_1$, $t_2 \in
V(T)$ and all $k \ge 0$ either there are $k$ mutually vertex-disjoint paths of $G$ from
$V(\tau(t_1))$ to $V(\tau(t_2))$, or some edge of the path of $T$ between $t_1$ and $t_2$
has order $< k$." -/
def ThomasStatement : Prop :=
  ∀ {α β : Type*} (G : Hypergraph α β), G.IsGraph → ∀ w : ℕ, TreeWidthLE G.toRooted w →
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition G.toRooted T τ ∧ WidthLE T τ w ∧
      ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ → ∀ k : ℕ,
        HasDisjointPaths G.skeleton (τ t₁).vertexSet (τ t₂).vertexSet k ∨
          ∃ f, T.OnPathEdge t₁ t₂ f ∧ edgeOrder T τ f < k

end GraphMinor.GM04
