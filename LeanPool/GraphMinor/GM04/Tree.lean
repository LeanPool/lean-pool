/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Rooted trees (Graph Minors IV, Section 2)

Graph Minors IV, Section 2 (page 230): "we define an *undirected tree* to be a non-null connected
finite undirected graph without circuits, and a *tree* $T$ to be a directed graph, the undirected
graph underlying which is an undirected tree, such that every vertex of $T$ is the head of at most
one edge. It follows that there is a unique vertex of each tree $T$ (called the *root* and denoted
by $o(T)$) which is the head of no edge of $T$, and every edge of $T$ is directed away from the
root."

## How a tree is represented

A `RootedTree ι` has a finite vertex set `verts` in the type `ι`, a root, and a function `parent`.
Every vertex `v` other than the root is the head of exactly one edge, and the tail of that edge is
`parent v`. Since an edge is determined by its head, **we identify each edge with its head**: the
edge set `E(T)` is `T.edges`, the vertex set minus the root, and the edge `f` has head `f` and tail
`T.parent f`. The condition that iterating `parent` from any vertex reaches the root says that the
underlying undirected graph is connected; it then has `|V(T)| - 1` edges, so it is a tree.
Conversely every tree in the sense of the paper arises in this way, with `parent v` the tail of
the edge with head `v`.

All trees of this file live in one type `ι`, so a sequence of disjoint trees, as in (2.1) and
(2.2), is a sequence of trees in `ι` with pairwise disjoint vertex sets, and subtrees and the
contraction of a tree are trees in the same type.

## Notions

* `T.Reaches u v`: there is a directed path of `T` from `u` to `v`, that is, `u` lies on the path
  of `T` from `o(T)` to `v` (possibly `u = v`).
* `T.subtreeAt v`: the vertex set of `T^v`, the maximal subtree of `T` with root `v`. For an edge
  `f`, `T^f = T^{head f}` is `T.subtreeAt f`, and `T.rootSide f` is the vertex set of `T_f`, the
  other component of `T \ f`, with root `o(T)`.
* `T.OnPath t₁ t₂ t`: `t` lies on the path of `T` between `t₁` and `t₂`. `T.OnPathEdge t₁ t₂ f`:
  the edge `f` is an edge of that path.
* `T.pathEdges f₂ f₁`: the edge set of the directed path of `T` with first edge `f₂` and last edge
  `f₁`. Such a path exists exactly when `T.Reaches f₂ f₁`.
* `T.Precedes φ v w`: `v` precedes `w` with respect to `φ`, as defined before (2.2).
* `T.IsComponentRoot F y x`, `T.componentAt F y`: `y` is the root of the component of `T \ F`
  containing `x`, and the vertex set of the component with root `y`.
* `T.IsContraction F S`: `S` is the contraction of `T` onto `F`, as defined before (2.2).
* `IsStar S`, `T.starAt s`: stars, and the maximal star with root `s` that is a subtree of `T`
  (Section 3).
* `IsRich M X`: `X` is `M`-rich. A set is `M`-stable when it is an independent set of `M`
  (Mathlib's `SimpleGraph.IsIndepSet`).
* `TreeLemma22Statement`: the statement of (2.2).
-/

@[expose] public section

namespace GraphMinor.GM04

variable {ι : Type*}

/-- A rooted tree (Graph Minors IV, Section 2), with vertex set `verts` in `ι`. Each vertex `v`
other than the root is the head of exactly one edge, whose tail is `parent v`; we identify this
edge with `v`. The value of `parent` at the root, and outside `verts`, carries no meaning; it is
the root at the root. -/
structure RootedTree (ι : Type*) where
  /-- The vertex set `V(T)`. -/
  verts : Finset ι
  /-- The root `o(T)`. -/
  root : ι
  /-- `parent v` is the tail of the edge with head `v`, for `v ≠ root`. -/
  parent : ι → ι
  root_mem : root ∈ verts
  parent_mem : ∀ v ∈ verts, parent v ∈ verts
  parent_root : parent root = root
  /-- From every vertex, following edges backwards leads to the root. -/
  exists_iterate_eq_root : ∀ v ∈ verts, ∃ n, parent^[n] v = root

namespace RootedTree

variable (T : RootedTree ι)

/-- The edge set `E(T)`: the vertices other than the root, each standing for the edge of which it
is the head. -/
noncomputable def edges : Finset ι := by classical exact T.verts.erase T.root

/-- There is a directed path of `T` from `u` to `v`, possibly with no edges. Equivalently, `u` lies
on the path of `T` from `o(T)` to `v`. -/
def Reaches (u v : ι) : Prop := v ∈ T.verts ∧ ∃ n, T.parent^[n] v = u

/-- The vertex set of `T^v`, the maximal subtree of `T` with root `v`: the vertices `w` such that
`v` lies on the path from `o(T)` to `w`. -/
noncomputable def subtreeAt (v : ι) : Finset ι := by classical exact T.verts.filter (T.Reaches v)

/-- The vertex set of `T_f` for an edge `f`: the component of `T \ f` that contains the root.
Its root is `o(T)`. -/
noncomputable def rootSide (f : ι) : Finset ι := by classical exact T.verts \ T.subtreeAt f

/-- `t` lies on the path of `T` between `t₁` and `t₂`. The common ancestors of `t₁` and `t₂` form a
directed path from the root, whose last vertex `a` is the vertex of the path between `t₁` and `t₂`
closest to the root; the path consists of the vertices from `a` to `t₁` and from `a` to `t₂`. So
`t` is on it when `t` lies on the path from the root to `t₁` or to `t₂`, and every common ancestor
of `t₁` and `t₂` lies on the path from the root to `t`. -/
def OnPath (t₁ t₂ t : ι) : Prop :=
  (T.Reaches t t₁ ∨ T.Reaches t t₂) ∧ ∀ x, T.Reaches x t₁ → T.Reaches x t₂ → T.Reaches x t

/-- The edge `f` is an edge of the path of `T` between `t₁` and `t₂`: both its head `f` and its
tail `T.parent f` lie on that path. -/
def OnPathEdge (t₁ t₂ f : ι) : Prop :=
  f ∈ T.edges ∧ T.OnPath t₁ t₂ f ∧ T.OnPath t₁ t₂ (T.parent f)

/-- The edge set of the directed path of `T` with first edge `f₂` and last edge `f₁` (it exists
when `T.Reaches f₂ f₁`): the edges `g` with `f₂` on the path from the root to `g` and `g` on the
path from the root to `f₁`. -/
def pathEdges (f₂ f₁ : ι) : Set ι := {g | T.Reaches f₂ g ∧ T.Reaches g f₁}

/-- `v` precedes `w` with respect to `φ` (Graph Minors IV, before (2.2)): `v ≠ o(T)`, there is a
directed path `P` of `T` from `v` to `w`, `φ(e) = φ(f)` where `e, f` are the edges with heads `v,
w`, and `φ(g) ≥ φ(f)` for every edge `g` of `P`. The edges of `P` are the vertices `g ≠ v` with
`v` on the path from the root to `g` and `g` on the path from the root to `w`. -/
def Precedes (φ : ι → ℕ) (v w : ι) : Prop :=
  v ≠ T.root ∧ T.Reaches v w ∧ φ v = φ w ∧
    ∀ g, g ≠ v → T.Reaches v g → T.Reaches g w → φ w ≤ φ g

/-- `y` is the root of the component of `T \ F` containing `x`: `y` lies on the path from the
root to `x`, `y` is the root of `T` or the head of an edge in `F`, and no other edge of the
directed path from `y` to `x` is in `F`. -/
def IsComponentRoot (F : Set ι) (y x : ι) : Prop :=
  T.Reaches y x ∧ (y = T.root ∨ y ∈ F) ∧ ∀ g, g ≠ y → T.Reaches y g → T.Reaches g x → g ∉ F

/-- The vertex set of the component of `T \ F` with root `y` (for `y` the root of `T` or the head
of an edge in `F`). -/
noncomputable def componentAt (F : Set ι) (y : ι) : Finset ι := by
  classical exact T.verts.filter (T.IsComponentRoot F y)

/-- `S` is the contraction of `T` onto `F ⊆ E(T)` (Graph Minors IV, before (2.2)): "the tree $S$
with $E(S) = F$ and $V(S)$ the set of roots of the components of $T\setminus
F$, in which $v \in V(S)$ is the head (or tail, respectively) of $f \in F$ if the head (or
tail, respectively) of $f$ in $T$ belongs to the component of $T\setminus F$ with root $v$." The
roots of the components of `T \ F` are
`o(T)` and the heads of the edges in `F`. The head of `f` in `T` is `f`, the root of its own
component, so `f` keeps its head; its tail in `S` is the root of the component containing its
tail `T.parent f` in `T`. -/
structure IsContraction (F : Set ι) (S : RootedTree ι) : Prop where
  verts_eq : (S.verts : Set ι) = insert T.root (F ∩ T.edges)
  root_eq : S.root = T.root
  parent_eq : ∀ f ∈ S.edges, T.IsComponentRoot F (S.parent f) (T.parent f)

/-- `S` is a star: its root is the tail of every edge. -/
def IsStar (S : RootedTree ι) : Prop := ∀ v ∈ S.edges, S.parent v = S.root

/-- The heads of the edges of `T` with tail `s`. -/
noncomputable def children (s : ι) : Finset ι := by
  classical exact T.edges.filter fun v ↦ T.parent v = s

/-- The maximal star with root `s` which is a subtree of `T` (Graph Minors IV, Section 3): the
vertex `s`, the heads of the edges of `T` with tail `s`, and these edges. -/
noncomputable def starAt (s : ι) : RootedTree ι where
  verts := by classical exact insert s (T.children s)
  root := s
  parent _ := s
  root_mem := by classical exact Finset.mem_insert_self s _
  parent_mem _ _ := by classical exact Finset.mem_insert_self s _
  parent_root := rfl
  exists_iterate_eq_root _ _ := ⟨1, rfl⟩

end RootedTree

/-- `X` is `M`-rich: no infinite subset of `X` is `M`-stable, that is, independent in `M`. -/
def IsRich (M : SimpleGraph ι) (X : Set ι) : Prop := ∀ Y ⊆ X, M.IsIndepSet Y → Y.Finite

/-- The statement of Graph Minors IV, (2.2). Let `T₁, T₂, …` be a countable sequence of disjoint
trees, let `n ≥ 0`, and for each `i` let `φᵢ : E(Tᵢ) → {0, 1, …, n}`. Let `M` be an infinite graph
with `V(M) = V(T₁ ∪ T₂ ∪ ⋯)` such that for `i' > i`, if `u ∈ V(Tᵢ)` is `M`-adjacent to
`w ∈ V(T_{i'})`, and `v ∈ V(T_{i'})` precedes `w` (with respect to `φ_{i'}`), then `u` is
`M`-adjacent to `v`. Let `{o(T₁), o(T₂), …}` be `M`-stable. Then there is an infinite `M`-stable
set `X ⊆ V(M)` such that `|X ∩ V(Tᵢ)| ≤ 1` for each `i` and such that the set of heads of all
edges of `T₁ ∪ T₂ ∪ ⋯` with tails in `X` is `M`-rich.

Here `M` is a simple graph on `ι`; only its adjacencies between vertices of the trees matter. The
sequence is indexed from `0`. -/
def TreeLemma22Statement : Prop :=
  ∀ {ι : Type*} (T : ℕ → RootedTree ι) (n : ℕ) (φ : ℕ → ι → ℕ) (M : SimpleGraph ι),
    Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts) →
    (∀ i, ∀ f ∈ (T i).edges, φ i f ≤ n) →
    (∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v) →
    M.IsIndepSet (Set.range fun i ↦ (T i).root) →
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X}

end GraphMinor.GM04
