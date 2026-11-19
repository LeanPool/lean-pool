/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Extending a graph by one new vertex

This file defines `SimpleGraph.addVertex`, the universal way to extend a graph `G : SimpleGraph
V` by a single brand-new vertex with an arbitrary prescribed neighbourhood among the old
vertices: `G.addVertex N` lives on `Option V`, the universal one-point extension of `V`, with the
new vertex `none` adjacent to exactly the vertices in `N`. Every one-vertex extension of `G` (up
to an isomorphism fixing `G`) is of this form for some choice of `N`.

This is a different construction from `SimpleGraph.replaceVertex`: `replaceVertex`
relabels one *existing* vertex's neighbourhood within the same vertex type `V`, while
`addVertex` enlarges the vertex type itself by one new element. `Option V` (rather than, say,
`V ⊕ Unit`) is used for the new vertex type to match `SimpleGraph.induceUnivIso`-style
conventions elsewhere in `Mathlib.Combinatorics.SimpleGraph`; `V ⊕ Unit` would be an equally
defensible choice and reviewers may prefer it.

## Main declarations

* `SimpleGraph.addVertex`: the one-vertex extension.
* `SimpleGraph.decidableRelAddVertexAdj`: `(G.addVertex N).Adj` is decidable whenever `G.Adj` and
  membership in `N` are.
* `SimpleGraph.neighborSet_addVertex_none`, `SimpleGraph.mem_neighborSet_addVertex_some`: the new
  and old vertices' neighbourhoods in `G.addVertex N`, in terms of `G`'s own neighbourhoods and
  `N`.
* `SimpleGraph.addVertex_isContained`: adding a vertex never removes structure.
* `SimpleGraph.CliqueFree.of_addVertex`: the deletion direction — if a one-vertex extension of
  `G` is `n`-clique-free, so was `G`.
* `SimpleGraph.Iso.addVertex`: `addVertex` transports along a graph isomorphism.

## Tags

graph theory, combinatorics
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*}

section AddVertex

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Extend `G` by one brand-new vertex `none`, adjacent to exactly the vertices of `N`. Since
`Option V` is the universal one-point extension of `V`, every one-vertex extension of `G` (up to
an isomorphism fixing `G`) is of this form for some choice of `N`. -/
def addVertex (G : SimpleGraph V) (N : Set V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | some a, none => a ∈ N
    | none, some b => b ∈ N
    | none, none => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro x h; cases x <;> simp_all⟩

@[simp]
theorem addVertex_adj_some_some {G : SimpleGraph V} {N : Set V} {a b : V} :
    (G.addVertex N).Adj (some a) (some b) ↔ G.Adj a b :=
  Iff.rfl

@[simp]
theorem addVertex_adj_some_none {G : SimpleGraph V} {N : Set V} {a : V} :
    (G.addVertex N).Adj (some a) none ↔ a ∈ N :=
  Iff.rfl

@[simp]
theorem addVertex_adj_none_some {G : SimpleGraph V} {N : Set V} {b : V} :
    (G.addVertex N).Adj none (some b) ↔ b ∈ N :=
  Iff.rfl

theorem addVertex_not_adj_none_none {G : SimpleGraph V} {N : Set V} :
    ¬(G.addVertex N).Adj none none :=
  (G.addVertex N).irrefl

/-- `(G.addVertex N).Adj` is decidable whenever `G.Adj` and membership in `N` are: the defining
`match` on the two `Option V` arguments reduces to exactly those two decidable propositions. -/
instance decidableRelAddVertexAdj {G : SimpleGraph V} {N : Set V} [DecidableRel G.Adj]
    [DecidablePred (· ∈ N)] : DecidableRel (G.addVertex N).Adj := fun x y =>
  match x, y with
  | some a, some b => inferInstanceAs (Decidable (G.Adj a b))
  | some a, none => inferInstanceAs (Decidable (a ∈ N))
  | none, some b => inferInstanceAs (Decidable (b ∈ N))
  | none, none => inferInstanceAs (Decidable False)

/-- The new vertex `none`'s neighbours in `G.addVertex N` are exactly the images of `N`. -/
@[simp]
theorem neighborSet_addVertex_none {G : SimpleGraph V} {N : Set V} :
    (G.addVertex N).neighborSet none = some '' N := by
  ext x
  cases x with
  | none => simp
  | some a => simp [Set.mem_image]

/-- An old vertex `some a`'s neighbours in `G.addVertex N` are the images of its old neighbours,
together with the new vertex `none` exactly when `a ∈ N`. -/
theorem mem_neighborSet_addVertex_some {G : SimpleGraph V} {N : Set V} {a : V} {x : Option V} :
    x ∈ (G.addVertex N).neighborSet (some a) ↔
      (∃ b, x = some b ∧ G.Adj a b) ∨ (x = none ∧ a ∈ N) := by
  cases x with
  | none => simp
  | some b => simp

/-- The embedding of `G` into `G.addVertex N` sending every old vertex to itself. Witnesses that
adding a vertex never removes structure. -/
def addVertexEmbedding (G : SimpleGraph V) (N : Set V) : G ↪g G.addVertex N where
  toFun := some
  inj' := Option.some_injective V
  map_rel_iff' := by simp

theorem addVertex_isContained (G : SimpleGraph V) (N : Set V) : G ⊑ G.addVertex N :=
  (addVertexEmbedding G N).isContained

/-- The deletion direction dual to `SimpleGraph.addVertex_isContained`: if a one-vertex
extension of `G` is `n`-clique-free, so was `G` itself — extending a graph can only make it
*harder* to stay clique-free, never easier. -/
theorem CliqueFree.of_addVertex {N : Set V} {n : ℕ} (h : (G.addVertex N).CliqueFree n) :
    G.CliqueFree n :=
  h.comap (addVertex_isContained G N)

/-- `SimpleGraph.addVertex` transports along a graph isomorphism: an isomorphism `e : G ≃g H`
together with the image neighbourhood `e '' N` extends to an isomorphism of the one-vertex
extensions, fixing the new vertex. -/
protected def Iso.addVertex (e : G ≃g H) (N : Set V) :
    G.addVertex N ≃g H.addVertex (e '' N) where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv := by rintro (_ | a) <;> simp
  right_inv := by rintro (_ | b) <;> simp
  map_rel_iff' := by
    rintro (_ | a) (_ | b) <;>
      simp [SimpleGraph.addVertex, e.map_adj_iff, e.injective.eq_iff, Set.mem_image]

/-! ### Worked example -/

/-- Concrete instance of `mem_neighborSet_addVertex_some`: extending the two-vertex complete graph
by a new vertex adjacent only to old vertex `0`, old vertex `0`'s neighbours become the old
neighbour `1` together with the new vertex, while the new vertex itself and `0` stay non-adjacent
(the graph has no loops). -/
theorem addVertex_neighborSet_some_example :
    some (1 : Fin 2) ∈
        ((⊤ : SimpleGraph (Fin 2)).addVertex ({0} : Set (Fin 2))).neighborSet (some 0) ∧
      (none : Option (Fin 2)) ∈
        ((⊤ : SimpleGraph (Fin 2)).addVertex ({0} : Set (Fin 2))).neighborSet (some 0) ∧
      some (0 : Fin 2) ∉
        ((⊤ : SimpleGraph (Fin 2)).addVertex ({0} : Set (Fin 2))).neighborSet (some 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

end AddVertex

end SimpleGraph
