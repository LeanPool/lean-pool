/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Transporting a join and `CliqueFree` along a graph isomorphism

An isomorphism `e : G ≃g H` is in particular a bijection of vertex types, so it can be used to
push any further graph structure on the source vertex type forward to the target. This file
records that joining a graph `K` into `G` transports along `e` to joining the pushforward
`K.map e` into `H`, together with the single-edge special case obtained from the pushforward
formula `SimpleGraph.map_edge`, and the fact that `SimpleGraph.CliqueFree` is an isomorphism
invariant.

## Main declarations

* `SimpleGraph.Iso.sup`: an isomorphism `G ≃g H` induces an isomorphism `G ⊔ K ≃g H ⊔ K.map e`
  for any graph `K` on the source vertex type.
* `SimpleGraph.map_edge`: pushing a single-edge graph forward along any map is again a
  single-edge graph, `(edge s t).map f = edge (f s) (f t)`.
* `SimpleGraph.Iso.supEdge`: the single-edge specialization of `SimpleGraph.Iso.sup`.
* `SimpleGraph.cliqueFree_iso_iff`: `CliqueFree` is invariant under graph isomorphism.
* `SimpleGraph.CliqueFree.cliqueFreeOn_commonNeighbors`: in an `(n + 2)`-clique-free graph the
  common neighbourhood of an edge is `n`-clique-free.

## Implementation notes

The declarations here belong in three different mathlib files, and are kept together here only
for convenience.
`Iso.sup` and its `apply` lemmas belong in `Mathlib.Combinatorics.SimpleGraph.Maps`, in the
existing `SimpleGraph.Iso` namespace beside `Iso.comap` and `Iso.map` (that is the file where
`≃g` itself is introduced, so nothing earlier can state them). `map_edge` and `Iso.supEdge`
belong in `Mathlib.Combinatorics.SimpleGraph.Operations`, where `SimpleGraph.edge` is defined.
`cliqueFree_iso_iff` belongs in `Mathlib.Combinatorics.SimpleGraph.Copy`, immediately after
`Iso.isContained`/`Iso.isContained'`, out of which it is built.

`CliqueFree.cliqueFreeOn_commonNeighbors` has no consumer yet: see its own docstring.

## Tags

graph theory, combinatorics
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*}

/-! ### Transporting a join along an isomorphism -/

section JoinTransport

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- An isomorphism `e : G ≃g H` extends to an isomorphism of the graphs obtained by joining a
graph `K` into `G` and its pushforward `K.map e` into `H`. -/
protected def Iso.sup (e : G ≃g H) (K : SimpleGraph V) : G ⊔ K ≃g H ⊔ K.map e where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    simp [sup_adj, map_adj', e.map_adj_iff, e.injective.eq_iff, and_iff_right_of_imp Adj.ne]

@[simp]
lemma Iso.sup_apply (e : G ≃g H) (K : SimpleGraph V) (v : V) : e.sup K v = e v := rfl

@[simp]
lemma Iso.sup_symm_apply (e : G ≃g H) (K : SimpleGraph V) (w : W) :
    (e.sup K).symm w = e.symm w := rfl

/-- Pushing a single-edge graph forward along an arbitrary map is again a single-edge graph. No
injectivity hypothesis is needed: if `f s = f t` then both sides are `⊥`, since `SimpleGraph.map`
never creates a loop and `edge u u = ⊥`. -/
@[simp]
lemma map_edge (f : V → W) (s t : V) : (edge s t).map f = edge (f s) (f t) := by
  ext a b
  simp only [map_adj', edge_adj, ne_eq]
  constructor
  · rintro ⟨hab, u, v, ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩, rfl, rfl⟩ <;> tauto
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hab⟩
    · exact ⟨hab, s, t, ⟨Or.inl ⟨rfl, rfl⟩, fun h ↦ hab (by rw [h])⟩, rfl, rfl⟩
    · exact ⟨hab, t, s, ⟨Or.inr ⟨rfl, rfl⟩, fun h ↦ hab (by rw [h])⟩, rfl, rfl⟩

/-- The single-edge case of `SimpleGraph.Iso.sup`: an isomorphism of graphs extends to an
isomorphism of the graphs obtained by joining each side with the (transported) same single
edge. -/
protected def Iso.supEdge (e : G ≃g H) (v w : V) :
    G ⊔ edge v w ≃g H ⊔ edge (e v) (e w) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    rw [← map_edge (⇑e) v w]
    exact (e.sup (edge v w)).map_rel_iff'

@[simp]
lemma Iso.supEdge_apply (e : G ≃g H) (v w u : V) : e.supEdge v w u = e u := rfl

@[simp]
lemma Iso.supEdge_symm_apply (e : G ≃g H) (v w : V) (u : W) :
    (e.supEdge v w).symm u = e.symm u := rfl

end JoinTransport

/-! ### `CliqueFree` is an isomorphism invariant -/

section IsoTransport

variable {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ}

/-- `CliqueFree` transports along a graph isomorphism. -/
theorem cliqueFree_iso_iff (e : G ≃g H) : G.CliqueFree n ↔ H.CliqueFree n :=
  ⟨fun h ↦ h.comap e.isContained', fun h ↦ h.comap e.isContained⟩

end IsoTransport

/-! ### A codegree bound -/

section Codegree

variable {G : SimpleGraph V} {n : ℕ}

/-- **Codegree bound.** In an `(n + 2)`-clique-free graph, the common neighbourhood of two
*adjacent* vertices `u`, `w` is `n`-clique-free. Adjacency is essential here: `u` and `w` can
each extend a clique in their common neighbourhood into a single larger clique only because they
are themselves adjacent. Proved by two applications of `SimpleGraph.CliqueFreeOn.of_succ`.

Nothing in mathlib or in this library uses this lemma yet, so it should go upstream only together
with its first use. -/
theorem CliqueFree.cliqueFreeOn_commonNeighbors {u w : V} (hG : G.CliqueFree (n + 2))
    (huw : G.Adj u w) : G.CliqueFreeOn (G.commonNeighbors u w) n := by
  rw [commonNeighbors_eq]
  have := ((cliqueFreeOn_univ G).mpr hG).of_succ (ha := Set.mem_univ u)
  exact (by simpa using this : G.CliqueFreeOn (G.neighborSet u) (n + 1)).of_succ (ha := huw)

end Codegree

/-! ### Worked example -/

/-- Concrete instance of `map_edge`: pushing the edge between `0` and `1` in `Fin 2` forward along
`i ↦ i.val + 1` (into `Fin 3`) gives the edge between `1` and `2`. -/
theorem map_edge_example :
    (edge (0 : Fin 2) 1).map (fun i : Fin 2 => (⟨i.val + 1, by omega⟩ : Fin 3)) =
      edge (1 : Fin 3) 2 := by
  rw [map_edge]
  rfl

end SimpleGraph
