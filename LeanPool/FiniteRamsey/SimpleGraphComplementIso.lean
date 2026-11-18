/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Isomorphisms of complements

An isomorphism of simple graphs is in particular a bijection of vertex types that preserves and
reflects adjacency, so it preserves and reflects non-adjacency between distinct vertices as well.
It therefore restricts to an isomorphism of the complements.

## Main declarations

* `SimpleGraph.Iso.compl`: the isomorphism `Gᶜ ≃g Hᶜ` induced by an isomorphism `G ≃g H`.

## Tags

graph theory, combinatorics
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- An isomorphism of graphs induces an isomorphism of their complements. -/
protected def Iso.compl (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by simp [compl_adj, e.map_adj_iff, e.injective.eq_iff]

@[simp]
lemma Iso.compl_apply (e : G ≃g H) (v : V) : e.compl v = e v := rfl

@[simp]
lemma Iso.compl_symm_apply (e : G ≃g H) (w : W) : e.compl.symm w = e.symm w := rfl

/-! ### Worked example -/

/-- The identity isomorphism of a graph with itself induces the identity isomorphism of its
complement with itself, the concrete case `G = H` and `e = Iso.refl` of `Iso.compl`. -/
theorem iso_compl_refl_example (G : SimpleGraph V) :
    (Iso.refl : G ≃g G).compl = Iso.refl := by
  ext v
  simp

end SimpleGraph
