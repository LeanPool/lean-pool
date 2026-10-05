/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Exclusion of induced four-vertex paths

The three edges and three nonedges below force all four vertices to be distinct.
No finiteness hypothesis is needed for this local exclusion predicate.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- There is no induced path on four vertices, in the order `a, b, c, d`. -/
def IsP4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
    ¬G.Adj a c → ¬G.Adj a d → ¬G.Adj b d → False

/-- Four-vertex path exclusion pulls back along vertex maps. -/
theorem IsP4Free.comap (h : G.IsP4Free) (f : W → V) : (G.comap f).IsP4Free := by
  intro a b c d hab hbc hcd hac had hbd
  exact h (f a) (f b) (f c) (f d) hab hbc hcd hac had hbd

/-- Every induced subgraph of a graph excluding `P₄` also excludes `P₄`. -/
theorem IsP4Free.induce (h : G.IsP4Free) (s : Set V) : (G.induce s).IsP4Free :=
  h.comap Subtype.val

/-- Graph isomorphisms preserve induced four-vertex path exclusion. -/
theorem Iso.isP4Free_iff {H : SimpleGraph W} (f : G ≃g H) : G.IsP4Free ↔ H.IsP4Free := by
  constructor
  · intro h
    have h' := h.comap f.symm.toEmbedding
    rwa [f.symm.toEmbedding.comap_eq] at h'
  · intro h
    have h' := h.comap f.toEmbedding
    rwa [f.toEmbedding.comap_eq] at h'

/-- The complement of an induced `P₄` is another induced `P₄`. -/
theorem IsP4Free.compl (h : G.IsP4Free) : Gᶜ.IsP4Free := by
  intro a b c d hab hbc hcd hac had hbd
  rw [G.compl_adj] at hab hbc hcd
  have hac' : G.Adj a c := by
    by_contra hn
    apply hac
    refine ⟨?_, hn⟩
    intro heq
    subst c
    exact had hcd
  have had' : G.Adj a d := by
    by_contra hn
    apply had
    refine ⟨?_, hn⟩
    intro heq
    subst d
    exact hac ⟨hcd.1.symm, fun he => hcd.2 he.symm⟩
  have hbd' : G.Adj b d := by
    by_contra hn
    apply hbd
    refine ⟨?_, hn⟩
    intro heq
    subst d
    exact had hab
  exact h c a d b hac'.symm had' hbd'.symm
    (fun he => hcd.2 he) (fun he => hbc.2 he.symm) hab.2

/-- Four-vertex path exclusion is invariant under complementation. -/
@[simp] theorem isP4Free_compl : Gᶜ.IsP4Free ↔ G.IsP4Free := by
  constructor
  · intro h
    simpa only [compl_compl] using h.compl
  · exact IsP4Free.compl

end SimpleGraph
