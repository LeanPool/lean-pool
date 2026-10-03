/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Threshold
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Data.Fintype.Sum

/-!
# Cotree semantics

A binary cotree constructs a finite graph from single vertices by disjoint union
and join. An explicit empty constructor handles the empty graph. Binary cotrees
need not be reduced or canonical; no uniqueness or recognition complexity is claimed.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Cographs are graphs with no induced four-vertex path. -/
def IsCograph (G : SimpleGraph V) : Prop := G.IsP4Free

/-- Disjoint union preserves exclusion of induced `P₄`. -/
theorem IsP4Free.sum (hG : G.IsP4Free) (hH : H.IsP4Free) : (G ⊕g H).IsP4Free := by
  rintro (a | a) (b | b) (c | c) (d | d) hab hbc hcd hac had hbd <;>
    simp only [sum_adj] at *
  all_goals first
    | contradiction
    | exact hG a b c d hab hbc hcd hac had hbd
    | exact hH a b c d hab hbc hcd hac had hbd

/-- The join is obtained by complementing the disjoint union of complements. -/
def graphJoin (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (Gᶜ ⊕g Hᶜ)ᶜ

/-- Join preserves exclusion of induced `P₄`. -/
theorem IsP4Free.graphJoin (hG : G.IsP4Free) (hH : H.IsP4Free) :
    (graphJoin G H).IsP4Free :=
  (hG.compl.sum hH.compl).compl

/-- A finite binary union/join expression for a graph. -/
inductive Cotree where
  /-- The empty graph. -/
  | empty
  /-- A single vertex. -/
  | leaf
  /-- Disjoint union of the graphs represented by two children. -/
  | union (left right : Cotree)
  /-- Join of the graphs represented by two children. -/
  | join (left right : Cotree)

namespace Cotree

/-- Leaves of a cotree, regarded as the vertices of its graph. -/
def Vertex : Cotree → Type
  | empty => PEmpty
  | leaf => Unit
  | union l r => l.Vertex ⊕ r.Vertex
  | join l r => l.Vertex ⊕ r.Vertex

/-- A cotree has finitely many leaves. -/
noncomputable instance vertexFintype (t : Cotree) : Fintype t.Vertex := by
  induction t with
  | empty => exact inferInstanceAs (Fintype PEmpty)
  | leaf => exact inferInstanceAs (Fintype Unit)
  | union l r ihl ihr =>
    letI := ihl
    letI := ihr
    exact inferInstanceAs (Fintype (l.Vertex ⊕ r.Vertex))
  | join l r ihl ihr =>
    letI := ihl
    letI := ihr
    exact inferInstanceAs (Fintype (l.Vertex ⊕ r.Vertex))

/-- Interpret union and join using Mathlib's graph operations. -/
def graph : (t : Cotree) → SimpleGraph t.Vertex
  | empty => ⊥
  | leaf => ⊥
  | union l r => l.graph ⊕g r.graph
  | join l r => graphJoin l.graph r.graph

/-- Every graph built by a cotree is `P₄`-free. -/
theorem graph_isP4Free (t : Cotree) : t.graph.IsP4Free := by
  induction t with
  | empty => intro a; exact PEmpty.elim a
  | leaf => intro a b c d hab; exact False.elim hab
  | union l r ihl ihr => exact ihl.sum ihr
  | join l r ihl ihr => exact ihl.graphJoin ihr

/-- A cotree always constructs a cograph. -/
theorem graph_isCograph (t : Cotree) : t.graph.IsCograph := t.graph_isP4Free

end Cotree

/-- A representation identifies the actual vertices with the leaves of a cotree. -/
structure CotreeRepresentation (G : SimpleGraph V) where
  /-- The finite union/join expression. -/
  cotree : Cotree
  /-- The graph isomorphism carrying its leaves to the original vertices. -/
  iso : cotree.graph ≃g G

/-- A cotree representation certifies cograph membership. -/
theorem CotreeRepresentation.isCograph (R : CotreeRepresentation G) : G.IsCograph := by
  have h := R.cotree.graph_isP4Free.comap R.iso.symm.toEmbedding
  rw [R.iso.symm.toEmbedding.comap_eq] at h
  exact h

/-- Threshold graphs are precisely split cographs. -/
theorem isThreshold_iff_isSplit_and_isCograph :
    G.IsThreshold ↔ G.IsSplit ∧ G.IsCograph :=
  isThreshold_iff_isSplit_and_isP4Free

end SimpleGraph
