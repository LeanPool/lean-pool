/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Split partitions

A split partition records a clique and an independent set covering the vertices.
Either part may be empty. Membership in the class is a proposition; a partition
is a separate certificate that can be restricted or transported.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V}

/-- A partition of the vertices into a clique and an independent set. -/
structure SplitPartition (G : SimpleGraph V) where
  /-- The clique part. -/
  clique : Set V
  /-- The independent part. -/
  independent : Set V
  /-- The clique part induces a complete graph. -/
  isClique : G.IsClique clique
  /-- The independent part contains no edges. -/
  isIndepSet : G.IsIndepSet independent
  /-- No vertex belongs to both parts. -/
  disjoint : Disjoint clique independent
  /-- Every vertex belongs to one of the parts. -/
  cover : clique ∪ independent = Set.univ

/-- A graph is split if it admits a split partition. -/
def IsSplit (G : SimpleGraph V) : Prop := Nonempty (SplitPartition G)

namespace SplitPartition

variable (P : SplitPartition G)

/-- Every vertex lies in one of the two parts. -/
theorem mem_clique_or_mem_independent (v : V) : v ∈ P.clique ∨ v ∈ P.independent := by
  have : v ∈ P.clique ∪ P.independent := by rw [P.cover]; trivial
  exact this

/-- Complementation exchanges the two parts. -/
def compl : SplitPartition Gᶜ where
  clique := P.independent
  independent := P.clique
  isClique := (G.isClique_compl).mpr P.isIndepSet
  isIndepSet := (G.isIndepSet_compl).mpr P.isClique
  disjoint := P.disjoint.symm
  cover := by rw [Set.union_comm, P.cover]

/-- Pull a partition back along an injective vertex map. -/
def comap (f : W ↪ V) : SplitPartition (G.comap f) where
  clique := f ⁻¹' P.clique
  independent := f ⁻¹' P.independent
  isClique := by
    intro u hu v hv hne
    exact P.isClique hu hv (fun h => hne (f.injective h))
  isIndepSet := by
    intro u hu v hv hne
    exact P.isIndepSet hu hv (fun h => hne (f.injective h))
  disjoint := by
    apply Set.disjoint_left.mpr
    intro v hv hi
    exact Set.disjoint_left.mp P.disjoint hv hi
  cover := by
    ext v
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
    exact P.mem_clique_or_mem_independent (f v)

/-- Restrict a split partition to an arbitrary induced subgraph. -/
def induce (s : Set V) : SplitPartition (G.induce s) := P.comap (Function.Embedding.subtype s)

end SplitPartition

/-- Split graphs are closed under complementation. -/
theorem IsSplit.compl (h : G.IsSplit) : Gᶜ.IsSplit := by
  obtain ⟨P⟩ := h
  exact ⟨P.compl⟩

/-- Split membership is invariant under complementation. -/
@[simp] theorem isSplit_compl : Gᶜ.IsSplit ↔ G.IsSplit := by
  constructor
  · intro h
    simpa only [compl_compl] using h.compl
  · exact IsSplit.compl

/-- Split membership pulls back along an injective vertex map. -/
theorem IsSplit.comap (h : G.IsSplit) (f : W ↪ V) : (G.comap f).IsSplit := by
  obtain ⟨P⟩ := h
  exact ⟨P.comap f⟩

/-- Every induced subgraph of a split graph is split. -/
theorem IsSplit.induce (h : G.IsSplit) (s : Set V) : (G.induce s).IsSplit :=
  h.comap (Function.Embedding.subtype s)

/-- Graph isomorphisms preserve split membership. -/
theorem Iso.isSplit_iff {H : SimpleGraph W} (f : G ≃g H) : G.IsSplit ↔ H.IsSplit := by
  constructor
  · intro h
    have h' := h.comap f.symm.toEmbedding.toEmbedding
    change (G.comap f.symm.toEmbedding).IsSplit at h'
    rwa [f.symm.toEmbedding.comap_eq] at h'
  · intro h
    have h' := h.comap f.toEmbedding.toEmbedding
    change (H.comap f.toEmbedding).IsSplit at h'
    rwa [f.toEmbedding.comap_eq] at h'

/-- Empty graphs are split, with every vertex in the independent part. -/
theorem isSplit_bot : (⊥ : SimpleGraph V).IsSplit := by
  refine ⟨⟨∅, Set.univ, ?_, ?_, ?_, ?_⟩⟩
  · exact isClique_empty
  · intro u hu v hv hne
    simp
  · simp
  · simp

/-- Complete graphs are split, with every vertex in the clique part. -/
theorem isSplit_top : (⊤ : SimpleGraph V).IsSplit := by
  have h := (isSplit_bot (V := V)).compl
  simpa using h

end SimpleGraph
