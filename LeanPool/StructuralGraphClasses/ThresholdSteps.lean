/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.PartitionOperations
public import LeanPool.StructuralGraphClasses.CotreeOperations
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Isolated and universal creation steps for threshold graphs

The new vertex is the left `Unit` summand. Operations preserve the supplied
partition; the elimination theorem supplies a reverse step in every nonempty
finite threshold graph, without asserting a recognition algorithm.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Add a single isolated vertex. -/
def addIsolated (G : SimpleGraph V) : SimpleGraph (Unit ⊕ V) :=
  (⊥ : SimpleGraph Unit) ⊕g G

/-- Add a single universal vertex, by complementing an isolated step. -/
def addUniversal (G : SimpleGraph V) : SimpleGraph (Unit ⊕ V) := (addIsolated Gᶜ)ᶜ

/-- The old vertices keep their adjacency in a universal step. -/
@[simp] theorem addUniversal_adj_inr (a b : V) :
    (addUniversal G).Adj (Sum.inr a) (Sum.inr b) ↔ G.Adj a b := by
  change (graphJoin (⊥ : SimpleGraph Unit) G).Adj (Sum.inr a) (Sum.inr b) ↔ _
  simp

/-- The new universal vertex is adjacent to every old vertex. -/
@[simp] theorem addUniversal_adj_new (a : V) :
    (addUniversal G).Adj (Sum.inl ()) (Sum.inr a) := by
  simp [addUniversal, addIsolated, compl_adj, sum_adj]

/-- Extend a split partition by putting the new isolated vertex in its independent part. -/
def SplitPartition.addIsolated (P : SplitPartition G) : SplitPartition (addIsolated G) where
  clique := {x | match x with | Sum.inl _ => False | Sum.inr v => v ∈ P.clique}
  independent := {x | match x with | Sum.inl _ => True | Sum.inr v => v ∈ P.independent}
  isClique := by
    rintro (a | a) ha (b | b) hb hab
    · exact ha.elim
    · exact ha.elim
    · exact hb.elim
    · exact P.isClique ha hb (fun he => hab (congrArg Sum.inr he))
  isIndepSet := by
    rintro (a | a) ha (b | b) hb hab
    · simp [SimpleGraph.addIsolated]
    · simp [SimpleGraph.addIsolated]
    · simp [SimpleGraph.addIsolated]
    · exact P.isIndepSet ha hb (fun he => hab (congrArg Sum.inr he))
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro (a | a) ha hb
    · exact ha.elim
    · exact Set.disjoint_left.mp P.disjoint ha hb
  cover := by
    ext x
    cases x with
    | inl a => simp
    | inr a => exact iff_true_intro (P.mem_clique_or_mem_independent a)

/-- Add an isolated vertex to the supplied threshold partition. -/
def ThresholdPartition.addIsolated (P : ThresholdPartition G) :
    ThresholdPartition (SimpleGraph.addIsolated G) where
  toSplitPartition := P.toSplitPartition.addIsolated
  nested := P.toSplitPartition.addIsolated.hasNestedNeighborhoods_of_isP4Free
    (isCograph_bot.sum (P.toSplitPartition.isP4Free_of_hasNestedNeighborhoods P.nested))

/-- Add a universal vertex using the complementary partition. -/
def ThresholdPartition.addUniversal (P : ThresholdPartition G) :
    ThresholdPartition (SimpleGraph.addUniversal G) := P.compl.addIsolated.compl

/-- Every nonempty finite threshold partition has an isolated or universal vertex. -/
theorem ThresholdPartition.exists_isolated_or_universal [Finite V] [Nonempty V]
    (P : ThresholdPartition G) :
    ∃ v, (∀ u, ¬G.Adj v u) ∨ (∀ u, u ≠ v → G.Adj v u) := by
  classical
  let := Fintype.ofFinite V
  by_cases hi : ∃ v, ∀ u, ¬G.Adj v u
  · obtain ⟨v, hv⟩ := hi
    exact ⟨v, Or.inl hv⟩
  have hneighbor (v : V) : ∃ u, G.Adj v u := by
    by_contra hn
    exact hi ⟨v, fun u hu => hn ⟨u, hu⟩⟩
  by_cases hI : P.independent.Nonempty
  · obtain ⟨v, hv, hmin⟩ := Set.exists_min_image P.independent
      (fun x => (G.neighborSet x).toFinset.card) (Set.toFinite _) hI
    have hsub (u : V) (hu : u ∈ P.independent) : G.neighborSet v ⊆ G.neighborSet u := by
      rcases P.nested v hv u hu with h | h
      · exact h
      · have hs : (G.neighborSet u).toFinset ⊆ (G.neighborSet v).toFinset := by
          simpa using h
        have he := Finset.eq_of_subset_of_card_le hs (hmin u hu)
        intro x hx
        have hx' : x ∈ (G.neighborSet v).toFinset := by simpa using hx
        rw [← he] at hx'
        simpa using hx'
    obtain ⟨c, hvc⟩ := hneighbor v
    have hc := P.toSplitPartition.mem_clique_of_adj hv hvc
    refine ⟨c, Or.inr ?_⟩
    intro u huc
    rcases P.toSplitPartition.mem_clique_or_mem_independent u with hu | hu
    · exact P.isClique hc hu huc.symm
    · exact (hsub u hu hvc).symm
  · obtain ⟨v⟩ := ‹Nonempty V›
    have hall (u : V) : u ∈ P.clique :=
      (P.toSplitPartition.mem_clique_or_mem_independent u).resolve_right
        (fun hu => hI ⟨u, hu⟩)
    exact ⟨v, Or.inr (fun u huv => P.isClique (hall v) (hall u) huv.symm)⟩

end SimpleGraph
