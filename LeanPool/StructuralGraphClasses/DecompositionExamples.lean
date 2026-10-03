/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.ThresholdCreation
public import LeanPool.StructuralGraphClasses.CographTwins
public import LeanPool.StructuralGraphClasses.SplitDecomposition

/-!
# Consumers of the decomposition interfaces

Creation certificates compose with the previous transport API, and maximum
clique partitions expose simplicial vertices without inspecting their proofs.
-/

@[expose] public section

namespace SimpleGraph.StructuralGraphClasses

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

example (R : CotreeRepresentation G) (s : Set V) :
    Nonempty (CotreeRepresentation (G.induce s)) := ⟨R.induce s⟩

example : (ThresholdSequence.universal (.isolated .empty)).graph.IsThreshold :=
  (ThresholdSequence.universal (.isolated .empty)).partition.isThreshold

example (R : ThresholdCreationRepresentation G) (f : G ≃g H) :
    (addUniversal (addIsolated H)).IsThreshold :=
  ((R.mapIso f).addIsolated.addUniversal).isThreshold

example (R : ThresholdCreationRepresentation G) :
    R.compl.sequence = R.sequence.complement := rfl

example [Finite V] (h : G.IsSplit) :
    ∃ P : SplitPartition G, ∃ C : Finset V, P.clique = (C : Set V) ∧
      G.IsNClique G.cliqueNum C ∧ ∀ v ∈ P.independent, G.IsSimplicial v := by
  obtain ⟨P, C, he, hc⟩ := h.exists_partition_with_maximum_clique
  exact ⟨P, C, he, hc, fun _ hv => P.isSimplicial_of_mem_independent hv⟩

example [Finite V] [Nontrivial V] (h : G.IsCograph) :
    ∃ a b, G.AreTwins a b ∧ (G.Adj a b ∨ ¬G.Adj a b) := by
  classical
  obtain ⟨a, b, hab⟩ := h.exists_twins
  exact ⟨a, b, hab, Classical.em _⟩

example [Finite V] [Nontrivial V] (h : G.IsThreshold) :
    ∃ a b, G.AreTwins a b := (isThreshold_iff_isSplit_and_isCograph.mp h).2.exists_twins

end SimpleGraph.StructuralGraphClasses
