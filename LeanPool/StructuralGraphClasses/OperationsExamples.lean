/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.PartitionOperations
public import LeanPool.StructuralGraphClasses.ChordalOperations
public import LeanPool.StructuralGraphClasses.CotreeOperations

/-!
# Certificate API regression examples

These consumers check that relabelling, restriction and composition expose
the supplied certificate data without reconstructing existential witnesses.
-/

@[expose] public section

namespace SimpleGraph.StructuralGraphClasses

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

example (P : ThresholdPartition G) (f : G ≃g H) (s : Set W) :
    (H.induce s).IsThreshold := ((P.mapIso f).induce s).isThreshold

example (P : ThresholdPartition G) (f : G ≃g H) (s : Set W) (v : s) :
    v ∈ ((P.mapIso f).induce s).clique ↔ f.symm v.val ∈ P.clique := by
  simp

example {ord : V → ℕ} (h : G.IsPEO ord) (f : G ≃g H) (s : Set W) :
    (H.induce s).IsPEO ((ord ∘ f.symm) ∘ Subtype.val) := (h.mapIso f).induce s

example {ι : Type*} (T : CliqueTree G ι) (f : G ≃g H) (s : Set W)
    [DecidablePred (· ∈ s)] (i : ι) (v : s) :
    v ∈ ((T.mapIso f).induce s).bag i ↔ f.symm v.val ∈ T.bag i := by
  simp

example {ι : Type*} (T : CliqueTree G ι) (s : Set V) [DecidablePred (· ∈ s)] :
    (G.induce s).IsChordal := IsChordal.of_nonempty_cliqueTree (T.induce s)

example (L : CotreeRepresentation G) (R : CotreeRepresentation H) :
    (graphJoin (G ⊕g H) G).IsCograph := ((L.sum R).graphJoin L).isCograph

example (a b : V) :
    (graphJoin G H).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by simp

example (a : V) (b : W) : (graphJoin G H).Adj (Sum.inl a) (Sum.inr b) := by simp

end SimpleGraph.StructuralGraphClasses
