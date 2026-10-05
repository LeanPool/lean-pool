/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Threshold

/-!
# Operations on split and threshold certificates

Transport preserves the supplied partition, rather than selecting a new one.
A threshold certificate packages this partition with its nested-neighborhood proof.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Relabel a split partition along an isomorphism. -/
def SplitPartition.mapIso (P : SplitPartition G) (f : G ≃g H) : SplitPartition H where
  clique := f.symm ⁻¹' P.clique
  independent := f.symm ⁻¹' P.independent
  isClique := by
    intro a ha b hb hab
    exact f.symm.map_rel_iff.mp
      (P.isClique ha hb (fun he => hab (f.symm.injective he)))
  isIndepSet := by
    intro a ha b hb hab hrel
    exact P.isIndepSet ha hb (fun he => hab (f.symm.injective he))
      (f.symm.map_rel_iff.mpr hrel)
  disjoint := Set.disjoint_left.mpr (fun _ ha hb => Set.disjoint_left.mp P.disjoint ha hb)
  cover := by
    ext v
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
    exact P.mem_clique_or_mem_independent (f.symm v)

/-- The clique part of a complemented partition is its original independent part. -/
@[simp] theorem SplitPartition.compl_clique (P : SplitPartition G) :
    P.compl.clique = P.independent := rfl

/-- The independent part of a complemented partition is its original clique part. -/
@[simp] theorem SplitPartition.compl_independent (P : SplitPartition G) :
    P.compl.independent = P.clique := rfl

/-- Restricting a partition restricts its clique part by preimage. -/
@[simp] theorem SplitPartition.induce_clique (P : SplitPartition G) (s : Set V) :
    (P.induce s).clique = Subtype.val ⁻¹' P.clique := rfl

/-- Restricting a partition restricts its independent part by preimage. -/
@[simp] theorem SplitPartition.induce_independent (P : SplitPartition G) (s : Set V) :
    (P.induce s).independent = Subtype.val ⁻¹' P.independent := rfl

/-- Membership in a relabelled clique is tested in the supplied original partition. -/
@[simp] theorem SplitPartition.mem_mapIso_clique (P : SplitPartition G) (f : G ≃g H)
    (v : W) : v ∈ (P.mapIso f).clique ↔ f.symm v ∈ P.clique := Iff.rfl

/-- Membership in a relabelled independent part is tested in the original partition. -/
@[simp] theorem SplitPartition.mem_mapIso_independent (P : SplitPartition G) (f : G ≃g H)
    (v : W) : v ∈ (P.mapIso f).independent ↔ f.symm v ∈ P.independent := Iff.rfl

/-- An explicit split partition with nested independent neighborhoods. -/
structure ThresholdPartition (G : SimpleGraph V) extends SplitPartition G where
  /-- Independent neighborhoods are comparable by inclusion. -/
  nested : toSplitPartition.HasNestedNeighborhoods

namespace ThresholdPartition

/-- A threshold partition certifies threshold membership. -/
theorem isThreshold (P : ThresholdPartition G) : G.IsThreshold :=
  ⟨P.toSplitPartition, P.nested⟩

/-- Pull back the supplied threshold partition along an injective map. -/
def comap (P : ThresholdPartition G) (f : W ↪ V) : ThresholdPartition (G.comap f) where
  toSplitPartition := P.toSplitPartition.comap f
  nested := (P.toSplitPartition.comap f).hasNestedNeighborhoods_of_isP4Free
    ((P.toSplitPartition.isP4Free_of_hasNestedNeighborhoods P.nested).comap f)

/-- Restrict the supplied threshold partition to an induced subgraph. -/
def induce (P : ThresholdPartition G) (s : Set V) : ThresholdPartition (G.induce s) :=
  P.comap (Function.Embedding.subtype s)

/-- Complementation exchanges the parts and preserves nestedness. -/
def compl (P : ThresholdPartition G) : ThresholdPartition Gᶜ where
  toSplitPartition := P.toSplitPartition.compl
  nested := P.toSplitPartition.compl.hasNestedNeighborhoods_of_isP4Free
    (P.toSplitPartition.isP4Free_of_hasNestedNeighborhoods P.nested).compl

/-- Relabel the supplied threshold partition. -/
def mapIso (P : ThresholdPartition G) (f : G ≃g H) : ThresholdPartition H where
  toSplitPartition := P.toSplitPartition.mapIso f
  nested := (P.toSplitPartition.mapIso f).hasNestedNeighborhoods_of_isP4Free
    (f.isP4Free_iff.mp (P.toSplitPartition.isP4Free_of_hasNestedNeighborhoods P.nested))

/-- Restriction uses the original split partition, not an existential replacement. -/
@[simp] theorem induce_toSplitPartition (P : ThresholdPartition G) (s : Set V) :
    (P.induce s).toSplitPartition = P.toSplitPartition.induce s := rfl

/-- Complementation uses the original split partition with exchanged parts. -/
@[simp] theorem compl_toSplitPartition (P : ThresholdPartition G) :
    P.compl.toSplitPartition = P.toSplitPartition.compl := rfl

/-- Relabelling uses the transported original split partition. -/
@[simp] theorem mapIso_toSplitPartition (P : ThresholdPartition G) (f : G ≃g H) :
    (P.mapIso f).toSplitPartition = P.toSplitPartition.mapIso f := rfl

end ThresholdPartition

/-- Threshold membership is equivalent to existence of an explicit threshold partition. -/
theorem isThreshold_iff_nonempty_thresholdPartition :
    G.IsThreshold ↔ Nonempty (ThresholdPartition G) := by
  constructor
  · rintro ⟨P, hn⟩
    exact ⟨⟨P, hn⟩⟩
  · rintro ⟨P⟩
    exact P.isThreshold

/-- Threshold membership pulls back along an injective vertex map. -/
theorem IsThreshold.comap (h : G.IsThreshold) (f : W ↪ V) : (G.comap f).IsThreshold := by
  obtain ⟨P⟩ := isThreshold_iff_nonempty_thresholdPartition.mp h
  exact (P.comap f).isThreshold

end SimpleGraph
