/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.PartitionOperations
public import LeanPool.StructuralGraphClasses.ChordalBridge
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Simplicial vertices and maximum-clique split partitions

A maximum clique part can be chosen, but partitions need not be unique or
comparable. The two-vertex edgeless example has two incomparable maximum parts.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Every independent-part vertex of a split partition is simplicial. -/
theorem SplitPartition.isSimplicial_of_mem_independent (P : SplitPartition G)
    {v : V} (hv : v ∈ P.independent) : G.IsSimplicial v := by
  intro a ha b hb hab
  exact P.isClique (P.mem_clique_of_adj hv ha) (P.mem_clique_of_adj hv hb) hab

/-- A finite split graph has a split partition whose clique part is a maximum clique. -/
theorem IsSplit.exists_maximum_clique_partition [Finite V] (h : G.IsSplit) :
    ∃ C : Finset V, G.IsNClique G.cliqueNum C ∧ G.IsIndepSet (C : Set V)ᶜ := by
  classical
  let := Fintype.ofFinite V
  obtain ⟨P⟩ := h
  let candidates : Set (Finset V) :=
    {C | G.IsClique (C : Set V) ∧ G.IsIndepSet (C : Set V)ᶜ}
  have hp : P.clique.toFinset ∈ candidates := by
    refine ⟨by simpa using P.isClique, ?_⟩
    intro a ha b hb hab
    have haI : a ∈ P.independent :=
      (P.mem_clique_or_mem_independent a).resolve_left (by simpa using ha)
    have hbI : b ∈ P.independent :=
      (P.mem_clique_or_mem_independent b).resolve_left (by simpa using hb)
    exact P.isIndepSet haI hbI hab
  obtain ⟨C, hC, hmax⟩ := Set.exists_max_image candidates Finset.card
    (Set.toFinite candidates) ⟨_, hp⟩
  have hall (D : Finset V) (hD : G.IsClique (D : Set V)) : D.card ≤ C.card := by
    by_contra hn
    have hsmall : (D \ C).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hab
      exact hC.2 (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).2 hab
        (hD (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
    have hcount := Finset.card_sdiff_add_card_inter D C
    have heq : D ∩ C = C := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    have hsub : (C : Set V) ⊆ (D : Set V) := by
      intro v hv
      have hv' : v ∈ D ∩ C := by rwa [heq]
      exact (Finset.mem_inter.mp hv').1
    have hDc : D ∈ candidates := ⟨hD, hC.2.mono (Set.compl_subset_compl.mpr hsub)⟩
    exact hn (hmax D hDc)
  obtain ⟨D, hD⟩ := G.exists_isNClique_cliqueNum
  have heq : C.card = G.cliqueNum := le_antisymm hC.1.card_le_cliqueNum
    (by simpa only [hD.card_eq] using hall D hD.isClique)
  exact ⟨C, ⟨hC.1, heq⟩, hC.2⟩

/-- Package the maximum clique as the clique part of an actual split certificate. -/
theorem IsSplit.exists_partition_with_maximum_clique [Finite V] (h : G.IsSplit) :
    ∃ P : SplitPartition G, ∃ C : Finset V,
      P.clique = (C : Set V) ∧ G.IsNClique G.cliqueNum C := by
  obtain ⟨C, hC, hi⟩ := h.exists_maximum_clique_partition
  exact ⟨⟨C, (C : Set V)ᶜ, hC.isClique, hi, disjoint_compl_right,
    Set.union_compl_self _⟩, C, rfl, hC⟩

/-- Either singleton can be the clique part of a two-vertex edgeless split graph. -/
def emptyPairPartition (v : Fin 2) : SplitPartition (⊥ : SimpleGraph (Fin 2)) where
  clique := {v}
  independent := {v}ᶜ
  isClique := isClique_singleton v
  isIndepSet := by intro a ha b hb hab; simp
  disjoint := disjoint_compl_right
  cover := Set.union_compl_self _

/-- Maximum clique parts of split partitions can be incomparable. -/
theorem emptyPairPartition_incomparable :
    ¬(emptyPairPartition 0).clique ⊆ (emptyPairPartition 1).clique ∧
      ¬(emptyPairPartition 1).clique ⊆ (emptyPairPartition 0).clique := by
  simp [emptyPairPartition]

/-- Each of the two incomparable singleton parts is a maximum clique. -/
theorem emptyPairPartition_maximum (v : Fin 2) :
    (⊥ : SimpleGraph (Fin 2)).IsNClique (⊥ : SimpleGraph (Fin 2)).cliqueNum {v} := by
  rw [cliqueNum_bot]
  exact ⟨by simp, Finset.card_singleton v⟩

end SimpleGraph
