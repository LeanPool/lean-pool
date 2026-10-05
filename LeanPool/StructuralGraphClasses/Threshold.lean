/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.Split
public import LeanPool.StructuralGraphClasses.PathFour

/-!
# Nested split partitions

Threshold membership is introduced using a split partition whose independent
vertices have comparable neighborhoods. The equivalence with split membership
and exclusion of induced `P₄` is a theorem, not the definition.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace SplitPartition

variable (P : SplitPartition G)

/-- The independent vertices have neighborhoods linearly ordered by inclusion. -/
def HasNestedNeighborhoods : Prop :=
  ∀ u ∈ P.independent, ∀ v ∈ P.independent,
    G.neighborSet u ⊆ G.neighborSet v ∨ G.neighborSet v ⊆ G.neighborSet u

/-- Every neighbor of an independent vertex is in the clique part. -/
theorem mem_clique_of_adj {u v : V} (hu : u ∈ P.independent) (h : G.Adj u v) :
    v ∈ P.clique := by
  rcases P.mem_clique_or_mem_independent v with hv | hv
  · exact hv
  · exact False.elim (P.isIndepSet hu hv h.ne h)

/-- Excluding `P₄` forces the independent neighborhoods to be comparable. -/
theorem hasNestedNeighborhoods_of_isP4Free (h : G.IsP4Free) :
    P.HasNestedNeighborhoods := by
  intro u hu v hv
  classical
  by_contra hn
  have h₁ : ¬G.neighborSet u ⊆ G.neighborSet v := fun hh => hn (Or.inl hh)
  have h₂ : ¬G.neighborSet v ⊆ G.neighborSet u := fun hh => hn (Or.inr hh)
  obtain ⟨x, hx, hxv⟩ := Set.not_subset.mp h₁
  obtain ⟨y, hy, hyu⟩ := Set.not_subset.mp h₂
  have hxC := P.mem_clique_of_adj hu hx
  have hyC := P.mem_clique_of_adj hv hy
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact hyu hx
  have huv : u ≠ v := by
    intro heq
    subst v
    exact hxv hx
  exact h u x y v hx (P.isClique hxC hyC hxy) hy.symm
    hyu (P.isIndepSet hu hv huv) (fun hh => hxv hh.symm)

/-- In a split partition with nested neighborhoods, an induced `P₄` is impossible. -/
theorem isP4Free_of_hasNestedNeighborhoods (hn : P.HasNestedNeighborhoods) :
    G.IsP4Free := by
  intro a b c d hab hbc hcd hac had hbd
  have hac_ne : a ≠ c := by
    intro heq
    subst c
    exact had hcd
  have hbd_ne : b ≠ d := by
    intro heq
    subst d
    exact had hab
  have hbC : b ∈ P.clique := by
    rcases P.mem_clique_or_mem_independent b with hb | hb
    · exact hb
    · have haC := P.mem_clique_of_adj hb hab.symm
      have hcC := P.mem_clique_of_adj hb hbc
      exact False.elim (hac (P.isClique haC hcC hac_ne))
  have hcC : c ∈ P.clique := by
    rcases P.mem_clique_or_mem_independent c with hc | hc
    · exact hc
    · have hdC := P.mem_clique_of_adj hc hcd
      exact False.elim (hbd (P.isClique hbC hdC hbd_ne))
  have haI : a ∈ P.independent := by
    rcases P.mem_clique_or_mem_independent a with ha | ha
    · exact False.elim (hac (P.isClique ha hcC hac_ne))
    · exact ha
  have hdI : d ∈ P.independent := by
    rcases P.mem_clique_or_mem_independent d with hd | hd
    · exact False.elim (hbd (P.isClique hbC hd hbd_ne))
    · exact hd
  rcases hn a haI d hdI with hsub | hsub
  · exact hbd (hsub hab).symm
  · exact hac (hsub hcd.symm)

/-- The nested-neighborhood condition is precisely `P₄` exclusion within split graphs. -/
theorem hasNestedNeighborhoods_iff_isP4Free : P.HasNestedNeighborhoods ↔ G.IsP4Free :=
  ⟨P.isP4Free_of_hasNestedNeighborhoods, P.hasNestedNeighborhoods_of_isP4Free⟩

end SplitPartition

/-- A threshold graph admits a split partition with nested independent neighborhoods. -/
def IsThreshold (G : SimpleGraph V) : Prop :=
  ∃ P : SplitPartition G, P.HasNestedNeighborhoods

/-- A structural characterization of threshold graphs within the split class. -/
theorem isThreshold_iff_isSplit_and_isP4Free :
    G.IsThreshold ↔ G.IsSplit ∧ G.IsP4Free := by
  constructor
  · rintro ⟨P, hn⟩
    exact ⟨⟨P⟩, P.isP4Free_of_hasNestedNeighborhoods hn⟩
  · rintro ⟨⟨P⟩, h⟩
    exact ⟨P, P.hasNestedNeighborhoods_of_isP4Free h⟩

/-- Threshold membership is closed under complementation. -/
theorem IsThreshold.compl (h : G.IsThreshold) : Gᶜ.IsThreshold := by
  obtain ⟨hs, hp⟩ := isThreshold_iff_isSplit_and_isP4Free.mp h
  exact isThreshold_iff_isSplit_and_isP4Free.mpr ⟨hs.compl, hp.compl⟩

/-- Every induced subgraph of a threshold graph is threshold. -/
theorem IsThreshold.induce (h : G.IsThreshold) (s : Set V) : (G.induce s).IsThreshold := by
  obtain ⟨hs, hp⟩ := isThreshold_iff_isSplit_and_isP4Free.mp h
  exact isThreshold_iff_isSplit_and_isP4Free.mpr ⟨hs.induce s, hp.induce s⟩

/-- Graph isomorphisms preserve threshold membership. -/
theorem Iso.isThreshold_iff {W : Type*} {H : SimpleGraph W} (f : G ≃g H) :
    G.IsThreshold ↔ H.IsThreshold := by
  simp only [isThreshold_iff_isSplit_and_isP4Free, f.isSplit_iff, f.isP4Free_iff]

end SimpleGraph
