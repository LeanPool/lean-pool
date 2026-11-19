/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.RamseyReservoir.RamseyBound
public import LeanPool.RamseyReservoir.Reservoir

/-!
# Homogeneous blocks and their quotient graph

A family of pairwise disjoint nonempty vertex sets (*blocks*) is *homogeneous* for `G` when between
any two distinct blocks either all pairs are edges or none are. Such a family has a quotient graph
on the block indices, and cliques and independent sets of the quotient lift to `G` by choosing one
representative per block. A clique inside one block glues to representatives of the other blocks
of a quotient clique containing it (*anchored gluing*), which is how recursive Ramsey arguments
combine cliques found at different scales.

## Main definitions

* `SimpleGraph.HomogeneousBlocks G ι`: a homogeneous family of blocks indexed by `ι`.
* `SimpleGraph.HomogeneousBlocks.quotient`: the quotient graph on `ι`.
* `SimpleGraph.HomogeneousBlocks.rep`: a choice of representative in each block.

## Main statements

* `SimpleGraph.HomogeneousBlocks.isNClique_map_rep`,
  `SimpleGraph.HomogeneousBlocks.isNClique_compl_map_rep`: cliques and independent sets of the
  quotient lift to `G`.
* `SimpleGraph.HomogeneousBlocks.isNClique_anchor`: **anchored gluing**. An `n`-clique inside one
  block of an `m`-clique of the quotient extends to an `(n + m - 1)`-clique of `G`.
* `SimpleGraph.HomogeneousBlocks.exists_of_ramseyBound`: a Ramsey bound for the quotient gives a
  clique or an independent set of `G`.
-/

@[expose] public section

open Finset Function

namespace SimpleGraph

variable {V ι : Type*}

/-- A *homogeneous block family* for `G`: pairwise disjoint nonempty blocks such that between any
two distinct blocks either every pair is an edge or no pair is. -/
structure HomogeneousBlocks (G : SimpleGraph V) (ι : Type*) where
  /-- The blocks. -/
  block : ι → Finset V
  nonempty : ∀ i, (block i).Nonempty
  pairwiseDisjoint : Pairwise (Disjoint on block)
  homogeneous : ∀ i j, i ≠ j →
    (∀ x ∈ block i, ∀ y ∈ block j, G.Adj x y) ∨ ∀ x ∈ block i, ∀ y ∈ block j, ¬G.Adj x y

namespace HomogeneousBlocks

variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)

/-- The quotient graph: distinct blocks are adjacent when every pair between them is an edge. -/
def quotient : SimpleGraph ι :=
  fromRel fun i j => ∀ x ∈ F.block i, ∀ y ∈ F.block j, G.Adj x y

/-- Adjacency in the quotient: distinct blocks joined in `G`. -/
theorem quotient_adj {i j : ι} :
    F.quotient.Adj i j ↔ i ≠ j ∧ ∀ x ∈ F.block i, ∀ y ∈ F.block j, G.Adj x y := by
  rw [quotient, fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_of_imp fun h x hx y hy => (h y hy x hx).symm

/-- Vertices of quotient-adjacent blocks are adjacent in `G`. -/
theorem adj_of_quotient_adj {i j : ι} (h : F.quotient.Adj i j) {x y : V} (hx : x ∈ F.block i)
    (hy : y ∈ F.block j) : G.Adj x y :=
  (F.quotient_adj.mp h).2 x hx y hy

/-- Vertices in distinct blocks are distinct. -/
theorem ne_of_mem_block {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ F.block i)
    (hy : y ∈ F.block j) : x ≠ y := by
  rintro rfl
  exact Finset.disjoint_left.mp (F.pairwiseDisjoint hij) hx hy

/-- Between non-adjacent distinct blocks every pair is an edge of the complement. -/
theorem compl_adj_of_quotient_compl_adj {i j : ι} (h : F.quotientᶜ.Adj i j) {x y : V}
    (hx : x ∈ F.block i) (hy : y ∈ F.block j) : Gᶜ.Adj x y := by
  rw [compl_adj] at h ⊢
  refine ⟨F.ne_of_mem_block h.1 hx hy, ?_⟩
  rcases F.homogeneous i j h.1 with hall | hnone
  · exact absurd (F.quotient_adj.mpr ⟨h.1, hall⟩) h.2
  · exact hnone x hx y hy

/-- A chosen representative of each block. -/
noncomputable def rep (i : ι) : V := (F.nonempty i).choose

/-- The representative of a block lies in it. -/
theorem rep_mem (i : ι) : F.rep i ∈ F.block i := (F.nonempty i).choose_spec

/-- Distinct blocks have distinct representatives. -/
theorem rep_injective : Injective F.rep := fun i j h => by
  by_contra hij
  exact F.ne_of_mem_block hij (F.rep_mem i) (F.rep_mem j) h

/-- The representatives as an embedding. -/
noncomputable def repEmbedding : ι ↪ V := ⟨F.rep, F.rep_injective⟩

/-- The representative embedding sends a block to its representative. -/
@[simp] theorem repEmbedding_apply (i : ι) : F.repEmbedding i = F.rep i := rfl

/-- The quotient is the graph induced on the representatives. -/
theorem quotient_adj_iff_adj_rep {i j : ι} : F.quotient.Adj i j ↔ G.Adj (F.rep i) (F.rep j) := by
  refine ⟨fun h => F.adj_of_quotient_adj h (F.rep_mem i) (F.rep_mem j), fun h => ?_⟩
  have hij : i ≠ j := fun hij => by subst hij; exact G.irrefl h
  rcases F.homogeneous i j hij with hall | hnone
  · exact F.quotient_adj.mpr ⟨hij, hall⟩
  · exact absurd h (hnone _ (F.rep_mem i) _ (F.rep_mem j))

/-- The representatives embed the quotient into `G` as an induced subgraph. -/
noncomputable def repGraphEmbedding : F.quotient ↪g G :=
  ⟨F.repEmbedding, F.quotient_adj_iff_adj_rep.symm⟩

/-- A graph embedding carries `m`-cliques to `m`-cliques. -/
private theorem isNClique_map_of_embedding {W : Type*} {H : SimpleGraph W} {K : SimpleGraph V}
    (e : H ↪g K) {m : ℕ} {I : Finset W} (hI : H.IsNClique m I) :
    K.IsNClique m (I.map e.toEmbedding) :=
  hI.map.mono (map_le_iff_le_comap.mpr fun _ _ h => e.map_adj_iff.mpr h)

/-- Cliques of the quotient lift to cliques of `G`. -/
theorem isNClique_map_rep {m : ℕ} {I : Finset ι} (hI : F.quotient.IsNClique m I) :
    G.IsNClique m (I.map F.repEmbedding) :=
  isNClique_map_of_embedding F.repGraphEmbedding hI

/-- Independent sets of the quotient lift to independent sets of `G`. -/
theorem isNClique_compl_map_rep {m : ℕ} {I : Finset ι} (hI : F.quotientᶜ.IsNClique m I) :
    Gᶜ.IsNClique m (I.map F.repEmbedding) :=
  isNClique_map_of_embedding (SimpleGraph.Embedding.complEquiv F.repGraphEmbedding) hI

/-- **Anchored gluing.** If `I` is an `m`-clique of the quotient containing `i₀`, and `t` is an
`n`-clique of `G` inside the block `i₀`, then `t` together with the representatives of the other
blocks of `I` is an `(n + m - 1)`-clique of `G`. -/
theorem isNClique_anchor [DecidableEq V] [DecidableEq ι] {m n : ℕ} {I : Finset ι}
    (hI : F.quotient.IsNClique m I) {i₀ : ι} (hi₀ : i₀ ∈ I) {t : Finset V}
    (ht : G.IsNClique n t) (hts : t ⊆ F.block i₀) :
    G.IsNClique (n + m - 1) (t ∪ (I.erase i₀).map F.repEmbedding) := by
  have hrest : G.IsNClique (m - 1) ((I.erase i₀).map F.repEmbedding) := by
    refine F.isNClique_map_rep ⟨hI.isClique.subset (by simp), ?_⟩
    rw [card_erase_of_mem hi₀, hI.card_eq]
  have hcross : ∀ x ∈ t, ∀ y ∈ (I.erase i₀).map F.repEmbedding, G.Adj x y := by
    intro x hx y hy
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
    have hj' := mem_erase.mp hj
    exact F.adj_of_quotient_adj (hI.isClique hi₀ hj'.2 (Ne.symm hj'.1)) (hts hx) (F.rep_mem j)
  have hdisj : Disjoint t ((I.erase i₀).map F.repEmbedding) :=
    Finset.disjoint_left.mpr fun x hx hy => (G.irrefl (hcross x hx x hy))
  refine ⟨?_, ?_⟩
  · rw [coe_union]
    exact ht.isClique.union_of_forall_adj hrest.isClique hcross
  · rw [card_union_of_disjoint hdisj, ht.card_eq, hrest.card_eq]
    have : 1 ≤ m := hI.card_eq ▸ card_pos.mpr ⟨i₀, hi₀⟩
    omega

include F in
/-- **Ramsey on the quotient.** If `RamseyBound n r s` and there are at least `n` blocks, `G` has
an `r`-clique or an independent `s`-set. -/
theorem exists_of_ramseyBound {n r s : ℕ} (h : RamseyBound n r s) {J : Finset ι} (hJ : n ≤ #J) :
    (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  rcases h.exists_isNClique_subset F.quotient hJ with ⟨I, -, hI⟩ | ⟨I, -, hI⟩
  exacts [.inl ⟨_, F.isNClique_map_rep hI⟩, .inr ⟨_, F.isNClique_compl_map_rep hI⟩]

end HomogeneousBlocks

end SimpleGraph
