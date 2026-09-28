/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — Yuster (edge-based): degree of `triangleHypergraphSub` = number of triangles on an edge

Standalone, Mathlib-only. The hypergraph-degree of an edge `E` in the edge-based triangle hypergraph
`triangleHypergraphSub G` equals the number of triangles of `G` containing `E` (= codegree in `G` of
`E`'s two endpoints). This is the architecture-independent bridge that ② (edge counting /
near-regularity)
needs: it turns the abstract "near-regular hypergraph" degree window into the graph condition
"most edges lie on ≈ d triangles".

* `triangleHypergraphSub_degree_eq` — `deg_E(E) = #{ t ∈ cliqueFinset 3 | E.val ⊆ t }`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterSubDegree

/-! # YusterSubDegreeChar -/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem mem_image_of_triangle {t : Finset V} (E : EdgeV G) :
    E ∈ (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) ↔ E.val ⊆ t := by
  rw [Finset.mem_subtype, Finset.mem_powersetCard]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq⟩

private theorem triple_injOn :
    Set.InjOn (fun t => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2))
      (G.cliqueFinset 3 : Set (Finset V)) := by
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  apply Finset.eq_of_subset_of_card_le _ (by rw [ht.card_eq, ht'.card_eq])
  intro a ha
  obtain ⟨b, hbt, hba⟩ : ∃ b ∈ t, b ≠ a := by
    have hne : (t.erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha, ht.card_eq]; omega
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, Finset.mem_of_mem_erase hb, Finset.ne_of_mem_erase hb⟩
  have hsub : ({a, b} : Finset V) ⊆ t := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hbt
  have hedge : ({a, b} : Finset V) ∈ G.cliqueFinset 2 := by
    rw [SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨ht.isClique.subset hsub, Finset.card_pair (Ne.symm hba)⟩
  have hmem : (⟨{a, b}, hedge⟩ : EdgeV G) ∈ (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) :=
    (mem_image_of_triangle G _).mpr hsub
  have heq' : (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)
      = (t'.powersetCard 2).subtype (· ∈ G.cliqueFinset 2) := heq
  rw [heq'] at hmem
  have := (mem_image_of_triangle G _).mp hmem
  exact this (by simp)

theorem triangleHypergraphSub_degree_eq (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).card := by
  have hset : (triangleHypergraphSub G).filter (fun T => E ∈ T)
      = ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).image
          (fun t => (t.powersetCard 2).subtype (· ∈ G.cliqueFinset 2)) := by
    ext T
    simp only [Finset.mem_filter, triangleHypergraphSub, Finset.mem_image]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hE⟩
      exact ⟨t, ⟨ht, (mem_image_of_triangle G E).mp hE⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hsub⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, (mem_image_of_triangle G E).mpr hsub⟩
  rw [Hypergraph.degree, hset, Finset.card_image_of_injOn]
  exact (triple_injOn G).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))

/-- The number of triangles containing edge `E` equals the number of common neighbours `c` of `E`'s
endpoints (those `c ∉ E.val` with `insert c E.val` a triangle). -/
theorem triangles_on_edge_eq_commonNbr (E : EdgeV G) :
    ((G.cliqueFinset 3).filter (fun t => E.val ⊆ t)).card
      = (Finset.univ.filter (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card := by
  have hE2 : E.val.card = 2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  symm
  apply Finset.card_bij (fun c _ => insert c E.val)
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
    exact ⟨hc.2, Finset.subset_insert _ _⟩
  · intro c hc c' hc' heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    have hcmem : c ∈ insert c' E.val := heq ▸ Finset.mem_insert_self c E.val
    rw [Finset.mem_insert] at hcmem
    rcases hcmem with h | h
    · exact h
    · exact absurd h hc.1
  · intro t ht
    rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at ht
    obtain ⟨htri, hsub⟩ := ht
    obtain ⟨c, hct, hcnotE⟩ : ∃ c ∈ t, c ∉ E.val := by
      by_contra h
      push Not at h
      have hts : t ⊆ E.val := fun x hx => h x hx
      have hle := Finset.card_le_card hts
      rw [htri.card_eq, hE2] at hle
      omega
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hcnotE, ?_⟩
      have : insert c E.val = t := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.insert_subset hct hsub
        · rw [htri.card_eq, Finset.card_insert_of_notMem hcnotE, hE2]
      rw [this]; exact htri
    · apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hct hsub
      · rw [htri.card_eq, Finset.card_insert_of_notMem hcnotE, hE2]

/-- **② bridge, graph form.** The hypergraph-degree of edge `E` in `triangleHypergraphSub G`
equals the
number of common neighbours of `E`'s endpoints (the codegree of `E` in `G`). -/
theorem triangleHypergraphSub_degree_eq_commonNbr (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = (Finset.univ.filter (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card := by
  rw [triangleHypergraphSub_degree_eq, triangles_on_edge_eq_commonNbr]

/-- **② mean codegree.** Summing the per-edge codegree (common-neighbour count) over all edges gives
`3·#triangles`, so the average edge codegree is `3·#triangles / |E(G)|` — the target `d` for the
near-regularity window `②`. -/
theorem sum_commonNbr_eq_three_mul_triangles :
    ∑ E : EdgeV G, (Finset.univ.filter
        (fun c => c ∉ E.val ∧ G.IsNClique 3 (insert c E.val))).card
      = 3 * (G.cliqueFinset 3).card := by
  rw [← sum_degree_triangleHypergraphSub G]
  exact Finset.sum_congr rfl fun E _ => (triangleHypergraphSub_degree_eq_commonNbr G E).symm

end Nibble.YusterE
