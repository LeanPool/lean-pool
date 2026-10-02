/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.Coverage
public import LeanPool.DrossFractionalTriangleDecomposition.Internal.K4Counting

/-!
# Counting bridges for Dross's cut argument

The graph's triangle and K₄ counts agree with the edge-node quantities used
in the auxiliary flow network.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A rooted K₄ pair is characterized by both partner endpoints being common neighbours. -/
public theorem k4pair_edge_iff (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    {c d : V} (hcd : G.Adj c d) :
    K4pair G (s(u, v)) (s(c, d)) ↔
      (c ∈ G.neighborFinset u ∩ G.neighborFinset v ∧
        d ∈ G.neighborFinset u ∩ G.neighborFinset v) := by
  rw [k4pair_iff_clique, SimpleGraph.isNClique_iff]
  simp only [Finset.mem_inter, mem_neighborFinset]
  constructor
  · rintro ⟨hcl, hcard⟩
    obtain ⟨_, hac, had, hbc, hbd, _⟩ := card4_pairwise hcard
    exact ⟨⟨hcl (by simp) (by simp) hac, hcl (by simp) (by simp) hbc⟩,
      hcl (by simp) (by simp) had, hcl (by simp) (by simp) hbd⟩
  · rintro ⟨⟨huc, hvc⟩, hud, hvd⟩
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hxy
          | assumption
          | (exact huv) | exact huv.symm
          | exact huc | exact huc.symm | exact hud | exact hud.symm
          | exact hvc | exact hvc.symm | exact hvd | exact hvd.symm
          | exact hcd | exact hcd.symm
    · have : u ≠ v := huv.ne
      have : u ≠ c := huc.ne
      have : u ≠ d := hud.ne
      have : v ≠ c := hvc.ne
      have : v ≠ d := hvd.ne
      have : c ≠ d := hcd.ne
      rw [show ({u, v, c, d} : Finset V).card = 4 from by
        rw [Finset.card_insert_of_notMem (by simp_all), Finset.card_insert_of_notMem (by simp_all),
          Finset.card_insert_of_notMem (by simp_all), Finset.card_singleton]]

/-- **Bridge #K₄-partners = numK4Through.** For an edge `uv`, the number of edges forming a
rooted-K₄ pair with it equals `numK4Through G u v` (Spine's K₄ count, bounded below by A6). -/
public theorem k4pair_count_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (G.edgeFinset.filter (fun e' => K4pair G (s(u, v)) e')).card = numK4Through G u v := by
  rw [numK4Through]
  congr 1
  apply Finset.filter_congr
  intro e' he'
  rw [SimpleGraph.mem_edgeFinset] at he'
  induction e' using Sym2.inductionOn with
  | hf c d =>
    rw [SimpleGraph.mem_edgeSet] at he'
    rw [k4pair_edge_iff G huv he']
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]

/-- **Bridge T_e = codeg.** The number of triangles through an edge `uv` equals the number of
common neighbours of `u` and `v` (Dross's `Tₑ`). This links `triThrough` to A6 (`Spine`). -/
public theorem triThrough_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    triThrough G (s(u, v)) = codeg G u v := by
  rw [triThrough, codeg]
  symm
  have hnuv : u ≠ v := huv.ne
  apply Finset.card_bij (fun w _ => ({u, v, w} : Finset V))
  · -- maps into the triangle set
    intro w hw
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw
    obtain ⟨hwu, hwv⟩ := hw
    rw [Finset.mem_filter, mem_cliqueFinset_iff]
    refine ⟨is3Clique_iff.2 ⟨u, v, w, huv, hwu, hwv, rfl⟩, ?_⟩
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨by simp, by simp⟩, hnuv⟩
  · -- injective
    intro w1 hw1 w2 hw2 heq
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hw1 hw2
    have h1 : w1 ∈ ({u, v, w2} : Finset V) := heq ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h | h | h
    · exact absurd h.symm hw1.1.ne
    · exact absurd h.symm hw1.2.ne
    · exact h
  · -- surjective
    intro t ht
    rw [Finset.mem_filter, mem_cliqueFinset_iff] at ht
    obtain ⟨hclique, hedge⟩ := ht
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff] at hedge
    obtain ⟨⟨hut, hvt⟩, _⟩ := hedge
    have hsub : ({u, v} : Finset V) ⊆ t := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hc2 : ({u, v} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hnuv]), Finset.card_singleton]
    have hc1 : (t \ ({u, v} : Finset V)).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hclique.card_eq, hc2]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc1
    have hwt : w ∈ t := (Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)).1
    have hwnuv : w ∉ ({u, v} : Finset V) :=
      (Finset.mem_sdiff.mp (hw ▸ Finset.mem_singleton_self w)).2
    have hwu : w ≠ u := fun h => hwnuv (by simp [h])
    have hwv : w ≠ v := fun h => hwnuv (by simp [h])
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact ⟨(hclique.1 hut hwt (Ne.symm hwu)), (hclique.1 hvt hwt (Ne.symm hwv))⟩
    · -- {u,v,w} = t
      have : t = insert u (insert v {w}) := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          by_cases hxuv : x ∈ ({u, v} : Finset V)
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv ⊢; tauto
          · have : x ∈ t \ ({u, v} : Finset V) := Finset.mem_sdiff.mpr ⟨hx, hxuv⟩
            rw [hw, Finset.mem_singleton] at this; simp [this]
        · rw [hclique.card_eq]
          have e1 := Finset.card_insert_le u (insert v {w} : Finset V)
          have e2 := Finset.card_insert_le v ({w} : Finset V)
          simp only [Finset.card_singleton] at e2
          omega
      exact this.symm

end LeanPool.DrossFractionalTriangleDecomposition
