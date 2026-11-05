/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Basic
public import LeanPool.Erdos111.Statement

/-!
# The challenge definitions in terms of edge costs

`bipartizationNumber H` counts the deletions that make the subgraph `H` bipartite, while
`edgeCost` minimizes the monochromatic edges over sign assignments. Deleting the
monochromatic edges of a sign assignment leaves a bipartite graph, and a 2-coloring of
what remains after deleting `D` leaves every monochromatic edge in `D`, so the two
agree. Hence the hypothesis of the challenge is `C`-linearity, and every finite edge set
of `G` on `n` vertices bounds `h G n` from below.
-/

@[expose] public section

open scoped NNReal

namespace Erdos111

variable {V : Type*} {G : SimpleGraph V}

/-- A finite edge set of `G` with ends in `s` is the edge set of a subgraph on `s`. -/
private theorem exists_subgraph {s : Finset V} {E : Finset (Sym2 V)} (hE : ↑E ⊆ G.edgeSet)
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) :
    ∃ H : G.Subgraph, H.verts = ↑s ∧ H.edgeSet = ↑E := by
  refine ⟨{ verts := ↑s
            Adj := fun a b => s(a, b) ∈ E
            adj_sub := fun h => hE h
            edge_vert := fun h => hEs _ h _ (Sym2.mem_mk_left _ _)
            symm := ⟨fun a b h => by rwa [Sym2.eq_swap]⟩ }, rfl, ?_⟩
  ext e
  induction e using Sym2.ind with
  | _ a b => exact Iff.rfl

/-- The number of deletions that make a finite subgraph bipartite is the edge cost of its
edge set. -/
theorem bipartizationNumber_eq_edgeCost (H : G.Subgraph) (E : Finset (Sym2 V))
    (hE : (E : Set (Sym2 V)) = H.edgeSet) :
    bipartizationNumber H = edgeCost E := by
  classical
  -- The monochromatic edges of a sign assignment are a feasible deletion.
  have hmem : ∀ σ : V → Bool, monoCount E σ ∈ {k : ℕ | ∃ D ⊆ H.edgeSet, D.ncard = k ∧
      (H.deleteEdges D).coe.IsBipartite} := by
    intro σ
    refine ⟨↑(E.filter (mono σ)), ?_, by rw [Set.ncard_coe_finset]; rfl, ?_⟩
    · rw [← hE]
      exact Finset.coe_subset.2 (Finset.filter_subset _ _)
    · have hc := (SimpleGraph.Coloring.mk (G := (H.deleteEdges (E.filter (mono σ) : Set _)).coe)
        (fun v => σ v) ?_).colorable
      · simpa using hc
      intro a b hab heq
      rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteEdges_adj] at hab
      apply hab.2
      have he : s(a.1, b.1) ∈ E := by
        rw [← Finset.mem_coe, hE]
        exact hab.1
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨he, heq⟩
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := exists_monoCount_eq_edgeCost E
    rw [← hσ]
    exact Nat.sInf_le (hmem σ)
  · obtain ⟨D, hD, hDk, ⟨c⟩⟩ := Nat.sInf_mem ⟨_, hmem fun _ => false⟩
    rw [bipartizationNumber, ← hDk]
    -- A 2-coloring of the rest leaves every monochromatic edge in `D`.
    let σ : V → Bool := fun v => if hv : v ∈ H.verts then finTwoEquiv (c ⟨v, hv⟩) else false
    have hDfin : D.Finite := (Set.Finite.subset (E.finite_toSet) (hE ▸ hD))
    refine (edgeCost_le_monoCount E σ).trans ?_
    rw [monoCount, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ hDfin
    intro e he
    rw [Finset.coe_filter] at he
    obtain ⟨heE, hmono⟩ := he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : H.Adj a b := by
        rw [← SimpleGraph.Subgraph.mem_edgeSet, ← hE]
        exact heE
      have ha := H.edge_vert hadj
      have hb := H.edge_vert hadj.symm
      by_contra hnot
      have hadj' : (H.deleteEdges D).coe.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
        rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteEdges_adj]
        exact ⟨hadj, hnot⟩
      apply c.valid hadj'
      have hab : σ a = σ b := hmono
      simpa [σ, ha, hb] using hab

/-- The hypothesis of the challenge is `C`-linearity. -/
theorem linear_of_bipartizationNumber_le {C : ℝ}
    (hC : ∀ H : G.Subgraph, H.verts.Finite →
      (bipartizationNumber H : ℝ) ≤ C * H.verts.ncard) :
    Linear G C.toNNReal := by
  intro s E hE hEs
  obtain ⟨H, hv, he⟩ := exists_subgraph hE hEs
  have hfin : H.verts.Finite := by
    rw [hv]
    exact s.finite_toSet
  have h1 := hC H hfin
  rw [bipartizationNumber_eq_edgeCost H E he.symm, hv, Set.ncard_coe_finset] at h1
  rw [← NNReal.coe_le_coe]
  push_cast
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  rw [Real.coe_toNNReal']
  exact le_max_left _ _

/-- A finite edge set of `G` with ends in `s` bounds `h G s.card` from below. -/
theorem edgeCost_le_h {s : Finset V} {E : Finset (Sym2 V)} (hE : ↑E ⊆ G.edgeSet)
    (hEs : ∀ e ∈ E, ∀ v ∈ e, v ∈ s) : edgeCost E ≤ h G s.card := by
  classical
  obtain ⟨H, hv, he⟩ := exists_subgraph hE hEs
  have hfin : H.verts.Finite := by
    rw [hv]
    exact s.finite_toSet
  apply le_csSup
  · -- A subgraph on `n` vertices has at most `(n + 1).choose 2` edges.
    refine ⟨(s.card + 1).choose 2, ?_⟩
    rintro k ⟨H', hH', hn, rfl⟩
    rw [bipartizationNumber_eq_edgeCost H' (hH'.toFinset.sym2.filter (· ∈ H'.edgeSet))]
    · calc edgeCost _ ≤ monoCount _ fun _ => false := edgeCost_le_monoCount _ _
        _ ≤ (hH'.toFinset.sym2.filter (· ∈ H'.edgeSet)).card := Finset.card_filter_le _ _
        _ ≤ hH'.toFinset.sym2.card := Finset.card_filter_le _ _
        _ = (s.card + 1).choose 2 := by
          rw [Finset.card_sym2, ← Set.ncard_eq_toFinset_card _ hH', hn]
    · ext e
      simp only [Finset.coe_filter, Finset.mem_sym2_iff, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h => ⟨fun v hv => H'.mem_verts_of_mem_edge h hv, h⟩⟩
  · exact ⟨H, hfin, by rw [hv, Set.ncard_coe_finset],
      bipartizationNumber_eq_edgeCost H E he.symm⟩

end Erdos111
