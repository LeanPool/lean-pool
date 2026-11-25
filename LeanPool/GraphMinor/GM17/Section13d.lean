/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section13c
public import LeanPool.GraphMinor.GM17.SubdivideDraw
public import LeanPool.GraphMinor.GM17.VortexPortrayal
public import LeanPool.GraphMinor.GM16.Section7

import LeanPool.GraphMinor.GM16.MainProof

import LeanPool.GraphMinor.GM17.Section8Proved

/-!
# Graph Minors XVII, (13.1)

We prove (13.1) (page 202) from XVI (3.1). The route is the paper's. Given a graph `H`, we apply
(3.1). If `G` has no minor controlled by the tangle, then (3.1) gives a set `Z` of few vertices and
a
central segregation of `G \ Z` of type `(ρ, κ)` with a proper arrangement in a surface in which `H`
cannot be drawn. The arrangement gives a portrayal, by `exists_portrayal_of_arrangement`.

There is one change. The minors of (3.1) use edges of `G`, and those of XVII use edges of the simple
graph `G*`. If `H` has loops or parallel edges, then a minor in the first sense need not give a
minor in the second. So we apply (3.1) to the double subdivision of `H`, which is simple. A minor of
it gives a minor of `H` in `G*` (`controlsMinor_of_subdiv`), and if it cannot be drawn in a surface
then `H` cannot either (`canBeDrawnIn_subdiv`).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

/-- A hypergraph with a tangle of positive order has a vertex. If not, then `G` and its complement
have no vertices, so neither axiom (i) nor axiom (iii) can hold. -/
theorem nonempty_of_isTangle {α : Type u} {β : Type v} {G : Hypergraph α β} {θ : ℕ} {𝒯 : Set
  (Hypergraph α β × Hypergraph α β)} (ht : IsTangle G θ 𝒯) : Nonempty α := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have hsub : ∀ A B : Set α, A = B := fun A B => Subsingleton.elim A B
  have hord : separationOrder G (complSubhypergraph G G) < θ := by
    have h1 := ht.one_le
    have : separationOrder G (complSubhypergraph G G) = 0 := by
      rw [separationOrder, hsub (G ∩ complSubhypergraph G G).vertexSet ∅, Set.ncard_empty]
    omega
  rcases ht.axiom1 (isSeparation_complSubhypergraph le_rfl) hord with h | h
  · exact ht.axiom3 h (hsub _ _)
  · exact ht.axiom3 h (hsub _ _)

/-- Graph Minors XVII (13.1) (page 202), for graphs. Subdivide each edge of `H` twice before
applying XVI (3.1). The controlled minor of the subdivision then gives a controlled `H`-minor. -/
theorem theorem_13_1_proof : Theorem131Statement.{u, v} := by
  classical
  intro α' β' H hH
  have hex : ∀ e : ↥H.edgeSet, ∃ x y, H.ends e.1 = {x, y} := fun e => exists_ends hH e.2
  choose a b hab using hex
  have ha : ∀ e, a e ∈ H.vertexSet := fun e => H.vertex_mem_of_inc (e := e.1) (by
    change a e ∈ H.ends e.1
    rw [hab]
    exact Or.inl rfl)
  have hb : ∀ e, b e ∈ H.vertexSet := fun e => H.vertex_mem_of_inc (e := e.1) (by
    change b e ∈ H.ends e.1
    rw [hab]
    exact Or.inr rfl)
  have : Finite ↥H.edgeSet := H.edgeSet_finite.to_subtype
  have hVL : (subdiv H a b ha hb).vertexSet.Finite := (H.vertexSet_finite.image _).union
    (Set.finite_range _)
  have hEL : (subdiv H a b ha hb).edgeSet.Finite := Set.toFinite _
  obtain ⟨κ, ρ, ζ, θ₀, -, hL⟩ := GraphMinor.GM16.theorem_3_1_proof.{u, v, 0, 0, 0}
    (subdiv H a b ha hb) hVL hEL
  refine ⟨ρ + 1, κ, ζ, max θ₀ (ζ + max 3 (2 * (ρ + 1) + 2) + 1), by omega, ?_⟩
  intro α β G hG θ' 𝒯 ht hθ
  have hθ₁ : θ₀ ≤ θ' := (le_max_left _ _).trans hθ
  have hθ₂ : ζ + max 3 (2 * (ρ + 1) + 2) + 1 ≤ θ' := (le_max_right _ _).trans hθ
  have := nonempty_of_isTangle ht
  obtain ⟨Gr, hV, hE, rfl⟩ : ∃ (Gr : Graph α β) (hV : Gr.vertexSet.Finite)
    (hE : Gr.edgeSet.Finite), Hypergraph.ofGraph Gr hV hE = G :=
    ⟨toGraph G hG, G.vertexSet_finite, G.edgeSet_finite, ofGraph_toGraph G hG _ _⟩
  by_cases hc : GM16.ControlsMinor Gr (subdiv H a b ha hb) 𝒯
  · exact .inl (controlsMinor_of_subdiv hH hab ha hb hV hE hc)
  right
  obtain ⟨Z, Seg, Sp, _, _, D, ν, hZ, hZ₁, hZ₂, hS, hcon, hnd, hcent, hty, harr⟩
    := hL Gr θ' 𝒯 ⟨hV, hE, ht⟩ hθ₁ hc
  have hV' : (GM09.deleteVertices Gr Z).vertexSet.Finite := hV.subset
    (by simp [GM09.deleteVertices])
  have hE' : (GM09.deleteVertices Gr Z).edgeSet.Finite := hE.subset (Gr.induce_le
    sdiff_subset).edgeSet_mono
  have hπ := exists_portrayal_of_arrangement hS hV' hE' hty harr
  rw [GM16.ofGraph_deleteVertices_eq Gr hV hE Z hV' hE'] at hπ
  obtain ⟨π, ⟨j, hj⟩, hw, hq, hcell⟩ := hπ
  refine ⟨Z, hZ, hZ₁, π, ?_, hw, hq, fun hd => hnd (canBeDrawnIn_subdiv hab ha hb
    (CanBeDrawn.of_isEmbedding hj hd))⟩
  intro c hcC
  have ht' := GM10.theorem_8_5_proof hG ht hZ hZ₂
  have hle := π.cellGraph_le c hcC
  have hsep := isSeparation_complSubhypergraph hle
  have hord : separationOrder (π.cellGraph c) (complSubhypergraph ((ofGraph Gr hV
    hE).deleteVertices Z) (π.cellGraph c)) < θ' - Z.ncard := by
    rw [separationOrder_complSubhypergraph]
    have hsub := π.attachments_cellGraph_subset_otherVertices hcC
    have h1 := Set.ncard_le_ncard hsub ((π.cellGraph c).vertexSet_finite.inter_of_left _)
    have h2 := π.ncard_cell_inter_other_le hw hcC
    omega
  rcases ht'.axiom1 hsep hord with h | h
  · exact ⟨_, h⟩
  · obtain ⟨s, hs, hsub⟩ := hcell c hcC
    exact absurd hsub (hcent.2 hs h)

end GraphMinor.GM17
