/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetExistsLines
public import LeanPool.GraphMinor.GM07.NetExistsWord
public import LeanPool.GraphMinor.GM07.MinimalNet
public import LeanPool.GraphMinor.GM11.EdgeSides

/-!
# A minimal net exists

Graph Minors VII, page 216: "It is easy to see that if $\Sigma$ is connected and $G$ is a proper
graph in $\Sigma$, there is a $G$-normal net."
We follow the three steps of the sketch there. Cut along the graph and write each component as a
polygon: its added edges avoid the graph
(`GM07/NetExistsHole.lean`). Cut the polygons so that each one has at most one side on an edge of
`G`, and paste along the edges of `G`,
which gives the discs of the sketch (`GM07/NetExistsGlue.lean`). Paste these discs into one polygon
(`exists_one_word_off`). Its boundary
meets `G` only in `V(G)`, so the polygon is a `G`-normal net (`exists_net_of_word`), and
`Net.exists_isMinimalFor` gives a minimal one.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

theorem arcComponentsIn_eq_of_mem {S : Type u} [TopologicalSpace S] {F C D : Set S}
  (hC : C ∈ arcComponentsIn F) (hD : D ∈ arcComponentsIn F) {x : S}
    (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  have h1 : IsPathConnected (C ∪ D) := hC.2.2.1.union hD.2.2.1 ⟨x, hxC, hxD⟩
  have h2 := hC.2.2.2 (C ∪ D) (union_subset hC.2.1 hD.2.1) h1 subset_union_left
  have h3 := hD.2.2.2 (C ∪ D) (union_subset hC.2.1 hD.2.1) h1 subset_union_right
  exact h2.symm.trans h3

/-- **A minimal net exists.** Graph Minors VII, page 216: a connected surface with at least two
cuffs has, for each proper graph `G`, a
minimal net. -/
theorem exists_minimal_net : ∀ (S : Type u) [TopologicalSpace S], IsSurface S
  → ConnectedSpace S → 2 ≤ (cuffs S).ncard →
    ∀ G : Drawing S, G.IsProper → ∃ N : Net S, N.IsMinimalFor G := by
  intro S _ hS _ hc G hG
  have : T2Space S := hS.2.1
  have hfin : Finite G.E := G.finite_edges.to_subtype
  have hp := fun e : G.E => GM11.exists_edge_param G e.2
  choose γ c1 c2 c3 c4 c5 using hp
  set c : G.E → ℝ → S := fun e => extI (γ e) with hc'
  have hIoo : ∀ {u : ℝ}, u ∈ Ioo (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 := fun hu => ⟨hu.1.le, hu.2.le⟩
  have hval : ∀ e, ∀ u (hu : u ∈ Ioo (0 : ℝ) 1), c e u = γ e ⟨u, hIoo hu⟩ := fun e u hu
    => extI_of_mem _ (hIoo hu)
  have hI : ∀ {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1), (⟨u, hIoo hu⟩ : unitInterval) ∈ Ioo
    (0 : unitInterval) 1 := fun hu => ⟨hu.1, hu.2⟩
  have hmem : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∈ e.1 := fun e u hu => by
    rw [hval e u hu, ← c5 e]
    exact mem_image_of_mem _ (hI hu)
  have hsub : ∀ e : G.E, e.1 ⊆ G.U \ G.V := fun e => e.2.2.1
  have hoff : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ G.V := fun e u hu => (hsub e (hmem e u hu)).2
  have h0 : ∀ e, c e 0 ∈ G.V := fun e => by
    rw [hc']
    simp only
    rw [extI_of_mem _ (by simp)]
    exact c2 e
  have h1 : ∀ e, c e 1 ∈ G.V := fun e => by
    rw [hc']
    simp only
    rw [extI_of_mem _ (by simp)]
    exact c3 e
  have hinj : ∀ e, InjOn (c e) (Ioo 0 1) := fun e u hu v hv he => by
    rw [hval e u hu, hval e v hv] at he
    exact congrArg Subtype.val (c4 e (hI hu) (hI hv) he)
  have hdis : ∀ e e', e ≠ e' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Ioo (0 : ℝ) 1, c e u ≠ c e' v
    := fun e e' hne u hu v hv he =>
    hne (Subtype.ext (arcComponentsIn_eq_of_mem e.2 e'.2 (hmem e u hu) (he ▸ hmem e' v hv)))
  have hbd : ∀ e, ∀ u ∈ Ioo (0 : ℝ) 1, c e u ∉ bd S := fun e u hu hb =>
    hoff e u hu (hG ⟨hb, (hsub e (hmem e u hu)).1⟩)
  obtain ⟨Y, t1, t2, κ, f, a, inner, ψ, ξ, η, hY, hC, hk⟩ := exists_edges_cut hS (fun e
    => continuous_extI (c1 e)) hinj h0 h1 hoff hdis hbd
  have hB : ∀ x ∈ G.U \ G.V, ∃ k, inner k ∧ ∃ u ∈ Ioo (0 : ℝ) 1, x = a k u := fun x hx => by
    have hxe : pathComponentIn (G.U \ G.V) x ∈ G.E := pathComponentIn_mem_arcComponentsIn hx
    have hx' : x ∈ (⟨_, hxe⟩ : G.E).1 := mem_pathComponentIn_self hx
    rw [← c5 ⟨_, hxe⟩] at hx'
    obtain ⟨⟨u, hu⟩, hu', he⟩ := hx'
    have hu2 : u ∈ Ioo (0 : ℝ) 1 := ⟨hu'.1, hu'.2⟩
    obtain ⟨k, h2, h3⟩ := hk ⟨_, hxe⟩
    refine ⟨k, h2, u, hu2, ?_⟩
    rw [h3 u hu2]
    exact he.symm.trans (hval _ u hu2).symm
  obtain ⟨w, g, h2, h3, h4, h5⟩ := exists_off_word_of_cut hC hY hB
  obtain ⟨N, hr, hseam⟩ := exists_net_of_word hS hc h2 h3 h4
  obtain ⟨J, hJ⟩ := Net.exists_isSeamGraphFor hS N hr
  refine Net.exists_isMinimalFor ⟨J, hJ, ?_⟩
  rintro x ⟨hx, hxU⟩
  rw [hJ.2.1] at hx
  obtain ⟨z, hz, rfl⟩ := hseam hx
  by_contra hn
  exact h5 z hz ⟨hxU, hn⟩

end GraphMinor.GM07
