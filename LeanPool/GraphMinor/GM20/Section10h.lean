/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10g

/-!
# Graph Minors XX, Section 10: the hull of a portrayal, continued

Let `π` be a portrayal of a rootless hypergraph `G`, with the properties that Graph Minors XVII
proves
for a true portrayal, and let `G'` be the heart of `(G, ℒ)`, for the location `ℒ` of Section10f.
Then `(Γ, β)` is a hull for `G'` (`hullOf`), and `(P, ℒ)` is shelled (`isShelled_of_portrayal`).
-/

@[expose] public section

namespace GraphMinor.GM17.Portrayal

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM20

universe u v

variable {α : Type u} {β : Type v} {P : UnlabeledPatchwork α β} {π : Portrayal P.G.toHypergraph}
  {e : RootedHypergraph α β → β} {Q : UnlabeledPatchwork α β}

theorem ends_cell (hdom : π.domγ = π.Γ.N) (hQ : IsPatchworkHeart P π.cellLocation e Q)
    {c : Set π.S} (hc : c ∈ π.Γ.C) : Q.G.ends (e (π.cellRooted c)) = π.rootsOf c := by
  rw [hQ.ends_newEdge ⟨c, hc, rfl⟩, rootSet_cellRooted hdom hc]

/-- A node's vertex is a vertex of the heart, since by (8.7) of Graph Minors XVII it is a root of
each
`A_c` that contains it. -/
theorem node_mem_heart (hdom : π.domγ = π.Γ.N)
    (h₈₇ : ∀ n ∈ π.Γ.N, ∃ c₁ ∈ π.Γ.C, ∃ c₂ ∈ π.Γ.C, c₁ ≠ c₂ ∧ n ∈ tilde c₁ ∧ n ∈ tilde c₂)
    (hQ : IsPatchworkHeart P π.cellLocation e Q) {n : π.S} (hn : n ∈ π.Γ.N) :
    π.nodeVertex n ∈ Q.G.vertexSet := by
  rw [hQ.vertexSet_eq, mem_core_iff]
  refine ⟨π.nodeVertex_mem n (hdom ▸ hn), ?_⟩
  rintro _ ⟨c, hc, rfl⟩ hv
  rw [rootSet_cellRooted hdom hc]
  obtain ⟨c₁, hc₁, c₂, hc₂, hne, h₁, h₂⟩ := h₈₇ n hn
  by_cases h : c₁ = c
  · have hne' : c₂ ≠ c := fun h' ↦ hne (h.trans h'.symm)
    exact mem_rootsOf_of_other hdom hc hc₂ hne' hv (π.p2 c₂ hc₂ n ⟨h₂, hdom ▸ hn⟩)
  · exact mem_rootsOf_of_other hdom hc hc₁ h hv (π.p2 c₁ hc₁ n ⟨h₁, hdom ▸ hn⟩)

/-- For a node `n` on the boundary, `β(n)` lies in `V(G')`, since `n ∈ cTilde` for a border cell
`c`. -/
theorem border_mem_heart (hdom : π.domγ = π.Γ.N) (hr : P.G.rootSet = ∅)
    (h₂ : ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) (hQ : IsPatchworkHeart P π.cellLocation e Q)
    {n : π.S} (hn : n ∈ π.Γ.N ∩ bd π.S) : π.borderSet n ⊆ Q.G.vertexSet := by
  intro v hv
  obtain ⟨Θ, hΘ, hnΘ⟩ := exists_cuff_of_bd hn.2
  obtain ⟨c, hc, -, -, -, hnc, -, hcΘ, -⟩ :=
    exists_two_cells π.isSurface (π.paintingOf' h₂) hΘ ⟨hn.1, hnΘ⟩
  rw [hQ.vertexSet_eq]
  have hroot : v ∈ (π.cellRooted c).rootSet := by
    rw [rootSet_cellRooted hdom hc]
    obtain ⟨x, hxc, hxΘ⟩ := hcΘ
    exact Or.inr ⟨⟨x, hxc, cuff_subset_bd hΘ hxΘ⟩, n, hnc, hv⟩
  exact root_mem_core (isRootedLocation hdom hr) ⟨c, hc, rfl⟩ hroot

/-- `(Γ, β)` is a `(Σ, ρ)`-hull for the heart `G'`. -/
noncomputable def hullOf (hdom : π.domγ = π.Γ.N) (hr : P.G.rootSet = ∅)
    (h₂ : ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard)
    (h₈₇ : ∀ n ∈ π.Γ.N, ∃ c₁ ∈ π.Γ.C, ∃ c₂ ∈ π.Γ.C, c₁ ≠ c₂ ∧ n ∈ tilde c₁ ∧ n ∈ tilde c₂)
    (hbd : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → ∀ n ∈ tilde c,
      Disjoint (π.borderSet n) (π.nodeVertex '' π.Γ.N))
    (hρ : ∀ Θ ∈ cuffs π.S, ∀ c ∈ π.Γ.C, (c ∩ Θ).Nonempty → ∀ n ∈ tilde c,
      (π.borderSet n).ncard = π.warpAt Θ)
    (he : InjOn e π.cellLocation) (hinj : InjOn π.cellRooted π.Γ.C)
    (hQ : IsPatchworkHeart P π.cellLocation e Q) (hE : Q.G.edgeSet = e '' π.cellLocation) :
    Hull (X := π.gradedOf) (π.paintingOf' h₂) Q.G.toHypergraph where
  node := π.nodeVertex
  cell := fun c ↦ e (π.cellRooted c)
  border := π.borderSet
  node_injOn := by
    have h := π.nodeVertex_injOn
    rw [hdom] at h
    exact h
  node_mem _ hn := node_mem_heart hdom h₈₇ hQ hn
  cell_bijOn := by
    refine ⟨fun c hc ↦ ?_, fun c₁ h₁ c₂ h₂' h ↦ hinj h₁ h₂' (he ⟨c₁, h₁, rfl⟩ ⟨c₂, h₂', rfl⟩ h), ?_⟩
    · rw [hE]
      exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    · intro f hf
      rw [hE] at hf
      obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hf
      exact ⟨c, hc, rfl⟩
  inc_iff n hn c hc := by
    have h := ends_cell hdom hQ hc
    change n ∈ tilde c ↔ π.nodeVertex n ∈ Q.G.ends (e (π.cellRooted c))
    rw [h]
    refine ⟨fun h ↦ Or.inl ⟨n, h, rfl⟩, ?_⟩
    rintro (⟨m, hm, hmn⟩ | ⟨hb, m, hm, hv⟩)
    · have hmN : m ∈ π.Γ.N := tilde_subset_nodes π.Γ hc hm
      rwa [π.nodeVertex_injOn (hdom ▸ hmN) (hdom ▸ hn) hmn] at hm
    · exact (Set.disjoint_left.mp (hbd c hc hb m hm) hv ⟨n, hn, rfl⟩).elim
  border_subset _ hn := border_mem_heart hdom hr h₂ hQ hn
  border_disjoint n hn := by
    obtain ⟨Θ, hΘ, hnΘ⟩ := exists_cuff_of_bd hn.2
    obtain ⟨c, hc, -, -, -, hnc, -, ⟨x, hxc, hxΘ⟩, -⟩ :=
      exists_two_cells π.isSurface (π.paintingOf' h₂) hΘ ⟨hn.1, hnΘ⟩
    exact hbd c hc ⟨x, hxc, cuff_subset_bd hΘ hxΘ⟩ n hnc
  border_ncard Θ hΘ n hn := by
    obtain ⟨c, hc, -, -, -, hnc, -, hcΘ, -⟩ :=
      exists_two_cells π.isSurface (π.paintingOf' h₂) hΘ hn
    exact hρ Θ hΘ c hc hcΘ n hnc
  border_cuffs := π.p4_disjoint
  vertexSet_eq := by
    apply Subset.antisymm
    · intro v hv
      rw [hQ.vertexSet_eq, mem_core_iff] at hv
      obtain ⟨hvG, hroot⟩ := hv
      obtain ⟨c, hc, hvc⟩ := π.p1_vertex v hvG
      have h := hroot _ ⟨c, hc, rfl⟩ hvc
      rw [rootSet_cellRooted hdom hc] at h
      rcases h with ⟨n, hn, rfl⟩ | ⟨hb, n, hn, hv⟩
      · exact Or.inl ⟨n, tilde_subset_nodes π.Γ hc hn, rfl⟩
      · exact Or.inr (mem_biUnion (x := n) ⟨tilde_subset_nodes π.Γ hc hn,
          tilde_subset_bd hc hb hn⟩ hv)
    · rintro v (⟨n, hn, rfl⟩ | hv)
      · exact node_mem_heart hdom h₈₇ hQ hn
      · obtain ⟨n, hn, hv⟩ := mem_iUnion₂.mp hv
        exact border_mem_heart hdom hr h₂ hQ hn hv
  ends_internal c hc hb := by
    rw [ends_cell hdom hQ hc]
    ext v
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact (hb h).elim
    · exact Or.inl
  ends_border c hc hb := by
    rw [ends_cell hdom hQ hc]
    ext v
    constructor
    · rintro (h | ⟨-, n, hn, hv⟩)
      · exact Or.inl h
      · exact Or.inr (mem_biUnion hn hv)
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨n, hn, hv⟩ := mem_iUnion₂.mp h
        exact Or.inr ⟨hb, n, hn, hv⟩
  border_order Θ hΘ n₁ h₁ n₂ h₂' n₃ h₃ n₄ h₄ hord v hv := by
    have hdisj : v ∉ π.nodeVertex '' π.Γ.N := by
      obtain ⟨c, hc, -, -, -, hnc, -, ⟨x, hxc, hxΘ⟩, -⟩ :=
        exists_two_cells π.isSurface (π.paintingOf' h₂) hΘ h₁
      exact Set.disjoint_left.mp (hbd c hc ⟨x, hxc, cuff_subset_bd hΘ hxΘ⟩ n₁ hnc) hv.1
    rcases π.p7 Θ hΘ n₁ h₁ n₂ h₂' n₃ h₃ n₄ h₄ hord v (Or.inl hv.1) (Or.inl hv.2) with
      (h | ⟨-, h⟩) | (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact (hdisj ⟨n₂, h₂'.1, h.symm⟩).elim
    · exact Or.inr h
    · exact (hdisj ⟨n₄, h₄.1, h.symm⟩).elim

end GraphMinor.GM17.Portrayal
