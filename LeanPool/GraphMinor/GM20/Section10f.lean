/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10e
public import LeanPool.GraphMinor.GM20.Section5d

/-!
# Graph Minors XX, Section 10: the location of a portrayal

The proof of (10.3) takes a portrayal `π = (Σ, Γ, α, β, γ)` of a rootless hypergraph `G` and makes a
rooted hypergraph `A_c` for each cell `c`. It has `A_c⁻ = α(c)`. Its march lists `γ(cTilde)` for an
internal
cell, and `γ(cTilde) ∪ β(n₁) ∪ β(n₂)` for a border cell with nodes `n₁, n₂`. This file shows that
the set of
all `A_c` is a fine rooted location. The axioms (P1), (P2), (P3), (P5), (P6) of a portrayal give
this: a vertex of `α(c)` that lies in another `α(c')` is a root of `A_c`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18

universe u v

variable {α : Type u} {β : Type v}

/-- A list of the members of a set, if the set is finite. -/
noncomputable def listOf {X : Type*} (s : Set X) : List X :=
  open Classical in if h : s.Finite then h.toFinset.toList else []

theorem nodup_listOf {X : Type*} (s : Set X) : (listOf s).Nodup := by
  classical
  unfold listOf
  split_ifs with h
  · exact Finset.nodup_toList _
  · exact List.nodup_nil

theorem mem_listOf {X : Type*} {s : Set X} (h : s.Finite) {x : X} : x ∈ listOf s ↔ x ∈ s := by
  classical
  simp [listOf, h]

end GraphMinor.GM20

namespace GraphMinor.GM17.Portrayal

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM20

universe u v

variable {α : Type u} {β : Type v}

variable {G₀ : RootedHypergraph α β} (π : Portrayal G₀.toHypergraph)

/-- The set `πBar(A_c)` of roots of the rooted hypergraph of a cell `c`. -/
def rootsOf (c : Set π.S) : Set α :=
  π.nodeVertex '' tilde c ∪ {v | (c ∩ bd π.S).Nonempty ∧ ∃ n ∈ tilde c, v ∈ π.borderSet n}

/-- The march of a cell before removing the terms outside `V(α(c))`: the list `γ(n)` for `n` in the
march of `c` if `c` is internal, and any list of the roots if `c` is a border cell. -/
noncomputable def rawMarch (c : Set π.S) : List α :=
  open Classical in
  if (c ∩ bd π.S).Nonempty then listOf (π.rootsOf c) else (listOf (tilde c)).map π.nodeVertex

/-- The rooted hypergraph `A_c` of a cell `c`. The filter and `dedup` do nothing for a cell, by
`rootSet_cellRooted`. They only make the definition total. -/
noncomputable def cellRooted (c : Set π.S) : RootedHypergraph α β where
  toHypergraph := π.cellGraph c
  roots := open Classical in ((π.rawMarch c).filter (· ∈ (π.cellGraph c).vertexSet)).dedup
  roots_nodup := by
    classical
    exact List.nodup_dedup _
  roots_subset v hv := by
    classical
    have h := List.mem_dedup.mp hv
    simpa using (List.mem_filter.mp h).2

/-- The rooted location `ℒ = {A_c : c ∈ C(Γ)}`. -/
noncomputable def cellLocation : Set (RootedHypergraph α β) := π.cellRooted '' π.Γ.C

variable {π}

theorem tilde_finite {c : Set π.S} (hc : c ∈ π.Γ.C) : (tilde c).Finite :=
  (π.Γ.cell_disc c hc).2.2.1

/-- (P2), (P3): the roots of a cell are vertices of `α(c)`. -/
theorem rootsOf_subset (hdom : π.domγ = π.Γ.N) {c : Set π.S} (hc : c ∈ π.Γ.C) :
    π.rootsOf c ⊆ (π.cellGraph c).vertexSet := by
  rintro v (⟨n, hn, rfl⟩ | ⟨hb, n, hn, hv⟩)
  · exact π.p2 c hc n ⟨hn, hdom ▸ tilde_subset_nodes π.Γ hc hn⟩
  · exact π.p3_subset c hc hb n hn hv

theorem rootsOf_finite (hdom : π.domγ = π.Γ.N) {c : Set π.S} (hc : c ∈ π.Γ.C) :
    (π.rootsOf c).Finite :=
  (π.cellGraph c).vertexSet_finite.subset (rootsOf_subset hdom hc)

theorem rootSet_cellRooted (hdom : π.domγ = π.Γ.N) {c : Set π.S} (hc : c ∈ π.Γ.C) :
    (π.cellRooted c).rootSet = π.rootsOf c := by
  classical
  ext v
  change v ∈ ((π.rawMarch c).filter (· ∈ (π.cellGraph c).vertexSet)).dedup ↔ _
  rw [List.mem_dedup, List.mem_filter]
  have hsub := rootsOf_subset hdom hc
  have key : v ∈ π.rawMarch c ↔ v ∈ π.rootsOf c := by
    unfold rawMarch
    split_ifs with hb
    · exact mem_listOf (rootsOf_finite hdom hc)
    · simp only [List.mem_map, mem_listOf (tilde_finite hc)]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact Or.inl ⟨n, hn, rfl⟩
      · rintro (⟨n, hn, rfl⟩ | ⟨hb', -⟩)
        · exact ⟨n, hn, rfl⟩
        · exact absurd hb' hb
  rw [key]
  simp only [decide_eq_true_eq]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hsub h⟩⟩

/-- An internal cell has the march `γ(n)`, for `n` in the chosen march of `c`. -/
theorem roots_cellRooted_internal (hdom : π.domγ = π.Γ.N) {c : Set π.S} (hc : c ∈ π.Γ.C)
    (hb : ¬ (c ∩ bd π.S).Nonempty) :
    (π.cellRooted c).roots = (listOf (tilde c)).map π.nodeVertex := by
  classical
  change ((π.rawMarch c).filter (· ∈ (π.cellGraph c).vertexSet)).dedup = _
  have hraw : π.rawMarch c = (listOf (tilde c)).map π.nodeVertex := by
    unfold rawMarch
    rw [ite_eq_right hb]
  have hsub : tilde c ⊆ π.domγ := hdom ▸ tilde_subset_nodes π.Γ hc
  have hnd : ((listOf (tilde c)).map π.nodeVertex).Nodup := by
    refine (nodup_listOf _).map_on fun x hx y hy hxy ↦ ?_
    exact π.nodeVertex_injOn (hsub ((mem_listOf (tilde_finite hc)).mp hx))
      (hsub ((mem_listOf (tilde_finite hc)).mp hy)) hxy
  rw [hraw, List.filter_eq_self.mpr, List.dedup_eq_self.mpr hnd]
  intro v hv
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hv
  have := rootsOf_subset hdom hc (Or.inl ⟨n, (mem_listOf (tilde_finite hc)).mp hn, rfl⟩)
  simpa using this

/-- (P5), (P6): a vertex of `α(c)` that lies in `α(c')` for another cell `c'` is a root of `A_c`. -/
theorem mem_rootsOf_of_other (_hdom : π.domγ = π.Γ.N) {c c' : Set π.S} (hc : c ∈ π.Γ.C)
    (hc' : c' ∈ π.Γ.C) (hne : c' ≠ c) {v : α} (hv : v ∈ (π.cellGraph c).vertexSet)
    (hv' : v ∈ (π.cellGraph c').vertexSet) : v ∈ π.rootsOf c := by
  by_cases hb : (c ∩ bd π.S).Nonempty
  · obtain ⟨n, hn, h | ⟨-, rfl⟩⟩ := π.p6 c hc hb v hv ⟨c', hc', hne, hv'⟩
    · exact Or.inr ⟨hb, n, hn, h⟩
    · exact Or.inl ⟨n, hn, rfl⟩
  · obtain ⟨n, ⟨hn, -⟩, rfl⟩ := π.p5 c hc hb v hv ⟨c', hc', hne, hv'⟩
    exact Or.inl ⟨n, hn, rfl⟩

/-- If an edge of `G` lies in `α(c')`, each of its ends in `G` lies in `α(c')`. -/
theorem vertex_mem_of_inc {c' : Set π.S} (hc' : c' ∈ π.Γ.C) {e : β} {v : α}
    (he : e ∈ (π.cellGraph c').edgeSet) (hv : G₀.Inc e v) :
    v ∈ (π.cellGraph c').vertexSet := by
  have hle := π.cellGraph_le c' hc'
  have h : v ∈ (π.cellGraph c').ends e := by
    rw [← hle.ends_eq e he]
    exact hv
  exact (π.cellGraph c').vertex_mem_of_inc h

theorem isComplemented_cellRooted (hdom : π.domγ = π.Γ.N) (hr : G₀.rootSet = ∅) {c : Set π.S}
    (hc : c ∈ π.Γ.C) : IsComplemented G₀ (π.cellRooted c) where
  le := π.cellGraph_le c hc
  roots_mem v _ hv := by
    rw [hr] at hv
    exact hv.elim
  inc_diff_mem v e hv he hinc := by
    obtain ⟨c', hc', hec'⟩ := π.p1_edge e he.1
    have hne : c' ≠ c := by
      rintro rfl
      exact he.2 hec'
    rw [rootSet_cellRooted hdom hc]
    exact mem_rootsOf_of_other hdom hc hc' hne hv (vertex_mem_of_inc hc' hec' hinc)

/-- `ℒ = {A_c}` is a rooted location: for distinct `c, c'` the vertices shared by `α(c')` and
`α(c)` are roots of `A_c` and the edges of `α(c)`, `α(c')` are disjoint by (P1). -/
theorem isRootedLocation (hdom : π.domγ = π.Γ.N) (hr : G₀.rootSet = ∅) :
    IsRootedLocation G₀ π.cellLocation where
  isComplemented := by
    rintro _ ⟨c, hc, rfl⟩
    exact isComplemented_cellRooted hdom hr hc
  le_complement := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
    have hc₁₂ : c₁ ≠ c₂ := fun h ↦ hne (by rw [h])
    have hle₁ := π.cellGraph_le c₁ hc₁
    have hedge : ∀ e ∈ (π.cellGraph c₁).edgeSet, e ∉ (π.cellGraph c₂).edgeSet := fun e he he₂ ↦
      Set.disjoint_left.mp (π.p1_disjoint c₁ hc₁ c₂ hc₂ hc₁₂) he he₂
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      by_cases hv₂ : v ∈ (π.cellGraph c₂).vertexSet
      · refine Or.inr ?_
        rw [rootSet_cellRooted hdom hc₂]
        exact mem_rootsOf_of_other hdom hc₂ hc₁ hc₁₂ hv₂ hv
      · exact Or.inl ⟨hle₁.vertexSet_subset hv, hv₂⟩
    · exact fun e he ↦ ⟨hle₁.edgeSet_subset he, hedge e he⟩
    · intro e he
      have hE : ∀ v, v ∈ G₀.ends e ↔ v ∈ (π.cellGraph c₁).ends e := fun v ↦ by
        rw [hle₁.ends_eq e he]
      ext v
      exact ⟨fun ⟨_, h⟩ ↦ (hE v).mp h, fun h ↦ ⟨⟨hle₁.edgeSet_subset he, hedge e he⟩, (hE v).mpr h⟩⟩

/-- (P1): `ℒ` is fine. -/
theorem isFine_cellLocation : IsFine G₀ π.cellLocation := by
  refine ⟨fun v hv ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨c, hc, h⟩ := π.p1_vertex v hv
    exact ⟨_, ⟨c, hc, rfl⟩, h⟩
  · obtain ⟨c, hc, h⟩ := π.p1_edge e he
    exact ⟨_, ⟨c, hc, rfl⟩, h⟩

theorem cellLocation_finite : π.cellLocation.Finite := π.Γ.finite_cells.image _

/-- The rooted hypergraphs of distinct cells are different. The roots that are images of nodes
determine `cTilde`, and two cells with the same `cTilde` are excluded by (8.8) of Graph Minors XVII.
This is where
the hypotheses `h₂`, `h₃` are used. -/
theorem injOn_cellRooted (hdom : π.domγ = π.Γ.N)
    (hbd : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → ∀ n ∈ tilde c,
      Disjoint (π.borderSet n) (π.nodeVertex '' π.Γ.N))
    (hsize : ∀ c ∈ π.Γ.C, (c ∩ bd π.S).Nonempty → (tilde c).ncard = 2)
    (h₈₈ : ∀ c₁ ∈ π.Γ.C, ∀ c₂ ∈ π.Γ.C, c₁ ≠ c₂ → tilde c₁ ⊆ tilde c₂ →
      (c₁ ∩ bd π.S).Nonempty ∧ (tilde c₂).ncard = 3) :
    InjOn π.cellRooted π.Γ.C := by
  intro c₁ hc₁ c₂ hc₂ heq
  by_contra hne
  have hroots : π.rootsOf c₁ = π.rootsOf c₂ := by
    rw [← rootSet_cellRooted hdom hc₁, ← rootSet_cellRooted hdom hc₂, heq]
  have hsub : ∀ {c c' : Set π.S}, c ∈ π.Γ.C → c' ∈ π.Γ.C → π.rootsOf c = π.rootsOf c' →
      tilde c ⊆ tilde c' := by
    intro c c' hc hc' h n hn
    have hnN := tilde_subset_nodes π.Γ hc hn
    have hmem : π.nodeVertex n ∈ π.rootsOf c' := h ▸ Or.inl ⟨n, hn, rfl⟩
    rcases hmem with ⟨m, hm, hmn⟩ | ⟨hb, m, hm, hv⟩
    · have hmN := tilde_subset_nodes π.Γ hc' hm
      rw [π.nodeVertex_injOn (hdom ▸ hmN) (hdom ▸ hnN) hmn] at hm
      exact hm
    · exact (Set.disjoint_left.mp (hbd c' hc' hb m hm) hv ⟨n, hnN, rfl⟩).elim
  obtain ⟨hb, h₃⟩ := h₈₈ c₁ hc₁ c₂ hc₂ hne (hsub hc₁ hc₂ hroots)
  have heq' : tilde c₁ = tilde c₂ := (hsub hc₁ hc₂ hroots).antisymm (hsub hc₂ hc₁ hroots.symm)
  have := hsize c₁ hc₁ hb
  rw [heq'] at this
  omega

end GraphMinor.GM17.Portrayal
