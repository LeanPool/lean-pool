/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.StructuralGraphClasses.ChordalBridge
public import Mathlib.Data.Finset.Image

/-!
# Operations on existing chordal certificates

The existing chordal predicate, perfect elimination orders and clique forests
are reused. Restriction keeps the given order and forest topology, including
empty bags and multiple roots; no new certificate is selected by choice.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Isomorphisms preserve chordality without an ambient finiteness assumption. -/
theorem Iso.isChordal_iff (f : G ≃g H) : G.IsChordal ↔ H.IsChordal := by
  constructor
  · intro h
    have h' := h.comap f.symm.toEmbedding.toEmbedding
    change (G.comap f.symm.toEmbedding).IsChordal at h'
    rwa [f.symm.toEmbedding.comap_eq] at h'
  · intro h
    have h' := h.comap f.toEmbedding.toEmbedding
    change (H.comap f.toEmbedding).IsChordal at h'
    rwa [f.toEmbedding.comap_eq] at h'

/-- Pull back the supplied elimination ranking along an injective map. -/
theorem IsPEO.comap {ord : V → ℕ} (h : G.IsPEO ord) (f : W ↪ V) :
    (G.comap f).IsPEO (ord ∘ f) where
  injective := h.injective.comp f.injective
  isClique_later := by
    intro v a ha b hb hab
    exact h.isClique_later (f v) ha hb (fun he => hab (f.injective he))

/-- Restrict a perfect elimination order without changing surviving ranks. -/
theorem IsPEO.induce {ord : V → ℕ} (h : G.IsPEO ord) (s : Set V) :
    (G.induce s).IsPEO (ord ∘ Subtype.val) := h.comap (Function.Embedding.subtype s)

/-- Relabel a perfect elimination order along an isomorphism. -/
theorem IsPEO.mapIso {ord : V → ℕ} (h : G.IsPEO ord) (f : G ≃g H) :
    H.IsPEO (ord ∘ f.symm) := by
  have h' := h.comap f.symm.toEmbedding.toEmbedding
  change (G.comap f.symm.toEmbedding).IsPEO (ord ∘ f.symm) at h'
  rwa [f.symm.toEmbedding.comap_eq] at h'

namespace CliqueTree

variable {ι : Type*}

/-- Restrict every bag while keeping the parent forest, ranks and top assignments. -/
def induce (T : CliqueTree G ι) (s : Set V) [DecidablePred (· ∈ s)] :
    CliqueTree (G.induce s) ι where
  bag := fun i => (T.bag i).subtype (· ∈ s)
  parent := T.parent
  rank := T.rank
  top := fun v => T.top v.val
  rank_injective := T.rank_injective
  rank_parent_lt := T.rank_parent_lt
  bag_isClique := by
    intro i a ha b hb hab
    exact T.bag_isClique i (by simpa using ha) (by simpa using hb)
      (fun he => hab (Subtype.ext he))
  mem_bag_top := by intro v; simpa using T.mem_bag_top v.val
  exists_bag_of_adj := by
    intro u v huv
    obtain ⟨i, hu, hv⟩ := T.exists_bag_of_adj huv
    exact ⟨i, by simpa using hu, by simpa using hv⟩
  mem_bag_parent := by
    intro i v hv hi
    obtain ⟨j, hj, hvj⟩ := T.mem_bag_parent (by simpa using hv) hi
    exact ⟨j, hj, by simpa using hvj⟩

/-- A surviving vertex belongs to exactly the same indexed bags after restriction. -/
@[simp] theorem mem_induce_bag (T : CliqueTree G ι) (s : Set V)
    [DecidablePred (· ∈ s)] (i : ι) (v : s) :
    v ∈ (T.induce s).bag i ↔ v.val ∈ T.bag i := by
  simp [induce]

/-- Relabel a clique forest without changing its indexed topology. -/
def mapIso (T : CliqueTree G ι) (f : G ≃g H) : CliqueTree H ι where
  bag := fun i => (T.bag i).map f.toEquiv.toEmbedding
  parent := T.parent
  rank := T.rank
  top := fun v => T.top (f.symm v)
  rank_injective := T.rank_injective
  rank_parent_lt := T.rank_parent_lt
  bag_isClique := by
    intro i a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    exact f.map_rel_iff.mpr (T.bag_isClique i ha' hb' (fun he => hab (congrArg f he)))
  mem_bag_top := by
    intro v
    exact Finset.mem_map.mpr ⟨f.symm v, T.mem_bag_top _, f.apply_symm_apply v⟩
  exists_bag_of_adj := by
    intro u v huv
    obtain ⟨i, hu, hv⟩ := T.exists_bag_of_adj (f.symm.map_rel_iff.mpr huv)
    exact ⟨i, Finset.mem_map.mpr ⟨_, hu, f.apply_symm_apply u⟩,
      Finset.mem_map.mpr ⟨_, hv, f.apply_symm_apply v⟩⟩
  mem_bag_parent := by
    intro i v hv hi
    obtain ⟨v', hv', he⟩ := Finset.mem_map.mp hv
    have hval : v' = f.symm v := by simpa using congrArg f.symm he
    obtain ⟨j, hj, hvj⟩ := T.mem_bag_parent hv' (by simpa only [hval] using hi)
    exact ⟨j, hj, Finset.mem_map.mpr ⟨_, hvj, he⟩⟩

/-- Membership in a relabelled bag is tested at the inverse image of the vertex. -/
@[simp] theorem mem_mapIso_bag (T : CliqueTree G ι) (f : G ≃g H) (i : ι) (v : W) :
    v ∈ (T.mapIso f).bag i ↔ f.symm v ∈ T.bag i := by
  simp only [mapIso, Finset.mem_map]
  constructor
  · rintro ⟨u, hu, he⟩
    have hval : u = f.symm v := by simpa using congrArg f.symm he
    simpa only [hval] using hu
  · intro hv
    exact ⟨f.symm v, hv, f.apply_symm_apply v⟩

/-- Restriction preserves the parent forest exactly, including all of its roots. -/
@[simp] theorem induce_parent (T : CliqueTree G ι) (s : Set V)
    [DecidablePred (· ∈ s)] : (T.induce s).parent = T.parent := rfl

/-- Relabelling preserves the parent forest exactly. -/
@[simp] theorem mapIso_parent (T : CliqueTree G ι) (f : G ≃g H) :
    (T.mapIso f).parent = T.parent := rfl

end CliqueTree

end SimpleGraph
