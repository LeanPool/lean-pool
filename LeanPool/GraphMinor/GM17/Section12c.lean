/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section12b

/-!
# Graph Minors XVII, Section 12: the embodiment of a tangle

This file proves (12.5) of Robertson and Seymour, *Graph Minors. XVII. Taming a Vortex*, J. Combin.
Theory Ser. B 77 (1999), 200: from a tangle `𝒯*` in the 1-skeleton `G*` we get a tangle in `G`,
called the embodiment of `𝒯*` in `G`.

- **(12.5)** (`theorem_12_5`, page 200).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- An edge of `A ≤ G` joins, in `A*`, any two distinct ends it has in `G`. -/
theorem skeleton_adj_of_mem {G A : Hypergraph α β} (hA : A ≤ G) {e : β}
  (he : e ∈ A.edgeSet) {x y : α}
    (hx : G.Inc e x) (hy : G.Inc e y) (hne : x ≠ y) : A.skeleton.Adj x y := by
  have h := hA.ends_eq e he
  have h' : ∀ z, G.Inc e z → A.Inc e z := fun z hz => by
    have : z ∈ G.ends e := hz
    rw [h] at this
    exact this
  exact ⟨hne, e, h' x hx, h' y hy⟩

/-- `H ≤ G` gives `H* ≤ G*`. -/
theorem oneSkeleton_le {G A : Hypergraph α β} (hA : A ≤ G) : oneSkeletonHypergraph A
  ≤ oneSkeletonHypergraph G := by
  have hE : A.skeleton.edgeSet ⊆ G.skeleton.edgeSet := by
    intro s hs
    induction s using Sym2.ind with
    | _ x y =>
      obtain ⟨hne, e, hx, hy⟩ := (SimpleGraph.mem_edgeSet _).1 hs
      have he := A.edge_mem_of_inc hx
      have hsub : A.ends e ⊆ G.ends e := by rw [hA.ends_eq e he]
      exact (SimpleGraph.mem_edgeSet _).2 ⟨hne, e, hsub hx, hsub hy⟩
  refine ⟨hA.vertexSet_subset, hE, fun s hs => ?_⟩
  ext v
  exact ⟨fun h => ⟨hs, h.2⟩, fun h => ⟨hE hs, h.2⟩⟩

/-- `(A₁ ∪ A₂ ∪ A₃)* = A₁* ∪ A₂* ∪ A₃*` when the `Aᵢ` are subhypergraphs of `A₁ ∪ A₂ ∪ A₃`. -/
theorem oneSkeleton_union {G A₁ A₂ A₃ : Hypergraph α β} (h : A₁ ∪ A₂ ∪ A₃ = G) (h₁ : A₁ ≤ G)
  (h₂ : A₂ ≤ G) (h₃ : A₃ ≤ G) :
    oneSkeletonHypergraph A₁ ∪ oneSkeletonHypergraph A₂ ∪ oneSkeletonHypergraph A₃
      = oneSkeletonHypergraph G := by
  have hE : ∀ s, s ∈ G.skeleton.edgeSet → s ∈ A₁.skeleton.edgeSet ∨ s ∈ A₂.skeleton.edgeSet
    ∨ s ∈ A₃.skeleton.edgeSet := by
    intro s hs
    induction s using Sym2.ind with
    | _ x y =>
      obtain ⟨hne, e, hx, hy⟩ := (SimpleGraph.mem_edgeSet _).1 hs
      have he : e ∈ (A₁ ∪ A₂ ∪ A₃).edgeSet := h ▸ G.edge_mem_of_inc hx
      rcases he with (he | he) | he
      · exact .inl ((SimpleGraph.mem_edgeSet _).2 (skeleton_adj_of_mem h₁ he hx hy hne))
      · exact .inr (.inl ((SimpleGraph.mem_edgeSet _).2 (skeleton_adj_of_mem h₂ he hx hy hne)))
      · exact .inr (.inr ((SimpleGraph.mem_edgeSet _).2 (skeleton_adj_of_mem h₃ he hx hy hne)))
  have hle : ∀ {A : Hypergraph α β}, A ≤ G → A.skeleton.edgeSet ⊆ G.skeleton.edgeSet := fun hA =>
    (oneSkeleton_le hA).edgeSet_subset
  refine Hypergraph.ext ?_ ?_ ?_
  · rw [← h]; rfl
  · refine Subset.antisymm ?_ fun s hs => ?_
    · rintro s ((hs | hs) | hs)
      exacts [hle h₁ hs, hle h₂ hs, hle h₃ hs]
    · rcases hE s hs with hs | hs | hs
      exacts [.inl (.inl hs), .inl (.inr hs), .inr hs]
  · funext s v
    apply propext
    constructor
    · rintro ((hs | hs) | hs)
      exacts [⟨hle h₁ hs.1, hs.2⟩, ⟨hle h₂ hs.1, hs.2⟩, ⟨hle h₃ hs.1, hs.2⟩]
    · rintro ⟨hs, hv⟩
      rcases hE s hs with hs | hs | hs
      exacts [.inl (.inl ⟨hs, hv⟩), .inl (.inr ⟨hs, hv⟩), .inr ⟨hs, hv⟩]

/-- Deleting edges keeps a subhypergraph. -/
theorem deleteEdges_le (G : Hypergraph α β) (F : Set β) : G.deleteEdges F ≤ G :=
  ⟨subset_rfl, sdiff_subset, fun f hf => by
    ext v
    exact ⟨fun h => ⟨h, hf.2⟩, fun h => h.1⟩⟩

/-- The separation `(A, B \ E(A))` of `G`, made from a separation with `V(A) ∪ V(B) = V(G)`. -/
theorem isSeparation_deleteEdges {G A B : Hypergraph α β} (hA : A ≤ G) (hB : B ≤ G)
  (hV : A.vertexSet ∪ B.vertexSet = G.vertexSet)
    (hE : A.edgeSet ∪ B.edgeSet = G.edgeSet) : G.IsSeparation A (B.deleteEdges A.edgeSet) := by
  refine (isSeparation_iff_of_le hA ((deleteEdges_le B _).trans hB)).2 ⟨hV, ?_, ?_⟩
  · rw [← hE]
    ext e
    change e ∈ A.edgeSet ∨ e ∈ B.edgeSet \ A.edgeSet ↔ _
    by_cases h : e ∈ A.edgeSet <;> simp [h]
  · ext e
    change e ∈ A.edgeSet ∩ (B.edgeSet \ A.edgeSet) ↔ _
    simp

/-- A separation of `G` covers the edges of `G*`. -/
theorem edgeSet_oneSkeleton_union {G A B : Hypergraph α β} (hsep : G.IsSeparation A B) :
    (oneSkeletonHypergraph A).edgeSet ∪ (oneSkeletonHypergraph B).edgeSet =
      (oneSkeletonHypergraph G).edgeSet := by
  have hA := oneSkeleton_le hsep.left_le
  have hB := oneSkeleton_le hsep.right_le
  refine Subset.antisymm (union_subset hA.edgeSet_subset hB.edgeSet_subset) fun t ht => ?_
  induction t using Sym2.ind with
  | _ x y =>
    obtain ⟨hne, e, hx, hy⟩ := (SimpleGraph.mem_edgeSet _).1 ht
    have he : e ∈ A.edgeSet ∪ B.edgeSet := hsep.edgeSet_union ▸ G.edge_mem_of_inc hx
    rcases he with he | he
    · exact .inl ((SimpleGraph.mem_edgeSet _).2 (skeleton_adj_of_mem hsep.left_le he hx hy hne))
    · exact .inr ((SimpleGraph.mem_edgeSet _).2 (skeleton_adj_of_mem hsep.right_le he hx hy hne))

/-- A separation `(A, B)` of `G` gives the separation `(A*, B* \ E(A*))` of `G*`, on the same
vertices. -/
theorem isSeparation_oneSkeleton {G A B : Hypergraph α β} (hsep : G.IsSeparation A B) :
    (oneSkeletonHypergraph G).IsSeparation (oneSkeletonHypergraph A)
      ((oneSkeletonHypergraph B).deleteEdges (oneSkeletonHypergraph A).edgeSet) :=
  isSeparation_deleteEdges (oneSkeleton_le hsep.left_le) (oneSkeleton_le hsep.right_le)
    hsep.vertexSet_union
    (edgeSet_oneSkeleton_union hsep)

/-- **Graph Minors XVII, (12.5)** (page 200): "Let $G$ be a hypergraph, and let $\mathscr{T}^*$ be a
tangle in $G^*$ of order $\theta$. Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$
of order $<\theta$ such that $A^*$ is small relative to $\mathscr{T}^*$. Then $\mathscr{T}$ is a
tangle in $G$ of order $\theta$." -/
theorem theorem_12_5_proof {G : Hypergraph α β} {θ : ℕ} {𝒯s : Set (Hypergraph α
  (Sym2 α) × Hypergraph α (Sym2 α))}
    (h𝒯 : IsTangle (oneSkeletonHypergraph G) θ 𝒯s) : IsTangle G θ (embodimentTangle G 𝒯s θ) := by
  refine ⟨h𝒯.one_le, fun _ _ h => h.1, fun _ _ h => h.2.1, ?_, ?_, ?_⟩
  · intro A B hsep hord
    have hA := oneSkeleton_le hsep.left_le
    have hB := oneSkeleton_le hsep.right_le
    have hV : A.vertexSet ∪ B.vertexSet = G.vertexSet := hsep.vertexSet_union
    have hE := edgeSet_oneSkeleton_union hsep
    have hs₁ := isSeparation_deleteEdges hA hB hV hE
    have hs₂ := isSeparation_deleteEdges hB hA
      (by rwa [Set.union_comm]) (by rwa [Set.union_comm])
    have ho₁ : separationOrder (oneSkeletonHypergraph A) ((oneSkeletonHypergraph B).deleteEdges
      (oneSkeletonHypergraph A).edgeSet) < θ := hord
    have ho₂ : separationOrder (oneSkeletonHypergraph B) ((oneSkeletonHypergraph A).deleteEdges
      (oneSkeletonHypergraph B).edgeSet) < θ := by
      change (B.vertexSet ∩ A.vertexSet).ncard < θ
      rw [Set.inter_comm]; exact hord
    rcases h𝒯.axiom1 hs₁ ho₁ with h | h
    · exact .inl ⟨hsep, hord, _, h⟩
    · have hord' : separationOrder B A < θ := by
        change (B.vertexSet ∩ A.vertexSet).ncard < θ
        rw [Set.inter_comm]; exact hord
      exact .inr ⟨hsep.symm, hord', _, GM10.theorem_2_9_proof h𝒯 h hs₂ ho₂ (.inr (.inl subset_rfl))⟩
  · rintro A₁ B₁ A₂ B₂ A₃ B₃ ⟨hs₁, -, C₁, h₁⟩ ⟨hs₂, -, C₂, h₂⟩ ⟨hs₃, -, C₃, h₃⟩ hG
    exact h𝒯.axiom2 h₁ h₂ h₃ (oneSkeleton_union hG hs₁.left_le hs₂.left_le hs₃.left_le)
  · rintro A B ⟨-, -, C, h⟩ hV
    exact h𝒯.axiom3 h hV

end GraphMinor.GM17
