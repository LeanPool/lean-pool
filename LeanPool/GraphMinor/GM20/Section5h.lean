/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5g

/-!
# Tools for (5.5) of Graph Minors XX

Here each member of `ℒ` lies on one side of each member of a set `ℳ` of separations. The location
`ℒ' = ℒ₁ ∪ {f(A, B) : (A, B) ∈ ℳ}` swallows each member of `ℒ` lying on the side `A` of some
`(A, B) ∈ ℳ`. This file does the part that needs no tangles: `ℒ'` is a fine rooted location, and its
heart is obtained from the heart of `ℒ` as in (4.13).

A member of `ℒ` may lie on the small side of several members of `ℳ`, when it has no edges. Each such
member gets one owner in `ℳ`, as the edges of a rooted location in the heart must be disjoint.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

open Classical in
/-- The rooted hypergraph `f(A, B)`, with `f(A, B)⁻ = A` and `πBar(f(A, B)) = V(A ∩ B)`. -/
noncomputable def sepRooted (A B : Hypergraph α β) : RootedHypergraph α β where
  toHypergraph := A
  roots := (A ∩ B).vertexSet_finite.toFinset.toList
  roots_nodup := Finset.nodup_toList _
  roots_subset v hv := by
    have h : v ∈ (A ∩ B).vertexSet := by simpa using hv
    exact h.1

theorem mem_sepRooted_rootSet {A B : Hypergraph α β} {v : α} :
    v ∈ (sepRooted A B).rootSet ↔ v ∈ (A ∩ B).vertexSet := by
  classical
  change v ∈ (A ∩ B).vertexSet_finite.toFinset.toList ↔ _
  simp

/-- The data of (5.5). -/
structure SideData (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β))
    (ℳ : Set (Hypergraph α β × Hypergraph α β)) : Prop where
  rootless : G.rootSet = ∅
  sep : ∀ p ∈ ℳ, G.toHypergraph.IsSeparation p.1 p.2
  cross : ∀ p ∈ ℳ, ∀ q ∈ ℳ, p ≠ q → p.1 ≤ q.2
  loc : IsRootedLocation G ℒ
  fine : IsFine G ℒ
  side : ∀ C ∈ ℒ, ∀ p ∈ ℳ, (C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph G C) ∨
    (C.toHypergraph ≤ p.2 ∧ p.1 ≤ complementHypergraph G C)
  inj : ∀ p ∈ ℳ, ∀ q ∈ ℳ, p.1 = q.1 → p = q

/-- The set `ℒ₁`. -/
def mainSet (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β))
    (ℳ : Set (Hypergraph α β × Hypergraph α β)) : Set (RootedHypergraph α β) :=
  {C ∈ ℒ | ¬ ∃ p ∈ ℳ, C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph G C}

/-- The set `ℒ' = ℒ₁ ∪ {f(A, B) : (A, B) ∈ ℳ}`. -/
noncomputable def sideSet (G : RootedHypergraph α β) (ℒ : Set (RootedHypergraph α β))
    (ℳ : Set (Hypergraph α β × Hypergraph α β)) : Set (RootedHypergraph α β) :=
  mainSet G ℒ ℳ ∪ (fun p ↦ sepRooted p.1 p.2) '' ℳ

variable {G : RootedHypergraph α β} {ℒ : Set (RootedHypergraph α β)}
  {ℳ : Set (Hypergraph α β × Hypergraph α β)}

theorem isComplemented_sepRooted (hr : G.rootSet = ∅) {A B : Hypergraph α β}
    (h : G.toHypergraph.IsSeparation A B) : IsComplemented G (sepRooted A B) := by
  refine ⟨h.left_le, fun v _ hv ↦ ?_, fun v e hv he hinc ↦ ?_⟩
  · rw [hr] at hv
    exact hv.elim
  · refine mem_sepRooted_rootSet.mpr ⟨hv, ?_⟩
    have heB : e ∈ A.edgeSet ∪ B.edgeSet := by
      rw [h.edgeSet_union]
      exact he.1
    have heB' := heB.resolve_left he.2
    have h₁ : v ∈ G.ends e := hinc
    rw [h.right_le.ends_eq e heB'] at h₁
    exact B.vertex_mem_of_inc h₁

theorem complementHypergraph_sepRooted (hr : G.rootSet = ∅) {A B : Hypergraph α β}
    (h : G.toHypergraph.IsSeparation A B) : complementHypergraph G (sepRooted A B) = B := by
  refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (complementHypergraph_le (isComplemented_sepRooted hr h)) h.right_le ?_ ?_
  · ext v
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · have : v ∈ A.vertexSet ∪ B.vertexSet := by
          rw [h.vertexSet_union]
          exact h₁
        exact this.resolve_left h₂
      · exact (mem_sepRooted_rootSet.mp h₂).2
    · intro hv
      have hvG : v ∈ G.vertexSet := h.right_le.vertexSet_subset hv
      by_cases hvA : v ∈ A.vertexSet
      · exact Or.inr ⟨hvG, mem_sepRooted_rootSet.mpr ⟨hvA, hv⟩⟩
      · exact Or.inl ⟨hvG, hvA⟩
  · ext e
    constructor
    · rintro ⟨h₁, h₂⟩
      have : e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [h.edgeSet_union]
        exact h₁
      exact this.resolve_left h₂
    · exact fun he ↦ ⟨h.right_le.edgeSet_subset he, fun he' ↦
        IsSeparation.not_mem_of_mem h he' he⟩

theorem mem_rootSet_of_le_complement {C : RootedHypergraph α β} {X : Hypergraph α β}
    (hX : X ≤ complementHypergraph G C) {v : α} (hv : v ∈ X.vertexSet) (hvC : v ∈ C.vertexSet) :
    v ∈ C.rootSet := by
  rcases hX.vertexSet_subset hv with h | h
  · exact absurd hvC h.2
  · exact h.2

namespace SideData

variable (hD : SideData G ℒ ℳ)

include hD

theorem main_side {C} (hC : C ∈ mainSet G ℒ ℳ) {p} (hp : p ∈ ℳ) :
    C.toHypergraph ≤ p.2 ∧ p.1 ≤ complementHypergraph G C := by
  rcases hD.side C hC.1 p hp with h | h
  · exact absurd ⟨p, hp, h⟩ hC.2
  · exact h

theorem sep_notMem_main {p} (hp : p ∈ ℳ) : sepRooted p.1 p.2 ∉ mainSet G ℒ ℳ := fun h ↦
  h.2 ⟨p, hp, le_rfl, (complementHypergraph_sepRooted hD.rootless (hD.sep p hp)).ge⟩

theorem isComplemented {L} (hL : L ∈ sideSet G ℒ ℳ) : IsComplemented G L := by
  rcases hL with h | ⟨p, hp, rfl⟩
  · exact hD.loc.isComplemented h.1
  · exact isComplemented_sepRooted hD.rootless (hD.sep p hp)

theorem isRootedLocation : IsRootedLocation G (sideSet G ℒ ℳ) := by
  refine ⟨fun _ h ↦ hD.isComplemented h, ?_⟩
  intro L₁ h₁ L₂ h₂ hne
  rw [complement_toHypergraph]
  rcases h₁ with h₁ | ⟨p, hp, rfl⟩ <;> rcases h₂ with h₂ | ⟨q, hq, rfl⟩
  · have := hD.loc.le_complement h₁.1 h₂.1 hne
    rwa [complement_toHypergraph] at this
  · rw [complementHypergraph_sepRooted hD.rootless (hD.sep q hq)]
    exact (hD.main_side h₁ hq).1
  · exact (hD.main_side h₂ hp).2
  · rw [complementHypergraph_sepRooted hD.rootless (hD.sep q hq)]
    exact hD.cross p hp q hq fun h ↦ hne (by rw [h])

theorem isFine : IsFine G (sideSet G ℒ ℳ) := by
  refine ⟨fun v hv ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨C, hC, hvC⟩ := hD.fine.1 v hv
    by_cases hm : C ∈ mainSet G ℒ ℳ
    · exact ⟨C, Or.inl hm, hvC⟩
    · have : ∃ p ∈ ℳ, C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph G C := by
        by_contra hn
        exact hm ⟨hC, hn⟩
      obtain ⟨p, hp, h₁, -⟩ := this
      exact ⟨_, Or.inr ⟨p, hp, rfl⟩, h₁.vertexSet_subset hvC⟩
  · obtain ⟨C, hC, hvC⟩ := hD.fine.2 e he
    by_cases hm : C ∈ mainSet G ℒ ℳ
    · exact ⟨C, Or.inl hm, hvC⟩
    · have : ∃ p ∈ ℳ, C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph G C := by
        by_contra hn
        exact hm ⟨hC, hn⟩
      obtain ⟨p, hp, h₁, -⟩ := this
      exact ⟨_, Or.inr ⟨p, hp, rfl⟩, h₁.edgeSet_subset hvC⟩

/-- `V(A ∩ B) ⊆ V(M(G, ℒ))`, since each member of `ℒ` lies on one side of `(A, B)`. -/
theorem sep_mem_core {p} (hp : p ∈ ℳ) {v : α} (hv : v ∈ (p.1 ∩ p.2).vertexSet) :
    v ∈ (rootedLocationCore G ℒ).vertexSet := by
  refine mem_core_iff.mpr ⟨(hD.sep p hp).left_le.vertexSet_subset hv.1, fun C hC hvC ↦ ?_⟩
  rcases hD.side C hC p hp with h | h
  · exact mem_rootSet_of_le_complement h.2 hv.2 hvC
  · exact mem_rootSet_of_le_complement h.2 hv.1 hvC

omit hD in
theorem core_subset : (rootedLocationCore G (sideSet G ℒ ℳ)).vertexSet ⊆
    (rootedLocationCore G ℒ).vertexSet := by
  intro v hv
  obtain ⟨hvG, hall⟩ := mem_core_iff.mp hv
  refine mem_core_iff.mpr ⟨hvG, fun C hC hvC ↦ ?_⟩
  by_cases hm : C ∈ mainSet G ℒ ℳ
  · exact hall C (Or.inl hm) hvC
  · have : ∃ p ∈ ℳ, C.toHypergraph ≤ p.1 ∧ p.2 ≤ complementHypergraph G C := by
      by_contra hn
      exact hm ⟨hC, hn⟩
    obtain ⟨p, hp, h₁, h₂⟩ := this
    have hr := hall _ (Or.inr ⟨p, hp, rfl⟩) (h₁.vertexSet_subset hvC)
    exact mem_rootSet_of_le_complement h₂ (mem_sepRooted_rootSet.mp hr).2 hvC

end SideData

/-- A heart of a fine rooted location is active. -/
theorem heart_isActive {P Q : UnlabeledPatchwork α β} {e : RootedHypergraph α β → β}
    (hfine : IsFine P.G ℒ) (hQ : IsPatchworkHeart P ℒ e Q) : IsActive Q := by
  intro v hv
  rw [hQ.vertexSet_eq] at hv
  obtain ⟨hvG, hall⟩ := mem_core_iff.mp hv
  obtain ⟨C, hC, hvC⟩ := hfine.1 v hvG
  refine ⟨e C, ?_, (hQ.inc_iff hfine).mpr ⟨C, hC, rfl, hall C hC hvC⟩⟩
  rw [hQ.dom_eq_image hfine]
  exact ⟨C, hC, rfl⟩

/-- The set of the relation in (4.13): `P₂` comes from `P₁ ∈ 𝓕₁` by replacing at most `w` disjoint
parts by single edges with at most `k` ends. -/
def locationReplaced (𝓕₁ : Set (UnlabeledPatchwork α β)) (k w : ℕ) :
    Set (UnlabeledPatchwork α β) :=
  {P₂ | ∃ F ⊆ P₂.dom, F.ncard ≤ w ∧ ∃ P₁ ∈ 𝓕₁, ∃ A : β → RootedHypergraph α β,
      IsRootedLocation P₁.G (A '' F) ∧ P₂.G.roots = P₁.G.roots ∧
      P₂.G.toHypergraph.deleteEdges F = rootedLocationCore P₁.G (A '' F) ∧
      IsCompletionOf (P₁.restrict (P₂.G.deleteEdges F)) (P₂.deleteEdges F) ∧
      ∀ f ∈ F, (A f).roots = P₂.μ f ∧ (P₂.G.ends f).ncard ≤ k}

theorem wellBehaved_locationReplaced {𝓕₁ : Set (UnlabeledPatchwork α β)} (h : WellBehaved 𝓕₁)
    (ha : ∀ P ∈ 𝓕₁, IsActive P) (k w : ℕ) : WellBehaved (locationReplaced 𝓕₁ k w) :=
  theorem_4_13_proof h ha k w fun _ h ↦ h

/-- A finite set has an injective map into an infinite type which avoids a given finite set. -/
theorem exists_injOn_avoid {γ δ : Type*} [Infinite δ] {s : Set γ} (hs : s.Finite) {T : Set δ}
    (hT : T.Finite) : ∃ f : γ → δ, InjOn f s ∧ ∀ x, f x ∉ T := by
  have : Infinite (Tᶜ : Set δ) := hT.infinite_compl.to_subtype
  have : Nonempty (Tᶜ : Set δ) := inferInstance
  obtain ⟨f, hf⟩ := exists_injOn_of_finite (δ := (Tᶜ : Set δ)) hs
  exact ⟨fun x ↦ (f x).1, fun x hx y hy h ↦ hf hx hy (Subtype.ext h), fun x ↦ (f x).2⟩

end GraphMinor.GM20
