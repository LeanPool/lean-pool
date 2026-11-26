/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section5b

/-!
# Tools for tangles and rooted locations

The proofs of (5.3)–(5.5) of Graph Minors XX use a few plain facts about the separation
`(A⁻, (G \ A)⁻)` of a complemented `A`, and about `ℳ(𝒯, W, θ)`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem complement_toHypergraph {G A : RootedHypergraph α β} (hA : IsComplemented G A) :
    (complement G A hA).toHypergraph = complementHypergraph G A := by
  have hsub : ∀ {v}, v ∈ A.rootSet → v ∈ G.vertexSet := fun hv ↦
    hA.le.vertexSet_subset (A.roots_subset _ hv)
  have hV : (G.vertexSet \ A.vertexSet) ∪ (G.vertexSet ∩ A.rootSet) =
      (G.vertexSet \ A.vertexSet) ∪ A.rootSet := by
    ext v
    exact or_congr_right ⟨fun h ↦ h.2, fun h ↦ ⟨hsub h, h⟩⟩
  apply Hypergraph.ext
  · exact hV.symm
  · rfl
  · funext e v
    apply propext
    constructor
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      rw [hV]
      exact (complement G A hA).vertex_mem_of_inc h
    · exact fun h ↦ ⟨h.1, h.2.1⟩

theorem complementHypergraph_le {G A : RootedHypergraph α β} (hA : IsComplemented G A) :
    complementHypergraph G A ≤ G.toHypergraph := by
  refine ⟨?_, fun _ h ↦ h.1, fun e he ↦ ?_⟩
  · rintro v (h | h)
    · exact h.1
    · exact h.1
  · ext v
    constructor
    · intro hinc
      have hG : G.Inc e v := hinc
      refine ⟨he, hG, ?_⟩
      by_cases hvA : v ∈ A.vertexSet
      · exact Or.inr ⟨G.vertex_mem_of_inc hG, hA.inc_diff_mem hvA he hG⟩
      · exact Or.inl ⟨G.vertex_mem_of_inc hG, hvA⟩
    · exact fun h ↦ h.2.1

/-- `(A⁻, (G \ A)⁻)` is a separation of `G⁻`. -/
theorem isSeparation_complement {G A : RootedHypergraph α β} (hA : IsComplemented G A) :
    G.toHypergraph.IsSeparation A.toHypergraph (complementHypergraph G A) := by
  rw [isSeparation_iff_of_le hA.le (complementHypergraph_le hA)]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro (h | h | h)
      · exact hA.le.vertexSet_subset h
      · exact h.1
      · exact h.1
    · intro h
      by_cases hvA : v ∈ A.vertexSet
      · exact Or.inl hvA
      · exact Or.inr (Or.inl ⟨h, hvA⟩)
  · ext e
    constructor
    · rintro (h | h)
      · exact hA.le.edgeSet_subset h
      · exact h.1
    · intro h
      by_cases heA : e ∈ A.edgeSet
      · exact Or.inl heA
      · exact Or.inr ⟨h, heA⟩
  · ext e
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun h₁ h₂ ↦ h₂.2 h₁

/-- The order of `(A⁻, (G \ A)⁻)` is at most `|πBar(A)|`. -/
theorem separationOrder_complement_le {G A : RootedHypergraph α β} :
    separationOrder A.toHypergraph (complementHypergraph G A) ≤ A.rootSet.ncard := by
  refine Set.ncard_le_ncard ?_ (List.finite_toSet _)
  rintro v ⟨h₁, h₂ | h₂⟩
  · exact absurd h₁ h₂.2
  · exact h₂.2

theorem order_le_of_lam_le {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β} (h₁ : G.IsSeparation A B) (h₂ : G.IsSeparation C D)
    (h : lam (A, B) ≤ lam (C, D)) : separationOrder A B ≤ separationOrder C D := by
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.mpr (hTB.axiom3 h₂ h₁ hlt))

/-- There are finitely many subhypergraphs of `G`. -/
theorem finite_le (G : Hypergraph α β) : {H | H ≤ G}.Finite := by
  have hfin : ((G.vertexSet.powerset ×ˢ G.edgeSet.powerset :
      Set (Set α × Set β))).Finite :=
    G.vertexSet_finite.finite_subsets.prod G.edgeSet_finite.finite_subsets
  refine Set.Finite.of_finite_image (f := fun H ↦ (H.vertexSet, H.edgeSet)) (hfin.subset ?_) ?_
  · rintro _ ⟨H, hH, rfl⟩
    exact ⟨hH.vertexSet_subset, hH.edgeSet_subset⟩
  · intro H₁ h₁ H₂ h₂ heq
    exact eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁ h₂ (congrArg Prod.fst heq)
      (congrArg Prod.snd heq)

variable {Λ : Type*} [LinearOrder Λ] {lam : Hypergraph α β × Hypergraph α β → Λ}
  {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {W : Set (α ⊕ β)} {θ θ₀ : ℕ}

theorem finite_inM (h𝒯 : IsTangle G θ₀ 𝒯) :
    {p : Hypergraph α β × Hypergraph α β | InM lam G 𝒯 W θ p.1 p.2}.Finite := by
  refine ((finite_le G).prod (finite_le G)).subset ?_
  intro p hp
  have hsep : G.IsSeparation p.1 p.2 := h𝒯.isSeparation hp.1.1
  exact ⟨hsep.left_le, hsep.right_le⟩

/-- Every `(A, B)` satisfying the first two conditions of `ℳ(𝒯, W, θ)` lies below a member of
`ℳ(𝒯, W, θ)`, since there are finitely many separations of `G`. -/
theorem exists_inM_above (h𝒯 : IsTangle G θ₀ 𝒯) {A B : Hypergraph α β}
    (h : InMPre lam G 𝒯 W θ A B) : ∃ A' B', InM lam G 𝒯 W θ A' B' ∧ A ≤ A' ∧ B' ≤ B := by
  classical
  let S : Set (Hypergraph α β × (Hypergraph α β)ᵒᵈ) :=
    {p | InMPre lam G 𝒯 W θ p.1 (OrderDual.ofDual p.2)}
  have hfin : S.Finite := by
    refine (((finite_le G).prod (finite_le G)).image
      (fun p ↦ (p.1, OrderDual.toDual p.2))).subset ?_
    intro p hp
    have hsep : G.IsSeparation p.1 (OrderDual.ofDual p.2) := h𝒯.isSeparation hp.1
    exact ⟨(p.1, OrderDual.ofDual p.2), ⟨hsep.left_le, hsep.right_le⟩, rfl⟩
  obtain ⟨m, hle, hmax⟩ := hfin.exists_le_maximal (a := (A, OrderDual.toDual B)) h
  refine ⟨m.1, OrderDual.ofDual m.2, ⟨hmax.prop, ?_⟩, hle.1, hle.2⟩
  rintro A' B' hpre hne ⟨h₁, h₂⟩
  have hm : (A', OrderDual.toDual B') ∈ S := hpre
  have hlem : m ≤ (A', OrderDual.toDual B') := ⟨h₁, h₂⟩
  have hge := hmax.le_of_ge hm hlem
  exact hne (Prod.ext (le_antisymm hge.1 h₁) (le_antisymm h₂ hge.2))

/-- If `(C, D)` has `D ⊆ B'` and `(B', A')` is in a tangle of order `> ` the order of `(C, D)`, then
`(D, C)` is in the tangle. -/
theorem mem_tangle_of_le {θ' : ℕ} {𝒯' : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯' : IsTangle G θ' 𝒯') {A' B' C D : Hypergraph α β} (hsep : G.IsSeparation C D)
    (hlt : separationOrder C D < θ') (hmem : (B', A') ∈ 𝒯') (hle : D ≤ B') : (D, C) ∈ 𝒯' := by
  rcases h𝒯'.axiom1 hsep hlt with h | h
  · exact (not_le_of_mem_tangle h𝒯' hmem h hle).elim
  · exact h

end GraphMinor.GM20
